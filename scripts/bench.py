#!/usr/bin/env python3
"""Open-library Lean proof completion benchmark; standard-library-only CLI.

Lean elaboration is executable code. This is a local research evaluator, not an
OS sandbox: use a disposable offline environment for untrusted model outputs.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time
import urllib.request
import urllib.parse

import verify_qhl_candidate as trusted

ROOT = Path(__file__).resolve().parents[1]
TASKS = ROOT / 'bench/tasks.json'
LOCK = ROOT / 'bench/benchmark.lock.json'
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}
# Defense in depth, not a sandbox. All acceptance also requires an axiom audit.
FORBIDDEN = re.compile(r'\b(sorry|admit|axiom|unsafe|opaque|initialize|elab|macro|syntax|run_tac|run_elab|native_decide|ofReduceBool|set_option|import|namespace|end|theorem|instance|def)\b|#|/\*|/\-|\-/')


def dump(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')


def load_tasks():
    data = json.loads(TASKS.read_text())
    tasks = data['tasks']
    if len({t['id'] for t in tasks}) != len(tasks):
        raise ValueError('Duplicate task IDs')
    return {t['id']: t for t in tasks}


def fingerprint():
    snapshot = trusted.snapshot()
    paths = [TASKS, ROOT/'scripts/bench.py', ROOT/'bench/references.jsonl', ROOT/'QuantumLeanLeap.lean']
    paths += sorted((ROOT/'QuantumLeanLeap').rglob('*.lean'))
    snapshot['benchmark_sha256'] = {str(p.relative_to(ROOT)): trusted.digest(p.read_bytes()) for p in paths}
    return snapshot


def check_lock(raw):
    if fingerprint() != json.loads(raw):
        raise RuntimeError('Benchmark baseline drift: do not refreeze during evaluation')
    if LOCK.read_bytes() != raw:
        raise RuntimeError('Benchmark lock changed during evaluation')


def prompt(task):
    imports = '\n'.join('import ' + x for x in task['imports'])
    return ('Complete the following Lean 4 theorem. Return ONLY a Lean proof term, '
            'usually starting with by. No Markdown fences, declarations, sorry, '
            'admit, axioms or native_decide. Library theorem reuse is allowed. '
            'The theorem type and imports are immutable.\n\n' + imports + '\n' +
            task['context'] + '\ntheorem answer ' + task['goal'] + ' := <PROOF>\n')


def source(task, proof):
    if not isinstance(proof, str) or not proof.strip() or len(proof.encode()) > 32768:
        raise ValueError('Missing proof or proof exceeds 32768 bytes')
    if FORBIDDEN.search(proof):
        raise ValueError('Proof contains forbidden declaration, tactic or placeholder')
    return ('\n'.join('import ' + x for x in task['imports']) + '\n' +
            'set_option maxHeartbeats 800000\nset_option maxRecDepth 2048\n' +
            'namespace QLLBenchSubmission\n' + task['context'] + '\n' +
            'theorem accepted ' + task['goal'] + ' := (\n' + proof + '\n)\n' +
            '#print axioms QLLBenchSubmission.accepted\nend QLLBenchSubmission\n')


def audit(output):
    matches = re.findall(r"'QLLBenchSubmission.accepted' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", output)
    if len(matches) != 1:
        raise ValueError('Missing or duplicate certificate axiom report')
    axioms = [x.strip() for x in matches[0].split(',') if x.strip()]
    if set(axioms) - ALLOWED:
        raise ValueError('Certificate uses unapproved axioms')
    return axioms


def pass_at_k(n, c, k):
    if n < k:
        return None
    return 1.0 if n-c < k else 1-math.comb(n-c, k)/math.comb(n, k)


def summarize(rows, tasks, ks):
    models = {}
    for model in sorted({r['model'] for r in rows}):
        groups = {t: [r for r in rows if r['model'] == model and r['task_id'] == t] for t in tasks}
        per_task = {}
        for t, samples in groups.items():
            c = sum(r['status'] == 'accepted' for r in samples)
            per_task[t] = {'n': len(samples), 'accepted': c,
                           'pass_at_k': {str(k): pass_at_k(len(samples), c, k) for k in ks}}
        scores = {}
        for k in ks:
            values = [t['pass_at_k'][str(k)] for t in per_task.values()]
            scores[str(k)] = None if any(x is None for x in values) else sum(values)/len(values)
        subset = [r for r in rows if r['model'] == model]
        models[model] = {'tasks_total': len(tasks),
                         'tasks_attempted': sum(bool(x) for x in groups.values()),
                         'tasks_solved': sum(t['accepted'] > 0 for t in per_task.values()),
                         'solved_fraction_full_suite': sum(t['accepted'] > 0 for t in per_task.values())/len(tasks),
                         'pass_at_k': scores, 'per_task': per_task,
                         'verification_seconds': sum(r['verification_seconds'] for r in subset),
                         'generation_seconds_reported': sum(r.get('generation_seconds', 0) for r in subset),
                         'usage_reported': [r.get('usage', {}) for r in subset]}
    return models


def evaluate(args):
    tasks = load_tasks()
    raw_lock = LOCK.read_bytes()
    check_lock(raw_lock)
    rows = []
    seen = set()
    samples = []
    for line in args.samples.read_text().splitlines():
        if not line.strip():
            continue
        s = json.loads(line, object_pairs_hook=trusted.unique_object)
        if s.get('task_id') not in tasks or not isinstance(s.get('model'), str) or not s['model']:
            raise ValueError('Unknown task or missing model')
        if type(s.get('attempt')) is not int or s['attempt'] < 0:
            raise ValueError('attempt must be a nonnegative integer')
        key = (s['model'], s['task_id'], s['attempt'])
        if key in seen:
            raise ValueError('Duplicate model/task/attempt')
        seen.add(key)
        samples.append(s)
    if not samples:
        raise ValueError('No samples')
    # Exclusive directory creation prevents stale success reports and overwrite.
    args.output.mkdir(parents=True, exist_ok=False)
    build = subprocess.run(['lake', 'build'], cwd=ROOT, capture_output=True, text=True, timeout=args.build_timeout)
    (args.output/'build.log').write_text(build.stdout + build.stderr)
    if build.returncode:
        raise RuntimeError('Trusted library build failed; no model score produced')
    for i, sample in enumerate(samples):
        check_lock(raw_lock)
        run = args.output / f'{i:05d}'
        run.mkdir()
        start = time.monotonic()
        row = {k: sample[k] for k in ('task_id', 'model', 'attempt')}
        for k in ('usage', 'generation_seconds'):
            if k in sample:
                row[k] = sample[k]
        row['proof_sha256'] = trusted.digest(str(sample.get('proof', '')).encode())
        row['status'] = 'not_certified'
        try:
            if sample.get('generation_error'):
                row.update(status='generation_error', reason=sample['generation_error'])
            else:
                code = source(tasks[sample['task_id']], sample.get('proof'))
                path = run/'Candidate.lean'
                path.write_text(code)
                proc = subprocess.run(['lake', 'env', 'lean', str(path.resolve())], cwd=ROOT,
                                      capture_output=True, text=True, timeout=args.timeout)
                output = proc.stdout + proc.stderr
                (run/'lean.log').write_text(output)
                row['lean_exit'] = proc.returncode
                if proc.returncode == 0:
                    row['axioms'] = audit(output)
                    row['status'] = 'accepted'
                else:
                    row['reason'] = 'Lean did not certify the fixed goal; not a proof of mathematical falsity'
        except subprocess.TimeoutExpired:
            row.update(status='timeout', reason='Lean verification timeout')
        except ValueError as exc:
            row.update(status='rejected_input', reason=str(exc))
        row['verification_seconds'] = time.monotonic()-start
        check_lock(raw_lock)
        rows.append(row)
        dump(run/'result.json', row)
    report = {'schema': 'qll-proof-results-v1', 'track': 'open-library-proof-completion',
              'valid_run': True, 'official_google_benchmark': False,
              'created_utc': datetime.now(timezone.utc).isoformat(),
              'lock_sha256': trusted.digest(raw_lock),
              'samples_sha256': trusted.digest(args.samples.read_bytes()),
              'timeout_seconds': args.timeout, 'models': summarize(rows, tasks, args.k), 'results': rows,
              'interpretation': 'pass@k estimator requires at least k samples for EVERY task. Correlated/adaptive attempts do not support the iid interpretation. Reference selftests are not model scores.'}
    dump(args.output/'report.json', report)
    print(json.dumps({m: {k:v for k,v in d.items() if k not in ('per_task','usage_reported')} for m,d in report['models'].items()},indent=2))


def generate(args):
    tasks = load_tasks()
    check_lock(LOCK.read_bytes())
    parsed = urllib.parse.urlparse(args.base_url)
    if parsed.scheme != 'https' and not (parsed.scheme == 'http' and parsed.hostname in {'localhost','127.0.0.1'}):
        raise ValueError('Use HTTPS, or HTTP on localhost')
    key = os.environ.get(args.key_env)
    if not key:
        raise ValueError(f'Set {args.key_env}; keys are never written to reports')
    # No shell, no automatic agent execution and no external tools granted to models.
    metadata = dict(model=args.model, base_url=args.base_url, samples_per_task=args.samples,
                    temperature=args.temperature, max_tokens=args.max_tokens,
                    timeout=args.timeout, lock_sha256=trusted.digest(LOCK.read_bytes()),
                    task_sha256=trusted.digest(TASKS.read_bytes()))
    with args.output.open('x') as f:
        dump(args.output.with_suffix(args.output.suffix+'.metadata.json'), metadata)
        for task in tasks.values():
            for attempt in range(args.samples):
                started = time.monotonic()
                row = dict(task_id=task['id'],model=args.model,attempt=attempt,proof='')
                body = dict(model=args.model,messages=[dict(role='user',content=prompt(task))],max_tokens=args.max_tokens,temperature=args.temperature)
                req = urllib.request.Request(args.base_url.rstrip('/')+'/chat/completions',data=json.dumps(body).encode(),headers={'Authorization':'Bearer '+key,'Content-Type':'application/json'})
                try:
                    with urllib.request.urlopen(req,timeout=args.timeout) as r:
                        answer = json.load(r)
                    row['proof'] = answer['choices'][0]['message']['content']
                    row['usage'] = answer.get('usage',{})
                except Exception as exc:
                    # Avoid provider error bodies or request headers leaking credentials.
                    row['generation_error'] = type(exc).__name__
                row['generation_seconds'] = time.monotonic()-started
                f.write(json.dumps(row,ensure_ascii=False)+'\n'); f.flush()


def main():
    p=argparse.ArgumentParser(description=__doc__); sub=p.add_subparsers(dest='cmd',required=True)
    sub.add_parser('list')
    ex=sub.add_parser('export'); ex.add_argument('output',type=Path)
    fr=sub.add_parser('freeze'); fr.add_argument('output',type=Path)
    ev=sub.add_parser('evaluate'); ev.add_argument('samples',type=Path); ev.add_argument('--output',type=Path,required=True); ev.add_argument('--timeout',type=int,default=120); ev.add_argument('--build-timeout',type=int,default=1800); ev.add_argument('--k',type=int,nargs='+',default=[1,5])
    g=sub.add_parser('generate'); g.add_argument('--model',required=True); g.add_argument('--base-url',required=True); g.add_argument('--key-env',default='QLEAP_API_KEY'); g.add_argument('--output',type=Path,required=True); g.add_argument('--samples',type=int,default=1); g.add_argument('--max-tokens',type=int,default=4096); g.add_argument('--temperature',type=float,default=0.0); g.add_argument('--timeout',type=int,default=180)
    args=p.parse_args()
    for name in ('timeout','build_timeout','samples','max_tokens'):
        v=getattr(args,name,None)
        if isinstance(v,int) and v<=0: p.error(name+' must be positive')
    if any(k<=0 for k in getattr(args,'k',[])): p.error('k must be positive')
    if args.cmd=='list':
        for t in load_tasks().values(): print(t['id'],t['category'])
    elif args.cmd=='export':
        with args.output.open('x') as f:
            for t in load_tasks().values(): f.write(json.dumps(dict(task_id=t['id'],prompt=prompt(t)),ensure_ascii=False)+'\n')
    elif args.cmd=='freeze':
        with args.output.open('x') as f: json.dump(fingerprint(),f,indent=2)
    elif args.cmd=='evaluate': evaluate(args)
    elif args.cmd=='generate': generate(args)

if __name__=='__main__': main()
