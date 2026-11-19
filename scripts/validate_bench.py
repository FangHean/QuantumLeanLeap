#!/usr/bin/env python3
"""Check all 36 immutable task types, without admitting or solving any goal."""
import json
from pathlib import Path
import re
import subprocess
import tempfile
import bench


def split_goal(header):
    depth = 0
    for i, c in enumerate(header):
        if c in '([{': depth += 1
        elif c in ')]}': depth -= 1
        elif c == ':' and depth == 0:
            return header[:i].strip(), header[i+1:].strip()
    raise ValueError('No top-level type separator')


def main():
    tasks = bench.load_tasks()
    mapping = json.loads((bench.ROOT/'bench/migration.json').read_text())['tasks']
    assert len(tasks) == 36 and sum(len(bench.goals(t)) for t in tasks.values()) == 44
    assert {t['id'] for t in mapping} == set(tasks)
    manifest = json.loads((bench.ROOT/'lake-manifest.json').read_text())
    assert all(p['name'] not in {'QuantumAlg','QAlgBench','cslib'} for p in manifest['packages'])
    for p in (bench.ROOT/'QuantumLeanLeap').rglob('*.lean'):
        assert not re.search(r'\b(sorry|admit|axiom)\b', p.read_text()), p
        assert not re.search(r'^import (QuantumAlg|QAlgBench|Cslib)',p.read_text(),re.M), p
    code = '\n'.join('import '+m for t in tasks.values() for m in t['imports'])
    code += '\nset_option autoImplicit false\nset_option linter.unusedVariables false\n'
    for i,t in enumerate(tasks.values()):
        code += f'\nnamespace TaskTypecheck{i}\nnoncomputable section\n'+t['context']+'\n'
        local = bench.ROOT / (t['imports'][0].replace('.','/')+'.lean')
        actual = local.with_name('Goals.lean').read_text()
        for j,g in enumerate(bench.goals(t)):
            binders, goal = split_goal(g['goal'])
            declaration=f'def obligation_{j} {binders} : Prop :=\n  {goal}'
            assert re.sub(r'\s+','',declaration) in re.sub(r'\s+','',actual), t['id']
            code += declaration+'\n'
        code += f'end\nend TaskTypecheck{i}\n'
    with tempfile.TemporaryDirectory(prefix='qll-types-') as d:
        p=Path(d)/'Types.lean';p.write_text(code)
        result=subprocess.run(['lake','env','lean',str(p)],cwd=bench.ROOT,text=True,capture_output=True,timeout=180)
        if result.returncode: raise RuntimeError(result.stdout+result.stderr)
    print('36 problems / 44 task types checked; no proof placeholders or Alg dependencies.')

if __name__=='__main__': main()
