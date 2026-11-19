#!/usr/bin/env python3
"""Frozen local reset benchmark; accepts JSON data, never candidate Lean code.

This is neither Google's verifier nor Lean Comparator. The checked-in lock,
this verifier, Lean/Lake and dependency installations are trusted. This does
not sandbox a hostile local filesystem, toolchain, or build cache.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
LOCK = ROOT / "verification/reset-release-v6.lock.json"
ARTIFACTS = ROOT / "artifacts/qhl-verification"
SCHEMA = "qhl-reset-v1"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MAX_BYTES, MAX_NODES, MAX_DEPTH = 16384, 63, 12
TIMEOUT = 120


class Rejected(ValueError):
    """Candidate data or generated proof was not certified."""


class EnvironmentMismatch(RuntimeError):
    """The trusted baseline changed or validation could not run."""


def digest(data):
    return hashlib.sha256(data).hexdigest()


def unique_object(pairs):
    obj = {}
    for key, value in pairs:
        if key in obj:
            raise Rejected(f"Duplicate JSON key: {key}")
        obj[key] = value
    return obj


def parse_candidate(raw):
    if len(raw) > MAX_BYTES:
        raise Rejected(f"Candidate exceeds {MAX_BYTES} bytes")
    try:
        doc = json.loads(raw, object_pairs_hook=unique_object)
    except (ValueError, UnicodeError, RecursionError) as exc:
        raise Rejected(f"Invalid JSON: {exc}") from exc
    if not isinstance(doc, dict) or set(doc) != {"schema", "program"} or doc["schema"] != SCHEMA:
        raise Rejected("Expected exactly schema=qhl-reset-v1 and program")
    count = 0

    def emit(node, depth):
        nonlocal count
        count += 1
        if count > MAX_NODES or depth > MAX_DEPTH:
            raise Rejected("Program exceeds node/depth limits")
        if not isinstance(node, dict) or not isinstance(node.get("op"), str):
            raise Rejected("Each node must be an object with a string op")
        op = node["op"]
        if op in {"skip", "x", "z", "measure"} and set(node) == {"op"}:
            return "." + op
        if op == "seq" and set(node) == {"op", "first", "second"}:
            return f"(.seq {emit(node['first'], depth + 1)} {emit(node['second'], depth + 1)})"
        if op == "if_zero" and set(node) == {"op", "zero", "nonzero"}:
            return f"(.ifZero {emit(node['zero'], depth + 1)} {emit(node['nonzero'], depth + 1)})"
        raise Rejected(f"Unknown op or fields: {op!r}")

    return emit(doc["program"], 0)


def proof_source(expression):
    # expression is emitted exclusively from the closed parser above. No raw
    # candidate strings, filenames, budgets, or proof terms enter Lean source.
    return f"""import QuantumLeanLeap.GoogleQHL.Verification.ResetNative
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
namespace QHLSubmission
open QuantumLeanLeap.GoogleQHL
open QuantumLeanLeap.GoogleQHL.Verification
open ResetLanguage Matrix
def candidate : Program := {expression}
theorem semantics : ∀ fuel (s : Store Unit) (rho : Operator 2),
    ((interpApprox candidate.compile fuel (s, rho)).map Prod.snd).sum = resetState 0 rho := by
  intro fuel s rho
  have hf : List.finRange 2 = [0, 1] := rfl
  simp only [candidate, Program.compile, interpApprox, hf, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Circuits.wireMeasurement, Circuits.wireProjector, conjugate, xUnitary, zUnitary,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      resetState, Matrix.single, Matrix.trace, Matrix.diagonal, Matrix.of_apply,
      Matrix.vecMul, dotProduct]
theorem gate_budget : ∀ fuel, worstCost ResetSpec.gateCost candidate.compile fuel ≤ 1 := by
  intro fuel
  norm_num [candidate, Program.compile, worstCost, ResetSpec.gateCost]
theorem measurement_budget : ∀ fuel,
    worstCost ResetSpec.measurementCost candidate.compile fuel ≤ 1 := by
  intro fuel
  norm_num [candidate, Program.compile, worstCost, ResetSpec.measurementCost]
theorem source_certificate : ResetSpec.Contract candidate.compile :=
  ⟨semantics, gate_budget, measurement_budget⟩
theorem accepted : ResetSpec.Contract candidate.toDynamic.compile ∧
    candidate.toDynamic.worstNativeGates ≤ 1 ∧
    (∀ (s : Store Unit) (rho : Operator 2),
      ((candidate.toDynamic.run (s, rho)).map Prod.snd).sum = resetState 0 rho) :=
  ⟨candidate.native_contract source_certificate,
    candidate.native_gate_budget source_certificate,
    candidate.native_output source_certificate⟩
#print axioms accepted
end QHLSubmission
"""


def command(args, timeout=TIMEOUT):
    try:
        return subprocess.run(args, cwd=ROOT, text=True, capture_output=True, timeout=timeout)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise EnvironmentMismatch(f"Could not finish {args[0]}: {exc}") from exc


def git(path, *args):
    result = command(["git", "-C", str(path), *args])
    if result.returncode:
        raise EnvironmentMismatch(result.stderr.strip())
    return result.stdout.strip()


def package_directory_name(name):
    """Lake serializes quoted Lean identifiers with guillemets in its manifest."""
    return name[1:-1] if name.startswith("«") and name.endswith("»") else name


def snapshot():
    files = sorted((ROOT / "QuantumLeanLeap/GoogleQHL").rglob("*.lean"))
    files += [ROOT / p for p in (
        "QuantumLeanLeap/GoogleQHL.lean", "lakefile.toml", "lake-manifest.json",
        "lean-toolchain", "scripts/verify_qhl_candidate.py", "verification/interface-sources.json")]
    dependencies = {}
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        path = ((ROOT / package["dir"]) if package["type"] == "path" else
                (ROOT / manifest["packagesDir"] / package_directory_name(package["name"]))).resolve()
        revision = git(path, "rev-parse", "HEAD")
        if package["type"] == "git" and revision != package["rev"]:
            raise EnvironmentMismatch(f"Manifest revision mismatch: {package['name']}")
        if git(path, "status", "--porcelain", "--untracked-files=no"):
            raise EnvironmentMismatch(f"Tracked dependency edits: {package['name']}")
        dependencies[package["name"]] = revision
    return {"sha256": {str(p.relative_to(ROOT)): digest(p.read_bytes()) for p in files},
            "dependencies": dependencies,
            "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip()}


def compare_snapshot(lock, current):
    if lock.get("schema") != SCHEMA or lock.get("lock_version") != 1:
        raise EnvironmentMismatch("Unknown frozen specification version")
    for field in ("sha256", "dependencies", "lean_toolchain"):
        if lock.get(field) != current[field]:
            raise EnvironmentMismatch(f"Frozen baseline mismatch: {field}; acceptance did not update the lock")


def audit_axioms(output):
    matches = re.findall(
        r"'QHLSubmission.accepted' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", output)
    if len(matches) != 1:
        raise Rejected("Missing or ambiguous accepted-theorem axiom report")
    axioms = [a.strip() for a in matches[0].split(",") if a.strip()]
    if set(axioms) - ALLOWED_AXIOMS:
        raise Rejected(f"Unapproved proof dependencies: {axioms}")
    return axioms


def verify(candidate_path):
    raw = candidate_path.read_bytes()
    run_dir = ARTIFACTS / digest(raw)
    run_dir.mkdir(parents=True, exist_ok=True)
    report_path = run_dir / "report.json"
    # Never let a previous acceptance survive a failed or interrupted new run.
    report_path.unlink(missing_ok=True)
    for name in ("Candidate.lean", "build.log", "lean.log"):
        (run_dir / name).unlink(missing_ok=True)
    report = {"schema": SCHEMA, "status": "error", "accepted": False,
              "candidate_sha256": digest(raw), "official_verifier_passed": False,
              "checked_at_utc": datetime.now(timezone.utc).isoformat()}
    code = 2
    try:
        expression = parse_candidate(raw)
        lock_raw = LOCK.read_bytes()
        lock = json.loads(lock_raw)
        report["lock_sha256"] = digest(lock_raw)
        compare_snapshot(lock, snapshot())
        report["baseline_verified"] = True
        result = command(["lake", "build", "QuantumLeanLeap.GoogleQHL.Verification.ResetNative"])
        (run_dir / "build.log").write_text(result.stdout + result.stderr)
        if result.returncode:
            raise EnvironmentMismatch("Trusted specification/language build failed; see build.log")
        source = proof_source(expression)
        source_path = run_dir / "Candidate.lean"
        source_path.write_text(source)
        report["generated_source_sha256"] = digest(source.encode())
        result = command(["lake", "env", "lean", str(source_path)])
        output = result.stdout + result.stderr
        (run_dir / "lean.log").write_text(output)
        if result.returncode:
            raise Rejected("Generated proof did not pass Lean; see lean.log (not a completeness claim)")
        report["axioms"] = audit_axioms(output)
        # Recheck source/dependency identities after the build and proof check.
        compare_snapshot(lock, snapshot())
        if LOCK.read_bytes() != lock_raw:
            raise EnvironmentMismatch("Lock changed during verification")
        report.update(status="accepted", accepted=True, native_backend_verified=True,
                      backend="QuantumAlg unitary gates with QHL dynamic measurement/control")
        code = 0
    except Rejected as exc:
        report.update(status="not_certified", reason=str(exc))
        code = 1
    except (EnvironmentMismatch, OSError, ValueError) as exc:
        report.update(status="error", reason=str(exc))
    report_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    return code, report_path, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate", nargs="?", type=Path)
    parser.add_argument("--freeze", type=Path, metavar="NEW_LOCK",
                        help="Explicitly create a new trusted baseline; refuses to overwrite")
    args = parser.parse_args()
    if args.freeze:
        if args.candidate:
            parser.error("Do not combine --freeze and candidate verification")
        baseline = {"schema": SCHEMA, "lock_version": 1, **snapshot()}
        with args.freeze.open("x") as f:
            f.write(json.dumps(baseline, indent=2, ensure_ascii=False) + "\n")
        print(f"Created baseline: {args.freeze}")
        return 0
    if not args.candidate:
        parser.error("A JSON candidate is required")
    try:
        code, report_path, report = verify(args.candidate)
    except (OSError, EnvironmentMismatch) as exc:
        print(f"Verification could not start: {exc}", file=sys.stderr)
        return 2
    print(f"{report['status']}: {report_path}")
    if "reason" in report:
        print(report["reason"])
    return code


if __name__ == "__main__":
    sys.exit(main())
