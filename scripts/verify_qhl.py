#!/usr/bin/env python3
"""Build the project and audit selected QHL declarations against standard axioms.

This is a local reproducibility audit, not Google's verifier or Lean Comparator.
Only Python's standard library is required. Run from any working directory.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "artifacts" / "qhl"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def run(args, log):
    result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True)
    output = result.stdout + result.stderr
    (ARTIFACTS / log).write_text(output)
    if result.returncode:
        print(output, file=sys.stderr)
        raise RuntimeError(f"Command failed: {args}")
    return output


def main():
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    # Remove a stale success report before checking the current source tree.
    report_path = ARTIFACTS / "audit.json"
    report_path.unlink(missing_ok=True)
    run(["lake", "build"], "build.log")
    output = run(["lake", "env", "lean", "scripts/QHLAudit.lean"], "axioms.log")
    requested = re.findall(r"^#print axioms (\S+)$", (ROOT / "scripts/QHLAudit.lean").read_text(), re.M)
    matches = re.findall(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
        output,
    )
    declarations = {name: [a.strip() for a in axioms.split(",") if a.strip()]
                    for name, axioms in matches}
    if len(declarations) != len(requested):
        raise RuntimeError(f"Expected {len(requested)} axiom reports, got {len(declarations)}")
    for short in requested:
        full = "QuantumLeanLeap.GoogleQHL." + short
        if full not in declarations:
            raise RuntimeError(f"Missing audited declaration: {full}")
        forbidden = set(declarations[full]) - ALLOWED
        if forbidden:
            raise RuntimeError(f"Unapproved axioms in {full}: {sorted(forbidden)}")
    files = sorted((ROOT / "QuantumLeanLeap" / "GoogleQHL").rglob("*.lean"))
    files += [ROOT / name for name in (
        "QuantumLeanLeap/GoogleQHL.lean", "QuantumLeanLeap.lean", "lakefile.toml",
        "lake-manifest.json", "lean-toolchain", "scripts/QHLAudit.lean", "scripts/verify_qhl.py",
        "scripts/verify_qhl_candidate.py", "scripts/test_qhl_candidate.py",
        "verification/reset-paper-v7.lock.json", "verification/interface-sources.json")]
    from verify_qhl_candidate import snapshot
    dependencies = snapshot()["dependencies"]
    report = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "clean-room QHL core, dynamic circuits and restricted task baselines",
        "full_google_reproduction": False,
        "official_verifier_passed": False,
        "parallel_grover": {
            "status": "exact query-model baseline",
            "N": 4, "k": 1, "m": "any positive natural",
            "find_any_probability": 1, "find_all_probability": 1,
            "expected_parallel_rounds": 1,
            "general_task_completed": False,
            "paper_performance_reproduced": False,
            "native_gate_compilation_verified": False,
            "qhl_dynamic_interpreter_bridge_verified": False,
        },
        "build_passed": True,
        "audited_declarations": len(declarations),
        "allowed_axioms": sorted(ALLOWED),
        "declarations": declarations,
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "dependency_commits": dependencies,
        "sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
    }
    report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(f"Build passed; {len(declarations)} declarations use only the allowed standard axioms.")
    print(f"Report: {report_path}")


if __name__ == "__main__":
    main()
