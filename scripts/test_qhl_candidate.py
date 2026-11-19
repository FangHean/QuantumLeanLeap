"""Negative controls for the independent local benchmark, including real Lean failures."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import verify_qhl_candidate as v


def atom(op):
    return {"op": op}


def seq(a, b):
    return {"op": "seq", "first": a, "second": b}


RESET = seq(atom("measure"), {"op": "if_zero", "zero": atom("skip"), "nonzero": atom("x")})


def encode(program):
    return json.dumps({"schema": v.SCHEMA, "program": program}).encode()


class ParserTests(unittest.TestCase):
    def test_quoted_lake_package_name(self):
        self.assertEqual(v.package_directory_name("«doc-gen4»"), "doc-gen4")
        self.assertEqual(v.package_directory_name("Physlib"), "Physlib")

    def test_closed_emission(self):
        self.assertEqual(v.parse_candidate(encode(RESET)), "(.seq .measure (.ifZero .skip .x))")

    def test_reject_extra_fields_and_code(self):
        for program in (atom("qset"), atom("x\naxiom false : False"),
                        {"op": "x", "cost": 0}, {"op": "measure", "matrix": [[1]]},
                        {"op": "skip", "proof": "by trivial"}, None, 1):
            with self.subTest(program=program), self.assertRaises(v.Rejected):
                v.parse_candidate(encode(program))

    def test_reject_duplicate_keys_and_schema(self):
        for raw in (b'{"schema":"qhl-reset-v1","program":{"op":"x","op":"skip"}}',
                    b'{"schema":"other","program":{"op":"skip"}}', b'[]', b'\xff'):
            with self.subTest(raw=raw), self.assertRaises(v.Rejected):
                v.parse_candidate(raw)

    def test_size_depth_and_node_limits(self):
        with self.assertRaises(v.Rejected):
            v.parse_candidate(b" " * (v.MAX_BYTES + 1))
        deep = atom("skip")
        for _ in range(v.MAX_DEPTH + 1):
            deep = seq(atom("skip"), deep)
        with self.assertRaises(v.Rejected):
            v.parse_candidate(encode(deep))
        wide = atom("skip")
        for _ in range(6):
            wide = seq(wide, wide)
        with self.assertRaises(v.Rejected):
            v.parse_candidate(encode(wide))

    def test_proof_dependency_audit(self):
        good = "'QHLSubmission.accepted' depends on axioms: [propext, Classical.choice, Quot.sound]"
        self.assertEqual(set(v.audit_axioms(good)), v.ALLOWED_AXIOMS)
        for out in (good + good, "", good.replace("propext", "sorryAx"),
                    good.replace("propext", "Candidate.magic"),
                    good.replace("propext", "Lean.ofReduceBool")):
            with self.subTest(output=out), self.assertRaises(v.Rejected):
                v.audit_axioms(out)

    def test_baseline_drift(self):
        current = {"sha256": {"Spec.lean": "a"}, "dependencies": {"mathlib": "b"},
                   "lean_toolchain": "lean-test"}
        lock = {"schema": v.SCHEMA, "lock_version": 1, **current}
        v.compare_snapshot(lock, current)
        for field in current:
            bad = copy.deepcopy(current)
            bad[field] = "changed"
            with self.subTest(field=field), self.assertRaises(v.EnvironmentMismatch):
                v.compare_snapshot(lock, bad)


class LeanIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="qhl-verifier-tests-")
        cls.directory = Path(cls.temp.name)
        cls.baseline = {"schema": v.SCHEMA, "lock_version": 1, **v.snapshot()}

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def setUp(self):
        self.lock = self.directory / "baseline.json"
        self.lock.write_text(json.dumps(self.baseline))
        self.lock_patch = patch.object(v, "LOCK", self.lock)
        self.artifact_patch = patch.object(v, "ARTIFACTS", self.directory / "artifacts")
        self.lock_patch.start()
        self.artifact_patch.start()
        self.addCleanup(self.lock_patch.stop)
        self.addCleanup(self.artifact_patch.stop)

    def run_candidate(self, program):
        path = self.directory / "submission.json"
        path.write_bytes(encode(program))
        return v.verify(path)

    def test_correct_feedback_and_skip_wrapper(self):
        z_feedback = seq(atom("measure"),
            {"op": "if_zero", "zero": atom("z"), "nonzero": atom("x")})
        for program in (RESET, seq(atom("skip"), RESET), z_feedback):
            code, report_path, report = self.run_candidate(program)
            self.assertEqual(code, 0, report)
            self.assertTrue(report["accepted"])
            self.assertTrue(report["matrix_semantics_verified"])
            self.assertEqual(report["candidate_sha256"], v.digest(encode(program)))
            self.assertEqual(set(report["axioms"]), v.ALLOWED_AXIOMS)
            source = (report_path.parent / "Candidate.lean").read_bytes()
            self.assertEqual(report["generated_source_sha256"], v.digest(source))
            self.assertIn(b"ResetSpec.Contract candidate.toDynamic.compile", source)
            self.assertIn(b"candidate.toDynamic.worstMatrixGates", source)

    def test_incorrect_quantum_semantics(self):
        wrong_feedback = seq(atom("measure"),
            {"op": "if_zero", "zero": atom("x"), "nonzero": atom("skip")})
        for program in (atom("skip"), atom("measure"), wrong_feedback,
                        seq(atom("measure"), atom("x"))):
            code, report_path, report = self.run_candidate(program)
            self.assertEqual(code, 1, report)
            self.assertFalse(report["accepted"])
            log = (report_path.parent / "lean.log").read_text()
            self.assertIn("unsolved goals", log)

    def test_semantically_correct_over_budget(self):
        for program, theorem in ((seq(seq(atom("x"), atom("x")), RESET), "gate_budget"),
                                 (seq(atom("measure"), RESET), "measurement_budget")):
            code, report_path, report = self.run_candidate(program)
            self.assertEqual(code, 1, report)
            source = (report_path.parent / "Candidate.lean").read_text().splitlines()
            start = next(i for i, line in enumerate(source, 1) if line.startswith(f"theorem {theorem}"))
            end = next(i for i, line in enumerate(source, 1) if i > start and line.startswith("theorem "))
            log = (report_path.parent / "lean.log").read_text()
            errors = [int(m) for m in __import__("re").findall(r"Candidate.lean:(\d+):\d+: error:", log)]
            self.assertTrue(errors, log)
            self.assertTrue(all(start <= line < end for line in errors), log)

    def test_lock_drift_revokes_previous_report(self):
        code, path, _ = self.run_candidate(RESET)
        self.assertEqual(code, 0)
        lock = copy.deepcopy(self.baseline)
        lock["sha256"]["QuantumLeanLeap/GoogleQHL/Verification/ResetSpec.lean"] = "changed"
        self.lock.write_text(json.dumps(lock))
        code, same_path, report = self.run_candidate(RESET)
        self.assertEqual(code, 2)
        self.assertEqual(same_path, path)
        self.assertFalse(json.loads(path.read_text())["accepted"])
        self.assertIn("Frozen baseline mismatch", report["reason"])
        self.assertFalse((path.parent / "Candidate.lean").exists())

    def test_timeout_never_accepts(self):
        with patch.object(v, "snapshot", return_value={k: self.baseline[k] for k in
                 ("sha256", "dependencies", "lean_toolchain")}), \
             patch.object(v, "command", side_effect=v.EnvironmentMismatch("timeout")):
            code, _, report = self.run_candidate(RESET)
        self.assertEqual(code, 2)
        self.assertFalse(report["accepted"])


if __name__ == "__main__":
    unittest.main()
