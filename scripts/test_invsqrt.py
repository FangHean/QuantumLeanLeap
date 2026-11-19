"""Small exhaustive semantic tests, including adversarial exported artifacts."""
from fractions import Fraction
from pathlib import Path
import tempfile
import unittest

import numpy as np

from invsqrt import (
    dyadic_decimal, generate, native_check, parse_dyadic, phase_word,
    verify, walsh_inplace,
)


def simulate(text: str, x: int, width: int) -> tuple[int, Fraction]:
    """Independent scalar interpreter, deliberately not using Walsh/parity code."""
    bits = [(x >> k) & 1 for k in range(width)]
    phase = Fraction(0)
    for line in text.splitlines():
        tokens = line.split("#", 1)[0].split()
        if not tokens:
            continue
        if tokens[0] == "CX":
            control, target = (int(t[1:]) for t in tokens[1:])
            bits[target] ^= bits[control]
        elif tokens[0] == "Z_POW":
            phase += bits[int(tokens[1][1:])] * Fraction(tokens[2]) / 2
        elif tokens[0] not in {"REGISTER", "APPEND_TO_REGISTER"}:
            raise ValueError(tokens)
    return sum(b << k for k, b in enumerate(bits)), phase % 1


class InverseSquareRootTests(unittest.TestCase):
    def test_exact_angle_serialization(self):
        for exponent in [0, 8, 40, 60]:
            for value in [0, 1, -1, 123456789012345, -123456789012345]:
                text = dyadic_decimal(value, exponent)
                self.assertEqual(Fraction(text), Fraction(value, 1 << exponent))
                self.assertEqual(parse_dyadic(text, exponent), value)
        with self.assertRaises(ValueError):
            parse_dyadic("0.1", 60)

    def test_walsh_round_trip_and_overflow(self):
        original = np.array([0, 3, 19, -5, 8, 31, -7, 2], dtype=np.int64)
        values = original.copy()
        walsh_inplace(values)
        walsh_inplace(values)
        np.testing.assert_array_equal(values, 8 * original)
        with self.assertRaises(OverflowError):
            walsh_inplace(np.array([1 << 62, 1 << 62], dtype=np.int64))

    def test_integer_sqrt_and_full_turn(self):
        self.assertEqual(phase_word(1), 1 << 40)
        self.assertEqual(phase_word(4), 1 << 39)
        for x in [2, 3, 17, 1023, 1024, 3_133_452]:
            q = phase_word(x)
            self.assertLessEqual(q*q*x, 1 << 80)
            self.assertLess(1 << 80, (q+1)*(q+1)*x)
        with self.assertRaises(ValueError):
            phase_word(0)

    def test_all_small_basis_states(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "test.kmx"
            for width, maximum in [(1, 1), (3, 5), (5, 31), (6, 47)]:
                with self.subTest(width=width):
                    report = generate(path, width, maximum, 40)
                    validation = verify(path, width, maximum, 40)
                    self.assertEqual(report["gate_counts"], validation["gate_counts"])
                    self.assertTrue(validation["contest_tolerance_bound_certified"])
                    text = path.read_text()
                    for x in range(1 << width):
                        output, phase = simulate(text, x, width)
                        expected = Fraction(phase_word(x), 1 << 40) % 1 if 1 <= x <= maximum else 0
                        self.assertEqual(output, x)
                        self.assertEqual(phase, expected)

    def test_reject_corrupted_phase_and_restoration(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "test.kmx"
            generate(path, 4, 13, 40)
            original = path.read_text()
            for change in ["Z_POW q0 0.5\n", "CX q0 q1\n", "X q0\n", "Z_POW q0 0.1\n"]:
                with self.subTest(change=change):
                    path.write_text(original + change)
                    with self.assertRaises(ValueError):
                        verify(path, 4, 13, 40)

    def test_low_precision_does_not_claim_contest_tolerance(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "test.kmx"
            generate(path, 4, 13, 8)
            self.assertFalse(verify(path, 4, 13, 8)["contest_tolerance_bound_certified"])

    def test_native_parser_simulator_and_binary_roundtrip(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "test.kmx"
            binary = Path(directory) / "test.kmb"
            generate(path, 6, 47, 40)
            result = native_check(path, 6, 47, 40, 64, binary)
            self.assertTrue(result["native_phases_match"])
            self.assertTrue(binary.exists())


if __name__ == "__main__":
    unittest.main()
