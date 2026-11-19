from pathlib import Path
import tempfile
import unittest

import numpy as np
import kickmix as km

from newton_invsqrt import Circuit, generate, native_check, word


def simulate_ops(circuit: Circuit, states: list[int]) -> list[int]:
    text = "\n".join(op[0] + " " + " ".join(f"q{w}" for w in op[1:]) for op in circuit.ops)
    sim = km.Simulator(batch_size=len(states))
    for i in range(circuit.next_wire):
        sim.write_across_shots(km.q(i), np.array([bool((s >> i) & 1) for s in states]))
    sim.do(km.Circuit(text))
    output = [0] * len(states)
    for i in range(circuit.next_wire):
        for j, bit in enumerate(sim.read_across_shots(km.q(i))):
            output[j] |= int(bit) << i
    return output


class NewtonTests(unittest.TestCase):
    def test_adder_all_inputs_with_wraparound(self):
        for n in [1, 2, 3, 4]:
            circuit = Circuit(2*n)
            circuit.add(list(range(n)), list(range(n, 2*n)))
            states = list(range(1 << (2*n)))
            expected = [(s & ((1 << n)-1)) | ((((s >> n) + (s & ((1 << n)-1))) % (1 << n)) << n) for s in states]
            self.assertEqual(simulate_ops(circuit, states), expected)

    def test_multiply_square_truncation_and_cleanup(self):
        for squared in [False, True]:
            for out_width in [2, 4, 6]:
                circuit = Circuit(3 if squared else 6)
                out = circuit.alloc(out_width)
                circuit.multiply([0, 1, 2], [0, 1, 2] if squared else [3, 4, 5], out)
                states = list(range(8 if squared else 64))
                expected = []
                for s in states:
                    a, b = s & 7, s & 7 if squared else s >> 3
                    expected.append(s | (((a*b) % (1 << out_width)) << out[0]))
                self.assertEqual(simulate_ops(circuit, states), expected)

    def test_constant_subtraction(self):
        circuit = Circuit(4)
        circuit.constant_minus([0, 1, 2, 3], 11)
        self.assertEqual(simulate_ops(circuit, list(range(16))), [(11-x) % 16 for x in range(16)])

    def test_seed_all_leading_bit_cases(self):
        for width in [1, 5, 6]:
            circuit = Circuit(width)
            q = circuit.seed(8)
            states = list(range(1 << width))
            expected = []
            for x in states:
                seed = 0 if x == 0 else 256 >> ((x.bit_length()-1)//2+1)
                expected.append(x | (seed << q[0]))
            self.assertEqual(simulate_ops(circuit, states), expected)

    def test_fixed_step_and_reused_workspace(self):
        bits, width = 7, 5
        circuit = Circuit(width)
        q = circuit.seed(bits)
        q0 = q
        for _ in range(2):
            q = circuit.step(list(range(width)), q, bits)
        # All intermediate iterates remain; scratch workspace must be zero.
        states = list(range(1 << width))
        actual = simulate_ops(circuit, states)
        for x, state in zip(states, actual, strict=True):
            q_value = sum(((state >> w) & 1) << i for i, w in enumerate(q))
            self.assertEqual(q_value, word(x, bits, 2))
        circuit.undo(0, len(circuit.ops))
        self.assertEqual(simulate_ops(circuit, states), states)

    def test_complete_phase_circuit(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "newton.kmx"
            generate(path, width=5, bits=12, steps=6)
            result = native_check(path, maximum=31, bits=12, steps=6, all_inputs=True, batch_size=31)
            self.assertEqual(result["native_inputs_checked"], 31)
            self.assertTrue(result["all_scratch_zero"])

    def test_integer_precision_bound_at_edges(self):
        for x in [1, 2, 3, 4, 15, 16, 17, 1023, 1024, 1025, 3133452]:
            q = word(x)
            self.assertLessEqual(q*q*x, 1 << 74)
            self.assertLessEqual((((1 << 24)-1)*(1 << 37))**2, q*q*x*(1 << 48))


if __name__ == "__main__":
    unittest.main()
