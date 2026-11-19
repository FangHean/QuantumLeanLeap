"""Reversible integer Newton baseline matching NewtonFixed.lean.

Only X/CX/CCX/Z_POW; no measurements, resets, opaque arithmetic gates, or
input-dependent classical control. Schoolbook products and Cuccaro adders
are expanded into primitive gates. Local compute-copy-uncompute recycles
work registers; global uncomputation restores all intermediate iterates.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import heapq
import json
from math import log2, pi, sqrt
from pathlib import Path
import random
import time

import numpy as np

from invsqrt import MAX_INPUT, dyadic_decimal, sha256

BITS = 37
STEPS = 6


def word(x: int, bits: int = BITS, steps: int = STEPS) -> int:
    if x <= 0:
        return 0
    exponent = (x.bit_length() - 1) // 2 + 1
    scale = 1 << bits
    q = scale >> exponent
    for _ in range(steps):
        q = q * (3 * scale * scale - x * q * q) // (2 * scale * scale)
    return q


class Circuit:
    def __init__(self, width: int):
        self.width = width
        self.next_wire = width
        self.available: list[int] = []
        self.ops: list[tuple] = []

    def alloc(self, count: int) -> list[int]:
        result = []
        for _ in range(count):
            if self.available:
                result.append(heapq.heappop(self.available))
            else:
                result.append(self.next_wire)
                self.next_wire += 1
        return result

    def free(self, wires: list[int]) -> None:
        # Callers may free only registers already restored to zero.
        for wire in wires:
            heapq.heappush(self.available, wire)

    def x(self, a: int) -> None:
        self.ops.append(("X", a))

    def cx(self, a: int, b: int) -> None:
        if a == b:
            raise ValueError("CNOT aliases")
        self.ops.append(("CX", a, b))

    def ccx(self, a: int, b: int, c: int) -> None:
        if a == b:
            self.cx(a, c)
            return
        if c in (a, b):
            raise ValueError("Toffoli target aliases control")
        self.ops.append(("CCX", a, b, c))

    def undo(self, start: int, end: int) -> None:
        operations = self.ops[start:end]
        if any(op[0] not in {"X", "CX", "CCX"} for op in operations):
            raise ValueError("undo accepts self-inverse reversible gates only")
        self.ops.extend(reversed(operations))

    def add(self, a: list[int], b: list[int]) -> None:
        """b += a modulo 2**n; restore a and the carry."""
        if len(a) != len(b) or not a or set(a) & set(b):
            raise ValueError("adder needs nonempty disjoint equal-width registers")
        carry = self.alloc(1)
        for i in range(len(a) - 1):
            c = carry[0] if i == 0 else a[i-1]
            self.cx(a[i], b[i])
            self.cx(a[i], c)
            self.ccx(b[i], c, a[i])
        self.cx(a[-1], b[-1])
        if len(a) > 1:
            self.cx(a[-2], b[-1])
        for i in reversed(range(len(a) - 1)):
            c = carry[0] if i == 0 else a[i-1]
            self.ccx(b[i], c, a[i])
            self.cx(a[i], c)
            self.cx(c, b[i])
        self.free(carry)

    def multiply(self, a: list[int], b: list[int], target: list[int]) -> None:
        """target += a*b mod 2**len(target); a and b may be identical."""
        if (set(a) | set(b)) & set(target):
            raise ValueError("product target aliases an operand")
        for i, control in enumerate(b[:len(target)]):
            part = target[i:]
            mask = self.alloc(len(part))
            for j, source in enumerate(a[:len(part)]):
                self.ccx(control, source, mask[j])
            self.add(mask, part)
            for j, source in enumerate(a[:len(part)]):
                self.ccx(control, source, mask[j])
            self.free(mask)

    def constant_minus(self, target: list[int], value: int) -> None:
        """target := value-target mod 2**len(target)."""
        constant = self.alloc(len(target))
        for wire in target:
            self.x(wire)
        for i, wire in enumerate(constant):
            if ((value + 1) >> i) & 1:
                self.x(wire)
        self.add(constant, target)
        for i, wire in enumerate(constant):
            if ((value + 1) >> i) & 1:
                self.x(wire)
        self.free(constant)

    def seed(self, bits: int) -> list[int]:
        if bits < (self.width + 1) // 2:
            raise ValueError("seed precision is too small for this input width")
        result = self.alloc(bits + 1)
        start = len(self.ops)
        # prefix[i] = OR(x[i], ..., x[width-1]).
        prefix = self.alloc(self.width)
        self.cx(self.width - 1, prefix[-1])
        for i in reversed(range(self.width - 1)):
            self.cx(i, prefix[i])
            self.cx(prefix[i+1], prefix[i])
            self.ccx(i, prefix[i+1], prefix[i])
        end = len(self.ops)
        for k in range((self.width + 1) // 2):
            target = result[bits - k - 1]
            self.cx(prefix[2*k], target)
            if 2*k + 2 < self.width:
                self.cx(prefix[2*k+2], target)
        self.undo(start, end)
        self.free(prefix)
        return result

    def step(self, x: list[int], q: list[int], bits: int) -> list[int]:
        output = self.alloc(bits + 1)
        start = len(self.ops)
        # x*q^2 <= S^2 on valid inputs. Keep 2p+2 bits so 3*S^2
        # and its subtraction fit; the circuit itself is defined modulo 2^n.
        squared = self.alloc(2*bits + 2)
        correction = self.alloc(2*bits + 2)
        product = self.alloc(3*bits + 2)
        self.multiply(q, q, squared)
        self.multiply(squared, x, correction)
        self.constant_minus(correction, 3 << (2*bits))
        self.multiply(q, correction, product)
        end = len(self.ops)
        for i, wire in enumerate(output):
            self.cx(product[2*bits + 1 + i], wire)
        self.undo(start, end)
        self.free(squared + correction + product)
        return output


def generate(path: Path, width: int = 22, bits: int = BITS, steps: int = STEPS) -> dict:
    if width < 1 or bits < (width + 1)//2 or steps < 1:
        raise ValueError("invalid generation parameters")
    start_time = time.monotonic()
    circuit = Circuit(width)
    q = circuit.seed(bits)
    for _ in range(steps):
        q = circuit.step(list(range(width)), q, bits)
    forward_end = len(circuit.ops)
    for i, wire in enumerate(q):
        if i < bits:
            circuit.ops.append(("Z_POW", wire, dyadic_decimal(1, bits-i-1)))
    circuit.undo(0, forward_end)
    counts = Counter(op[0] for op in circuit.ops)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", buffering=1 << 20) as out:
        out.write(f"# Integer Newton: bits={bits}, steps={steps}; no measurement.\n")
        for i in range(width):
            out.write(f"APPEND_TO_REGISTER q{i} r0\n")
        out.write('REGISTER r0 "x"\n')
        for op in circuit.ops:
            if op[0] == "Z_POW":
                out.write(f"Z_POW q{op[1]} {op[2]}\n")
            else:
                out.write(op[0] + " " + " ".join(f"q{w}" for w in op[1:]) + "\n")
    return {
        "algorithm": "power-of-two seed and six fixed-point Newton steps",
        "input_width": width, "fraction_bits": bits, "iterations": steps,
        "qubits": circuit.next_wire, "scratch_qubits": circuit.next_wire - width,
        "gate_counts": dict(counts), "total_gates": sum(counts.values()),
        "kmx_sha256": sha256(path), "kmx_bytes": path.stat().st_size,
        "generation_seconds": time.monotonic() - start_time,
        "lean_integer_algorithm_proved": bits == BITS and steps == STEPS and width == 22,
        "lean_gate_semantics_proved": False, "official_verifier_run": False,
    }


def audit_arithmetic(maximum: int = MAX_INPUT, bits: int = BITS, steps: int = STEPS) -> dict:
    start = time.monotonic()
    scale = 1 << bits
    precision = 1 << 24
    min_margin, max_relative = float("inf"), 0.0
    margin_x = relative_x = 0
    for x in range(1, maximum + 1):
        q = word(x, bits, steps)
        if not q*q*x <= scale*scale:
            raise ValueError(f"not a lower approximation at x={x}")
        if ((precision-1)*scale)**2 > q*q*x*precision**2:
            raise ValueError(f"relative error exceeds 2^-24 at x={x}")
        target = 1 / sqrt(x)
        error = target - q / scale
        relative = error / target
        margin = target / precision - error
        if relative > max_relative:
            max_relative, relative_x = relative, x
        if margin < min_margin:
            min_margin, margin_x = margin, x
    return {
        "valid_inputs_checked": maximum, "fraction_bits": bits, "iterations": steps,
        "integer_squared_error_check_passed": True,
        "max_relative_error_float64": max_relative, "max_relative_error_input": relative_x,
        "minimum_margin_turns_float64": min_margin, "minimum_margin_input": margin_x,
        "arithmetic_audit_seconds": time.monotonic() - start,
    }


def native_check(path: Path, maximum: int = MAX_INPUT, bits: int = BITS,
                 steps: int = STEPS, samples: int = 512, all_inputs: bool = False,
                 batch_size: int = 4096, binary: Path | None = None) -> dict:
    import kickmix as km

    start = time.monotonic()
    circuit = km.Circuit.from_file(path)
    inputs = list(circuit.register_data["x"])
    width = len(inputs)
    if inputs != [km.q(i) for i in range(width)] or len(circuit.register_data) != 1:
        raise ValueError("incorrect input register")
    stats = circuit.operation_statistics()
    if sum(stats[name] for name in ["X", "CX", "CCX", "Z_POW"]) != stats.num_instructions:
        raise ValueError("unexpected quantum operations")
    rng = random.Random(20261116)
    if all_inputs:
        xs = range(1, maximum + 1)
    else:
        xs = sorted({0, 1, maximum, *range(1, min(64, maximum) + 1),
                     *(min(maximum, max(1, 4**k + d)) for k in range(12) for d in [-1, 0, 1]),
                     *(rng.randrange(1, maximum+1) for _ in range(samples))})
    checked = 0
    for offset in range(0, len(xs), batch_size):
        batch = np.array(xs[offset:offset+batch_size], dtype=np.uint64)
        sim = km.Simulator(batch_size=len(batch))
        for i in range(width):
            sim.write_across_shots(km.q(i), ((batch >> i) & 1).astype(bool))
        sim.do(circuit)
        for i in range(width):
            if not np.array_equal(sim.read_across_shots(km.q(i)), ((batch >> i) & 1).astype(bool)):
                raise ValueError(f"input not restored: batch={offset}, wire={i}")
        for i in range(width, circuit.num_qubits):
            if sim.read_across_shots(km.q(i), out=int):
                raise ValueError(f"scratch not cleared: batch={offset}, wire={i}")
        for shot, x in enumerate(batch):
            expected = Fraction(2 * (word(int(x), bits, steps) % (1 << bits)), 1 << bits)
            if sim.read_shot_phase(shot) % 2 != expected:
                raise ValueError(f"phase mismatch at x={x}")
        checked += len(batch)
        if all_inputs and (offset // batch_size) % 16 == 0:
            print(f"native basis inputs checked: {checked}/{len(xs)}", flush=True)
    result = {
        "kmx_sha256": sha256(path), "native_inputs_checked": checked,
        "exhaustive_valid_domain": all_inputs, "input_restored": True,
        "all_scratch_zero": True, "exact_rational_phases_match": True,
        "qubits": circuit.num_qubits, "toffoli_like": stats.num_toffoli_like,
        "direct_t_like": stats.num_t_like,
        "fine_rotations": stats.num_z_pow(min_clifford_hierarchy_level=4),
        "native_seconds": time.monotonic() - start,
        "lean_gate_semantics_proved": False, "official_verifier_run": False,
    }
    if binary:
        circuit.to_file(binary, format="kmb")
        if km.Circuit.from_file(binary) != circuit:
            raise ValueError("binary round-trip failed")
        result.update(kmb_sha256=sha256(binary), kmb_bytes=binary.stat().st_size)
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["generate", "arithmetic", "native"])
    parser.add_argument("--path", type=Path, default=Path("artifacts/newton.kmx"))
    parser.add_argument("--report", type=Path)
    parser.add_argument("--width", type=int, default=22)
    parser.add_argument("--bits", type=int, default=BITS)
    parser.add_argument("--steps", type=int, default=STEPS)
    parser.add_argument("--max-input", type=int, default=MAX_INPUT)
    parser.add_argument("--samples", type=int, default=512)
    parser.add_argument("--all-inputs", action="store_true")
    parser.add_argument("--batch-size", type=int, default=4096)
    parser.add_argument("--binary", type=Path)
    args = parser.parse_args()
    if args.action == "generate":
        result = generate(args.path, args.width, args.bits, args.steps)
    elif args.action == "arithmetic":
        result = audit_arithmetic(args.max_input, args.bits, args.steps)
    else:
        result = native_check(args.path, args.max_input, args.bits, args.steps,
                              args.samples, args.all_inputs, args.batch_size, args.binary)
    text = json.dumps(result, indent=2) + "\n"
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
