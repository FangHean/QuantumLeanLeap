"""Exact, ancilla-free inverse-square-root phase synthesis and verification.

This is an intentionally expensive correctness baseline, not a competitive
submission. All angles are dyadic rationals; no floating point is used.
The verifier interprets the EXPORTED gates as parity phase polynomials, then
checks their action on every basis input with an integer Walsh transform.
This computational certificate is separate from the Lean kernel proofs.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from math import isqrt
from pathlib import Path
import random
import shlex
import time

import numpy as np

INPUT_WIDTH = 22
MAX_INPUT = 3_133_452
PHASE_BITS = 40
INT64_MAX = (1 << 63) - 1


def phase_word(x: int, bits: int = PHASE_BITS) -> int:
    """Lean's phaseWord, including the full turn at x=1."""
    if x < 1:
        raise ValueError("phase_word requires x >= 1")
    return isqrt((1 << (2 * bits)) // x)


def check_parameters(width: int, max_input: int, bits: int) -> None:
    if not 1 <= width <= INPUT_WIDTH or not 1 <= max_input < (1 << width):
        raise ValueError("require 1 <= width <= 22 and 1 <= max_input < 2**width")
    if not 2 <= bits <= PHASE_BITS or bits + width > 62:
        raise ValueError("unsupported exact-integer precision")


def phase_table(width: int, max_input: int, bits: int) -> np.ndarray:
    check_parameters(width, max_input, bits)
    result = np.zeros(1 << width, dtype=np.int64)
    scale = 1 << bits
    result[1:max_input + 1] = np.fromiter(
        (phase_word(x, bits) % scale for x in range(1, max_input + 1)),
        dtype=np.int64, count=max_input,
    )
    return result


def walsh_inplace(values: np.ndarray) -> None:
    """Unnormalized H with H(H(v)) = len(v)*v, checked against overflow."""
    if values.dtype != np.int64 or values.ndim != 1 or not len(values):
        raise ValueError("expected a nonempty int64 vector")
    if len(values) & (len(values) - 1):
        raise ValueError("vector length must be a power of two")
    stride = 1
    while stride < len(values):
        block = values.reshape(-1, 2, stride)
        left = block[:, 0, :].copy()
        right = block[:, 1, :]
        bound = max(abs(int(left.min())), abs(int(left.max())))
        bound += max(abs(int(right.min())), abs(int(right.max())))
        if bound > INT64_MAX:
            raise OverflowError("Walsh butterfly could exceed int64")
        block[:, 0, :] = left + right
        block[:, 1, :] = left - right
        stride *= 2


def dyadic_decimal(numerator: int, exponent: int) -> str:
    """Exact decimal numerator/2**exponent, with no exponent notation."""
    sign = "-" if numerator < 0 else ""
    digits = str(abs(numerator) * 5**exponent).zfill(exponent + 1)
    if exponent == 0:
        return f"{sign}{digits}.0"
    return f"{sign}{digits[:-exponent]}.{digits[-exponent:]}"


def parse_dyadic(text: str, exponent: int) -> int:
    """Read an exact decimal on the specified dyadic grid; reject rounding."""
    if text.count(".") != 1 or "e" in text.lower():
        raise ValueError("expected an exact, non-scientific decimal")
    whole, fraction = text.split(".")
    if not fraction.isdigit() or not whole.lstrip("+-").isdigit():
        raise ValueError("invalid decimal")
    sign = -1 if whole.startswith("-") else 1
    value = sign * int(whole.lstrip("+-") + fraction)
    numerator, remainder = divmod(value * (1 << exponent), 10**len(fraction))
    if remainder:
        raise ValueError("angle is not on the declared exact dyadic grid")
    return numerator


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def generate(path: Path, width: int, max_input: int, bits: int) -> dict:
    start = time.monotonic()
    coefficients = phase_table(width, max_input, bits)
    walsh_inplace(coefficients)
    # For s != 0: half_turns_s = -4*H(q)[s]/(2**width * 2**bits).
    # Since q(0)=0, the missing constant phase is exactly zero.
    exponent = bits + width - 2
    counts: Counter[str] = Counter()
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="ascii", buffering=1 << 20) as output:
        output.write("# Exact Walsh lookup baseline; no ancillas or measurements.\n")
        for wire in range(width):
            output.write(f"APPEND_TO_REGISTER q{wire} r0\n")
        output.write('REGISTER r0 "x"\n')
        for target in range(width):
            previous = 0
            for index in range(1 << target):
                gray = index ^ (index >> 1)
                if index:
                    control = (gray ^ previous).bit_length() - 1
                    output.write(f"CX q{control} q{target}\n")
                    counts["CX"] += 1
                numerator = -int(coefficients[(1 << target) | gray])
                if numerator:
                    output.write(f"Z_POW q{target} {dyadic_decimal(numerator, exponent)}\n")
                    counts["Z_POW"] += 1
                previous = gray
            # Close the Gray cycle, restoring this input wire before the next group.
            if previous:
                output.write(f"CX q{previous.bit_length() - 1} q{target}\n")
                counts["CX"] += 1
    return {
        "algorithm": "exact Walsh parity-phase lookup",
        "input_width": width, "max_input": max_input, "phase_bits": bits,
        "qubits": width, "scratch_qubits": 0, "gate_counts": dict(counts),
        "total_gates": sum(counts.values()), "ccx": 0,
        "half_turn_denominator_exponent": exponent,
        "kmx_sha256": sha256(path), "kmx_bytes": path.stat().st_size,
        "generation_seconds": time.monotonic() - start,
        "lean_basis_action_proved": False, "official_verifier_passed": False,
        "competition_score": None,
    }


def verify(path: Path, width: int, max_input: int, bits: int) -> dict:
    """Independently interpret serialized gates and exhaustively check phases.

    Each wire is represented by its input parity mask. CNOT XORs these masks;
    Z_POW adds an exact coefficient to the current parity. The final transform
    evaluates this phase polynomial at ALL 2**width words simultaneously.
    """
    start = time.monotonic()
    check_parameters(width, max_input, bits)
    exponent = bits + width - 2
    parity = [1 << wire for wire in range(width)]
    coefficients = np.zeros(1 << width, dtype=np.int64)
    counts: Counter[str] = Counter()
    register_wires: list[int] = []
    named = False

    def wire(token: str) -> int:
        if not token.startswith("q") or not token[1:].isdigit():
            raise ValueError(f"invalid qubit: {token}")
        index = int(token[1:])
        if not 0 <= index < width:
            raise ValueError(f"out-of-range qubit: {token}")
        return index

    with path.open(encoding="ascii") as source:
        for line_number, line in enumerate(source, 1):
            tokens = line.split("#", 1)[0].split()
            if not tokens:
                continue
            op = tokens[0]
            if op == "APPEND_TO_REGISTER" and len(tokens) == 3 and tokens[2] == "r0":
                if named:
                    raise ValueError("register changed after declaration")
                register_wires.append(wire(tokens[1]))
            elif op == "REGISTER" and shlex.split(line.strip()) == ["REGISTER", "r0", "x"]:
                if named or register_wires != list(range(width)):
                    raise ValueError("input register must be little endian and declared once")
                named = True
            elif op == "CX" and len(tokens) == 3:
                control, target = map(wire, tokens[1:])
                if control == target:
                    raise ValueError("CNOT needs distinct wires")
                parity[target] ^= parity[control]
                counts[op] += 1
            elif op == "Z_POW" and len(tokens) == 3:
                mask = parity[wire(tokens[1])]
                value = int(coefficients[mask]) + parse_dyadic(tokens[2], exponent)
                if abs(value) > INT64_MAX:
                    raise OverflowError("phase coefficient exceeds int64")
                coefficients[mask] = value
                counts[op] += 1
            else:
                raise ValueError(f"unsupported instruction at line {line_number}: {line.strip()}")
    if not named or parity != [1 << wire for wire in range(width)]:
        raise ValueError("input not restored or input register missing")
    # Sum in Python integers, not a potentially overflowing numpy reduction.
    total = sum(map(int, coefficients))
    walsh_inplace(coefficients)
    if abs(total) + max(abs(int(coefficients.min())), abs(int(coefficients.max()))) > INT64_MAX:
        raise OverflowError("phase reconstruction could exceed int64")
    actual = total - coefficients
    # Independently recompute every desired word and audit its integer bounds.
    expected = np.zeros(1 << width, dtype=np.int64)
    scale = 1 << bits
    for x in range(1, max_input + 1):
        q = phase_word(x, bits)
        if not q*q*x <= scale*scale < (q+1)*(q+1)*x:
            raise ValueError(f"integer square-root certificate failed at x={x}")
        expected[x] = (q % scale) << width
    modulus = 1 << (bits + width)
    actual %= modulus
    bad = np.flatnonzero(actual != expected)
    if len(bad):
        raise ValueError(f"phase mismatch at x={int(bad[0])}; {len(bad)} failing inputs")
    # A sufficient full-domain bound: absolute error < 2^-bits, whereas
    # tolerance >= 2^-24/sqrt(max_input). Only claim the contest bound if true.
    margin_certified = bits >= 24 and max_input < (1 << (2 * (bits - 24)))
    return {
        "method": "exact symbolic gate interpretation and exhaustive integer Walsh evaluation",
        "kmx_sha256": sha256(path), "basis_states_checked": 1 << width,
        "valid_inputs_checked": max_input, "input_restored": True,
        "scratch_qubits": 0, "all_phases_match_quantized_target": True,
        "invalid_inputs_have_zero_phase": True,
        "integer_sqrt_bounds_checked": max_input,
        "contest_tolerance_bound_certified": margin_certified,
        "gate_counts": dict(counts), "verification_seconds": time.monotonic() - start,
        "lean_basis_action_proved": False, "official_verifier_passed": False,
    }


def native_check(path: Path, width: int, max_input: int, bits: int,
                 samples: int, binary: Path | None) -> dict:
    """Additional native kickmix check; NOT the official competition verifier."""
    import kickmix as km

    check_parameters(width, max_input, bits)
    if samples < 0:
        raise ValueError("samples must be nonnegative")
    start = time.monotonic()
    circuit = km.Circuit.from_file(str(path))
    if circuit.num_qubits != width or list(circuit.register_data) != ["x"]:
        raise ValueError("unexpected qubit count or named registers")
    if list(circuit.register_data["x"]) != [km.q(wire) for wire in range(width)]:
        raise ValueError("native input register has wrong width or endianness")
    rng = random.Random(20261116)
    xs = sorted({0, 1, max_input, (1 << width) - 1,
                 *range(1, min(16, max_input) + 1),
                 *(1 << k for k in range(width)),
                 *(rng.randrange(1, max_input + 1) for _ in range(samples))})
    sim = km.Simulator(batch_size=len(xs))
    for wire in range(width):
        sim.write_across_shots(km.q(wire), np.array([bool((x >> wire) & 1) for x in xs]))
    sim.do(circuit)
    for wire in range(width):
        if sim.read_across_shots(km.q(wire)).tolist() != [bool((x >> wire) & 1) for x in xs]:
            raise ValueError(f"native input restoration failed on wire {wire}")
    # Use exact rational half-turn access, never floating-point phases.
    for shot, x in enumerate(xs):
        phase = sim.read_shot_phase(shot)
        expected = phase_word(x, bits) % (1 << bits) if 1 <= x <= max_input else 0
        if phase % 2 != Fraction(2 * expected, 1 << bits):
            raise ValueError(f"native phase mismatch at x={x}: {phase}")
    result = {
        "native_kickmix_samples": len(xs), "native_phases_match": True,
        "native_input_restored": True, "qubits": circuit.num_qubits,
        "official_verifier_passed": False,
        "native_seconds": time.monotonic() - start,
    }
    if binary is not None:
        circuit.to_file(str(binary), format="kmb")
        if km.Circuit.from_file(str(binary), format="kmb") != circuit:
            raise ValueError("native binary round-trip changed the circuit")
        result.update(kmb_sha256=sha256(binary), kmb_bytes=binary.stat().st_size)
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["generate", "verify", "native"])
    parser.add_argument("path", type=Path)
    parser.add_argument("--width", type=int, default=INPUT_WIDTH)
    parser.add_argument("--max-input", type=int, default=MAX_INPUT)
    parser.add_argument("--phase-bits", type=int, default=PHASE_BITS)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--samples", type=int, default=256)
    parser.add_argument("--binary", type=Path)
    args = parser.parse_args()
    if args.action == "native":
        result = native_check(args.path, args.width, args.max_input, args.phase_bits,
                              args.samples, args.binary)
    else:
        function = generate if args.action == "generate" else verify
        result = function(args.path, args.width, args.max_input, args.phase_bits)
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.report:
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
