# QuantumLeanLeap

A Lean 4 formalization library reproducing the framework presented in [Discovering Formally Verified Quantum Programs with AI](https://arxiv.org/abs/2611.09822), together with a benchmark modeled after the 36 problems in AlgBench.

**Public repository:** [FangHean/QuantumLeanLeap](https://github.com/FangHean/QuantumLeanLeap)  
**License:** Apache-2.0

## Contents

- `QuantumLeanLeap.GoogleQHL`: Quantum Hoare logic, classical–quantum states, measurement and feedback, weakest preconditions (WP), unbounded loop semantics, and expected resource costs.
- `GoogleQHL.Compatibility`: Compatibility with the paper's public interfaces, Physlib's Hermitian types, and Mathlib's ω-CPO and least fixed-point constructions.
- `GoogleQHL.Tasks.ParallelGrover`: A restricted instance of the paper's Parallel Grover task with N = 4, k = 1, and positive integer m. This does not constitute a reproduction of the general task or the performance results reported in the paper.
- `GoogleQHL.Bench36`: Ports all **36 AlgBench problems and 44 proof goals** into the mathematical representations used in this project.
- `scripts/bench.py`: Fixed benchmark targets, JSONL import, API-based generation adapters, Lean and axiom checks, and full-benchmark pass@k evaluation.
- `scripts/verify_qhl_candidate.py`: An independent verifier for single-qubit measurement-feedback reset candidates, using a closed JSON-based program language.

For problem mappings, type conversions, and limitations of the original tasks, see the [Migration Guide](docs/Bench36-migration.md).

## Getting Started

**Requirements:** Lean `4.33.1` and Python `3.10+`.

The Lean dependencies are limited to Mathlib, Physlib, and their transitive dependencies, with versions pinned to specific commits.

```sh
git clone https://github.com/FangHean/QuantumLeanLeap.git
cd QuantumLeanLeap
lake exe cache get
lake build
python3 scripts/bench.py list
python3 scripts/bench.py export /tmp/quantumleanleap-prompts.jsonl
```

Import the library in Lean:

```lean
import QuantumLeanLeap.GoogleQHL
import QuantumLeanLeap.GoogleQHL.Bench36
```

For more details, see [Installation and Dependencies](docs/Installation.md), [Benchmark Documentation](docs/Benchmark.md), and [Scope of the GoogleQHL Reproduction](docs/GoogleQHL-reproduction.md).

## Verification and Limitations

```sh
python3 scripts/verify_qhl.py
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify_qhl_candidate.py verification/candidates/reset-feedback.json
python3 scripts/package_release.py
```
