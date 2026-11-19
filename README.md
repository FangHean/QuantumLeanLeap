# QuantumLeanLeap

《[Discovering formally verified quantum programs with AI](https://arxiv.org/abs/2611.09822)》的独立 Lean 4 复现与配套 benchmark。
本项目不依赖 Lean-QuantumAlg，不包含算法合集或 Google VQCC 竞赛代码。
公开仓库：[FangHean/QuantumLeanLeap](https://github.com/FangHean/QuantumLeanLeap)。许可证：Apache-2.0。

## 内容

- `QuantumLeanLeap.GoogleQHL`：量子 Hoare 逻辑、经典–量子状态、测量和反馈、WP、无界循环语义、期望资源成本。
- `GoogleQHL.Compatibility`：论文公开接口、Physlib Hermitian 类型、Mathlib ω-CPO 与最小不动点适配。
- `GoogleQHL.Tasks.ParallelGrover`：论文 Parallel Grover 的 N=4、k=1、正整数 m 子实例；非一般任务或论文性能复现。
- `GoogleQHL.Bench36`：将 AlgBench 的 **36 道题、44 个证明目标**迁移到本项目的数学表示。只使用原题规格，不引入 Alg 算法库、Register/Gate/Circuit 系统或 cslib。
- `scripts/bench.py`：固定目标、JSONL 导入、API 生成适配器、Lean/公理检查、全题集 pass@k；多目标题全部认证才算通过。
- `scripts/verify_qhl_candidate.py`：独立的单量子比特测量反馈复位候选验收，候选为闭合 JSON 程序语言。

36 题的目标是待证明的 `Prop` 定义，**不是 36 个已经证明的定理**。目前未运行实际模型评测。
纯代数、傅里叶与分析命题位于数学支撑层；不把它们强行改写成不等价的 Hoare 三元组。
题目对应关系、类型转换和原题限制见 [迁移说明](docs/Bench36-migration.md)。

## 使用

Lean `4.33.1`；Python `3.10+`。Lean 依赖仅 Mathlib 与 Physlib 及其传递依赖，固定 commit。

```sh
git clone https://github.com/FangHean/QuantumLeanLeap.git
cd QuantumLeanLeap
lake exe cache get
lake build
python3 scripts/bench.py list
python3 scripts/bench.py export /tmp/quantumleanleap-prompts.jsonl
```

```lean
import QuantumLeanLeap.GoogleQHL
import QuantumLeanLeap.GoogleQHL.Bench36
```

详见 [安装与依赖](docs/Installation.md)、[评测说明](docs/Benchmark.md)、[论文复现范围](docs/GoogleQHL-reproduction.md)。

## 验证与边界

```sh
python3 scripts/verify_qhl.py
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify_qhl_candidate.py verification/candidates/reset-feedback.json
python3 scripts/package_release.py
```

`lake build` 检查全部题目规格的类型，不代表解出了题目。12 题小型校准集单独保留在
`bench/calibration.json`，用于评测器自测，不混入正式 36 题或替代未完成的目标。

本项目尚未完整复现 Google 的全部五项应用任务、AI 搜索流程、官方验证器和性能结果。
没有确认可作逐行比对的 Google 官方源码版本；论文接口适配不等于官方 API 完全兼容。
具体门执行层仅保留经过矩阵证明的单比特 X/Z 复位片段，没有通用原生门编译器。
