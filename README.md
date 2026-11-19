# Quantum Lean Leap

**v0.1.0 · Lean 4.33.1 · Apache-2.0**

已提供固定 Git 依赖的 Lake 库和 12 题开放库证明补全 benchmark。
[安装与作为依赖使用](docs/Installation.md) · [模型评测说明](docs/Benchmark.md)

```sh
lake build
python3 scripts/bench.py evaluate bench/references.jsonl --output artifacts/bench/reference --k 1
```

参考自测结果不代表任何模型成绩。公开仓库：[FangHean/QuantumLeanLeap](https://github.com/FangHean/QuantumLeanLeap)。

这是一个建立在 Mathlib 与 `Lean-QuantumAlg` 上的机器验证量子算法库。统一入口是：

```lean
import QuantumLeanLeap.Algorithms
```

核心注册表当前覆盖 12 个具有完整 `Algorithm.Solves` 证书的算法族，包括 oracle 算法、
相位/幅度估计、量子通信、阶查找、整数分解和离散对数。范围定义、证书入口和扩展标准见
[`docs/AlgorithmLibrary.md`](docs/AlgorithmLibrary.md)。

本仓库同时包含两条彼此隔离的 Google 复现线：

1. 基于 [Lean-QuantumAlg](https://github.com/QudeLeap/Lean-QuantumAlg) 的 Google VQCC `invsqrt`
   规格、证明和电路生成实验
2. 根据论文附录净室复现 Google 的经典—量子 Hoare 逻辑库核心；详见
   [`docs/GoogleQHL-reproduction.md`](docs/GoogleQHL-reproduction.md)

第二条线是净室实现，尚未确认可用于逐项比对的官方实现版本，不能称作完整复现。
目前已加入完整无界输出 CQState、状态级 WP 对偶与可靠性/最弱性、循环展开及最小固定点、
概率加权成本极限、无界 seq/qif/qwhile 成本等式、期望迭代次数与成本上界、
WP 续行概率及几何收缩判据、动态电路编译。
另有测量反馈复位任务的独立冻结规格、JSON 候选验收，以及到 QuantumAlg 原生 X/Z 的语义与资源桥接，见
[`docs/QHL-candidate-verification.md`](docs/QHL-candidate-verification.md)。
已接入固定版本 Physlib，并提供论文公开调用形式的已验证适配层，见
[`docs/GoogleQHL-interface-alignment.md`](docs/GoogleQHL-interface-alignment.md)。
适配层现有 Mathlib ω-CPO 实例、`wp`/`interp` 的 ω-Scott 连续映射，以及循环 WP 与
从底元素迭代所得 Kleene 上确界相等的证明。
官方源码 API 的逐项对照、验收流程向一般任务推广、独立无缓存构建验证及论文五个任务仍待完成。
第一个任务 Parallel Grover 已开始：现有 `N = 4`、一个未知标记、任意正数个查询槽的精确基线，
证明 Find-Any/Find-All 均以概率 1 成功且只需一轮查询；这不代表一般任务或论文性能提升已复现。
入口及边界见 [`docs/ParallelGrover-task1.md`](docs/ParallelGrover-task1.md)。
运行 `python3 scripts/verify_qhl.py` 可重新构建并审计关键声明；详细范围见上述复现说明。
下面记录独立的 VQCC `invsqrt` 部分。

## 已完成与证明边界

| 部分 | 当前状态 |
| --- | --- |
| 输入范围、目标相位、模一周误差、输入恢复与辅助位清零 | Lean 规格已实现 |
| 整数平方根量化及 40 位定点误差界 | Lean 已证明，覆盖全部合法输入 |
| 整周取模，包括 `x=1` 的相位 `1 ≡ 0` | Lean 已证明保持精度 |
| X/CX/CCX/有理数 Z_POW 到 QuantumAlg 原生门的编译 | 已实现，线号有界、控制/目标互异、无 oracle |
| 完整 22 位电路生成 | 已生成 `.kmx` 与原生 `.kmb` |
| 导出门序列的相位和输入恢复 | Python 精确整数符号解释，覆盖全部 `2^22` 个输入字 |
| 原生 kickmix 解析、模拟与二进制往返 | 548 个边界/随机样本通过 |
| 导出门序列的 QuantumAlg `basis_action` 证明 | **尚未完成**，没有构造 `VerifiedCandidate` 实例 |
| 官方竞赛 verifier、提交与排名 | **尚未运行/提交**，没有官方得分 |

Python 的全域校验不是 Lean 内核证明。`VerifiedCandidate` 把真实编译电路的
`basis_action` 和 `accurate` 都列为必需证明，不能用独立声明的理想矩阵替代。
Lean 源码没有证明占位符或新增公理；公理依赖审计见 `scripts/Audit.lean`。

## 第一题规格

采用默认参数 `n_p = 10, β = 1`，输入 `x` 为 little-endian 的 22 个量子比特：

\[
1\le x\le 3(2^{10}-2)^2=3\,133\,452
\]

要求输入恢复、辅助位清零，并实现相位：

\[
|x\rangle|0\rangle\longmapsto e^{2\pi i\phi(x)}|x\rangle|0\rangle,
\qquad d_{\mathbb R/\mathbb Z}\!\left(\phi(x),\frac1{\sqrt{x}}\right)
\le\frac{2^{-24}}{\sqrt{x}}
\]

这里形式化的是实数上的数学目标。官方 verifier 使用 64 位定点相位比较并为旋转合成计价；
本项目没有把它的 Python 实现或计分逻辑形式化。无测量电路不依赖随机测量分支；带 HMR 的候选不属于当前 Lean 编译子集。

QuantumAlg 的矩阵基底使用 big-endian 标号，因此 `physicalPosition` 反转导出的线号。
`cleanWord` 把 `x` 放在数值低位，辅助位放在高位。

## 数值构造与电路

用整数除法和整数平方根计算：

\[
q(x)=\operatorname{isqrt}\!\left(\left\lfloor\frac{2^{80}}x\right\rfloor\right),
\qquad \phi(x)=\frac{q(x)\bmod 2^{40}}{2^{40}}
\]

`Arithmetic.lean` 先证明

\[
q(x)^2x\le 2^{80}<(q(x)+1)^2x
\]

再推出量化误差小于 `2^-40`。合法范围内 `sqrt(x) < 2048`，所以该误差严格小于允许误差。
在非法输入 `x=0` 和 `x>maxInput` 上，生成器选择零相位。

电路生成器对完整整数表作 Walsh 变换。若 `N=2^22`、`f(x)=q(x) mod 2^40`
（非法输入处为零），定义

\[
A_s=\sum_x f(x)(-1)^{\langle s,x\rangle}
\]

对每个非零掩码 `s`，在奇偶位上施加 half-turn 指数 `-A_s/2^60` 的 `Z_POW`。
由于 `f(0)=0`，这些相位相加恰好给出 `f(x)/2^40`，无需额外全局相位。
Gray-code 顺序复用 CNOT 奇偶计算，并在每组结束时恢复输入。
所有角度导出为精确有限小数，不经过浮点数。

当前完整基准资源：

| 资源 | 数量 |
| --- | ---: |
| 量子比特 | 22 |
| 辅助位 | 0 |
| CX | 4,194,302 |
| Z_POW | 4,194,303 |
| 总门数（不含寄存器元数据） | 8,388,605 |
| KMX 文件 | 349,735,457 字节 |
| KMB 文件 | 125,829,482 字节 |

这是一份正确性基准，**不是资源优化结果**。没有 Toffoli 不代表零成本；大量精细旋转需要计入合成成本。
不应把原始门数当作竞赛得分。下一步优化应优先考虑分段近似与可逆算术，而不是继续扩大查表电路。

## 复现

Lean 依赖通过 `../../../Lean-QuantumAlg` 指向本机仓库，工具链为 Lean 4.33.1。
在其他目录使用时，需要调整 `lakefile.toml` 中的依赖路径。

```sh
lake build
lake env lean scripts/Audit.lean
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
.venv/bin/python -m unittest discover -s scripts -v
```

完整电路及验证：

```sh
.venv/bin/python scripts/invsqrt.py generate artifacts/invsqrt.kmx --report artifacts/generation.json
.venv/bin/python scripts/invsqrt.py verify artifacts/invsqrt.kmx --report artifacts/validation.json
.venv/bin/python scripts/invsqrt.py native artifacts/invsqrt.kmx --samples 512 --binary artifacts/invsqrt.kmb --report artifacts/native.json
```

生成和验证需要数百 MB 内存及约 454 MiB 的电路文件空间。大型电路文件、虚拟环境和编译缓存已加入 `.gitignore`。
验证读取**磁盘上的实际门序列**，解释每根线的输入奇偶掩码和有理数相位，检查输入线全部恢复，
再通过整数 Walsh 变换计算全部基态相位。它还逐一检查全部 3,133,452 个合法输入的整数平方根上下界。
原生检查另外读取 KMX、模拟实际门、导出 KMB，并重新读回比较电路相等。
JSON 报告包含 SHA-256，可用于把验证结果绑定到生成文件。

先查看小电路：

```sh
.venv/bin/python scripts/invsqrt.py generate artifacts/toy.kmx --width 3 --max-input 5
.venv/bin/python scripts/invsqrt.py verify artifacts/toy.kmx --width 3 --max-input 5
```

## 文件与下一步

- `QuantumLeanLeap/GoogleVQCC/InvSqrt/Specification.lean`：任务定义、矩阵语义证书、任意合法叠加态的线性扩展
- `QuantumLeanLeap/GoogleVQCC/InvSqrt/Arithmetic.lean`：可执行整数相位算法和全域精度证明
- `QuantumLeanLeap/GoogleVQCC/InvSqrt/Circuit.lean`：受限门语言、大小端转换、原生编译和 `VerifiedCandidate` 接口
- `scripts/invsqrt.py`：精确电路生成、导出文件全域校验、原生模拟及 KMB 导出
- `scripts/test_invsqrt.py`：小规模逐基态模拟、错误电路拒绝、溢出保护、精确角度序列化等 7 项测试
- `artifacts/*.json`：本次完整规模运行报告

后续证明工作是建立奇偶相位解释器到 `compile … .binaryMatrix` 的可靠性定理，并在 Lean 中核验
Walsh 重构证书，最终填入 `VerifiedCandidate.basis_action`。现有数值误差定理可直接复用。
后续电路搜索可复用 `generate → verify → native` 流程；有官方 verifier 后应额外加入官方验收与计分。

## 来源

- [官方竞赛页面](https://www.kaggle.com/competitions/google-verifiable-quantum-circuit-compilation/)
- [官方论文 §III.1.3：参数、精度、输入/辅助位约束、验证与计分](https://arxiv.org/html/2610.23832v1#S3.SS1.SSS3)
- [Qualtran：KMX 文件格式](https://github.com/quantumlib/Qualtran/blob/main/docs/kickmix/kickmix_format.md)
- [Qualtran：Z_POW 等门的语义](https://github.com/quantumlib/Qualtran/blob/main/docs/kickmix/kickmix_instructions.md)

参数与语义核对日期：2026-11-16。官方 Kaggle verifier 文件尚未下载；不声称已经逐行核对该实现。
