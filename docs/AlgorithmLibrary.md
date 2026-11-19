# Quantum Lean Leap：量子算法库

## “完整”的可验证定义

量子算法没有封闭的有限全集，因此本项目不把“完整”解释成“收录世界上所有算法”。
库采用两个明确层次：

1. **核心范围完整**：`CoreFamily` 枚举的 12 个基础算法族必须各出现一次，并具有可调用的
   正确性证书
2. **研究范围持续扩展**：HHL、QSVT、Hamiltonian simulation、量子游走、QML、QEC 等
   只有在语义、正确性、成功率和资源界连接到同一个执行对象后，才能进入 verified catalog

`verifiedCatalog_covers_core` 和 `verifiedCatalog_families_nodup` 分别证明核心范围无缺项、无重复。

## 公共入口

```lean
import QuantumLeanLeap.Algorithms
```

这个入口统一导出：

- Mathlib 上的有限维量子线性代数
- 状态、密度算子、测量、动态电路和 oracle
- QFT、相位回踢、Hadamard/SWAP test 等基础构件
- 12 个完整算法端点
- 证明值别名 `QuantumLeanLeap.Algorithms.Certificates`
- 机器检查的算法注册表 `QuantumLeanLeap.Algorithms.verifiedCatalog`

## 当前已验证核心

| 类别 | 算法 | 证书入口 |
| --- | --- | --- |
| Oracle | Bernstein–Vazirani | `Certificates.bernsteinVazirani` |
| Oracle | Deutsch–Jozsa | `Certificates.deutschJozsa` |
| Oracle | Simon | `Certificates.simon` |
| Oracle | Grover search | `Certificates.groverSearch` |
| Estimation | Quantum phase estimation | `Certificates.quantumPhaseEstimation` |
| Estimation | Amplitude estimation | `Certificates.amplitudeEstimation` |
| Communication | Teleportation | `Certificates.teleportation` |
| Communication | Superdense coding | `Certificates.superdenseCoding` |
| Number theory | Exact order finding | `Certificates.exactOrderFinding` |
| Number theory | Shor-style factoring | `Certificates.integerFactoring` |
| Number theory | Finite-cyclic DLP | `Certificates.finiteCyclicDLP` |
| Number theory | Elliptic-curve DLP | `Certificates.ellipticCurveDLP` |

这些端点复用固定版本的 `Lean-QuantumAlg`。其 `Algorithm.Solves` 合约把成功概率、输出状态、
借用寄存器恢复、事件上界、空间上界和深度上界绑定到同一实际执行，而不是互不相干的声明。

## 本仓库自己的扩展

- `GoogleQHL`：经典—量子程序语法、状态/断言、有限展开 WP 和资源计数
- `GoogleVQCC.InvSqrt`：VQCC inverse-square-root phase 规格和数值精度证明

VQCC 目前还没有导出电路的完整 `basis_action` Lean 证明，所以不会放入 verified algorithm
catalog。Python 全域枚举检查也不会冒充 Lean 内核证明。

## 下一批模块

按基础依赖和证明复用价值排序：

1. Hamiltonian simulation 与 product formula / LCU / qubitization
2. QSVT 与 block encoding
3. HHL/QLSA（输出为量子态，单独形式化可观测量读取成本）
4. Quantum walks 与 counting
5. VQE/QAOA 的参数化电路语义，不把经典优化器成功当作无条件定理
6. Quantum kernels 与线性代数子程序
7. QEC 编码、syndrome、decoder specification 与逻辑错误事件

每个新算法进入注册表前必须提供：

- 独立问题规格
- 一个命名执行对象
- 正确性或近似误差定理
- 成功概率定理（若为随机算法）
- ancilla/borrowed-state 恢复
- 事件、空间与深度界
- 无 `sorry`、无额外公理的构建审计

## 验证命令

```sh
lake build
lake env lean scripts/AlgorithmAudit.lean
rg -n '\bsorry\b|^\s*axiom\b' QuantumLeanLeap
```

