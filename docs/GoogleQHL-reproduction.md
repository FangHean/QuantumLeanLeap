# Google 量子形式化库净室复现

本项目根据 *Discovering formally verified quantum programs with AI* 附录 A、B
重建经典—量子 Hoare 逻辑与电路接口。它是净室实现，不是官方源码镜像，**尚未完成完整复现**。
2026-11-18 直接核对的论文 v2 代码声明仍是“将公开”；该声明不能证明当天所有官方渠道均未发布代码。
这里没有确认可用于逐项比对的官方实现版本，也不宣称与其 API 或五个问题的验收结果等价。

统一入口：

```lean
import QuantumLeanLeap.GoogleQHL
```

## 已实现并证明的部分

| 层次 | 实现与主要证明 | 范围 |
| --- | --- | --- |
| 基础对象 | 整数 Store、PartialDensity、CQState、Observable、酉和测量 | 有限量子维度，经典状态允许无限可求和支持 |
| 正向执行 | interpApprox、interpApprox_positive、interpApprox_trace_nonincreasing | 全部 QProg 构造子及嵌套循环的有限展开 |
| 有界 WP | expect_wpApprox、wpApprox_effect、wpApprox_mono | 与独立正向执行严格对偶，保持 Löwner 序和效应区间 |
| 有界 Hoare 逻辑 | hoareBounded_iff、wpBounded_soundness、wpBounded_weakest | 总正确性，含顺序与 consequence 规则 |
| 无限展开 | effectChain_exists_lub、pairing_effectSup | 递增效应算子序列的最小上界，及与期望上确界的交换 |
| 无界 WP | wp、expect_wp、wp_soundness、wp_weakest | 对任意 PSD 输入分支，和正向执行期望极限一致 |
| 无界组合 | wp_seq、hoare_seq、wp_while_unfold、wp_while_least | 顺序组合、嵌套循环展开、最小固定点性质 |
| 状态与期望 | expectation_summable、expectation_bounds | 任意合法 CQState 的期望求和收敛且位于 [0,1] |
| 有限状态桥接 | FiniteState.toCQState、expect_interpFinite | 同一经典状态的历史分支相加，得到合法输出 CQState |
| 状态极限与混合 | stateSup、stateSup_density_isLUB、stateSum | 逐状态 Löwner 最小上界、可求和混合、期望与无限求和/极限交换 |
| 完整正向状态 | interp、interp_mass_le、expect_interp | 任意可求和 CQState 输入、无界及嵌套循环，实际输出 CQState 的正性与总质量界 |
| 状态级规则 | interp_seq、interp_while_unfold、wp_state_soundness、wp_state_weakest | 顺序/循环的输出状态等式，物理初态量化的 Triple 与原 Hoare 等价 |
| 基本指令 | wp_assign、wp_qset、wp_apply、wp_measure、interp_assign | 无界 WP 基本规则；赋值按前像求和，完备测量和酉操作保持质量 |
| 资源成本 | expectedCostApprox_le、expectedCostApprox_mono、expectedCostApprox_tendsto | 概率加权前缀成本、语法预算上界、单调极限，允许无限成本 |
| 初态混合成本 | expectedCost、expectedCost_le_mass | 对各经典初态的成本求和，已有分支上界到总质量上界的规则 |
| 无界成本组合 | expectedCost_stateSup、expectedCost_stateSum、expectedCost_seq、expectedCost_if、expectedCost_while_unfold | 成本对状态极限连续、对混合可加；seq/qif/qwhile 的精确等式，允许无限成本 |
| 成本上界规则 | CostBound、costBound_seq、costBound_if、expectedCost_while_le_potential | 顺序预算相加、分支预算取最大、用非负算子势函数证明循环成本上界 |
| 期望迭代次数 | expectedCost_while_eq_tsum、expectedCost_while_le_iterations、expectedCost_while_eq_iterations | 循环成本等于各轮实际进入状态上的体成本之和；每轮预算乘期望迭代次数，上界及均匀计费等式 |
| WP 续行判据 | entryProbability_eq_wp、expectedIterations_eq_wp_series、expectedCost_while_le_of_wp | 用续行程序的 WP 表达进入概率；从 Löwner 算子收缩条件推出几何成本界 |
| 具体门 | PrimitiveGate.unitary、native_trace_length | H/X/Y/Z/S/T/CX/SWAP/TOFF，实际 QuantumAlg 矩阵和原生电路 |
| 动态电路 | compile_correct、DynamicCircuit.expect_wp、runCost_le | 单量子比特测量、经典分支、到 QProg 的语义保持编译、最坏路径计数上界 |
| 验收候选原生桥接 | ResetLanguage.Program.toDynamic_compile、toDynamic_run、native_count、native_expected_gate_bound | 复位候选的 X/Z 对齐 QuantumAlg 实际原生矩阵；逐历史语义及最坏/期望原生门预算保持 |
| 论文接口与 Physlib 桥接 | PaperAPI.stateEquiv、expect_eq_core、expect_wp、triple_iff、wpOrderHom | 实际 HermitianMat 类型、Prop 条件、零态复位、interp.toStateFun；双向表示转换和期望/偏序保持 |
| 标准序结构与连续映射 | PaperAPI.observableOmegaCPO、cqStateOmegaCPO、wpContinuousHom、interpContinuousHom | 实际 Mathlib ω-CPO 与底元素；断言采用逐点实例；WP 和正向语义保持递增链上确界 |
| 标准循环不动点接口 | PaperAPI.loopContinuousHom、wp_qwhile_eq_omegaSup_iterates | 循环 WP 等于 Mathlib Kleene 链从底元素开始的上确界；每步采用循环体完整无界语义 |

`expect_wp` 保留了原有的分支极限接口；新增 `expect_interp` 证明完整状态级等式：

```lean
expectation (interp p S) Q = expectation S (wp p Q)
```

`interp` 从有限正向历史的状态最小上界和初态混合构造，不通过上述期望等式定义输出。
`Triple` 对所有合法 CQState 量化，`triple_iff_hoare` 证明它与原先未归一化 PSD 测试版本等价。
非终止和中止的历史不计作成功。接口命名和封装仍不声称与官方源码逐项一致。

## 语义约定

- `fuel = 0` 的循环输出为空，包括条件已经为假的循环；这代表从底元素开始的近似。
  条件为假的循环在第一次展开即可返回输入。无界极限消除此近似截断。
- 嵌套循环在外层第 `k+1` 次展开时使用 `k` 展开体程序。这一共同递增近似方式已经证明单调，
  其上确界满足无界循环展开和最小固定点等式。
- 测量产生未归一化 PSD 分支；不把每个分支重新归一化后当作概率一，也不覆盖同名经典状态。
- `Measurement.complete` 允许小于等于恒等算子，因而支持丢失概率质量的操作。
  完备测量保持总迹另有 `measurement_preserves_mass` 定理。
- 成本在指令执行时支付。后续 abort 不会取消此前成本；非终止成本可为无穷大。
- `expectedIterations` 对各轮进入循环体的质量求和。第零项是初始条件为真的质量；
  对未归一化输入不作条件归一化。中止或体程序不终止会减少之后的进入质量，
  这种减少不能直接解释为正常退出概率。
- 外层循环展开保留体程序的无界语义；`expectedCost_while_eq_iSup_unroll` 证明它与
  共同递增 fuel 近似具有相同成本上确界。因此循环成本级数也适用于含嵌套循环的体程序。
- 效应算子的序是 **Löwner 序**，不是矩阵元素逐项大小关系。
- 动态电路使用 QuantumAlg 的 big-endian 物理线号，测量投影也采用相同约定。
- 这九种门是本实现明确选定的封闭门集，不能在没有官方源码对照时宣称是官方逐构造子的复制。
  SWAP 源层计数为一，原生展开计数为三个 CNOT。测量源门计数为零，分支取最大值。
  不同门类别各自的最大计数，可能来自不同执行路径。

## 回归证明

`Regression.lean` 检查了有实际语义差异的情形：

1. 对任意二维输入矩阵，Z 测量后按结果条件执行 X，两条输出历史的量子矩阵之和
   等于原始迹乘 `|0⟩⟨0|`；因此覆盖混合态和非零非对角元。
2. 完备测量保持总迹。
3. 永远为真的恒等门循环，任意有限展开输出为空，无界输出期望为零。
4. 同一循环每轮计费一次，前缀成本为 `k × tr(ρ)`；迹为一时总成本为无穷大。
5. 一个门后立即 abort，已执行的门仍被计费。
6. 分支门数取最大值；SWAP 的源层门数和原生展开门数分别为一和三。

`StateRegression.lean` 另外检查完整状态语义：

1. 初始条件为假的无界循环严格返回原初态，包括无限可求和的经典混合。
2. 永久循环严格输出零 CQState，而不是仅某一个 observable 的期望为零。
3. 覆盖唯一经典变量时，所有前像的量子矩阵相加；定理对任意合法 CQState 成立。
4. 任意程序后接 abort，不改变其已经付出的期望成本，包括程序内部有无界循环的情况。

`IterationRegression.lean` 检查迭代次数与实际成本的区别：

1. 条件恒为假时，期望迭代次数为零。
2. 循环体立即 abort 时，期望迭代次数恰好是初始进入质量；不会把中止后的轮次继续计数。
3. 四结果完备 Kraus 测量，各算子为 `I/2`，其中两个结果触发重试。
   已证明续行效应恰好为 `I/2`，期望迭代次数及按每次测量收费一单位的期望成本，
   均不超过初始进入质量的两倍。这是测量语义层实例，未声明其原生门分解。
4. 恒真条件下的 skip 循环，对正质量初态有无限期望迭代次数，尽管 skip 的资源成本为零。

这些是 Lean 定理，不是浮点数模拟抽样。

## 迭代成本规则

令 `Sₙ` 是第 n 轮实际进入循环体的未归一化 CQState，`pₙ = mass(Sₙ)`。
已证明（成本和求和均允许取无穷大）：

\[
\operatorname{Cost}(\text{while},S)
=\sum_{n\ge0}\operatorname{Cost}(\text{body},S_n)
\le C\sum_{n\ge0}p_n
=C\,\mathbb E[N]
\]

前提是体程序对所有合法初态的成本至多为 `C × mass`。
若每轮均匀计费恰好为该值，上述不等式也提升为等式。
若在满足循环条件的经典状态上，体程序对条件指示算子的 WP 满足
`wp(body, guardIndicator) ≤ q • I`，其中 `0 ≤ q < 1`，则：

\[
\mathbb E[N]\le\frac{p_0}{1-q},\qquad
\operatorname{Cost}(\text{while},S)\le\frac{C p_0}{1-q}
\]

Lean 的通用版本在 ENNReal 中书写，也覆盖无穷上界；取得有限结论需要相应的有限预算和严格收缩条件。

## 距离完整复现仍缺什么

按依赖顺序，后续工作是：

1. **官方源码 API 对齐**：已接入固定版本的真实 Physlib HermitianMat，并对齐论文公开的
   Prop 条件、状态子类型、期望、interp.toStateFun 和 WP/Triple 调用形式，见
   [接口对齐说明](GoogleQHL-interface-alignment.md)。仍需确认 Google 官方源码版本，核对
   完整类型类、内部封装和自动化接口；当前适配不能替代该源码对照。
2. **验收流程推广与对齐**：已有测量反馈复位的独立冻结规格、JSON 候选入口、原生 X/Z 桥接和 Lean 证书检查，
   详见 [候选验收说明](QHL-candidate-verification.md)。仍需扩展到一般程序及论文任务，
   接入 Lean Comparator 或经过验证的等价流程。当前工具不声称是官方验证器。
3. **论文五个任务**：分别建立并验证 parallel Grover、fixed-point arcsin、stopping power、
   non-Born–Oppenheimer dynamics、P450 的规格、实际电路与资源上界。
   Parallel Grover 已有 `N = 4, k = 1, m > 0` 的精确查询模型基线、正规化位 oracle 桥接、
   Find-Any/Find-All 概率 1 与一轮成本证明，见 [任务一说明](ParallelGrover-task1.md)。
   一般规模、多目标、自适应循环及论文性能结果仍未完成。
   项目原有的普通 Grover 证书和 VQCC invsqrt 实验不能充当这些任务的完成证明。
4. **可移植构建**：QuantumAlg 目前是本地路径依赖；审计记录实际 commit，但配置尚未固定该 commit。
   需要在独立干净环境中完成依赖固定与构建，才能宣称他人可以直接复现相同版本。

不以代码行数、算法名称数或 Lake 构建任务数计算“复现百分比”。

## 验证与证据

```sh
python3 scripts/verify_qhl.py
```

脚本先运行全项目 `lake build`，再执行 `scripts/QHLAudit.lean`。
对列出的关键声明，递归公理依赖仅允许 `propext`、`Classical.choice`、`Quot.sound`，
任何其他公理（包括证明占位符和额外计算信任公理）使审计失败。
报告包含被检查的声明、实际依赖 commit、工具链和 QHL 源码 SHA-256；不会记录虚构的官方通过状态。

- `artifacts/qhl/audit.json`：机器可读审计结果
- `artifacts/qhl/build.log`：构建日志
- `artifacts/qhl/axioms.log`：Lean 公理依赖输出

审计覆盖所列关键声明的传递依赖，不宣称已经对全部上游源码做独立安全审查。

候选验收单独运行 `python3 scripts/verify_qhl_candidate.py verification/candidates/reset-feedback.json`。
该入口针对一个固定本地任务，分别检查实际输出矩阵与两类资源预算；不接受候选自行提供的规格或成本。
冻结清单核对实际依赖 commit，但不改变项目仍使用本地 QuantumAlg 路径依赖的事实。

## 公开依据

- [论文 v2，附录 A/B 与代码声明](https://arxiv.org/html/2611.09822v2)
- [Physlib](https://github.com/leanprover-community/physlib)
- [Lean-QuantumAlg](https://github.com/QudeLeap/Lean-QuantumAlg)


2026-11-19 发布准备更新：QuantumAlg 已改为固定 commit 的公开 Git 依赖，旧版本所述本地路径限制已移除；
独立无缓存构建仍待验证。当前复位基线为 `reset-release-v6.lock.json`，保留 v1–v5 历史文件。
