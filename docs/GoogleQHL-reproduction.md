# 论文复现范围

目标是《Discovering formally verified quantum programs with AI》的形式化框架及本项目的评测基准。
这是独立实现，不是 Google 官方库的逐行副本。来源快照见 `verification/interface-sources.json`。

已实现并纳入 Lean 构建的部分：

- 经典存储、部分密度算子、可求和 CQState、可观测量与期望。
- 程序语法、测量、经典反馈、最弱前置条件、分支和完整状态语义及对偶定理。
- 无界循环、递增链、ω-CPO、连续性、最小不动点和资源成本。
- Physlib Hermitian 类型与论文公开形式的适配；详见 [接口说明](GoogleQHL-interface-alignment.md)。
- Parallel Grover 的受限精确子实例；详见 [任务说明](ParallelGrover-task1.md)。
- 独立矩阵定义的 X/Z 门、测量反馈复位语言及冻结规格验收。
- 原 AlgBench 36 题的规格迁移，及统一证明补全评测器。

未完成：五项应用任务的一般实例、Google 官方代码兼容性验证、官方 Lean Comparator、
论文 AI 搜索系统及性能复现、一般量子门编译器。Parallel Grover 的查询模型尚未整体接入动态 QHL 解释器。

2026-11-19 按项目范围调整移除了算法合集、Lean-QuantumAlg 依赖和 VQCC/invsqrt 竞赛实现。
当前依赖为固定版本 Mathlib 与 Physlib。旧的本机结果只作为历史证据，不代表当前版本验证结果。
`scripts/verify_qhl.py` 对当前源码重新构建并审计公理依赖；只接受 propext、Classical.choice、Quot.sound。
