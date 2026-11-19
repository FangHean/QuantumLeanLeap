# 测量反馈复位候选验收

独立的小型程序生成任务，与正式 36 题证明补全分开。

```sh
python3 scripts/verify_qhl_candidate.py verification/candidates/reset-feedback.json
```

候选仅包含 `skip`、`x`、`z`、`measure`、顺序组合和 `if_zero`，不接受自定义矩阵、预算或 Lean 证明。
目标对任意输入矩阵证明复位语义，并验证最坏路径最多一个 X/Z 门、一次测量。
`ResetSemantics.lean` 将闭合语言连接到独立动态矩阵语义，证明逐测量历史与期望成本保持。
X/Z 矩阵在本库直接定义并证明酉性；不依赖外部算法库或原生编译后端。

当前基线为 `verification/reset-paper-v7.lock.json`，包含源码、工具链和依赖 commit。
验收不会自动刷新基线，环境变化会撤销成功结论。报告位于 `artifacts/qhl-verification/`。

这不是 Google 官方验证器，不保证证明自动化完备，也不为可执行 Lean 代码提供操作系统沙箱。
