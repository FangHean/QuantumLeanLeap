# 任务一：Parallel Grover Search

当前完成的是一个可机器检查的**精确查询模型基线**：`N = 4`、`k = 1`、任意 `m > 0`。
同一份不依赖未知标记位置的电路，从零地址寄存器开始，一轮并行 oracle 查询后，
每个地址槽都等于唯一标记元素。Find-Any 和去重后的 Find-All 成功概率均为 1，期望查询深度为 1。
这不是论文一般规模、多目标算法或性能提升的复现。

## 论文规格

依据 [论文 v2 的 Appendix E.1–E.3](https://arxiv.org/html/2611.09822v2)，
本次使用已有 v2 正文快照，其 SHA-256 记录于 `verification/interface-sources.json`。

- 搜索空间 `N = 2^n`，`n ≥ 1`；未知标记集合大小为已知 `k > 0`。
- Find-Any 输出一个标记元素；Find-All 输出全部标记元素。
- 要求以概率 1 终止且零错误，不能用较低成功概率交换查询数。
- 可逆 oracle 为 `|b,x⟩ ↦ |b xor marked(x),x⟩`。
- 一轮可在 `m` 个互不重叠的查询槽上同时调用 oracle，计费为 **一轮**。
- 与标记集合无关的酉变换、测量和经典控制不计 oracle 费用。
- 论文比较的是大 N 极限下的表现，m、k 分别取 1 至 1024 的二次幂，共 121 组设置。

`Specification.Instance` 表达基本合法输入条件；论文参数网格与渐近评价另属评估层，尚未实现。

## 已证明的内容

| 文件 | 保证 |
| --- | --- |
| `Oracle.lean` | 任意 N、m 的可逆位 oracle；并行置换矩阵酉性；相位反冲；全 `\|+⟩` 目标位不受 oracle 影响 |
| `Embedding.lean` | 将任意地址态（包括纠缠态）嵌入正规化 `\|−⟩` 辅助目标位后保持总 Born 权重；真实位 oracle 实现相位查询 |
| `ExactFour.lean` | `H ⊗ H` 准备、四维扩散矩阵及酉性；对全部四种未知标记位置的一次 Grover 精确输出；任意 m 的张量积推广 |
| `Circuit.lean` | 免费酉门、并行查询、顺序组合的受限电路语言；解释所得矩阵的酉性；固定电路的零输入输出等式及一轮查询计数 |
| `Specification.lean` | 独立 Find-Any/Find-All 判定、Born 权重、总概率与期望轮数；`exactFour_contract` 汇总证书 |
| `Regression.lean` | 无查询时成功率仅 1/4；两个标记时同一单槽迭代成功率仅 1/2；零查询槽不能输出全部标记；两个槽仍只计一轮 |

目录为 `QuantumLeanLeap/GoogleQHL/Tasks/ParallelGrover/`。
`exactFourCircuit m` 没有 target/marked 参数。未知标记只在解释电路时传给查询节点，
准备门和扩散门因此是固定的。一般调用者仍应保持同一电路用于所有 oracle 实例，
而不是在外部根据答案生成不同的免费门。

`expectedRounds` 在这个有限、无分支语言中按最终 Born 权重乘确定查询轮数求和；
它不是一般自适应循环成本解释器。本实例已单独证明总权重为 1。

## 使用与验证

```lean
import QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover

open QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover

example (target : Fin 4) :
    successWeight (exactFourCircuit 2) (singletonMark target)
      (acceptsAll (singletonMark target)) = 1 :=
  exactFour_findAll 2 target

example : (exactFourCircuit 2).rounds = 1 := exactFourCircuit_rounds 2
```

```sh
lake build QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover
python3 scripts/verify_qhl.py
```

核心声明纳入统一公理审计，仅允许 Lean/Mathlib 的标准公理。
有限矩阵运算使用 Lean 证明核检查；没有浮点抽样、`sorry`、额外公理或 `native_decide`。
既有 JSON 复位候选验收仍只接受复位任务；没有把它冒充为 Parallel Grover 候选验证器。

## 尚未完成

1. 一般 `N = 2^n`、`k ≥ 1` 的零错误算法：普通 Grover 的固定次数测量通常不保证确定成功。
   下一步应接入已知 Grover 成功概率、oracle 验证结果，以及失败重启的概率 1 终止和期望轮数证明。
2. 并行多目标及 Find-All 的去重、已找到元素的消标记和继续搜索。
3. 论文的弱测量策略、分区/重启组合、Johnson 图相干机制及 121 组参数的性能比较。
4. 受限查询电路到现有 CQState/QProg 动态执行及资源语义的端到端桥接；实际辅助位准备、
   全寄存器电路到原生门语言的编译。当前已证明正规化嵌入和 oracle 等式，未声称这些编译步骤完成。
5. 独立任务候选入口、官方规格/API 对照与官方验收。

该子实例并未展示并行加速：m 个槽最终得到同一个标记，一个槽也只需一轮。
它用于建立精确的 oracle、概率和计费基线，不能据此宣称复现了论文的 1.22× 或 2.55× 提升。
