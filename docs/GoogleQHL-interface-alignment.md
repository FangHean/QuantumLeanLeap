# 论文公开接口与 Physlib 类型对齐

本轮对齐的是 Google 论文附录公开的数学定义、打印出的 Lean 调用形式，以及真实 Physlib 类型。
这是有证明的适配层，命名为 `QuantumLeanLeap.GoogleQHL.PaperAPI`。
没有确认 Google 官方源码 commit，因此不宣称其模块路径、命名空间、全部构造子参数或实例完全兼容。

## 来源与版本

2026-11-18 直接读取了 [论文 v2](https://arxiv.org/html/2611.09822v2)。Code availability 和
参考文献 191 仍说库、规格和结果将公开；该页没有给出可用于本次比对的源码版本。
这不能证明所有其他官方渠道都未发布代码。读取来源及正文 SHA-256 见
`verification/interface-sources.json`。

Physlib 实际依赖已加入 `lakefile.toml`，固定为
[`a50684a1919e84dc1c761028ff4f77cd59e2de6b`](https://github.com/leanprover-community/physlib/tree/a50684a1919e84dc1c761028ff4f77cd59e2de6b)。
该版本上游声明 Lean 4.33.0。本项目保持 Lean 4.33.1 和 Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`，在这组版本上编译并验证实际导入的
`QuantumInfo.ForMathlib.HermitianMat.Inner` 及其依赖。

查询时 Physlib HEAD 为 `4222166c0e3e41300971ee768ad535d5679c0146`，要求 Lean 4.35.0。
本轮没有升级到该版本，也没有构建整个 Physlib、QuantumInfo 或文档生成目标。
Physlib 带入的文档依赖由 Lake manifest 记录；其存在不表示这些目标已经被测试。

## 已对齐的接口

| 论文/上游公开形式 | 原本地形式 | 当前适配与验证 |
| --- | --- | --- |
| Hermitian 算子、实数 trace | 复矩阵及 PSD 证明 | 直接使用 Physlib `HermitianMat`，未自行仿造同名类型 |
| 部分密度算子子类型 | `PartialDensity` 结构 | `densityEquiv` 双向转换及往返恒等 |
| 区间 Observable 子类型 | `Observable` 结构 | `observableEquiv`；Löwner 序保持 |
| 存在总质量的 CQState 子类型 | 显式 mass 与 HasSum 字段 | `stateEquiv`；任意合法 CQState 往返恒等 |
| 实 Hermitian 内积定义的 `expect` | 复矩阵乘积迹的实部求和 | `expect_eq_core` 严格相等 |
| 可判定 `Store → Prop` guard | `Store → Bool` | `QProg.toCore` 使用随构造子携带的判定过程；分支/循环规则已证明 |
| `qset` 复位至基态零，维数正 | 可指定任意 `Fin d` 基态 | 新入口 `qset` 无索引参数，要求 `[NeZero d]`，固定映射至 0 |
| `(interp p).toStateFun S` | `interp p S` | `StateTransformer` 公开投影及顺序语义等式 |
| `expect_wp p S Q`，WP 期望在等号左侧 | 核心分支/状态定理具有不同签名 | 新入口同参数顺序、同等式方向，证明复用已验证的完整状态语义 |
| 状态级 `Triple` | 已有核心 `Triple` 与 `Hoare` | `triple_iff_core` 和 `triple_iff`；可靠性、最弱性、单调 WP |
| ω-CPO 与连续语义 | 自定义递增矩阵/状态极限 | Mathlib `OmegaCompletePartialOrder` 和 `OrderBot` 实例；`wpContinuousHom`、`interpContinuousHom` |
| 循环最小不动点 | 已有核心展开/最弱前不动点证明 | `loopContinuousHom` 与标准 `fixedPoints.iterateChain`；WP 等于从底元素迭代的上确界 |

适配层的 `Density`、`Observable` 子类型采用论文的数学约束；这些名字不是从未公开的 Google
源码中取得。`Unitary` 和 `Measurement` 暂用现有核心类型，尚无证据称它们等于 Google 内部类型。
`StateTransformer` 只实现论文可见的 `toStateFun` 投影及已证明的语义，不猜测其内部其他字段。
适配层允许一般 `Var`，覆盖论文的有限经典变量情形；这是一项泛化，不表示论文声明支持无限变量。

## 使用

```lean
import QuantumLeanLeap.GoogleQHL.Compatibility.PaperAPI

namespace QuantumLeanLeap.GoogleQHL.PaperAPI

def stopAtZero : QProg Unit 2 :=
  .qwhile (fun s => s () ≠ 0) (.assign () (fun _ => 0))

example (S : CQState Unit 2) (Q : CQAssertion Unit 2) :
    expect S (wp stopAtZero Q) = expect ((interp stopAtZero).toStateFun S) Q :=
  expect_wp stopAtZero S Q

end QuantumLeanLeap.GoogleQHL.PaperAPI
```

此入口与原核心并存。新代码可使用 Prop 条件和 Physlib Observable，已有程序无需重写。
`CQState.toCore/ofCore`、`CQAssertion.toCore/ofCore` 用于显式跨接口转换。
Observable、Density、CQState 有实际 Löwner 偏序；`wpOrderHom` 将 WP 封装为保序映射。
`Compatibility.OmegaOrder` 提供实际 Mathlib ω-CPO 与底元素实例；断言通过 Mathlib 的 Pi
实例获得逐点序结构。这里只构造递增链的上确界，不声称非对易效应算子具有任意格上确界。

## 连续语义与循环接口

`Compatibility.Continuity` 证明期望对断言递增链保持上确界，并由完整状态对偶定理推出
`wp_map_omegaSup`。`Compatibility.StateContinuity` 证明状态序可由全部断言期望刻画，
据此得到正向解释器的单调性和 `interp_map_omegaSup`。两者均包装成 Mathlib
`ContinuousHom`，并证明 `ωScottContinuous`；这里的连续性是对可数递增链的序连续性。
证明适用于任意合法的可求和经典混合，不要求只有有限个经典状态。

`Compatibility.FixedPoint` 的 `loopContinuousHom` 定义循环泛函：条件成立时应用体程序 WP，
否则返回后置断言。已证明循环 WP 是其最小前不动点，且严格等于 Mathlib
`fixedPoints.iterateChain` 从 `⊥` 开始迭代的上确界。每轮使用循环体完整的无界语义，
允许体程序自身含循环。

```lean
import QuantumLeanLeap.GoogleQHL.Compatibility.FixedPoint

open OmegaCompletePartialOrder
open QuantumLeanLeap.GoogleQHL.PaperAPI

example (g : Store Unit → Prop) [DecidablePred g]
    (body : QProg Unit 2) (Q : CQAssertion Unit 2) :
    wp (.qwhile g body) Q = ωSup (loopIterates g body Q) :=
  wp_qwhile_eq_omegaSup_iterates g body Q
```

这些是基于已固定 Mathlib 版本的适配接口。Google 源码中的实例名称、具体连续映射封装及自动化
策略仍待官方源码对照；`StateTransformer` 原有公开投影保持不变，连续映射通过新入口取得。

## 回归与验收

`Compatibility/Regression.lean` 证明：

- False 命题条件的循环返回原输入，包括可求和经典混合。
- 全部既有 JSON 候选可翻译到新入口，保持其独立矩阵动态电路的每条测量历史。
- 对任意合法混合初态和断言，新入口的实内积期望与独立矩阵动态电路期望一致。
- 恒真 `skip` 循环的每个断言都是泛函不动点，但循环 WP 和 Kleene 链上确界均为底元素。
  这区分了“满足不动点方程”和“选取最小解”。
- 恒假条件的 Kleene 链上确界严格等于原后置断言。

`scripts/QHLAudit.lean` 审计这些适配定理的传递公理依赖。
本地候选验收当前使用 `verification/reset-paper-v7.lock.json`。
当前范围移除了算法库和竞赛依赖，候选入口仍仅支持复位任务。

## 后续边界

要完成严格的 Google 源码 API 对齐，仍需确认官方仓库及 commit，并执行同版本编译对照。
随后才可逐项核对构造子参数、类型转换与 notation、语义变换器字段、ω-CPO 实例、资源接口和自动化策略。
本轮也没有实现论文五个应用任务或执行 Google 官方验收。
