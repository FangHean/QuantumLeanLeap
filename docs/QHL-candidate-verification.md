# 本地候选验收：测量反馈复位

这是一个独立的小型验收任务，用来验证“固定规格 → 提交电路 → Lean 检查 → 接受或拒绝”的流程。
它不是 Google 官方验证器、Lean Comparator，也不属于论文的五个应用任务。

## 固定规格

`QuantumLeanLeap/GoogleQHL/Verification/ResetSpec.lean` 不导入候选语言或任何候选实现。
其 `Contract` 要求：

- 对任意经典初态和任意二维复矩阵，所有输出历史的量子矩阵之和恰好为
  `tr(ρ) |0⟩⟨0|`，因此包括混合态、相干项和未归一化输入。
- 每条最坏路径至多执行一个酉门、一次测量。
- 经典输出不作要求；目标是丢弃测量记录后的量子态复位。

候选语言没有循环，`Program.fuel_independent` 已证明其解释结果与 fuel 无关。
规格仍对所有 fuel 量化。X/Z 用精确复矩阵定义，Z 测量复用已证明完备的计算基投影。
`ResetNative.lean` 已证明这两个矩阵与 QuantumAlg 原生门的 `binaryMatrix` 一致，
并将候选编译到 `DynamicCircuit Unit 1`。`Program.toDynamic_compile` 证明两条编译路径
得到相同的 QProg；`Program.toDynamic_run` 进一步证明每条测量历史及其经典状态均相同。

原生门的 `eventTrace.length` 与最坏路径预算也已连接：X/Z 各为一个原生事件，
`Program.native_count` 证明本语言的原生门预算与源层预算相等。
对任意 PSD 输入，`Program.native_expected_gate_bound` 给出按概率加权的原生门成本上界。
测量和经典分支仍处于 QHL 动态电路层；这里没有将测量转化为一个酉电路或声称已导出硬件可执行文件。

## 提交格式

候选只提交 JSON 数据，不提交 Lean 源码、证明、矩阵、规格或资源计数。
允许的节点是 `skip`、`x`、`z`、`measure`、`seq` 和 `if_zero`。
只有一个经典整数变量；`measure` 覆盖该变量，`if_zero` 判断其是否为零。

```json
{
  "schema": "qhl-reset-v1",
  "program": {
    "op": "seq",
    "first": {"op": "measure"},
    "second": {
      "op": "if_zero",
      "zero": {"op": "skip"},
      "nonzero": {"op": "x"}
    }
  }
}
```

解析器拒绝重复键、未知字段、直接 reset、任意代码以及超出限制的输入。
限制为 16 KiB、63 个节点、根深度为 0 时最大深度 12。
候选字符串不会直接插入生成的 Lean 文件；所有构造子均由固定映射生成。

## 运行

在项目根目录运行：

```sh
python3 scripts/verify_qhl_candidate.py verification/candidates/reset-feedback.json
python3 -m unittest discover -s scripts -p 'test_qhl_candidate.py' -v
```

验证器先核对已保存的 `verification/reset-task1-v5.lock.json`，再构建可信规格及原生桥接模块，
生成当前候选的语义证明、门预算证明和测量预算证明，最后由这三项构造 `Contract` 证书。
最终被审计的 `accepted` 声明还要求原生动态电路满足同一 Contract、原生门数不超过一，
并满足动态执行后的复位矩阵等式；因此只有源层证明不足以通过当前入口。
生成文件仅使用固定证明策略，不运行候选提供的命令。
Lean 检查成功后，还检查证书传递依赖只使用 `propext`、`Classical.choice`、`Quot.sound`，
并再次核对锁定的文件和依赖。

退出码与报告状态：

| 退出码 | 状态 | 含义 |
| --- | --- | --- |
| 0 | `accepted` | 当前候选的完整 Contract 证明已通过，且通过公理及锁定检查 |
| 1 | `not_certified` | 输入被拒绝，或固定证明策略未能完成证书 |
| 2 | `error` | 基线不匹配、依赖构建失败、超时或无法运行验证 |

`not_certified` 不等于已经证明候选错误：当前策略不是完备判定程序。
测试中的错误反馈和超预算候选有明确失败原因；不能将这一点推广为所有拒绝的原因。

报告、生成的 `Candidate.lean` 和日志放在 `artifacts/qhl-verification/<候选 SHA-256>/`。
每次重新验证同一候选会先移除旧成功报告及旧日志；中断或失败不会保留旧的成功状态。
报告保存候选原始字节、生成源码和锁定清单的 SHA-256。
通过时报告包含 `native_backend_verified: true`，范围限于上述原生酉门与动态控制语义。
同一候选应串行验证；当前目录布局不提供并发运行隔离。

## 冻结范围与信任边界

锁定清单记录 QHL Lean 源码、候选验证器、Lake 配置、工具链声明，以及所有解析依赖的实际 git commit。
验收前后都要求依赖的已跟踪文件无修改。候选验证不会自动刷新清单。
首版 `reset-v1.lock.json` 和原生桥接版 `reset-native-v2.lock.json` 保留为历史清单，未被覆盖；
Physlib 适配版 `reset-physlib-v3.lock.json` 和 ω-CPO 版 `reset-omega-v4.lock.json` 同样保留。
当前 v5 清单记录新增 Parallel Grover 子实例后的源码集合；复位任务规格与预算未改变，
此验收入口仍然只验证复位候选，不验证 Grover 候选。
JSON 的 `schema` 仍为 `qhl-reset-v1`，因为任务规格和候选语法没有改变。
需要改变规格或验证器时，应审查变更后显式创建新版本清单：

```sh
python3 scripts/verify_qhl_candidate.py --freeze /tmp/reset-next.lock.json
```

该命令拒绝覆盖已有文件，也不自动将新清单设为当前可信基线。
创建清单只记录当前状态；它本身不能证明当前状态正确，仍需构建、测试和规格审查。

可信边界包括锁定清单、验证器、Lean/Lake、已安装依赖和构建缓存。
这套流程隔离候选数据与规格，不是防御恶意本机文件系统或编译缓存的操作系统沙箱。
QuantumAlg 仍通过本地路径加载；这里检查实际 commit，不代表项目依赖配置已可移植。

## 拒绝测试

测试覆盖正确反馈、带 skip 包装的版本、零分支执行 Z 的正确版本、仅测量、错误反馈、无条件 X、语义正确但
多执行两个 X 的超门预算电路、语义正确但多测量一次的超测量预算电路。
超预算测试还核对 Lean 错误只发生在相应预算证明中。
另有规格摘要变更、公理白名单、旧成功报告失效、超时及输入格式/规模限制测试。

这是独立验收流程的第一个可运行实例。支持任意量子程序、更广的原生门集、论文五个任务及
与官方验证流程对齐，仍是后续工作。


2026-11-19 发布准备更新：QuantumAlg 已改为固定 commit 的公开 Git 依赖，旧版本所述本地路径限制已移除；
独立无缓存构建仍待验证。当前复位基线为 `reset-release-v6.lock.json`，保留 v1–v5 历史文件。
