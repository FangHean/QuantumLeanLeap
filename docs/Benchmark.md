# QuantumLeanLeap Proof Bench v0.1

这是从 AlgBench 原题迁移得到的 **36 题、44 个证明目标**的开放库定理补全基准。
它使用本项目的 QHL/矩阵表示，没有 Alg 库依赖，也不是 Google 官方 benchmark。
完整对应关系和翻译边界见 [迁移说明](Bench36-migration.md)。
36 题覆盖 8 类数学与量子计算问题；某些原题采用条件式规格，不能把证明结果理解成从零发现算法。
规格已经类型检查，参考证明目前仅覆盖两题；未运行真实模型。

## 题目与提交

- `bench/tasks.json`：固定 imports、上下文、定理目标与题号；评分时不能修改。
- `bench/references.jsonl`：两题公开参考证明，用于验证评测器自身，不是完整答案库或模型输出。
- `bench/benchmark.lock.json`：题目、参考证明、评测器、库源码、工具链和全部依赖 commit 的摘要。
- `scripts/bench.py`：仅需 Python 3.10+ 标准库，依赖已安装的 Lean/Lake。

```sh
python3 scripts/bench.py list
python3 scripts/bench.py export /tmp/qll-prompts.jsonl
python3 scripts/bench.py evaluate bench/references.jsonl --output artifacts/bench/reference --k 1
```

评测目录必须不存在，防止混用旧成功报告。每份提交为 JSONL 一行：

```json
{"task_id":"BitOracleUnitaryHermitian","model":"my-model","attempt":0,"proof":["by ...", "by ..."]}
```

`proof` 数组必须按该题 goals 顺序提供全部证明；任何一个目标失败，整题都不通过。上例的省略号需要替换为实际证明。

`attempt` 在同一模型、同一题内不可重复。不同模型可以放在同一文件中，报告分别评分。
可附 `generation_seconds`、`usage` 和 `generation_error`，这些是提交方报告的生成指标；
验证时间由评测器实测，不能混同为模型生成时间。未提供的 token 用量不视为实际零消耗。

## 接模型

可以把提示 JSONL 交给任意模型或 agent，再导入统一提交格式。
提示只提供目标和 imports；需要检索库定义的 agent 可以读取相应源码，但不得读取参考答案。
生成 API 要求返回证明字符串的 JSON 数组。纯 API 模式不提供文件检索，须在比较模型时保持相同上下文条件。

也提供 OpenAI-compatible **Chat Completions** 生成入口：

```sh
# 在环境中设置 QLEAP_API_KEY；不要把密钥写进仓库。
python3 scripts/bench.py generate \
  --base-url https://YOUR_PROVIDER/v1 --model YOUR_MODEL \
  --samples 5 --temperature 0.7 --output /tmp/model-samples.jsonl
python3 scripts/bench.py evaluate /tmp/model-samples.jsonl \
  --output artifacts/bench/model-run --k 1 5
```

这是提供商兼容适配器，不保证所有模型支持 `max_tokens`、`temperature` 等参数。
它不调用模型工具、不授予本机文件访问，也不自动反复修复证明。API 失败保留为失败样本，
不会静默丢弃；未配置模型/API key 时不会发生付费调用。密钥只从指定环境变量读取，不写报告。

## 验证与评分

每个证明嵌入**固定定理类型**，由 Lean 检查，并审计最终证书的传递公理依赖。
仅允许 `propext`、`Classical.choice`、`Quot.sound`；拒绝占位符、额外公理和 `native_decide`。
未通过证明自动化只表示“未认证”，不表示命题为假。

- `accepted`：固定目标通过 Lean 和公理检查。
- `not_certified`：Lean 未认证。
- `rejected_input`：不支持或禁止的提交形式。
- `timeout`：证明验证超时。
- `generation_error`：生成 API/agent 报错。
- 可信库构建失败、环境变化或评测器故障：整个运行失败，不输出有效排行榜。

报告为 `report.json`，每次尝试另存证明、Lean 日志与结果。
全题集 solved fraction 的分母始终为 36，漏题不会提高分数。
对每题的 n 个尝试、c 个通过，使用 `1 - C(n-c,k)/C(n,k)` 估计 pass@k，再对全部题等权平均。
只要任意一题少于 k 个样本，整套 pass@k 就是 null；不会把少样本题删除。
概率解释要求相同条件下的独立采样，不能把带反馈重试或高度相关的样本当成独立抽样。

`generation_seconds`、温度、采样数、提示条件、验证时限与工具链应随比较结果一起报告。
首版不自动计算美元成本，也不把 Lean 验证耗时当成量子电路运行成本。

## 信任边界

Lean 的 elaborator/tactic 可以执行代码。文本限制、公理检查和摘要锁**不是操作系统沙箱**。
这个入口用于受控本地研究；不要把它直接作为接收恶意公网 Lean 代码的服务。
评测不可信模型代码时，应在无密钥、禁网、仅开放结果目录写权限的可丢弃容器/虚拟机中运行，
并在容器层设置 CPU、内存、进程数与总时限。模型生成和证明验证应使用不同环境。

参考证明公开，且部分目标可调用库中已有定理。本基准测的是在声明的开放库条件下完成证明的能力，
不声称答案保密、无训练污染或测试了从零发现算法。扩大难题集和建立隐藏测试集是后续工作。

修改题目或验证器后，需显式建立并审查新版本基线：

```sh
python3 scripts/bench.py freeze /tmp/new-benchmark.lock.json
```

此命令不会覆盖或启用现有基线；不要在模型评测中途刷新锁。

## 评测器校准集

原来的 12 道小题仅保留为自测，不属于正式 36 题：

```sh
python3 scripts/bench.py --suite calibration evaluate bench/calibration-references.jsonl --output artifacts/bench/calibration --k 1
```

两种 suite 使用同一可信源码基线，但分别计分。禁止把校准集的 12/12 当成正式 benchmark 的结果。
