# 安装与依赖

版本：0.1.0。Lean：`leanprover/lean4:v4.33.1`。Python 评测脚本要求 Python 3.10+。
所有 Lean 依赖都使用公开 Git URL 和固定 commit；不再要求作者个人目录存在。

## 下载源码包

解压 `QuantumLeanLeap-0.1.0.tar.gz`，安装 elan/Lean 后执行：

```sh
cd QuantumLeanLeap-0.1.0
lake exe cache get
lake build
python3 scripts/verify_qhl.py
```

第一次构建需要联网下载 Git 依赖和工具链，并可能消耗较多时间、内存及磁盘。
Mathlib 缓存命令只负责其覆盖范围，不保证包含全部 QuantumAlg/Physlib 目标。

## 在另一个 Lake 项目中依赖

源码包解压到项目旁边时，向使用方 `lakefile.toml` 添加：

```toml
[[require]]
name = "QuantumLeanLeap"
path = "../QuantumLeanLeap-0.1.0"
```

使用方 `lean-toolchain` 采用相同版本，随后 `lake update`、`lake build`。
模块入口：

```lean
import QuantumLeanLeap.GoogleQHL
import QuantumLeanLeap.Algorithms
import QuantumLeanLeap.GoogleQHL.Tasks.ParallelGrover
```

公开仓库为 `https://github.com/FangHean/QuantumLeanLeap`。Git 依赖形式：

```toml
[[require]]
name = "QuantumLeanLeap"
git = "https://github.com/FangHean/QuantumLeanLeap.git"
rev = "v0.1.0"
```

需使用已发布标签；也可把 `rev` 换成该标签对应的完整 commit SHA。`scripts/package_release.py` 生成源码包和 SHA-256，
打包采用明确目录白名单，排除 `.lake`、个人配置、API 密钥、运行日志和大型实验输出。

## 验证范围

本地已使用现有依赖缓存进行构建和测试；外部消费项目的测试同样可复用缓存。
这与“全新机器无缓存构建通过”是不同的证据。GitHub Actions 工作流会在发布仓库后提供独立 CI 证据；
仅添加工作流文件不表示远程 CI 已运行。冻结依赖 commit 不冻结操作系统或 Python/Lean 二进制供应链。

许可证为 Apache-2.0，第三方归属见 `NOTICE`。当前是研究库，Google 官方等价性和完整任务复现均未宣称。
