# 入门指南

[English](../en/GETTING_STARTED.md) · [简体中文](GETTING_STARTED.md) ·
[日本語](../ja/GETTING_STARTED.md) · [Esperanto](../eo/GETTING_STARTED.md)

本指南从全新检出开始，依次完成工具链安装和可验证构建，最后介绍具有代表性的可执行模型。

## 环境要求

请安装：

- Git；
- 兼容 POSIX 的 shell；
- Lean 工具链管理器 [elan](https://github.com/leanprover/elan)。

仓库在 `lean-toolchain` 中锁定 Lean，在 `lakefile.lean` 与
`lake-manifest.json` 中锁定 Mathlib。不要改用全局安装的其他 Lean 版本。

## 克隆与构建

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
lake build
```

如果存在匹配版本，`lake exe cache get` 会下载预编译的 Mathlib 产物；随后
`lake build` 会编译完整的 `Ript` 库，并把 Lean 警告视为错误。

## 运行质量门禁

```bash
./scripts/quality-gate.sh
```

门禁按以下顺序执行：

1. 源码策略与文档检查；
2. 根模块覆盖检查；
3. 完整内核构建；
4. 声明 lint；
5. 可执行示例断言；
6. 内核假设 allowlist 检查。

需要快速迭代时，可单独运行：

```bash
./scripts/check-source-quality.sh
lake exe mk_all --check
lake build
lake env lean Ript/Audit/Lint.lean
./scripts/check-examples.sh
./scripts/check-axioms.sh
```

准备合并 pull request 前仍必须运行完整门禁。

## 探索可执行示例

以下每个示例都是普通 Lean 模块；运行它会检查全部声明并输出其中的 `#eval` 结果。

核心资源与函数：

```bash
lake env lean Ript/Examples/BitProcesses.lean
lake env lean Ript/Examples/CostFiltration.lean
lake env lean Ript/Examples/ClassicalCopy.lean
```

精确随机与决策模型：

```bash
lake env lean Ript/Examples/StochasticBits.lean
lake env lean Ript/Examples/KleisliBits.lean
lake env lean Ript/Examples/SimpleDecision.lean
lake env lean Ript/Examples/StochasticSeparation.lean
```

计算与因果：

```bash
lake env lean Ript/Examples/SimpleComputation.lean
lake env lean Ript/Examples/SimpleCausalModel.lean
```

热力学：

```bash
lake env lean Ript/Examples/SimpleThermalModel.lean
lake env lean Ript/Examples/ApproximateErasure.lean
lake env lean Ript/Examples/ExactWorkCycle.lean
```

量子与内部单值语义：

```bash
lake env lean Ript/Examples/QubitChannel.lean
lake env lean Ript/Examples/UnivalentProcessUniverse.lean
lake env lean Ript/Examples/UnivalentSimplicial.lean
```

预期输出由 `scripts/check-examples.sh` 强制检查；这些示例不是仅供阅读的代码片段。

## 将 Ript 作为依赖

Ript 尚未发布稳定的带标签版本，请锁定完整 commit SHA：

```lean
require ript from git
  "https://github.com/miuchan/ript.git" @ "<commit-sha>"
```

修改 `lakefile.lean` 后运行：

```bash
lake update ript
lake exe cache get
lake build
```

优先使用窄范围导入：

```lean
import Ript.Resource.Budget
import Ript.Core.CostedProcess
import Ript.Models.FiniteStochastic
```

总入口 `import Ript` 适合探索，但会导入更多内容。

## 可复现研究用法

研究产物中应记录：

- 完整的 Ript commit SHA；
- `lean-toolchain` 的内容；
- `lake-manifest.json` 中的 Mathlib 修订版本；
- 实际使用的验证命令；
- `AXIOMS.md` 所记录的相关定理假设。

在 API 尚不稳定时，仅记录包版本并不足以保证复现。

## 故障排查

### Lean 版本不匹配

在仓库根目录运行 `elan show`。Elan 应选择 `lean-toolchain` 指定的工具链；若没有，
请先修复 elan 安装，不要修改仓库文件来迁就错误工具链。

### 缺少预编译 Mathlib 产物

重新运行 `lake exe cache get`。如果当前平台没有缓存，`lake build` 会在本地编译依赖，
耗时会更长。

### 根模块覆盖失败

每个公开实现模块都必须由 `Ript.lean` 导入。添加相应的窄范围导入后，重新运行
`lake exe mk_all --check`。

### 公理 allowlist 失败

不要放宽检查脚本。先对相关声明运行 `#print axioms`，判断依赖是否符合预期；只有当
定理及其可信边界确实改变时，才同时更新 `Ript/Audit/AxiomChecks.lean` 和
`AXIOMS.md`。

### 可执行示例输出改变

先检查语义变化。只有新输出是有意且已由相应示例模块证明时，才能更新
`scripts/check-examples.sh`。

## 继续阅读

- [架构](ARCHITECTURE.md)：模块与依赖边界；
- [研究状态](RESEARCH_STATUS.md)：当前数学前沿；
- [形式化蓝图](reference/BLUEPRINT.md)：定理级状态。
- [贡献指南](CONTRIBUTING.md)：开发与审查流程；
- [治理](GOVERNANCE.md)和[安全](SECURITY.md)：项目策略。
