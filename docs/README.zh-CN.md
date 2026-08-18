# Ript

**面向资源索引过程理论、由 Lean 4 内核检查的形式化基础。**

[English](../README.md) · [简体中文](README.zh-CN.md) ·
[日本語](README.ja.md) · [Esperanto](README.eo.md)

[![质量门禁](https://github.com/miuchan/ript/actions/workflows/ci.yml/badge.svg)](https://github.com/miuchan/ript/actions/workflows/ci.yml)
![Lean 4.33.0](https://img.shields.io/badge/Lean-4.33.0-0d6efd)
![mathlib 4.33.0](https://img.shields.io/badge/mathlib-4.33.0-a42e2b)
![研究状态](https://img.shields.io/badge/status-early--stage%20research-orange)

Ript 形式化 **Resource-Indexed Information Process Theory（资源索引信息过程理论）**：
过程带有类型，行为与资源消耗都可以组合；可执行模型与成本上界、可靠性、相对完备性和
结构保持语义的内核证明相连接。

> [!IMPORTANT]
> Ript 是早期研究软件。已编译结果由 Lean 内核检查，但公共 API 尚不稳定；本项目也不声称
> 当前成果已经构成完整的物理信息理论。

## 为什么需要 Ript？

普通过程理论描述“哪些过程可以组合”。资源敏感理论还必须解释组合需要多少资源、哪些
改写保持成本，以及语法估计何时对语义有效。

Ript 把这些义务变成显式接口和定理：

- 资源构成带序的加法代数；
- 串行与并行组合带有已证明的成本上界；
- 可执行语法与基于商的证明模型保持分离；
- 解释保持类型、等式和声明的资源界；
- 确定性、随机、计算、因果、热力学与量子模型实现通用接口；
- 每个旗舰定理都登记实际的内核公理依赖。

Ript 是 **Resource-Indexed Information Process Theory** 的缩写。

## 已实现内容

### 形式化核心

- 有序加法资源、预算、单调性与成本过滤；
- 带串行和并行组合的成本范畴；
- 可执行的串行与对称幺半群语法；
- 显式等式推导、可靠性、项模型、相对完备性和幺半群初始性。

### 精确有限模型

- 有限函数，以及带计量的总计算和部分计算；
- 基于非负有理数的精确有限随机信道；
- 有限分布 Kleisli 表示和到 `Stoch` 的 faithful 桥；
- Blackwell 比较、精确有限 Bayes 风险和任务相对语义价值；
- 带归一化硬干预的有限 DAG 因果模型；
- 有限 Gibbs-preserving 系统、KL/自由能结果和可执行 Landauer 见证；
- 有限维 Kraus 信道和 faithful 经典退相干嵌入。

### 高阶组织与内部单值边界

- 资源索引对称幺半群过程模型的双范畴；
- 成本精确模型等价、普通同伦局部化和非平凡 walking-localization 测试；
- 不引入公理的内部身份深嵌入语法；
- 群胚、商、预层、单纯神经与分类图语义；
- 明确限制在 0/1-truncated 范围内，不把任意 Lean 等价冒充 Lean 相等。

准确的能力、限制和定理状态请查阅[模型矩阵](../MODEL_MATRIX.md)、
[研究状态](RESEARCH_STATUS.md)和[形式化蓝图](../BLUEPRINT.md)。这些文件是权威记录；
本页刻意只保留项目入口信息。

## 快速开始

需要 Git、POSIX shell 和 [elan](https://github.com/leanprover/elan)。

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
lake build
```

提交改动前运行完整门禁：

```bash
./scripts/quality-gate.sh
```

它会检查源码政策、根模块覆盖、无警告内核构建、声明 lint、可执行示例和公理白名单。

可以直接运行端到端示例：

```bash
lake env lean Ript/Examples/StochasticBits.lean
lake env lean Ript/Examples/SimpleDecision.lean
lake env lean Ript/Examples/SimpleCausalModel.lean
```

完整示例索引、单项验证命令和故障排查见[入门指南](GETTING_STARTED.md)。

## 作为 Lean 依赖使用

在正式 tag 发布前，请固定完整 commit SHA：

```lean
require ript from git
  "https://github.com/miuchan/ript.git" @ "<commit-sha>"
```

优先导入最小模块，例如：

```lean
import Ript.Resource.Budget
import Ript.Models.FiniteStochastic
```

## 文档导航

- [文档中心](README.md)：按任务选择最短阅读路径。
- [入门指南](GETTING_STARTED.md)：安装、示例、依赖使用和故障排查。
- [架构](ARCHITECTURE.md)：分层、依赖方向和可执行/证明边界。
- [研究状态](RESEARCH_STATUS.md)：已完成支柱、当前前沿和明确未声称的结论。
- [模型能力矩阵](../MODEL_MATRIX.md)：只登记已经实现并编译的能力。
- [形式化蓝图](../BLUEPRINT.md)：定理依赖图和准确状态。
- [公理清单](../AXIOMS.md)：审计后的 `#print axioms` 输出。
- [猜想登记册](../CONJECTURES.md)：开放和近期解决的研究命题。
- [贡献指南](../CONTRIBUTING.md)：强制执行的证明与质量政策。

详细技术文档目前以英文为单一事实源；Lean 声明、蓝图、模型矩阵和公理审计不依赖自然语言
翻译。

## 信任与可复现性

Ript 禁止证明占位符、项目自定义公理、编译器信任逃逸、`unsafe` 声明以及库模块中的
`import Mathlib` 总入口。CI 使用固定的 Lean 与 Mathlib 版本重新构建，并把警告视为错误。

部分定理使用 Mathlib 的标准基础，如商相等、命题外延或经典选择。实际依赖逐一定录于
[AXIOMS.md](../AXIOMS.md)。

## 当前研究前沿

当前高阶前沿是任意、非可分的二维 walking-localization 分解。对象、1-态射、2-态射、
恒等比较、组合比较以及所有箭头上的自然性数据已经编译；左单位方程也已在每个规范正向
目标箭头上编译通过。其逆箭头分支、完整右单位律、oplax 结合律、pseudofunctor 封装和
最终的伴随等价分解仍未完成。

一般可测因果模型、带弱等价的 Mathlib 原生 complete-Segal-space 接口，以及完整的双范畴或
Dwyer–Kan 局部化定理也仍属于开放方向。精确边界见[研究状态](RESEARCH_STATUS.md)。

## 参与贡献

贡献必须保持项目的证明边界，并只按实际证明强度表述结论。请先阅读
[CONTRIBUTING.md](../CONTRIBUTING.md)，运行 `./scripts/quality-gate.sh`；若旗舰定理发生变化，
同时更新蓝图和公理清单。

## 版本、引用与许可证

Lake 包版本为 `0.1.0`，尚无稳定 API。研究产物应记录所用的完整 commit SHA。

Ript 尚无归档论文或 DOI；当前请引用仓库地址和固定 commit。

项目尚未选择开源许可证。在加入许可证文件前，源码公开并不自动授予复制、再分发或创作
衍生作品的许可。

## 致谢

Ript 构建于 [Lean 4](https://lean-lang.org/) 与
[Mathlib](https://github.com/leanprover-community/mathlib4) 之上。
