# Ript

**面向资源索引过程理论、由内核核验的 Lean 4 基础库。**

[English](../README.md) · [简体中文](README.zh-CN.md) ·
[日本語](README.ja.md) · [Esperanto](README.eo.md)

[![Quality Gate](https://github.com/miuchan/ript/actions/workflows/ci.yml/badge.svg)](https://github.com/miuchan/ript/actions/workflows/ci.yml)
![Lean 4.33.0](https://img.shields.io/badge/Lean-4.33.0-0d6efd)
![mathlib 4.33.0](https://img.shields.io/badge/mathlib-4.33.0-a42e2b)
![研究状态](https://img.shields.io/badge/status-early--stage%20research-orange)

Ript 形式化 **Resource-Indexed Information Process Theory（资源索引信息过程理论）**：
使带类型过程的行为与资源消耗能够组合，并把可执行有限模型与成本界、可靠性、完备性结果和
保结构语义的内核核验证明连接起来。

> [!IMPORTANT]
> Ript 是早期研究软件。已编译结果由 Lean 内核核验，但公共 API 尚不稳定；项目也不声称
> 已给出完整的物理信息理论。

## 为什么需要 Ript

普通过程理论描述哪些过程可以组合；资源敏感理论还必须描述成本如何组合、哪些重写保持成本，
以及语法估计何时在语义上成立。Ript 将这些义务显式化并交给机器检查。

- 有序加法资源刻画串行与并行预算；
- 可执行语法与基于商类型的证明模型保持分离；
- 解释函数证明类型、方程和资源界均被保持；
- 张量、复制、丢弃、凸性、因果性和热力学等能力彼此独立，不被隐式推导；
- 旗舰定理都带有经过审计的内核假设记录。

## 核心亮点

- **形式化核心：** 带成本范畴、可执行顺序/幺半语法、可靠性、相对完备性和幺半初始性；
- **精确有限模型：** 确定性、随机、决策、计算、因果、热力学和量子实例；
- **高阶组织：** 过程模型双范畴、成本精确等价和已核验的 walking-localization 构造；
- **内部恒等语义：** 无附加公理的深层语法，以及群胚、商、预层、单纯和分类图解释。

精确能力见[模型能力矩阵](../MODEL_MATRIX.md)，限制与研究边界见[研究状态](RESEARCH_STATUS.md)。

## 快速开始

安装 [elan](https://github.com/leanprover/elan) 后运行：

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
lake build
```

提交改动前执行完整本地 CI 合约：

```bash
./scripts/quality-gate.sh
```

直接核验一个可执行模型：

```bash
lake env lean Ript/Examples/StochasticBits.lean
```

[入门指南](GETTING_STARTED.md)涵盖环境要求、示例、依赖配置、可复现性和故障排查。

## 在 Lean 中使用

稳定标签发布前，请固定完整提交 SHA：

```lean
require ript from git
  "https://github.com/miuchan/ript.git" @ "<commit-sha>"
```

优先导入满足需求的最小模块，例如：

```lean
import Ript.Resource.Budget
import Ript.Models.FiniteStochastic
```

## 文档导航

- [文档中心](README.md) — 按任务选择最短阅读路径；
- [入门指南](GETTING_STARTED.md) — 构建、运行和依赖使用；
- [架构](ARCHITECTURE.md) — 分层与依赖边界；
- [研究状态](RESEARCH_STATUS.md) — 已证明、进行中和明确不作出的主张；
- [模型能力矩阵](../MODEL_MATRIX.md) — 已编译的模型能力；
- [形式化蓝图](../BLUEPRINT.md) — 定理依赖和精确状态；
- [公理清单](../AXIOMS.md) — 经审计的 `#print axioms` 输出；
- [猜想登记册](../CONJECTURES.md) — 开放研究命题；
- [贡献指南](../CONTRIBUTING.md) — 证明与质量政策。

## 可信边界、状态与治理

Ript 禁止证明占位符、项目自定义公理、编译器信任逃逸和不安全库声明。CI 固定 Lean 与
Mathlib 版本，将警告视为错误，执行代表性模型，并核对公理允许清单。精确依赖记录在
[AXIOMS.md](../AXIOMS.md)。

当前前沿是任意二维 walking-localization 分解：所有箭头上的自然性和完整左右单位律已经编译；
oplax 结合律、pseudofunctor 封装和最终伴随等价仍未完成。权威边界见
[RESEARCH_STATUS.md](RESEARCH_STATUS.md)。

Lake 包版本为 `0.1.0`，尚无稳定 API 版本或归档 DOI。研究成果应引用仓库及完整提交 SHA。
项目尚未选择开源许可证；源码公开本身不代表授予复用权。

## 参与贡献

只要主张与已编译定理的强度一致并保持证明边界，贡献就非常欢迎。提交 PR 前请阅读
[CONTRIBUTING.md](../CONTRIBUTING.md)并运行 `./scripts/quality-gate.sh`。

Ript 基于 [Lean 4](https://lean-lang.org/) 与
[Mathlib](https://github.com/leanprover-community/mathlib4) 构建。
