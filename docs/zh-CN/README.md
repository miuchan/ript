# Ript

**面向资源索引过程理论、由内核核验的 Lean 4 基础库。**

[English](../en/README.md) · [简体中文](README.md) ·
[日本語](../ja/README.md) · [Esperanto](../eo/README.md)

[![Quality Gate](https://github.com/miuchan/ript/actions/workflows/ci.yml/badge.svg)](https://github.com/miuchan/ript/actions/workflows/ci.yml)
![Lean 4.33.0](https://img.shields.io/badge/Lean-4.33.0-0d6efd)
![mathlib 4.33.0](https://img.shields.io/badge/mathlib-4.33.0-a42e2b)
![研究状态](https://img.shields.io/badge/status-early--stage%20research-orange)

Ript 形式化行为与资源消耗均可组合的带类型过程，并把可执行有限模型连接到资源界、
可靠性、完备性和保结构语义的内核核验结果。
首个字面共享的六模型切片，已经把同一个布尔过程签名解释到概率、量子、因果、计算、语义和热模型。

Ript 的核心研究目标是：构造一种可计算、机器可验证、单值化、高阶范畴化的资源受限
信息过程理论，使经典概率、量子过程、因果模型、计算、语义信息和热力学成为它的不同
模型，并证明连接这些模型的表示定理与完备性定理。本仓库包含通向该目标的已编译层；
整体目标目前还不是一个已经证明的定理。

> [!IMPORTANT]
> Ript 是早期研究软件。已编译结果由 Lean 内核核验；公共 API 与研究前沿仍在演进。

## 快速开始

安装 [elan](https://github.com/leanprover/elan) 后构建锁定版本的 Lean 与 Mathlib 项目：

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
lake build
```

环境要求、可执行示例、依赖接入、可复现使用和故障排查见[入门指南](GETTING_STARTED.md)。

## 按需阅读

- **已经实现了什么？** 查看[模型能力矩阵](reference/MODEL_MATRIX.md)；
- **哪些已经证明，哪些仍然开放？** 查看[研究状态](RESEARCH_STATUS.md)；
- **代码如何组织？** 阅读[架构指南](ARCHITECTURE.md)；
- **可信边界和成熟度如何？** 阅读[项目范围与可信边界](PROJECT_SCOPE.md)；
- **精确研究记录在哪里？** 查阅[形式化蓝图](reference/BLUEPRINT.md)、
  [公理清单](reference/AXIOMS.md)和[猜想登记册](reference/CONJECTURES.md)。

## 参与贡献

请先阅读[贡献指南](CONTRIBUTING.md)，并在提交 PR 前运行
`./scripts/quality-gate.sh`。

Ript 基于 [Lean 4](https://lean-lang.org/) 与
[Mathlib](https://github.com/leanprover-community/mathlib4) 构建。
