# Ript

**面向资源索引过程理论、由内核核验的 Lean 4 基础库。**

[English](../README.md) · [简体中文](README.zh-CN.md) ·
[日本語](README.ja.md) · [Esperanto](README.eo.md)

[![Quality Gate](https://github.com/miuchan/ript/actions/workflows/ci.yml/badge.svg)](https://github.com/miuchan/ript/actions/workflows/ci.yml)
![Lean 4.33.0](https://img.shields.io/badge/Lean-4.33.0-0d6efd)
![mathlib 4.33.0](https://img.shields.io/badge/mathlib-4.33.0-a42e2b)
![研究状态](https://img.shields.io/badge/status-early--stage%20research-orange)

Ript 形式化行为与资源消耗均可组合的带类型过程，并把可执行有限模型连接到资源界、
可靠性、完备性和保结构语义的内核核验结果。

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

- **已经实现了什么？** 查看[模型能力矩阵](../MODEL_MATRIX.md)；
- **哪些已经证明，哪些仍然开放？** 查看[研究状态](RESEARCH_STATUS.md)；
- **代码如何组织？** 阅读[架构指南](ARCHITECTURE.md)；
- **可信边界和成熟度如何？** 阅读[项目范围与可信边界](PROJECT_SCOPE.md)；
- **精确研究记录在哪里？** 查阅[形式化蓝图](../BLUEPRINT.md)、
  [公理清单](../AXIOMS.md)和[猜想登记册](../CONJECTURES.md)；
- **不确定从哪里开始？** 打开[文档中心](README.md)。

## 参与贡献

请先阅读[贡献指南](../CONTRIBUTING.md)，并在提交 PR 前运行
`./scripts/quality-gate.sh`。

Ript 基于 [Lean 4](https://lean-lang.org/) 与
[Mathlib](https://github.com/leanprover-community/mathlib4) 构建。
