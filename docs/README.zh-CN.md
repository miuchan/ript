# Ript

**面向资源索引过程理论、由内核核验的 Lean 4 基础库。**

[English](../README.md) · [简体中文](README.zh-CN.md) ·
[日本語](README.ja.md) · [Esperanto](README.eo.md)

[![Quality Gate](https://github.com/miuchan/ript/actions/workflows/ci.yml/badge.svg)](https://github.com/miuchan/ript/actions/workflows/ci.yml)
![Lean 4.33.0](https://img.shields.io/badge/Lean-4.33.0-0d6efd)
![mathlib 4.33.0](https://img.shields.io/badge/mathlib-4.33.0-a42e2b)
![研究状态](https://img.shields.io/badge/status-early--stage%20research-orange)

Ript 形式化 **Resource-Indexed Information Process Theory（资源索引信息过程理论）**：
使带类型过程的行为与资源消耗能够组合，并把可执行有限模型连接到资源界、可靠性、
完备性结果和保结构语义的内核核验证明。

> [!IMPORTANT]
> Ript 是早期研究软件。已编译结果由 Lean 内核核验；公共 API 与研究前沿仍在演进。

## 已包含的内容

- **形式化基础：** 带成本范畴、可执行语法、解释、可靠性、相对完备性和幺半初始性；
- **精确有限模型：** 确定性、随机、决策、计算、因果、热力学和量子实例；
- **高阶结构：** 过程模型双范畴、成本精确等价和 walking-localization 构造；
- **可审计证明：** CI 拒绝占位证明和未登记假设，旗舰定理有明确的公理清单。

已实现能力见[模型能力矩阵](../MODEL_MATRIX.md)；已证明、开放和明确不作出的主张见
[研究状态](RESEARCH_STATUS.md)。

## 快速开始

安装 [elan](https://github.com/leanprover/elan) 后运行：

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
lake build
```

提交改动前执行完整本地质量门禁：

```bash
./scripts/quality-gate.sh
```

环境要求、示例、依赖使用和故障排查见[入门指南](GETTING_STARTED.md)。

## 文档

- [文档中心](README.md) — 按任务选择最短阅读路径；
- [项目范围与可信边界](PROJECT_SCOPE.md) — 设计、主张、证明政策、成熟度与许可；
- [架构](ARCHITECTURE.md) — 分层与依赖边界；
- [研究状态](RESEARCH_STATUS.md) — 已实现、进行中和开放内容；
- [形式化蓝图](../BLUEPRINT.md) · [公理清单](../AXIOMS.md) ·
  [猜想登记册](../CONJECTURES.md) — 权威研究记录。

## 参与贡献

请先阅读[贡献指南](../CONTRIBUTING.md)，并在提交 PR 前运行
`./scripts/quality-gate.sh`。

Ript 基于 [Lean 4](https://lean-lang.org/) 与
[Mathlib](https://github.com/leanprover-community/mathlib4) 构建。
