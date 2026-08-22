# Ript 文档

[English](../en/README.md) · [简体中文](README.md) ·
[日本語](../ja/README.md) · [Esperanto](../eo/README.md)

Ript 是面向资源索引信息过程的 Lean 4 内核核验研究库。它连接可执行有限语法与概率、量子、
因果、计算、语义信息、决策和热力学模型，同时保持各种可选能力彼此分离。

> [!IMPORTANT]
> 仓库已经包含大量真实证明，但仍是早期研究项目；最终全局定理与稳定 API 尚未完成。

## 当前快照

- 资源敏感语法、预算、可靠性、相对完备性与自由语义均已编译；
- 六类模型均有具体实例和经检查的非平凡示例；
- 模型及资源变换态射组成经验证的双范畴层；
- 内部单值与 complete-Segal 基础位于可执行核心下游；
- generated hammock mapping spaces 已与实际局部化目标等价，并具有显式 nerve 同伦逆和终止约化。

当前前沿是 critical-pair joinability、经典 reduced-hammock 不变性、标准弱等价封装与全局 Rezk 定理。

## 从这里开始

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
./scripts/quality-gate.sh
```

后续步骤见[入门指南](GETTING_STARTED.md)。

## 按任务阅读

- **理解项目：** [范围与可信边界](PROJECT_SCOPE.md) · [架构](ARCHITECTURE.md)
- **查看已证明内容：** [研究状态](RESEARCH_STATUS.md) · [模型能力矩阵](reference/MODEL_MATRIX.md)
- **审计精确证据：** [蓝图](reference/BLUEPRINT.md) · [公理](reference/AXIOMS.md) ·
  [猜想](reference/CONJECTURES.md)
- **参与项目：** [贡献指南](CONTRIBUTING.md) · [治理](GOVERNANCE.md) · [安全](SECURITY.md)
- **切换语言：** [多语言文档中心](../README.md)

## 成熟度与复用

可复现研究应固定完整 commit SHA。项目没有稳定发行或 API 兼容承诺。当前尚未选择开源许可证，
公开可见不等于获得复制、修改或再分发权；详见[项目范围](PROJECT_SCOPE.md#许可)。
