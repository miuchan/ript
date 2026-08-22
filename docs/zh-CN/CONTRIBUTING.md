# 为 Ript 做贡献

[English](../en/CONTRIBUTING.md) · [简体中文](CONTRIBUTING.md) ·
[日本語](../ja/CONTRIBUTING.md) · [Esperanto](../eo/CONTRIBUTING.md)

Ript 接受证明、模型、示例、文档和工具贡献。可信度、显式依赖、可复现性和准确公开声明都是合并要求。

## 开始之前

阅读[项目范围](PROJECT_SCOPE.md)、[架构](ARCHITECTURE.md)与[研究状态](RESEARCH_STATUS.md)，
搜索 issue 和[猜想登记册](reference/CONJECTURES.md)。范围、公开定理陈述、架构、可信依赖、治理、
安全或许可证变更应先讨论。安全问题按[安全策略](SECURITY.md)私密报告。

## 工作流

```bash
git switch -c <focused-branch>
lake exe cache get
lake build <affected.module>
./scripts/quality-gate.sh
```

分支和提交应保持聚焦。PR 必须说明结果、验证、公理足迹、兼容影响和剩余边界；合并要求 CI 全绿并
获得维护者批准。

## 证明与实现策略

- 禁止证明占位符、项目公理、信任逃逸和 unsafe 声明；
- 保持 `autoImplicit false`，使用窄 Mathlib 导入；
- 通用缺失基础设施放在 `Ript/ForMathlib/`；
- 可执行数据保持在商和选择代表元的上游；
- 保持能力边界，使用领域准确的定理名称；
- 未完成陈述进入 `CONJECTURES.md`；
- 旗舰声明登记到 `Ript/Audit/AxiomChecks.lean` 与 `AXIOMS.md`；
- 只有有意且有证明支持时才更新可执行输出断言。

## 文档策略

所有维护页面按相同路径镜像到四种语言。命令、声明、状态或可信边界变化时同步相关语言。根目录蓝图、
模型矩阵、公理与猜想记录是机器规范来源；公理表变化后运行 `./scripts/sync-doc-reference-tables.sh`。

## 必须通过的门禁

`./scripts/quality-gate.sh` 检查源代码/文档策略、根导入、完整内核构建、声明 lint、可执行示例和公理
allowlist。不得为通过变更而削弱检查。

## PR 清单

- [ ] 目的单一，剩余边界明确；
- [ ] 锁定工具链下定向和完整构建通过；
- [ ] 旗舰假设与执行变化已经审计；
- [ ] 架构、状态、参考资料和相关语言均为最新；
- [ ] 不含无关、生成、秘密或私有文件。

审查同时评估定理陈述、建模意图与证明。决策规则见[治理](GOVERNANCE.md)。
