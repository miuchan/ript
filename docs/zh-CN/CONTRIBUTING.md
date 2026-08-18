# 为 Ript 做贡献

[English](../en/CONTRIBUTING.md) · [简体中文](CONTRIBUTING.md) ·
[日本語](../ja/CONTRIBUTING.md) · [Esperanto](../eo/CONTRIBUTING.md)

Ript 把证明可信度、显式依赖和可复现计算视为合并要求，而不仅是代码审查惯例。

## 必须通过的质量门禁

在仓库根目录运行：

```bash
./scripts/quality-gate.sh
```

门禁会拒绝证明占位符、项目自定义公理、不安全声明、编译器信任逃逸、过宽的 `Mathlib` 导入、
隐式 Lean 标识符、陈旧的根模块导入、声明 lint 失败、可执行行为变化、构建警告和未记录的定理
假设，随后执行完整内核构建。

CI 以稳定的 `Lean quality gate` job 暴露同一组检查。只有该 job 通过，变更才可合并。

## 证明与依赖策略

- 未证明研究陈述写入 `CONJECTURES.md`，不要声明为定理或公理；
- 导入尽可能窄的 Mathlib 模块；
- 每个实现模块保留 `set_option autoImplicit false`；
- 旗舰定理同时登记到 `Ript/Audit/AxiomChecks.lean` 和 `AXIOMS.md`；
- 若有意改变可执行行为，应在同一变更中更新 `scripts/check-examples.sh` 的示例断言。

## 文档策略

- 每个逻辑页面必须以相同相对路径镜像到 `docs/en`、`docs/zh-CN`、`docs/ja` 和 `docs/eo`；
- 公开声明、命令、状态或可信边界改变时，同步更新四种语言；
- 根目录 `AXIOMS.md`、`BLUEPRINT.md`、`CONJECTURES.md` 和 `MODEL_MATRIX.md`
  保持为机器真源；
- 修改公理清单后，先运行 `./scripts/sync-doc-reference-tables.sh`，再运行质量门禁。
