# Ript へのコントリビューション

[English](../en/CONTRIBUTING.md) · [简体中文](../zh-CN/CONTRIBUTING.md) ·
[日本語](CONTRIBUTING.md) · [Esperanto](../eo/CONTRIBUTING.md)

証明、モデル、例、文書、ツールの貢献を受け付けます。信頼性、明示的依存、再現性、正確な公開主張は
マージ要件です。

## 開始前

[範囲](PROJECT_SCOPE.md)、[アーキテクチャ](ARCHITECTURE.md)、[研究状況](RESEARCH_STATUS.md)、
issue と[予想台帳](reference/CONJECTURES.md)を確認します。範囲、公開定理、構成、信頼依存、
ガバナンス、セキュリティ、ライセンスの変更は先に議論してください。脆弱性は
[セキュリティポリシー](SECURITY.md)に従います。

## ワークフロー

```bash
git switch -c <focused-branch>
lake exe cache get
lake build <affected.module>
./scripts/quality-gate.sh
```

ブランチと commit を集中させ、PR に成果、検証、公理依存、互換性、残る境界を書きます。
マージには CI 成功とメンテナ承認が必要です。

## 証明・実装方針

- 証明穴、独自公理、信頼回避、unsafe 宣言は禁止
- `autoImplicit false` と狭い Mathlib import を維持
- 汎用基盤は `Ript/ForMathlib/` へ配置
- 実行データを商・選択代表の上流に保つ
- 能力境界と分野に正確な定理名を維持
- 未完了命題は `CONJECTURES.md` へ記録
- 主要宣言を AxiomChecks と `AXIOMS.md` で監査

## 文書と品質ゲート

保守ページを四言語で同じパスに置き、公開変更を同期します。公理表の変更後は
`./scripts/sync-doc-reference-tables.sh` を実行します。必須の
`./scripts/quality-gate.sh` は文書、根 import、全ビルド、lint、例、公理を検査します。

## PR チェック

- [ ] 目的と残る境界が明確
- [ ] 固定ツールチェーンで局所・全体ビルド成功
- [ ] 主要仮定と実行変更を監査済み
- [ ] 構成、状況、参照、全対象言語が最新
- [ ] 無関係・生成・秘密・私有ファイルなし

レビューは証明だけでなく定理文とモデル意図も確認します。[ガバナンス](GOVERNANCE.md)を参照してください。
