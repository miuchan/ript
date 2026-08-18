# Ript へのコントリビューション

[English](../en/CONTRIBUTING.md) · [简体中文](../zh-CN/CONTRIBUTING.md) ·
[日本語](CONTRIBUTING.md) · [Esperanto](../eo/CONTRIBUTING.md)

Ript は証明の信頼性、明示的依存関係、再現可能な計算をレビュー慣習ではなくマージ要件とします。

## 必須品質ゲート

リポジトリルートで実行してください。

```bash
./scripts/quality-gate.sh
```

ゲートは証明穴、独自公理、unsafe 宣言、コンパイラ信頼回避、広すぎる `Mathlib` import、暗黙の
Lean 識別子、古いルート import、宣言 lint エラー、実行動作の変化、ビルド警告、未文書化の仮定を
拒否し、完全なカーネルビルドを行います。

CI の安定ジョブ名は `Lean quality gate` です。これが成功した変更だけをマージできます。

## 証明と依存関係の方針

- 未証明の研究命題は `CONJECTURES.md` に置き、定理や公理として宣言しない
- 実用上もっとも狭い Mathlib モジュールを import する
- 全実装モジュールで `set_option autoImplicit false` を維持する
- 主要定理を `Ript/Audit/AxiomChecks.lean` と `AXIOMS.md` の両方に追加する
- 実行動作を意図的に変更する場合、同じ変更で `scripts/check-examples.sh` の期待値を更新する

## ドキュメント方針

- 全論理ページを同じ相対パスで `docs/en`、`docs/zh-CN`、`docs/ja`、`docs/eo` に配置する
- 公開主張、コマンド、状態、信頼境界を変更したときは四言語すべてを更新する
- ルートの `AXIOMS.md`、`BLUEPRINT.md`、`CONJECTURES.md`、`MODEL_MATRIX.md` を
  機械的正本として維持する
- 公理一覧の変更後は `./scripts/sync-doc-reference-tables.sh` を実行してから品質ゲートを実行する
