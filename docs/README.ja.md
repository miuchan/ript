# Ript

**資源添字付きプロセス理論のための、カーネル検証済み Lean 4 基盤。**

[English](../README.md) · [简体中文](README.zh-CN.md) ·
[日本語](README.ja.md) · [Esperanto](README.eo.md)

[![Quality Gate](https://github.com/miuchan/ript/actions/workflows/ci.yml/badge.svg)](https://github.com/miuchan/ript/actions/workflows/ci.yml)
![Lean 4.33.0](https://img.shields.io/badge/Lean-4.33.0-0d6efd)
![mathlib 4.33.0](https://img.shields.io/badge/mathlib-4.33.0-a42e2b)
![研究状況](https://img.shields.io/badge/status-early--stage%20research-orange)

Ript は **Resource-Indexed Information Process Theory（資源添字付き情報プロセス理論）**
を形式化します。型付きプロセスの振る舞いと資源使用を合成可能にし、実行可能な有限モデルを、
資源上界・健全性・完全性結果・構造保存意味論のカーネル検証済み証明へ接続します。

> [!IMPORTANT]
> Ript は初期段階の研究ソフトウェアです。コンパイル済み結果は Lean カーネルで検証されますが、
> 公開 API と研究の最前線は現在も変化しています。

## 収録内容

- **形式的基盤：** コスト付き圏、実行可能構文、解釈、健全性、相対完全性、モノイダル初期性。
- **正確な有限モデル：** 決定論、確率、意思決定、計算、因果、熱、量子の各インスタンス。
- **高次構造：** プロセスモデルの双圏、コスト完全な同値、walking-localization 構成。
- **監査可能な証明：** CI はプレースホルダーと未記録の仮定を拒否し、主要定理には公理一覧があります。

実装済み機能は[モデル機能行列](../MODEL_MATRIX.md)、証明済み・未解決・主張しない結果は
[研究状況](RESEARCH_STATUS.md)を参照してください。

## クイックスタート

[elan](https://github.com/leanprover/elan) をインストールして実行します。

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
lake build
```

変更を提出する前に、完全なローカル品質ゲートを実行します。

```bash
./scripts/quality-gate.sh
```

要件、例、依存利用、トラブルシューティングは[導入ガイド](GETTING_STARTED.md)にあります。

## ドキュメント

- [ドキュメントハブ](README.md) — 目的別の最短経路。
- [プロジェクトの範囲と信頼境界](PROJECT_SCOPE.md) — 設計、主張、証明方針、成熟度、ライセンス。
- [アーキテクチャ](ARCHITECTURE.md) — レイヤーと依存境界。
- [研究状況](RESEARCH_STATUS.md) — 実装済み、進行中、未解決。
- [形式化ブループリント](../BLUEPRINT.md) · [公理一覧](../AXIOMS.md) ·
  [予想台帳](../CONJECTURES.md) — 権威ある研究記録。

## コントリビューション

[コントリビューションガイド](../CONTRIBUTING.md)を読み、PR の前に
`./scripts/quality-gate.sh` を実行してください。

Ript は [Lean 4](https://lean-lang.org/) と
[Mathlib](https://github.com/leanprover-community/mathlib4) によって構築されています。
