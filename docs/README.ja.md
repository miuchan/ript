# Ript

**資源添字付きプロセス理論のための、カーネル検証済み Lean 4 基盤。**

[English](../README.md) · [简体中文](README.zh-CN.md) ·
[日本語](README.ja.md) · [Esperanto](README.eo.md)

[![Quality Gate](https://github.com/miuchan/ript/actions/workflows/ci.yml/badge.svg)](https://github.com/miuchan/ript/actions/workflows/ci.yml)
![Lean 4.33.0](https://img.shields.io/badge/Lean-4.33.0-0d6efd)
![mathlib 4.33.0](https://img.shields.io/badge/mathlib-4.33.0-a42e2b)
![研究状況](https://img.shields.io/badge/status-early--stage%20research-orange)

Ript は、振る舞いと資源使用を合成できる型付きプロセスを形式化し、実行可能な有限モデルを
資源上界・健全性・完全性・構造保存意味論のカーネル検証済み結果へ接続します。

> [!IMPORTANT]
> Ript は初期段階の研究ソフトウェアです。コンパイル済み結果はカーネル検証されていますが、
> 公開 API と研究の最前線は現在も変化しています。

## クイックスタート

[elan](https://github.com/leanprover/elan) をインストールし、固定された Lean と Mathlib の
プロジェクトをビルドします。

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
lake build
```

要件、実行可能な例、依存利用、再現可能性、トラブルシューティングは
[導入ガイド](GETTING_STARTED.md)を参照してください。

## 目的別ガイド

- **何が実装済みか？** [モデル機能行列](../MODEL_MATRIX.md)
- **何が証明済みで、何が未解決か？** [研究状況](RESEARCH_STATUS.md)
- **ライブラリはどう構成されているか？** [アーキテクチャ](ARCHITECTURE.md)
- **信頼境界と成熟度は？** [プロジェクトの範囲と信頼境界](PROJECT_SCOPE.md)
- **正確な研究記録は？** [形式化ブループリント](../BLUEPRINT.md)、
  [公理一覧](../AXIOMS.md)、[予想台帳](../CONJECTURES.md)
- **どこから読めばよいか？** [ドキュメントハブ](README.md)

## コントリビューション

[コントリビューションガイド](../CONTRIBUTING.md)を読み、PR の前に
`./scripts/quality-gate.sh` を実行してください。

Ript は [Lean 4](https://lean-lang.org/) と
[Mathlib](https://github.com/leanprover-community/mathlib4) で構築されています。
