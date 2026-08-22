# Ript ドキュメント

[English](../en/README.md) · [简体中文](../zh-CN/README.md) ·
[日本語](README.md) · [Esperanto](../eo/README.md)

Ript は資源添字付き情報過程のための Lean 4 カーネル検証済み研究ライブラリです。実行可能な
有限構文を、確率・量子・因果・計算・意味情報・意思決定・熱力学モデルへ接続し、任意能力を
分離して扱います。

> [!IMPORTANT]
> 多くの実証済み基盤がありますが、初期研究段階です。最終大域定理と安定 API は未完成です。

## 現在のスナップショット

- 資源感応構文、予算、健全性、相対完全性、自由意味論がコンパイル済み
- 六モデル族すべてに具体インスタンスと検査済み非自明例がある
- モデルと資源変換射は検証済み双圏層を形成する
- 内部ユニヴァレンスと complete-Segal 基盤は実行可能コアの下流にある
- generated hammock mapping space は実際の局所化対象と同値で、明示的 nerve ホモトピー逆と
  停止する簡約を持つ

現在の最前線は critical-pair joinability、古典的 reduced-hammock 不変性、標準弱同値包装、
大域 Rezk 定理です。

## はじめに

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
./scripts/quality-gate.sh
```

続きは[導入ガイド](GETTING_STARTED.md)を参照してください。

## 目的別に読む

- **プロジェクトを理解：** [範囲と信頼境界](PROJECT_SCOPE.md) · [アーキテクチャ](ARCHITECTURE.md)
- **証明済み内容を見る：** [研究状況](RESEARCH_STATUS.md) · [モデル機能行列](reference/MODEL_MATRIX.md)
- **厳密な証拠を監査：** [ブループリント](reference/BLUEPRINT.md) ·
  [公理](reference/AXIOMS.md) · [予想](reference/CONJECTURES.md)
- **参加する：** [コントリビューション](CONTRIBUTING.md) · [ガバナンス](GOVERNANCE.md) ·
  [セキュリティ](SECURITY.md)
- **言語を変更：** [多言語ドキュメントハブ](../README.md)

## 成熟度と再利用

再現可能性には完全な commit SHA を固定してください。安定リリースや API 互換保証はありません。
オープンソースライセンスは未選択で、公開表示だけでは複製・変更・再配布権を与えません。
