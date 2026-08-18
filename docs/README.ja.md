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
コスト上界・健全性・完全性結果・構造保存意味論のカーネル検証済み証明へ接続します。

> [!IMPORTANT]
> Ript は初期段階の研究ソフトウェアです。コンパイル済み結果は Lean のカーネルで検証されますが、
> 公開 API は安定しておらず、完全な物理情報理論を主張するものでもありません。

## なぜ Ript なのか

通常のプロセス理論は何が合成できるかを記述します。資源に敏感な理論では、コストの合成、
コストを保存する書き換え、構文的見積もりが意味論的に妥当となる条件も必要です。Ript は
これらの義務を明示し、機械検証可能にします。

- 順序付き加法資源で直列・並列予算を追跡します。
- 実行可能な構文と商型に基づく証明モデルを分離します。
- 解釈が型、方程式、資源上界を保存することを証明します。
- テンソル、コピー、破棄、凸性、因果性、熱力学などの能力を相互に推論しません。
- 主要定理ごとにカーネル仮定の監査記録を保持します。

## 主な特徴

- **形式的な核：** コスト付き圏、実行可能な逐次・モノイダル構文、健全性、相対完全性、
  モノイダル初期性。
- **正確な有限モデル：** 決定論、確率、意思決定、計算、因果、熱、量子の各インスタンス。
- **高次構造：** プロセスモデルの双圏、コスト完全な同値、検証済み walking-localization 構成。
- **内部同一性意味論：** 公理を追加しない深い構文と、群作用圏、商、前層、単体、
  classifying diagram による解釈。

正確な機能は[モデル機能行列](../MODEL_MATRIX.md)、制限は[研究状況](RESEARCH_STATUS.md)を
参照してください。

## クイックスタート

[elan](https://github.com/leanprover/elan) をインストールして実行します。

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
lake build
```

変更を提出する前に、ローカルの完全な CI 契約を実行します。

```bash
./scripts/quality-gate.sh
```

実行可能なモデルを直接検証する例：

```bash
lake env lean Ript/Examples/StochasticBits.lean
```

[導入ガイド](GETTING_STARTED.md)には、要件、例、依存設定、再現性、トラブルシューティングが
まとまっています。

## Lean から使う

タグ付きリリースが提供されるまでは、完全なコミット SHA を固定してください。

```lean
require ript from git
  "https://github.com/miuchan/ript.git" @ "<commit-sha>"
```

必要な API を提供する最小のモジュールを優先します。

```lean
import Ript.Resource.Budget
import Ript.Models.FiniteStochastic
```

## ドキュメント

- [ドキュメントハブ](README.md) — 目的別の最短経路。
- [導入ガイド](GETTING_STARTED.md) — ビルド、実行、依存利用。
- [アーキテクチャ](ARCHITECTURE.md) — レイヤーと依存境界。
- [研究状況](RESEARCH_STATUS.md) — 証明済み、進行中、主張しない結果。
- [モデル機能行列](../MODEL_MATRIX.md) — コンパイル済み機能。
- [形式化ブループリント](../BLUEPRINT.md) — 定理依存関係と正確な状況。
- [公理一覧](../AXIOMS.md) — 監査済み `#print axioms` 出力。
- [予想台帳](../CONJECTURES.md) — 未解決の研究命題。
- [コントリビューションガイド](../CONTRIBUTING.md) — 証明と品質の方針。

## 信頼境界、状況、ガバナンス

Ript は証明プレースホルダー、プロジェクト固有公理、コンパイラ信頼回避、不安全なライブラリ
宣言を禁止します。CI は Lean と Mathlib の版を固定し、警告をエラーとして扱い、代表モデルを
実行し、公理許可リストを検査します。正確な依存は [AXIOMS.md](../AXIOMS.md) に記録されます。

現在の最前線は任意の二次元 walking-localization 因子分解です。全射の自然性と完全な左右単位律は
コンパイル済みで、oplax 結合律、pseudofunctor 化、最終的な随伴同値が未完成です。
権威ある境界は [RESEARCH_STATUS.md](RESEARCH_STATUS.md) を参照してください。

Lake パッケージ版は `0.1.0` で、安定 API リリースやアーカイブ DOI はまだありません。研究成果では
リポジトリと完全なコミット SHA を引用してください。オープンソースライセンスは未選定であり、
ソース公開だけでは再利用権は付与されません。

## コントリビューション

主張がコンパイル済み定理の強さと一致し、証明境界を保つ変更を歓迎します。PR の前に
[CONTRIBUTING.md](../CONTRIBUTING.md)を読み、`./scripts/quality-gate.sh` を実行してください。

Ript は [Lean 4](https://lean-lang.org/) と
[Mathlib](https://github.com/leanprover-community/mathlib4) によって構築されています。
