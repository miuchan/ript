# Ript

**資源添字付きプロセス理論のための、Lean 4 カーネル検査済み基盤。**

[English](../README.md) · [简体中文](README.zh-CN.md) ·
[日本語](README.ja.md) · [Esperanto](README.eo.md)

[![品質ゲート](https://github.com/miuchan/ript/actions/workflows/ci.yml/badge.svg)](https://github.com/miuchan/ript/actions/workflows/ci.yml)
![Lean 4.33.0](https://img.shields.io/badge/Lean-4.33.0-0d6efd)
![mathlib 4.33.0](https://img.shields.io/badge/mathlib-4.33.0-a42e2b)
![研究状況](https://img.shields.io/badge/status-early--stage%20research-orange)

Ript は **Resource-Indexed Information Process Theory** を形式化します。
型付きプロセスの振る舞いと資源使用を合成可能にし、実行可能なモデルを、コスト上界・
健全性・相対完全性・構造保存意味論のカーネル検査済み証明へ接続します。

> [!IMPORTANT]
> Ript は初期段階の研究ソフトウェアです。コンパイル済みの結果は Lean のカーネルで
> 検査されますが、公開 API は安定しておらず、物理情報の完全な理論を主張しません。

## なぜ Ript なのか

通常のプロセス理論は、どのプロセスを合成できるかを記述します。資源を扱う理論では、
さらに合成のコスト、コストを保存する書き換え、構文上の見積もりが意味論的に妥当となる
条件を説明する必要があります。

Ript はこれらを明示的なインターフェースと定理にします。

- 資源は順序付き加法代数をなす。
- 直列・並列合成には証明済みの上界がある。
- 実行可能な構文と商に基づく証明モデルを分離する。
- 解釈は型・等式・宣言された資源境界を保存する。
- 決定論、確率、計算、因果、熱力学、量子モデルが共通インターフェースを実装する。
- 主要定理ごとに実際のカーネル仮定を監査する。

## 実装済みの内容

### 形式的な核

- 順序付き加法資源、予算、単調性、コスト filtration。
- 直列・並列合成を備えたコスト付き圏。
- 実行可能な直列構文と対称モノイダル構文。
- 明示的等式導出、健全性、項モデル、相対完全性、モノイダル初期性。

### 正確な有限モデル

- 有限関数、計量付き全域計算・部分計算。
- 非負有理数による正確な有限確率チャネル。
- 有限分布 Kleisli 表現と `Stoch` への忠実な橋渡し。
- Blackwell 比較、有限 Bayes リスク、タスク相対的意味価値。
- 正規化されたハード介入を持つ有限 DAG 因果モデル。
- 有限 Gibbs-preserving 系、KL/自由エネルギー定理、実行可能な Landauer 例。
- 有限次元 Kraus チャネルと忠実な古典的 dephasing 埋め込み。

### 高次構造と内部ユニバレンス境界

- 資源添字付き対称モノイダルプロセスモデルの双圏。
- コスト完全なモデル同値、通常のホモトピー局所化、非自明な walking-localization 例。
- 公理を追加しない内部同一視の深い埋め込み構文。
- 群oid、商、前層、単体神経、classifying diagram の意味論。
- 0/1-truncated な範囲を明示し、任意の Lean 同値を Lean の等式とはみなさない。

能力、制限、定理状態の正確な記録は、[モデル行列](../MODEL_MATRIX.md)、
[研究状況](RESEARCH_STATUS.md)、[形式化ブループリント](../BLUEPRINT.md)を参照してください。
このページは意図的に概要だけを残しています。

## クイックスタート

Git、POSIX shell、[elan](https://github.com/leanprover/elan) が必要です。

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
lake build
```

変更を提出する前に、全品質ゲートを実行してください。

```bash
./scripts/quality-gate.sh
```

エンドツーエンドの例も直接実行できます。

```bash
lake env lean Ript/Examples/StochasticBits.lean
lake env lean Ript/Examples/SimpleDecision.lean
lake env lean Ript/Examples/SimpleCausalModel.lean
```

全例一覧、個別検証、トラブルシューティングは
[入門ガイド](GETTING_STARTED.md)にあります。

## Lean 依存パッケージとして使う

タグ付きリリースまでは、完全な commit SHA を固定してください。

```lean
require ript from git
  "https://github.com/miuchan/ript.git" @ "<commit-sha>"
```

必要な最小モジュールを import します。

```lean
import Ript.Resource.Budget
import Ript.Models.FiniteStochastic
```

## ドキュメント

- [ドキュメントハブ](README.md)：目的別の最短ルート。
- [入門ガイド](GETTING_STARTED.md)：セットアップ、例、依存利用、問題解決。
- [アーキテクチャ](ARCHITECTURE.md)：層、依存方向、実行/証明境界。
- [研究状況](RESEARCH_STATUS.md)：完成した柱、現在の最前線、主張しない結果。
- [モデル能力行列](../MODEL_MATRIX.md)：実装・コンパイル済み能力のみ。
- [形式化ブループリント](../BLUEPRINT.md)：定理依存グラフと正確な状態。
- [公理一覧](../AXIOMS.md)：監査済み `#print axioms` 出力。
- [予想レジスター](../CONJECTURES.md)：未解決・最近解決した研究命題。
- [コントリビューション](../CONTRIBUTING.md)：必須の証明・品質方針。

詳細な技術文書は英語を単一の情報源としています。Lean 宣言、ブループリント、モデル行列、
公理監査は自然言語翻訳に依存しません。

## 信頼性と再現性

Ript は証明プレースホルダー、プロジェクト固有公理、コンパイラ信頼の迂回、`unsafe` 宣言、
ライブラリモジュールでの包括的な `import Mathlib` を禁止します。CI は固定された Lean と
Mathlib で再構築し、警告をエラーとして扱います。

商の健全性、命題外延性、古典選択などを使う定理の実際の依存関係は
[AXIOMS.md](../AXIOMS.md) に記録されています。

## 現在の研究最前線

現在の高次圏論的最前線は、任意の非分離二次元 walking-localization の因子分解です。
対象、1-射、2-射、恒等比較、合成比較、全射上の自然性データはコンパイル済みです。
oplax 単位・結合律、pseudofunctor 化、随伴同値による因子分解は未完成です。

一般可測因果モデル、弱同値を備えた Mathlib ネイティブ complete-Segal-space API、完全な
双圏的または Dwyer–Kan 局所化も未解決です。正確な境界は
[研究状況](RESEARCH_STATUS.md)を参照してください。

## コントリビューション

貢献は証明境界を保ち、実際に証明された強さだけを主張する必要があります。
[CONTRIBUTING.md](../CONTRIBUTING.md) を読み、`./scripts/quality-gate.sh` を実行し、
主要定理の変更時にはブループリントと公理一覧も更新してください。

## バージョン、引用、ライセンス

Lake パッケージは `0.1.0` で、安定 API はまだありません。研究成果では使用した完全な
commit SHA を記録してください。論文や DOI はまだないため、リポジトリ URL と固定 commit を
引用してください。

オープンソースライセンスはまだ選択されていません。ライセンスファイルが追加されるまで、
公開ソースだけでは複製、再配布、派生物作成の許可になりません。

## 謝辞

Ript は [Lean 4](https://lean-lang.org/) と
[Mathlib](https://github.com/leanprover-community/mathlib4) の上に構築されています。
