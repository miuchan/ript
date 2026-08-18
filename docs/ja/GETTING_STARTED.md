# はじめに

[English](../en/GETTING_STARTED.md) · [简体中文](../zh-CN/GETTING_STARTED.md) ·
[日本語](GETTING_STARTED.md) · [Esperanto](../eo/GETTING_STARTED.md)

このガイドでは、新しいチェックアウトにツールチェーンを導入し、検証済みビルドを作成した後、
代表的な実行可能モデルを確認します。

## 前提条件

次をインストールしてください。

- Git
- POSIX 互換シェル
- Lean ツールチェーンマネージャー [elan](https://github.com/leanprover/elan)

Lean は `lean-toolchain`、Mathlib は `lakefile.lean` と `lake-manifest.json` で固定されています。
システムに別途インストールされた Lean で置き換えないでください。

## クローンとビルド

```bash
git clone https://github.com/miuchan/ript.git
cd ript
lake exe cache get
lake build
```

利用可能な場合、`lake exe cache get` は一致する Mathlib のプリコンパイル済み成果物を取得します。
`lake build` は警告をエラーとして扱い、`Ript` ライブラリ全体をコンパイルします。

## 品質ゲート

```bash
./scripts/quality-gate.sh
```

ゲートは次の順に実行されます。

1. ソースポリシーと文書の検査
2. ルートモジュールの網羅性確認
3. カーネルによる完全ビルド
4. 宣言 lint
5. 実行可能例のアサーション
6. カーネル仮定 allowlist

個別に反復するときは次を利用できます。

```bash
./scripts/check-source-quality.sh
lake exe mk_all --check
lake build
lake env lean Ript/Audit/Lint.lean
./scripts/check-examples.sh
./scripts/check-axioms.sh
```

pull request をマージ可能にする前には、完全なゲートが必要です。

## 実行可能例

以下は通常の Lean モジュールです。実行すると全宣言を検査し、`#eval` の結果を表示します。

コア資源と関数：

```bash
lake env lean Ript/Examples/BitProcesses.lean
lake env lean Ript/Examples/CostFiltration.lean
lake env lean Ript/Examples/ClassicalCopy.lean
```

厳密な確率・意思決定モデル：

```bash
lake env lean Ript/Examples/StochasticBits.lean
lake env lean Ript/Examples/KleisliBits.lean
lake env lean Ript/Examples/SimpleDecision.lean
lake env lean Ript/Examples/StochasticSeparation.lean
```

計算と因果：

```bash
lake env lean Ript/Examples/SimpleComputation.lean
lake env lean Ript/Examples/SimpleCausalModel.lean
```

熱力学：

```bash
lake env lean Ript/Examples/SimpleThermalModel.lean
lake env lean Ript/Examples/ApproximateErasure.lean
lake env lean Ript/Examples/ExactWorkCycle.lean
```

量子・内部ユニバレント意味論：

```bash
lake env lean Ript/Examples/QubitChannel.lean
lake env lean Ript/Examples/UnivalentProcessUniverse.lean
lake env lean Ript/Examples/UnivalentSimplicial.lean
```

期待される出力は `scripts/check-examples.sh` が強制します。単なる説明用スニペットではありません。

## 依存パッケージとして使う

Ript にはまだ安定したタグ付きリリースがありません。完全な commit SHA を固定してください。

```lean
require ript from git
  "https://github.com/miuchan/ript.git" @ "<commit-sha>"
```

`lakefile.lean` を変更した後は次を実行します。

```bash
lake update ript
lake exe cache get
lake build
```

狭い import を推奨します。

```lean
import Ript.Resource.Budget
import Ript.Core.CostedProcess
import Ript.Models.FiniteStochastic
```

`import Ript` は探索には便利ですが、意図的に広い import です。

## 再現可能な研究利用

成果物には次を記録してください。

- Ript の完全な commit SHA
- `lean-toolchain` の内容
- `lake-manifest.json` に記録された Mathlib リビジョン
- 実際の検証コマンド
- `AXIOMS.md` に監査された対象定理の仮定

API が不安定な間は、パッケージ版だけでは再現に不十分です。

## トラブルシューティング

### Lean バージョンが一致しない

リポジトリルートで `elan show` を実行します。`lean-toolchain` が指定するツールチェーンが選ばれない
場合は、リポジトリを変更する前に elan を修復してください。

### Mathlib のコンパイル済み成果物がない

`lake exe cache get` を再実行します。プラットフォーム用キャッシュがなければ、`lake build` が
依存関係をローカルでコンパイルするため時間がかかります。

### ルートモジュール網羅性エラー

すべての公開実装モジュールは `Ript.lean` から import されなければなりません。狭い import を追加し、
`lake exe mk_all --check` を再実行してください。

### 公理 allowlist エラー

スクリプトを緩和しないでください。該当宣言に `#print axioms` を実行し、依存が妥当か確認します。
定理と信頼境界が実際に変わった場合だけ、`Ript/Audit/AxiomChecks.lean` と `AXIOMS.md` を同時に
更新してください。

### 実行例の出力が変わった

まず意味論上の変更を調査します。新しい出力が意図的で、対応する例で証明されている場合だけ
`scripts/check-examples.sh` を更新してください。

## 次に読むもの

- [アーキテクチャ](ARCHITECTURE.md)
- [研究状況](RESEARCH_STATUS.md)
- [形式化ブループリント](reference/BLUEPRINT.md)
