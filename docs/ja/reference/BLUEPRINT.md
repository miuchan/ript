# Ript 形式化ブループリント

[English](../../en/reference/BLUEPRINT.md) · [简体中文](../../zh-CN/reference/BLUEPRINT.md) ·
[日本語](BLUEPRINT.md) · [Esperanto](../../eo/reference/BLUEPRINT.md)

この文書は Lean カーネルが検査した実装状態だけを記録します。状態は `DEFINED`、
`STATEMENT_FORMALIZED`、`PROVED`、`BLOCKED`、`OPEN_RESEARCH` に限定されます。
[機械的正本](../../../BLUEPRINT.md)には全宣言の Lean 型、依存関係、仮定、ソースを収録し、
この日本語版は同じ段階境界と定理族を案内します。

## 研究目標

計算可能・機械検証可能・ユニバレント・高次圏論的な資源制約情報過程理論を構築し、古典確率、
量子過程、因果モデル、計算、意味情報、熱力学を異なるモデルとして表現・完全性定理で結ぶことです。
個別段階の `PROVED` は、この全体目標の完了を意味しません。

## 依存関係の幹

```text
資源代数 → コスト付き過程 → 予算/フィルトレーション/資源変更
    ↓
逐次構文 → 解釈 → 健全性 → 項モデル → 相対完全性/厳密初期性/経路表現
    ↓
モノイダル構文 → 並列コスト → 解釈/健全性 → 自由モデル初期性
    ↓
有限関数 / 確率 / 意思決定 / 計算 / 因果 / 熱 / 量子モデル
    ↓
モデル双圏 → 異種全双圏 → 通常・高次局所化
    ↓
内部ユニバレント構文 → 亜群/商/骨格 → Yoneda → 単体神経 → 分類図
```

共通モノイダル構文は `φ : R →+o S` に沿ってコストだけを押し出せます。ワイヤと生成元は不変、
式変換は可逆、異種解釈は通常の押し出し解釈と同値で、自由モデルは変換予算を厳密に実現します。

## 段階状態

| 段階 | 範囲 | 状態 |
| --- | --- | --- |
| 0 | 環境、プロジェクト、文書、CI、監査基準 | `PROVED` |
| 1 | 逐次資源過程の縦断 | `PROVED` |
| 1（有限決定論） | デカルトテンソル、古典複製/破棄、因果性、Boolean 証拠 | `PROVED` |
| 1（表現） | コストと到達予算フィルトレーションの往復 | `PROVED` |
| 2 | テンソル、対称性、並列資源、自由普遍 lift | `PROVED` |
| 2（一般逐次表現） | 任意シグネチャの生成元経路、商項モデルと経路圏の明示的同値、厳密自由コスト、意味経路像、経路忠実完全性 | `PROVED` |
| 2（逐次初期性） | 解釈と自由源資源関手の分類同値；通常および `φ : R →+o S` に沿う異種厳密延長型の可縮性 | `PROVED` |
| 3–5 | 有限確率、有限分布 Kleisli、Mathlib `Stoch` 表現 | `PROVED` |
| 6 | Blackwell 順序、有限リスク、完全有限逆定理、有理分離、意味価値、全タスク意味順序・数値プロファイル完全性 | `PROVED` |
| 7（計算） | 多次元全計算と `Option` 部分計算 | `PROVED` |
| 7（ランダム化計算） | 厳密確率核、四次元資源、実行可能予算、逐次/並列厳密加算、完全対称モノイダル構造 | `PROVED` |
| 7（因果） | 有限 DAG、同時分布、固定 DAG soft/stochastic/hard 介入、縮約 last-write-wins 正規形、厳密モデル/チャネル表現・完全性 | `PROVED` |
| 8 | 有限平衡、Gibbs 保存チャネル内在像・一意 lift、Gibbs 分類、自由エネルギー、相関、Landauer、電池証人 | `PROVED` |
| 9 | Kraus チャネル/操作、正規化 instrument、依存 bind と Born 連鎖則、第一級再帰 instrument 木、正規依存履歴、厳密分岐表現、計算可能履歴コスト/木予算、記録表現、完全対称モノイダル構造 | `PROVED` |
| 10 | 固定資源モデル双圏、2-セル、整合性、コスト厳密同値 | `PROVED` |
| 10（異種資源） | 資源再添字、異種強モデル射、予算移送 | `PROVED` |
| 10（異種構文） | 可逆な式/導出変換、証明論的保存性、異種健全性、直接強対称資源変更自由 lift、可縮な厳密延長、厳密予算 | `PROVED` |
| 10（六モデル共通スライス） | 同一単位コスト Boolean flip の確率、量子、因果、計算、意味、熱解釈と一致定理 | `PROVED` |
| 10（六モデル合成スライス） | 三インターフェース二 flip を確率合成、Pauli-X、三ノード因果鎖、資源加算、意味後処理、閉熱プロトコルで検証 | `PROVED` |
| 10（六モデル線形完全性） | 計算可能正規経路、一意正規化、薄い項モデル、単元像表現、資源変換保存性、六解釈の等号反映 | `PROVED` |
| 10（六モデル操作的消去） | 二座標 expose–erase、古典定数化、量子 reset、因果機構置換、計算コスト、意味価値消失、Landauer 飽和 | `PROVED` |
| 10（六モデル非薄完全性） | 四資源菱形構文、形式的に異なる二平行経路、分岐保持正規化、厳密二元像、経路分離条件、六モデル完全性 | `PROVED` |
| 10（六モデル並列スライス） | 共通対称モノイダル `flip ⊗ flip` の六モデル検証；六つの正準異種自由 lift を同一共通構文対象から出る全資源モデル双圏 1-セルへ昇格 | `PROVED` |
| 10（六モデル厳密ノイズ） | 4 分の 1 crossover BSC の確率、random-unitary 量子、ノイズ因果、四資源ランダム化計算、意味、Gibbs 保存解釈；厳密一致、コヒーレンス分離、意味価値、六自由 lift | `PROVED` |
| 10（六モデル適応分岐木） | 固定深度二分結果依存生成元選択、正履歴正規形、厳密経路コスト/最悪時予算、記録チャネル表現と観測完全性、確率・コヒーレント量子・因果・計算・意味・熱の二段実現 | `PROVED` |
| 10（依存有限分岐） | 可変深度、生成元依存任意有限結果、依存 Sigma 履歴、厳密高さ/経路コスト/最悪時予算、明示的履歴同値に沿う表現・観測完全性、固定深度二分言語の保守的埋め込み | `PROVED` |
| 10（自由依存分岐代数） | 分岐代数圏、始木代数、一意 fold、明示的健全かつ絶対完全な合同、結合的単位的葉接ぎ木、劣加法的高さ/予算 fold | `PROVED` |
| 10（対称モノイダル分岐代数） | 分岐代数の選択終対象/二元積、笛卡尔対称モノイダル構造と完全整合/コピー/破棄、成分積 fold、二モデル同時等号、木項モデル共同完全性 | `PROVED` |
| 10（木レベル独立並列分岐） | 明示的異種二レーン、対正規履歴/状態、厳密チャネル成分分解、資源加算、レーン対称性、共有境界接ぎ木、厳密テンソル–逐次交換則、並列観測完全性 | `PROVED` |
| 10（全双圏） | 資源代数を束ねた対象、異種 1/2-セル、交換、五角形、三角形 | `PROVED` |
| 12（全モデル単体ブリッジ） | Kan strict-Segal 対象同値コア、内部同値類と恒等辺の厳密対応、非可逆 2-セルを保持する完全局所 mapping nerve、整合的大域 Duskin 3-骨格、全次元座標 semi-simplicial nerve、および全縮退を含む strictly unitary lax 有限順序図の native 完全 Duskin nerve | `PROVED` |
| 10（通常局所化） | モデルホモトピー 1-圏のコスト厳密局所化 | `PROVED` |
| 11 | 公理なしの深い過程構文、商亜群、内部ユニバレンス | `PROVED` |
| 12（切断/前層/亜群） | 対象完備化、骨格、Yoneda、通常局所化 | `PROVED` |
| 12（単体） | Kan、strict Segal、quasicategory、2-coskeletal、ホモトピー圏回復 | `PROVED` |
| 12（分類図） | Rezk 分類図、外 Segal、matching limit と fibration | `PROVED` |
| 12（高次局所化仕様） | marked inversion、擬関手前合成、局所同値、walking テスト族 | `PROVED` |
| 12（高次局所化構成） | 全資源過程双圏の局所化擬関手、native normal-lax/座標 Duskin 単体の次元別同値、complete-Segal 2-space 組立て、対応する弱同値と普遍比較 | `OPEN_RESEARCH` |

## 主要定理族

- 資源：予算付き恒等/合成、コスト–フィルトレーション往復、資源再添字。
- `SequentialNormalForm`：任意逐次シグネチャの項圏–経路圏同値、厳密コスト保存、経路像、経路忠実完全性。
- `SequentialFree/ResourceChangingSequentialFree`：解釈–自由源資源関手分類、可縮な厳密延長型、自由 lift、コスト境界。
- 構文・意味論：`eval_cost_le`、逐次/モノイダル健全性、項モデル相対完全性、自由 lift の存在・一意性。
- 異種構文：`equivMappedCostInterpretation`、変換後評価境界、自由モデル厳密予算。
- 六モデル：モデル固有の Boolean flip 解釈、計算資源変換、`sixModelFlipAgreement`。
- 合成スライス：二段 flip の恒等回復と `sixModelCompositionAgreement`。
- `CompositionalBitCompleteness`：正規形、厳密像表現、`sixModelSemanticCompleteness`。
- 操作的消去：六モデルの reset、介入、価値消失、`sixModelErasureAgreement`。
- `DiamondBitTheory/Realizations`：非薄な厳密像、六モデル経路分離、意味完全性、六つの正準異種自由 lift。
- `ParallelBitRealizations/HigherModels`：六モデル並列挙動、完全 Kraus 量子目標、任意の積密度行列上の Pauli-X テンソル、厳密計算資源加算、検査済み資源写像付き全双圏 1-セル。
- `QubitInstrument/InstrumentSyntax`：plus 状態測定・フィードバック、三履歴確率 `1/2、1/2、0`・予算 `2` の第一級再帰木、履歴分岐表現、一/二単位資源自由 lift。
- `NoisyBitRealizations`：六モデル共通 `3/4–1/4` ノイズ境界、plus コヒーレンスを保持する random-unitary 量子と保持しない measurement–preparation の分離、厳密計算資源と意味リスク/価値。
- `Syntax.Branching/AdaptiveNoiseRealizations`：任意固定深度二分木の実行可能履歴、正分岐表正規形、厳密コスト、表現、観測完全性；二生成元適応木の四厳密分岐、六モデル表現、量子コヒーレンス分離、完全性による木の分離。
- `Syntax.DependentBranching/Examples.DependentBranching`：可変深度で生成元ごとに異なる有限結果型を持つ木、明示的履歴同値、記録表表現/完全性、保守的二分埋め込み；`Bool`/`Fin 3` 例は五つの異なる長さの履歴を持つ。
- `DependentBranchingRealization`：任意の有限正依存正規形の六モデル一般表現、経路コスト/履歴長資源境界、全台支持因果忠実性、共同等号反映完全性、外部指定の互換目標平衡への一意熱 lift。
- `Syntax.DependentBranching.Free`：分岐代数と準同型の圏、始木代数、一意自由解釈、全代数での健全/完全等式、逐次接ぎ木モノイド、高さ/予算数値 fold。
- `Syntax.DependentBranching.Monoidal`：分岐モデル代数の選択有限積と笛卡尔対称モノイダル整合、二モデル解釈を厳密に対にする積 fold、木項モデル積の共同完全性。
- `Syntax.DependentBranching.Parallel`：木レベル明示二レーン、独立確率チャネル分解、交換対称、資源加算、共有境界逐次接ぎ木、厳密交換則、並列完全性。
- 確率・意思決定：`FiniteStochastic` 圏、Kleisli と `Stoch` の表現、Blackwell 逆定理、有理分離、全タスク厳密数値プロファイル完全性、単一タスクの不完全性証人。
- 計算・因果：多次元資源境界、部分計算、DAG 正規化、soft/stochastic/hard 介入の縮約正規形・表現・完全性。
- 熱：Gibbs 保存チャネルの内在像/一意 lift、KL、自由エネルギー、相関、Landauer、浴/電池付き証人。
- 量子：Kraus 正値性・トレース保存、操作と有限 instrument、正規化 Born 確率と事後状態、逐次/並列 instrument 則、古典記録チャネル表現、完全対称モノイダル整合律、完全正値性、トレース破棄、古典埋め込み。
- 高次：固定/全モデル双圏、コスト厳密同値、通常局所化、非可逆 2-セル保持の walking 試験。
- ユニバレント：内部恒等、対象完備化、Yoneda、Kan 神経、strict Segal、分類図。

各宣言の正確な Lean 型と `Classical.choice` 境界は
[英語完全版](../../en/reference/BLUEPRINT.md)または[機械的正本](../../../BLUEPRINT.md)を参照してください。

## 未完了の境界

資源制約付き意味プロファイルまたはより豊かな/無限タスク言語、異種ノードキャリア・グラフ変更・ポリシー依存因果介入、エネルギー分解された熱操作 dilation へ拡張するモデル固有像の表現/保存性/
完全性、真のモデル間比較、全資源過程双圏の内部ユニバレントまたは標準 complete-Segal 普遍局所化
は未証明です。これらを Lean の公理や仮定済み定理として隠していません。
