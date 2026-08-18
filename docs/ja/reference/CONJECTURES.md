# 予想と未証明研究命題

[English](../../en/reference/CONJECTURES.md) · [简体中文](../../zh-CN/reference/CONJECTURES.md) ·
[日本語](CONJECTURES.md) · [Esperanto](../../eo/reference/CONJECTURES.md)

この台帳は、Lean 命題としてコンパイルされるがカーネル検査済み証明をまだ持たない命題を記録します。
有効な項目には `FORMALIZED_BUT_UNPROVED` と宣言名が必要です。機械的正本は
[`CONJECTURES.md`](../../../CONJECTURES.md)です。

## 現在の台帳

現在、有効な `FORMALIZED_BUT_UNPROVED` 命題はありません。研究計画が完成したという意味では
ありません。まだ正確な Lean 命題に定式化されていない構成課題を、暗黙の仮定や公理として扱いません。

## 全体目標と未解決の定理族

Ript は古典確率、量子、因果、計算、意味情報、熱力学を資源制約付き情報過程の異なるモデルとして
統合し、表現・完全性定理を証明することを目指します。異なる資源代数を束ねる全モデル双圏と、
資源写像に沿う共通構文のコスト押し出し、可逆式変換、解釈表現、自由モデル予算は実装済みです。

最初の字面どおりの共通構文スライスも実装済みです。一つの Boolean flip 生成元を厳密確率、
Pauli-X 量子、有限因果、多次元計算、タスク意味、Gibbs 保存熱モデルで実現し、六つの観測等式を
`sixModelFlipAgreement` が束ねます。

未解決の中心は次です。

1. Boolean スライスを六モデル族の特徴的構造を表現する共通合成構文へ拡張する。
2. 各解釈の正確な像を特徴づける表現・保存性定理を証明する。
3. 妥当な範囲で相対または絶対完全性を証明する。
4. 全異種モデル理論に普遍性を持つユニバレントまたは complete-Segal 意味論を構成する。

## 分類図の境界

外側全体と `n ↦ Map(Δ[n], N(M.Object))` の自然同型、真の境界 matching limit、普遍 limit lift、
全 matching map の fibration、各水平行の Kan/strict-Segal 構造、実際の completeness map の
`SSet.NerveEquivalenceWitness`、`SSet.GroupoidalCompleteSegal` への束縛は証明済みです。

固定 Mathlib には単体集合の弱同値クラスと完成した Quillen モデル構造がないため、Mathlib ネイティブな
標準 complete-Segal インスタンスはまだ記述できません。これは基盤 API の境界です。

## 双圏局所化の境界

`IsBicategoricalLocalization` は、marked 1-射の随伴同値化、全 inverting 擬関手の biessential
factorization、強変換/modification の各局所圏での前合成同値を要求します。Ript 版は
`IsCostExactBicategoricalLocalization` です。

実装済み：

- 恒等擬関手の完全な普遍性検査と、非自明なゼロコスト離散反例。
- `Fin 2` walking arrow の自由亜群化、明示的逆射と二つの逆法則。
- walking 座標だけを局所化し、非可逆 Boolean discard 2-セルを保持するパラメータ化積。
- retained、groupoid-valued、separable mixed、および随伴同値閉包に対する factorization。
- 自由亜群の端点正規形、thinness、`Fin 2` 上の codiscrete 亜群との同値。
- 強変換と modification の lift、および各局所圏での前合成同値。
- 一般の非分離 inverting 擬関手に対する `PrelaxFunctor` の対象・1/2-射作用、恒等比較、八つの
  endpoint-normalized 二項 compositor。
- 左右自然性、任意射の左右単位則、全 forward 三項結合則、最初の inverse/retained/retained
  (`1→0→0→0`) 結合分岐。

未完了：逆または相殺を含む残り十の端点結合則、擬関手への束縛、最終 source-factorization の随伴
同値、全資源過程双圏への一般化。これらが欠けている global `lift` フィールドに対応します。

## 完成済みの通常局所化

内部亜群の恒等・骨格・制限 Yoneda は Mathlib `Functor.IsLocalization` を満たします。またモデル
双圏のホモトピー 1-圏には cost-reflecting class の Gabriel–Zisman 局所化があります。非可逆 marked
arrow は逆射が実際に追加されることを示し、非可逆モノイダル 2-セルは locally discrete target が
二次元情報を保持できない理由を示します。

## 最近完了：有限確率 Blackwell 逆定理

`Ript.Models.Decision.RationalSeparation.finiteBlackwellShermanStein` はカーネル検査済みです。非空有限
隠れ状態に対し、すべての厳密有限意思決定問題でのリスク順序は厳密確率 garbling を導きます。
非空条件は `EmptyParameterBoundary` 反例により必要です。

証明は、確率 garbling の有理決定論的単体表現、有理点の実凸包から有理凸包への反映、
Hahn–Banach 分離と有理密度、signed separator の非負有理 decision certificate への変換を接続します。
仮定は `[propext, Classical.choice, Quot.sound]` で、LP ソルバーの抽出は主張しません。

## アルゴリズム境界

有限実エネルギースペクトルでは、基準状態に対する全 Boltzmann 比が正有理数であることと、正規化
Gibbs 確率が厳密有理であることが同値です。有理重みの実行例と `sqrt 2` 障害はありますが、任意の
実指数式の等号を判定する一般アルゴリズムは提供しません。
