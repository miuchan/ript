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

三インターフェース二 flip の合成拡張も証明済みで、六モデルの合成則を
`sixModelCompositionAgreement` が束ねます。

対称モノイダル拡張は同じ `flip ⊗ flip` 式を六モデル族へ解釈し、独立並列挙動と厳密計算資源加算、
六つの正準強対称資源変更自由 lift を証明します。モノイダル導出変換は証明論的に保存的で、各異種
モノイダル解釈の厳密延長型は可縮です。量子目標は完全有限 Kraus 圏であり、基底同値が全整合律を
持つ対称モノイダル構造を与え、テンソル Pauli-X は任意の積密度行列へ成分ごとに作用します。
有限量子 instrument も正規化完全正分岐族として実装され、事後状態、逐次・テンソル則、古典記録
CPTP 表現、結果選択トレース保存フィードバックを持ちます。コヒーレント測定例は古典結果で両事後状態を同一基底状態へ補正し、資源対応自由構文へ接続されます。
依存 bind は次の instrument と結果型を現在結果に依存させ、Born 連鎖則と Sigma 木再結合結合律を満たします。三履歴例は資源構文に統合済みです。
第一級帰納的 `InstrumentTree` は正規依存履歴、厳密履歴分岐表現、有限帰納、計算可能経路/木予算を与えます。
古典記録チャネルは有限 instrument 上で単射で、明示的履歴同値に沿う木評価、全再帰分岐写像、記録チャネルの等しさは同値です。
Kraus 行スライスにより、ブロック対角な古典結果チャネルは一意な instrument 原像を持ち、履歴再ラベル付け後の一段 instrument tree で実現されます。
単一の 4 分の 1 crossover ノイズ生成元も六モデル共有です。量子実現は random-unitary でコヒーレント入力上 measurement–preparation と区別でき、ランダム化計算は四資源を保持し、意味リスク/価値は厳密です。
対象宇宙 lift は共通構文と完全 Kraus 過程モデルを含む六目標を全資源モデル双圏へ束ね、六実現を検査済み資源写像付き強組紐
1-セルとして与えます。

独立した `expose ≫ erase` 構文は、古典消去、量子 reset、因果介入、計算、意味価値損失、電池が
支払う Landauer 飽和を `sixModelErasureAgreement` で接続します。
有限 hard-intervention プログラムは last-write-wins 部分代入へ計算可能に正規化され、実行は一回の正規介入に一致します。基底機構が恒定 Dirac 強制機構へ退化しないとき、局所機構意味論は正規形に完全です。

線形 bit 理論の表現・完全性は全面的未解決ではありません。六解釈の正規経路像と等号反映は証明済みで、
最初の非薄一般化も有限菱形について証明済みです。厳密二経路像と独立した経路分離証拠による六モデル
完全性を持ちます。一般自由経路正規化、経路像表現、経路忠実完全性は任意型付き逐次シグネチャで
成立済みです。さらに項圏–経路圏の明示的同値と厳密コスト保存、自由源資源関手による通常・異種解釈空間の分類、可縮な厳密延長型も証明され、
六菱形モデルでは生成元一致と変換後コスト境界を検査済みです。より豊かな操作言語におけるモデル
固有経路忠実性と像特徴づけが未解決です。
適応ノイズの第二の一般化もコンパイル済みです。任意固定深度二分木に実行可能な正履歴正規形、厳密コスト、記録チャネル表現、観測完全性があり、二段二生成元木は六つの固有モデル実現と統一表現定理を持ちます。
この境界は生成元依存の任意有限結果と可変深度分岐へさらに一般化されました。依存 Sigma 履歴、有限上限予算、明示的履歴同値に沿う厳密記録表表現/観測完全性、固定深度二分言語の保守的埋め込みがコンパイル済みです。
さらに任意の有限正依存正規形は六モデルへ一般的に実現されます。確率、measurement–preparation 量子、固定資源ランダム計算、構造化意味実験、熱チャネルは正規形等号を反映し、全台支持事前分布を持つ二節点因果結合も同様です。
厳密有限意味の数値境界も特徴づけられました。全タスクでの非負意味価値は Blackwell 支配と同値であり、正準無情報実験に対する全厳密タスク価値の一致は Blackwell 同値と同値です。Boolean 反例は単一タスクスカラーが完全不変量でないことを証明します。
熱過程の忘却写像の内在像も特徴づけられました。源/目標平衡を指定すると、有限確率チャネルは源平衡を目標平衡へ厳密に押し出す場合に限り、一意な Gibbs 保存 lift を持ちます。任意の依存正規形と外部指定目標平衡にも特殊化済みです。
固定 DAG 因果境界は任意の親代入依存 soft 機構置換を含み、stochastic 介入と Dirac hard 介入はその特殊例です。有限プログラムは last-write-wins 後に基底機構と等しい冗長書込みを計算可能に削除し、縮約正規形はモデル、チャネル、局所機構意味論に対し表現/完全です。
全資源モデル双圏は二層の単体ブリッジも持ちます。Kan 対象コアで内部モデル同値類と恒等辺が厳密に対応し、各モデル対の完全局所 mapping nerve が全 1/2-セルを保持します。垂直合成は 2-単体、水平合成は単体写像で、非可逆 discard 2-セルは全モデル復号後も非可逆です。
大域 2/3 次元 Duskin データも明示化され、三角形は任意の合成比較 2-セルを保持します。四面体境界は、結合子修正四面体整合式が成立する場合に限り一意な 3-単体を持ちます。
これらのデータは現在、全次元の真の大域 semi-simplicial Duskin nerve へ拡張済みです。すべての厳密単調順序埋め込みが制限による厳密な面写像として作用し、2/3 次元は上記の三角形/四面体データを厳密に復元します。
縮退の境界も native な完全 Duskin nerve によって閉じました。`n`-単体は局所離散有限順序 `[n]` から全資源モデル双圏への strictly unitary lax functor です。縮退を含むすべての単調順序写像が normal-lax 前合成で作用し、恒等/合成則は厳密に成立します。最初の縮退は頂点を複製し恒等 1-セルを生成し、lax 結合則は結合子修正四面体方程そのものです。完全 nerve の面制限から従来の座標 semi-simplicial nerve への自然変換も証明済みです。
逆表現には構成子正規基盤があります。`Ordinal n` と `Fin (n + 1)` の同値は明示的で、`fromFin` と finite-to-normal lax core は擬逆を選択しません。辺、比較、全 8 分岐の四面体整合性、始域輸送がすべてコンパイル済みです。座標単体と native normal-lax 単体の両往復は完全構造上で成立し、次元ごとの同値を形成します。輸送された座標 nerve は全ての面と縮退を持ち、全順序写像に関して native Duskin nerve と自然同型です。残るのは complete-Segal 2-space の組立てと高次局所化比較です。
その第一層として、総モデルホモトピー圏の Rezk core 図、全垂直レベルの Kan 性、既存対象 core との圏同値、選択 Kan 同値矢印空間の categorical completeness witness がコンパイル済みです。透明な恒等矢印函子、旧前向函子との自然同型、selected core inclusion も完成しました。その合成は実際の零縮退と明示的に自然同型であり、同値・inclusion・縮退・比較は機械可読な圏論的因子化として一括されています。新しい一般的な cylinder 構成は任意の自然変換から nerve 写像間の `SSet.Homotopy` を作り、ここでも中介 completeness 写像と実際の零縮退の単体ホモトピーを与えます。さらに各水平行は垂直同値列の圏の通常 nerve と自然同型で、実際の外側 spine は全双次数で同値です。これらは `SegalCompletenessCore` に一括されました。選択同値圏は実際の外側可逆矢印の充満部分圏とも明示的に圏同値で、そこへ直接入る completeness 写像も圏同値の nerve であり、inclusion 後は実際の零縮退と単体ホモトピックです。残るのは高次 Reedy matching fibration、非可逆局所 mapping nerve の接続と普遍比較です。
Reedy の基礎橋もコンパイル済みです。`Functor.IsIsofibration` は厳密な対象/同型 lift を記録し、一次元はその lift、二次元は群胚での消去、高次元は圏 nerve の horn 一意性で処理されます。`Functor.nerveMap_fibration` は群胚間 isofibration の nerve map が Kan fibration であることを証明します。
degree 1 の適用は文字通りの outer-zero 座標で完成しました。実際の `d₁,d₀` 面写像対 `degreeOneMatchingFunctor : Core(ComposableArrows C 1) ⟶ Core(ComposableArrows C 0) × Core(ComposableArrows C 0)` は厳密な isofibration で、その nerve map は Kan fibration、二つの投影は実際の外側面です。明示的な圏積極限同型と nerve の積保存同型で Mathlib の選択単体集合二項積へ輸送され、標準 matching map は厳密に `⟨d₁,d₀⟩` かつ Kan fibration です。`DegreeOneReedyCore` はこのデータを `SegalCompletenessCore` に組み込みます。degree 2 には三辺を独立に持つ `TriangleBoundary C` があり、境界が拡張可能であることと長辺が二短辺の合成であることが同値です。maximal-core restriction は厳密な isofibration、その nerve は Kan fibration で、`DegreeTwoMatchingCore` に一括されています。抽象 degree-2 Reedy matching 極限との比較と 3 次元以上が残ります。
任意の試験圏 `T` に対する度 2 の hom-wise 表現 `(T ⥤ TriangleBoundary C) ≃ TriangleBoundary (T ⥤ C)` も証明済みです。任意の単体空間の抽象境界 matching 図と実際の境界制限 cone も `∂Δ[n]` の要素圏から構成され、matching map は定義的に選択極限への universal lift です。
明示的三角境界 nerve から選択極限への canonical comparison cone と写像、および全 `fac` 方程もコンパイル済みです。明示的境界 map との合成は抽象 universal matching map に厳密に等しく、残るのは comparison の可逆性だけです。
三つの標準非退化面インデックスと射影は厳密に `δ₀,δ₁,δ₂` を復号し、comparison は三つすべてと可換です。
三つの標準頂点と六つの面–端点 incidence 射も明示化され、matching cone の自然性が抽象辺射影の端点整合性を証明します。
各 `TriangleBoundary C` はすべての面と縮退に自然な完全単体符号化 `∂Δ[2] ⟶ nerve C` も持ちます。
逆向きの `ofBoundaryNerveMap` decoder もコンパイル済みで、incidence 自然性により標準辺を共有頂点へ輸送します。三つの輸送辺等式と二つの完全な往復はすべて証明済みで、任意の非全射 `Δ[2]` 単体は標準余面を経由して分解されます。`boundaryNerveEquiv` は `TriangleBoundary C ≃ (∂Δ[2] ⟶ nerve C)` を与えます。
canonical comparison の各垂直次数での逆は `degreeTwoAbstractMatchingBoundaryMap`、`triangleBoundaryEquivalenceStringEquiv`、`degreeTwoBoundaryComparisonInverseApp` により明示化され、二つの逆律、次数ごとの全単射、`degreeTwoBoundaryAbstractMatchingIso` はすべて証明されて `DegreeTwoReedyCore` に封装済みです。残るのは degree 3 以上です。
任意次数の `abstractMatchingBoundaryMap`、全極限射影の保持、単射性もコンパイル済みで、universal matching map を圏 nerve の境界制限へ厳密に移します。`boundaryRestriction_injective` と `boundaryRestriction_surjective` が一意性と高次存在性を閉じるため、全 `n ≥ 3` matching map は同型かつ Kan fibration で、`HigherMatchingCore` に封装済みです。正次数 Reedy package は完成しました。
非可逆局所 mapping nerve 接続は `HigherCompleteSegalCore` により完了し、Rezk 対象頂点、完全局所 nerve、任意 2-セルの厳密復号、非可逆性保存、単体的水平合成を同一接口にまとめます。
自由逐次代数層も完了しました。分岐代数は圏をなし、木代数は始対象、形式合同は健全かつ絶対完全で、結合的単位的葉接ぎ木は高さ/予算 fold と劣加法界を持ちます。
モデル代数圏は選択有限積と笛卡尔対称モノイダル構造も持ち、積 fold は成分ごと、二モデル等号は厳密で、木項モデルと任意第二モデルの積は共同完全です。
二元木レベル並列プロトコルも明示的独立レーンとしてコンパイル済みです。確率成分は分解し、対称性は確率/コストを保存し、成分接ぎ木は厳密テンソル–逐次交換則と高さ/予算劣加法界を満たします。

未解決の中心は次です。

1. 異種ノードキャリア、グラフ変更、またはポリシー依存因果介入、資源制約付き意味プロファイルまたはより豊かな/無限タスク言語、エネルギー分解された熱操作 dilation などの内在的像特徴づけを証明する。固定 DAG soft/stochastic/hard 介入プログラム、有限コヒーレント量子 instrument tree、無制限の厳密有限意味価値プロファイル、任意指定の Gibbs 保存目標平衡の像・完全性は証明済みです。
2. 一般自由項圏–経路圏同値と証明済み有限二経路像を越えるモデル固有表現・保存性定理を証明する。
3. 一般経路忠実条件と証明済み有限経路分離菱形を越える拡張可能な相対または絶対完全性を証明する。
4. 既に自然同型な完全座標/native Duskin nerve と局所 mapping nerve を complete-Segal 2-space へ組み立て、外層 Segal/完全性整合と高次局所化の普遍性を証明する。

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

inverse/retained/retained、retained/retained/inverse、retained/inverse/retained、
forward/retained/inverse、retained/forward/inverse、forward/inverse/retained、
inverse/forward/retained、inverse/retained/forward、retained/inverse/forward、
forward/inverse/forward、そして対偶 inverse/forward/inverse を含む全十六端点列が
target・source・transport・all-arrow の各層でコンパイル済みです。端点と自由亜群の正規化により、
一般の非薄対象でも `generalLiftPseudofunctor` に束ねられます。
`generalLiftFactorization` と `generalLiftFactorsThrough` が任意の source 分解を与え、
`inclusion_isBicategoricalLocalization` が三つの普遍性フィールドをすべて満たします。
パラメータ化 walking 例は完成し、全資源過程双圏への一般化だけが後続課題です。

## 完成済みの通常局所化

内部亜群の恒等・骨格・制限 Yoneda は Mathlib `Functor.IsLocalization` を満たします。またモデル
双圏のホモトピー 1-圏には cost-reflecting class の Gabriel–Zisman 局所化があります。非可逆 marked
arrow は逆射が実際に追加されることを示し、非可逆モノイダル 2-セルは locally discrete target が
二次元情報を保持できない理由を示します。
`CostExactRezkComparison.comparison` は universe-balanced な通常コスト厳密局所化を Rezk 図の自然変換へ持ち上げ、各 marked arrow の外側 1-矢印頂点を対象の実際の同値矢印部分空間へ厳密に因子化します。非可逆 2-セルは別の完全局所 mapping nerves に残ります。
高次局所比較は異なる universe にも拡張済みです。`CostExactZigzagGlobalComparison.core` が外側 Rezk 写像と完全局所層を包装し、頂点・恒等・水平合成の接着律もコンパイル済みです。残るのは高次の大域互換性と Complete-Segal/Rezk 弱同値です。
`MarkedZigzag.Word`/`Cell` の関係閉包は水平 whiskering、interchange、五角形、双圏三角形、marked unit/counit の両随伴三角式を含みます。`InversionData.factorization` が双本質的分解を、`LocalExtension` が mate による強変換と modification の延長を与え、局所前合成は忠実・充満・本質的全射です。

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
