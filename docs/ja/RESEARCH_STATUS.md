# 研究状況

[English](../en/RESEARCH_STATUS.md) · [简体中文](../zh-CN/RESEARCH_STATUS.md) ·
[日本語](RESEARCH_STATUS.md) · [Esperanto](../eo/RESEARCH_STATUS.md)

これは簡潔な研究地図であり、定理台帳ではありません。正確な型、依存関係、ソース、仮定は
[形式化ブループリント](reference/BLUEPRINT.md)と[公理一覧](reference/AXIOMS.md)にあります。

## 状態語彙

- `DEFINED`：インターフェースまたは構成が存在する
- `STATEMENT_FORMALIZED`：定理の型は存在するが、証明済みとは主張しない
- `PROVED`：プロジェクト公理や証明穴なしで Lean が受理する
- `BLOCKED`：具体的な依存関係または API の不足を記録した
- `OPEN_RESEARCH`：命題または正しい定式化が研究途上にある

README とモデル行列は、実装されコンパイルされた内容だけを要約します。

## 実装済みの柱

### 資源感応的構文と意味論

逐次・対称モノイダルコアには、実行可能構文、構文コスト、解釈、明示的導出、健全性、項モデル、
相対完全性、モノイダル初期性があります。コスト関数と到達可能予算フィルトレーションには、
明示的仮定の下で往復則があります。

同じモノイダル言語を、ワイヤや生成元を変えずに順序付き加法資源写像に沿って押し出せます。
式変換は計算可能で可逆です。異種解釈は押し出しシグネチャの通常解釈と厳密に同値で、評価は
変換後の予算に従い、自由モデルは相対完全かつ変換コストを厳密に実現します。

最初の具体的なモデル横断スライスもコンパイルされます。同じ単位コスト Boolean flip シグネチャを、
厳密確率 NOT、Pauli-X 量子発展、有限因果機構、多次元資源計算、タスク相対意味情報実験、
Gibbs 保存熱過程として解釈します。六つの観測境界等式を一つのカーネル検査済み定理に束ねます。
計算は固有のベクトル資源を保持し、量子・熱の解析的観測量はこのスライスのゼロ抽象コストと
分離します。

第二の共通シグネチャは単一境界を越えて逐次合成を証明します。二つの型付き flip が、厳密確率
合成、Pauli-X 発展、正規化三ノード因果鎖、厳密な二ステップ二ゲート資源、可逆意味後処理、閉じた
Gibbs 保存熱プロトコルを通じて入力を復元します。

最初の共有対称モノイダルスライスもコンパイルされます。同じ `flip ⊗ flip` 式が、確率、完全有限
Kraus 量子モデル、二つの因果機構、厳密四座標計算、意味実験、Gibbs 保存熱過程で
独立に作用します。対応する具体モデルには検査済み対称モノイダル構造があります。モノイダル資源
量子インスタンスは任意の Kraus チャネルを含み、テンソル Pauli-X は任意の積密度行列へ成分ごとに作用します。
モノイダル資源変換は証明論的に保存的で、各異種解釈の強対称自由 lift と可縮な厳密延長型が証明済みです。
共通構文と六目標は全資源モデル双圏の対象としても束ねられ、六 lift は各ネイティブ資源写像を持つ
検査済み強組紐 1-セルになります。

この線形合成理論には最初の絶対完全性・表現結果もあります。正規化は各到達可能端点対の一意経路を
計算し、項モデルは薄く、各意味 hom 像は正規単元集合に一致し、資源変換は証明論的に保存的で、
六解釈すべてが等号を反映します。これは競合経路がない現在の構文に依存します。

最初の特徴的不可逆パイプラインもコンパイルされます。共通二座標 `expose ≫ erase` 構文が古典
定数消去、量子 reset、hard 因果機構置換、厳密計算資源、意味価値消失、厳密 Landauer 飽和を伴う
仕事補助熱消去を実現します。熱インターフェースは電池を明示し、無料閉消去を推論しません。

最初の非薄共通理論もコンパイルされます。四資源菱形は形式的に異なる二平行経路を保持し、分岐を
潰さず全式を正規化し、入力–出力像を厳密に二つの意味として表現し、経路分離が意味完全性を導く
ことを証明します。六つの具体解釈は独立したモデル固有証拠で経路を分離し、すべて等号を反映します。

この機構は菱形固有ではなく一般基盤へ抽出されました。任意型付き逐次シグネチャについて
`SequentialNormalForm` は生成元経路、導出 iff 経路等号、異種意味像＝経路像、経路忠実解釈の
完全性を証明し、商項モデルと型付き経路圏の明示的圏同値および自由コストの厳密保存も与えます。
`SequentialFree` と `ResourceChangingSequentialFree` は通常解釈と異種解釈の一意な厳密自由 lift、
および変換後コスト境界を証明し、両方の厳密延長型は可縮です。さらに通常・異種解釈空間全体を
自由源資源非増加関手・資源変更関手が分類します。六つの菱形モデルはこの異種 lift を具体化します。

### 厳密な有限確率と意思決定

正規化有理確率チャネルはテンソル、凸混合、複製、破棄を備えた圏を形成します。有限分布の
Kleisli 表現と Mathlib `Stoch` への忠実な有限離散ブリッジがコンパイルされます。意思決定層には
Blackwell 単調性、必要な非空隠れ状態境界付き有限逆定理、厳密分離証明書があります。厳密有限意味
境界では、全タスクでの非負意味価値が Blackwell 支配と同値であり、正準な無情報実験に対する全厳密
タスク価値の一致が Blackwell 同値と同値です。Boolean 零損失タスクは完全観測と無情報観測に同じ
一標量を割り当てるため、単一タスク価値が完全不変量でないことも証明済みです。

### 因果、計算、熱モデル

有限 DAG 因果モデルは正規化観測意味論と hard intervention を持ちます。任意の有限 hard-intervention プログラムは節点ごとの last-write-wins 部分代入へ計算可能に正規化され、実行は一回の正規介入とその確率状態に厳密一致します。基底機構が親代入に依らない Dirac 強制機構でないという明示条件の下、局所機構意味論はこの正規形に完全です。固定 DAG 拡張は任意の親代入依存 soft 機構置換を許し、stochastic/hard 介入を特殊例とします。正規化は last-write-wins 後に基底機構と等しい冗長書込みを削除し、この縮約形は最終モデル、厳密同時状態チャネル、局所機構意味論に対し表現/完全です。Boolean 証人は独立公平子ノードと randomize-then-restore が空プログラムへ正規化されることを検証します。全計算と `Option` 部分計算
は形式的ステップ、問い合わせ、記憶、ゲート数を追跡します。有限 Gibbs 保存モデルは明示的解析
仮定の下で、厳密有理操作を KL、自由エネルギー、相関、近似消去、Landauer 証人へ接続します。厳密操作境界では、任意に指定した源/目標平衡間で確率チャネルが一意な Gibbs 保存 lift を持つのは、前者を後者へ厳密に押し出す場合に限ります。依存正規形も外部指定の互換目標に対しこの判定と等号反映を持ちます。

### 有限量子チャネル

有限 Kraus 族は正値性とトレース保存の証明後にだけチャネル化されます。恒等、合成、テンソル、自然性と全整合律を備えた完全対称モノイダル構造、
トレース破棄、有限恒等拡大に対する完全正値性、忠実な古典脱位相化埋め込みがコンパイルされます。
普遍的量子複製は主張しません。
有限 instrument は総和がトレース保存となる完全正操作分岐族です。非負正規化結果確率、事後状態、
逐次・テンソル則、明示的古典記録 CPTP 表現を持ちます。コヒーレント plus 状態の計算基底測定は
厳密な 1/2・1/4 確率を検証し、`InstrumentSyntax` は一/二単位資源境界と正準自由 lift を与えます。
結果選択 Pauli-X フィードバックは記録確率を保存し、両事後状態と結果を忘れた総チャネルを `false` へリセットします。
依存 bind は次の instrument と結果型が現在結果に依存する多ラウンド instrument を支援します。結合確率は Born 連鎖則、嵌め込み bind は Sigma 木再ラベル付け結合律を満たし、三履歴例は `1/2、1/2、0` です。
`InstrumentTree` は有限適応木を第一級帰納構文にします。依存履歴は正規形、評価は厳密分岐表現を持ち、計算可能経路コストは構造木予算で有界です。
古典記録チャネルは有限 instrument 上で単射であり、明示的な履歴同値の下では、評価 instrument の等しさ、全再帰分岐写像の等しさ、記録チャネルの等しさが同値です。
Kraus 行スライスは逆向き像定理も与えます。`Outcome × residual-system` へのチャネルは、結果の非対角ブロックがすべて消える場合に限り一意な有限 instrument から生じ、同値に履歴再ラベル付け後の一段 instrument tree から生じます。

最初の六モデル共有ノイズ生成元もコンパイルされます。4 分の 1 crossover BSC が厳密確率、コヒーレンス保持 random-unitary 量子ノイズ、ノイズ因果、四資源ランダム化計算、意味情報、Gibbs 保存になり、一致、コヒーレンス分離、意味リスク/価値、並列資源、六自由 lift が証明済みです。

共有ノイズ境界は真正な適応木へ拡張されました。一般の固定深度二分木言語は完全履歴、正の有理
分岐表、厳密経路コスト、最悪時予算を計算し、記録確率チャネル表現の忠実性から観測完全性を
得ます。二段 quarter/half-flip 木は、確率、コヒーレント random-unitary 量子 instrument 木、
四ノード因果 DAG、資源付きランダム化計算、意味決定情報、Gibbs 保存熱過程として実現されます。
四分岐の厳密質量、六モデル表現、量子コヒーレンス分離、決定的履歴復号、Bayes リスク 0、
意味価値 `1/2`、完全性による木の分離がコンパイル済みです。

一般確率言語は可変深度の依存有限分岐にも拡張されました。各生成元は固有の有限結果型を持ち、
各結果は異なる形の継続木を選べます。依存 Sigma 履歴、高さ、厳密経路コスト、最悪時予算、記録表
表現、明示的履歴同値に沿う観測完全性がコンパイルされ、固定深度二分言語は保守的に埋め込まれます。
`Bool`/`Fin 3` 例は長さ一から三の五履歴、高さ `3`、予算 `4`、確率
`1/2、1/6、1/6、1/12、1/12` を計算します。

依存構文には自由代数意味論も加わりました。分岐代数と準同型は圏をなし、木代数は始対象、構造
fold は一意な解釈です。生成合同は全代数で健全で、木項モデルにより絶対完全です。逐次葉接ぎ木は
結合的単位的モノイドをなし、高さと予算は標準数値 fold で、接ぎ木に対して劣加法的です。例は葉数
`5`、接ぎ木高さ `6`、予算 `8` を計算します。

分岐モデル代数は笛卡尔対称モノイダル圏になりました。一点代数と点ごとの積は真の終対象/積普遍性を
満たし、結合子、単位子、組紐、コピー、破棄、全整合律がコンパイルされます。共通木の `A ⊗ B`
への fold は二つの fold の対に厳密一致し、等号は成分ごとで、木項モデルと任意第二モデルの積は
共同完全です。例の葉数/予算並列観測は `(5,4)` で、組紐が交換します。

木レベル独立並列プロトコルは二つの異種レーンを明示的に保持します。履歴と状態の対は有限、確率は
積で正規化され、各記録チャネル成分は二レーン成分の積に分解し、資源コストは加算されます。レーン
交換は確率とコストを保存します。成分ごとの葉接ぎ木は結合的単位的で、厳密テンソル–逐次交換則を
満たします。fair/biased 例は `25` 履歴、高さ `3`、予算 `8`、短履歴質量 `3/8`、二段予算 `16` を
計算し、並列観測完全性が fair/fair と fair/biased を分離します。

### 高次対象としてのモデル

資源添字付き対称モノイダル過程モデル、資源非増加強組紐モノイダル関手、モノイダル自然変換は
双圏を形成します。コスト厳密同値は数値反映を明示し、通常ホモトピー局所化と複数の walking
局所化例がコンパイルされます。

通常局所化は Rezk 外層にも接続されました。`CostExactRezkComparison.comparison` は universe-balanced な源ホモトピー圏とコスト厳密局所化の間に双単体図の自然変換を構成します。輸送された各 marked arrow は可逆となり、その外側 1-矢印頂点は対象の実際の同値矢印部分空間を厳密に経由します。これは通常局所化の外層比較であり、非可逆 2-セルは別の完全局所 mapping nerves に保持されます。

完全局所層の高次比較は異なる universe にも拡張されました。擬関手の単位制約と compositor 制約は、すべての単体次数で実際の nerve homotopy に持ち上げられ、それらを支える結合子および左右単位子方程も common-universe 局所 nerve の厳密な 1-単体等式になりました。`CostExactZigzagGlobalComparison.core` は外側 Rezk 写像と完全局所層を包装し、局所頂点、恒等、水平合成、結合子、左右単位子の厳密な外側/局所接着律を持ち、任意の可逆局所 2-セルを対応する外側等式へ復号します。復号された結合子貼り合わせは五角形律を、結合子/単位子貼り合わせは三角形律を明示的に満たします。残るのはこれらの証明の全次元単体的組立てと Complete-Segal/Rezk 弱同値定理です。

始域と実際の終域の外側 completeness 写像は、どちらも明示的な単体ホモトピー逆と両方向の逆律ホモトピーを持ちます。

正しい相対 Rezk 始域もコンパイル済みです。外側 `n` 次はすべての始域列を含み、垂直変換は成分ごとに cost-exact です。実際の局所化関手は、すべての内外単体次数でこれを終域 Rezk core へ自然に写し、表示された矢印頂点上で厳密に計算します。実際の局所 0-単体と任意の 2-セル辺の写像/復号も厳密で、可逆と限らない各 2-セルについて両相対外側端点と対象局所辺が一括されます。垂直合成可能な任意の 2-セル対は、対象局所 2-単体へ厳密に写され、二つの一骨格証明、完全な三角形、依存的合成対角線が一括されます。可逆とは限らない任意の二つの 2-セルの同時水平合成も compositor ホモトピーの両側で厳密に写され、水平合成された一骨格、二つの外側合成端点、可換な自然性正方形が一括されます。垂直合成可能な二段の水平 2-セル対については、始域と終域の interchange、両側の common-universe pair 2-単体の厳密な写像、二つの正方形を貼り合わせた可換長方形、全因子/合成局所証明も一括されます。実際の compositor ホモトピーは degree-two プリズムを三分割する三つの対象局所 3-単体も与え、十二面すべてが同定され、二つの外側面は正準 pair 2-単体へ厳密に簡約されます。この構成は全次数にも包装され、各水平積単体は添字付き対象プリズム単体を持ち、一つの大域 cost-exact core が全モデル三つ組について七つの端面/側面/共有面/退化法則族を記録します。最初の相対外側橋も厳密で、通常/relative 二矢印頂点は三面と二つの恒等退化を持ち、relative comparison はそれらを保存し、各 degree-two 局所プリズムの三つの水平 pair 頂点は外側頂点へ接着され、対象中央面は実際の写像済み局所合成から復号されます。任意外側列頂点は全単体写像に沿って厳密に制限され relative comparison に保存され、all-degree 局所プリズムの全始域頂点は完全な two-arrow glue を持つ始域 1-セル対へ復号されます。残るのは全プリズム面射影の接着と Dwyer–Kan/Rezk 弱同値です。

その実構成には可計算な表示構文があります。`MarkedZigzag.Word` は二分弱合成を使い、関係商は五角形・双圏三角形と marked unit/counit の両随伴三角式を含む `Presented.localizationBicategory` を形成します。`InversionData.lift` と `InversionData.factorization` は任意の marking 反転擬関手の持ち上げと随伴同値因子分解を与えます。`LocalExtension.extension` は形式逆射上で mate を用いて strong transformation を再帰的に延長し、modification も恒等・逆射・合成に沿って延長します。したがって前合成は忠実、充満、本質的全射であり、`CostExactZigzag.inclusion_isBicategoricalLocalization` が完全な高次局所化普遍性を証明します。

さらに、始域 pair の復号は各水平積単体に対する任意の単体圏制限の下で厳密に自然であり、各制限後の頂点には完全な two-arrow glue が再び与えられます。したがって、全次数の面と退化を一つの定理で統一的に扱えます。実際の対象プリズムの各面頂点は圏 nerve の面射影として文字通り与えられ、compositor の切替点の前後で `map(composite)` または `map(f) ≫ map(g)` に厳密に分類されます。両方の局所表示は同じ外側合成へ復号され、完全な two-arrow glue を持ちます。完全な局所面/退化 core は保持されるため、非可逆局所セルを relative outer maximal core に混入させません。始域で定義された marked-zigzag word/商 2-cell nerve は、各モデル対に明示的な relative mapping-space 表示を与えるようになりました。これは実際の対象局所 nerve と圏同値で、`NerveEquivalenceWitness` と明示的な単体ホモトピー逆を持ち、既存の local map は全次数で厳密にこの表示を経由し、forward word と任意の 2-cell に正確に作用します。外側ホモトピー関手も本質的全射です。未解決なのは、この表示のモデル非依存な derived/hammock mapping-space 特徴付け、受理可能な弱同値包装、および Dwyer–Kan/Rezk 定理です。

基礎となる商 mapping category は、具体的な対象に依存しない代数的普遍性も持つようになりました。words を対象へ、raw 2-cell を射へ写し、全関係・恒等・垂直合成を保存する任意の解釈は一意な整合 lift として関手へ下降し、すべての raw 代表元上で厳密に計算します。一般下降の依存は `Quot.sound` のみであり、未解決なのはこの代数的普遍性を derived/hammock ホモトピー特徴付けへ強化することです。

この普遍性は全次数の common-universe 圏 nerve にも持ち上がりました。任意の整合 lift は同じ正準 nerve map を誘導し、word 頂点、raw 2-cell 辺、任意 simplex は厳密に計算され、下降した解釈間の自然変換または自然同型は実際の一方向または双方向 `SSet.Homotopy` を与えます。独立した derived/hammock 構成との比較は未解決です。

`PresentedDwyerKanCore` は outer essential surjectivity と全 presented mapping-space 条件を一つの監査済み命題に統合します。そこには nerve 同値、明示的ホモトピー逆、代数的/単体的表示普遍性、厳密因子化、全次数の厳密作用が含まれます。`Presented` という限定は不可欠であり、独立した hammock 定理ではありません。

制限付きながら真に独立した右結合 linear hammock 対象モデルもできました。typed step 列は二分 words と相互変換・平坦化され、長さを厳密に保存し、同値な mapping category、nerve の明示的ホモトピー逆、実際の対象 local nerve への直接比較を与えます。`LinearHammockDwyerKanCore` はこれを outer essential surjectivity と統合します。古典的な任意グリッド hammock または他の受理された derived 構成との比較は未解決です。

任意高さの垂直 grid も明示化されました。`n`-grid は `n + 1` 行の linear hammocks、`n` 本の隣接商 2-cell 辺、全端点方程式を持ち、strict-Segal 再構成により linear hammock nerve の `n`-simplex と同値です。行、辺、復号、双方向 round trip は厳密に証明されています。固定形状の水平多列部分も形式化されました。同形の行は各共通列に一つの raw atomic 2-cell を持ち、幅と実行可能な水平 append は厳密で、商解釈は interchange により列ごとの恒等と垂直合成を保存し、任意高さの aligned grid は行と解釈済み辺を厳密に保つ genuine simplex を再構成します。基本的な前向き列 refinement も実行可能です。恒等列の挿入/削除、合成列の展開/縮約、任意の共通 prefix 下での move、推移合成、符号付き幅変化、商意味論での双方向 cancellation が証明されています。marked reverse 構造にも unit pair `f ; f⁻¹` と counit pair `f⁻¹ ; f` の実行可能な挿入/削除が加わり、符号付き幅 `±2`、厳密な意味同型、双方向 round trip、任意 prefix 安定性が証明されました。各 refinement は実行可能な逆と統一意味同型を持ちます。二本脚 common-refinement span は同値関係と行商を構成し、商等式は common-refinability と同値で、対象等式を仮定せず意味同型を与えます。商 mapping category/nerve、競合 move coherence、reduced-hammock 不変性、標準弱同値 packaging は未解決です。

異なる資源代数のモデルは順序付き加法準同型で比較できます。直列、並列、構造、予算則が再添字
付けされ、異種強モデル射は資源写像とともに合成します。これらは、資源代数とモデルを対象、
資源変換と強モデル射を 1-セル、資源変換の等号とモノイダル自然変換を 2-セルとする全双圏を
形成します。水平合成、交換則、結合子、単位子、五角形、三角形がコンパイル済みです。

全双圏は二層の単体意味論も持ちます。対象コアは Kan・strict-Segal nerve で、明示的に商をとった内部モデル同値類は対象恒等辺と厳密に同値です。各局所 hom 圏は全 1/2-セルを保持する strict-Segal mapping nerve を持ち、垂直合成は 2-単体、水平合成は交換則から単体写像になります。決定的 discard 2-セルは全モデル化と nerve 復号後も非可逆と証明されます。
大域の 2/3 次元 Duskin データも明示化されました。三角形は任意の合成比較 2-セルを保持し、四面体は六辺と四面セルを持ちます。境界は結合子修正四面体方程が成立する場合に限り一意な 3-単体を持ち、正準三重合成は実際の双圏結合子を長面に使います。
この構成は全次元の大域 Duskin 半単体 nerve へ拡張されました。各単体は全増加頂点/辺/三角/四項組を記録し、任意の厳密単調順序写像はデータを文字通り制限します。恒等・合成制限則が証明され、2/3 次元で明示的三角形/四面体を厳密に回復します。
縮退層も native に実装済みです。`n`-単体は局所離散有限順序 `[n]` から全資源モデル双圏への strictly unitary lax functor です。全単調順序写像が前合成で面/縮退を一様に与え、恒等/合成則は厳密です。最初の縮退は恒等辺を作り、lax 結合則は四面体方程を与え、自然変換が完全 nerve を座標半単体 nerve へ復号します。
逆方向には `Fin (n + 1)` と明示的に圏同値な構成子正規有限順序があり、`fromFin` と finite-to-normal lax core は擬逆を選択しません。恒等/厳密辺、比較セル、全 8 構成子パターンの異質四面体整合性、始域の単位子・恒等輸送・結合子がすべてコンパイル済みです。座標単体と native normal-lax 単体の完全構造上の両往復が証明され、次元ごとの同値を形成します。この同値で native 作用を輸送した座標 simplicial nerve は全ての面と縮退を持ち、native Duskin nerve と自然同型です。残るのは complete-Segal 2-space の組立てと高次局所化比較です。
complete-Segal 組立ての第一層もコンパイル済みです。総モデルのホモトピー圏の Rezk core 図は各外次数で有限列圏の maximal core を用いるため全垂直レベルが Kan で、外側対象空間は既存の対象 core と圏同値です。選択された Kan 同値矢印空間には `NerveEquivalenceWitness` があります。completeness 同値は定義的に透明な恒等矢印函子へ正規化され、旧前向函子との自然同型と selected core の実際の外側 1 次空間への inclusion もコンパイル済みです。その合成は実際の零縮退と明示的に自然同型で、同値・inclusion・縮退・比較は再利用可能な圏論的因子化として一括されています。新しい一般的 cylinder 構成は任意の自然変換を nerve 写像間の `SSet.Homotopy` へ持ち上げ、ここでも中介 completeness 写像と実際の零縮退の単体ホモトピーを証明します。さらに各水平行は垂直同値列の圏の通常 nerve と自然同型で、実際の外側 spine は全双次数で同値です。`SegalCompletenessCore` がこれらを垂直 Kan・completeness データと一括します。選択同値圏は実際の外側可逆矢印の充満部分圏とも明示的に圏同値で、直接 completeness 写像も圏同値の nerve であり、その inclusion は実際の零縮退と単体ホモトピックです。残るのは高次 Reedy matching fibration、非可逆局所 mapping nerve の接続、高次局所化比較です。

これらの圏同値で表示される completeness 写像はすべて `HomotopyEquivalenceWitness` を自動的に得ます。
Reedy 基盤には厳密な `Functor.IsIsofibration` lift、恒等/core inclusion インスタンス、順逆同型 lift 方程式が加わりました。全次元 horn 定理も完成し、二次元は群胚消去、高次元は圏 nerve horn 一意性で処理され、`Functor.nerveMap_fibration` が Kan fibration を与えます。
degree 1 matching は文字通りの outer-zero 座標でコンパイル済みです。`degreeOneMatchingFunctor` は `Core(ComposableArrows C 1)` から二つの `Core(ComposableArrows C 0)` への実際の `d₁,d₀` 面写像対です。端点共役により厳密な isofibration となり、その nerve map は Kan fibration で、二つの投影は実際の外側面に等しいことも証明済みです。明示的な圏積極限同型と nerve の積保存同型により Mathlib が選択する単体集合の二項積へ輸送され、標準 matching map は厳密に `⟨d₁,d₀⟩` で Kan fibration です。`DegreeOneReedyCore` がこれを `SegalCompletenessCore` に組み込みます。degree 2 には三辺を独立に記録する明示的な `TriangleBoundary C` 圏があります。境界が `ComposableArrows C 2` へ拡張できるのは長辺が二短辺の合成に等しい場合に限る、という厳密像表現定理を証明しました。maximal core 上の制限は厳密な isofibration、その nerve は Kan fibration で、`DegreeTwoMatchingCore` に一括されています。この境界 nerve と抽象 degree-2 Reedy matching 極限との同一視、および 3 次元以上が残ります。

さらに、任意の試験圏 `T` に対する hom-wise 表現 `(T ⥤ TriangleBoundary C) ≃ TriangleBoundary (T ⥤ C)` もコンパイル済みです。任意の単体空間に対する抽象 `simplicialSpaceBoundaryMatchingDiagram` と実際の境界制限 cone も `∂Δ[n]` の要素圏から構成され、matching map は定義的に選択極限への universal lift です。

明示的三角境界 nerve から選択抽象極限への canonical comparison cone と写像もコンパイル済みで、全 `fac` 方程が証明されています。明示的境界 map との合成は抽象 universal matching map に厳密に等しいため、二つの degree-2 matching map の整合性は完了し、残るのは comparison の可逆性だけです。

三つの標準非退化面インデックスと射影も明示化され、厳密に `δ₀,δ₁,δ₂` を復号し、comparison は三つすべてと可換です。

三つの標準頂点と六つの面–端点 incidence 射も明示化され、matching cone の自然性が抽象辺射影の端点整合性を証明します。

各 `TriangleBoundary C` はさらに完全な単体符号化 `∂Δ[2] ⟶ nerve C` を持ち、すべての面と縮退に自然です。

逆向きの `ofBoundaryNerveMap` decoder もコンパイル済みで、incidence 自然性により標準辺を共有頂点へ輸送します。三つの輸送辺等式と二つの完全な往復はすべて証明済みです。任意の非全射 `Δ[2]` 単体は標準余面を経由して分解され、`boundaryNerveEquiv` が厳密な表現 `TriangleBoundary C ≃ (∂Δ[2] ⟶ nerve C)` を与えます。

選択された抽象 degree-2 Reedy 極限との同型も完成しました。`degreeTwoAbstractMatchingBoundaryMap` が抽象 matching 単体を `nerve (EquivalenceString C k)` 内の完全境界へ組み立て、`triangleBoundaryEquivalenceStringEquiv` が三角境界と垂直同値列を交換し、`degreeTwoBoundaryComparisonInverseApp` が復号して maximal core へ持ち上げます。二つの逆律、次数ごとの全単射、`degreeTwoBoundaryAbstractMatchingIso` はすべて証明され、`DegreeTwoReedyCore` に封装済みです。残るのは degree 3 以上です。

任意次数の統一橋もコンパイル済みです。`abstractMatchingBoundaryMap` はすべての `n` で完全境界写像を組み立て、全極限射影を保持して単射であり、`abstractMatchingMap` を通常の圏 nerve の境界制限へ厳密に移します。`boundaryRestriction_injective` は全 `n ≥ 2` の一意性を証明し、`boundaryRestriction_surjective` は内 horn 充填と余次元二の復元により全 `n ≥ 3` の存在性を証明します。したがって全高次 matching map は単体集合同型かつ Kan fibration で、`HigherMatchingCore` に一括されます。正次数 Reedy matching package は完成しました。

上記の非可逆局所 mapping nerve 接続は `HigherCompleteSegalCore` により完了し、未完項目ではありません。同一構造が Rezk 対象頂点、完全局所 nerve、任意 2-セルの厳密復号、非可逆性保存、局所 strict-Segal/quasicategory/2-coskeletal 証拠、単体的水平合成を保持します。

### 限定的内部ユニバレント層

深い構文は内部恒等と構造同値を分離し、外部公理なしに解釈します。亜群、対象商、骨格、Yoneda
包絡、Kan 単体神経、プロジェクト固有の groupoidal complete-Segal インターフェースを満たす分類図が
コンパイルされています。

## 現在のフロンティア

目標は、計算可能・機械検証可能・ユニバレント・高次圏論的な資源制約付き情報過程理論を構成し、
古典確率、量子過程、因果モデル、計算、意味情報、熱力学を異なるモデルとして、証明済み表現定理・
完全性定理で接続することです。

可変資源代数上の最初の全高次圏には次が含まれます。

- 過程、並列、構造、証明付き予算則の順序付き加法再添字付け
- 資源変更関手、恒等資源互換性、合成、予算移送
- 再添字付け `ProcessModel` と合成可能な資源変換付き異種強組紐モデル射
- 固定資源変換ごとのモノイダル 2-セルと局所圏
- 全資源モデル、異種水平合成と whiskering、交換則、結合子、単位子、五角形、三角形
- Kan 対象同値コア、内部同値類–恒等辺の厳密対応、全局所 mapping nerve、垂直 2-単体、水平合成単体写像、保持された非可逆 2-セル
- 大域 Duskin 三角形/四面体と、結合子修正境界の一意 3-単体充填定理
- 全次元大域 Duskin 半単体 nerve、全順序埋め込みの厳密制限則、厳密低次元回復
- strictly unitary lax 有限順序図からなる native 完全 Duskin nerve、全縮退、恒等辺証拠、四面体整合、半単体 nerve への自然座標復号
- 逆座標表現用の構成子正規有限順序同値、全辺/比較正規化条款、全厳密四面体分岐
- 各モデル固有の資源代数へコストを変換できる共通構文、可逆式変換、厳密解釈表現、変換後自由
  モデル完全性
- 同一 Boolean flip シグネチャの六つのモデル固有解釈と、カーネル検査済みモデル横断一致定理
- 三インターフェース二段シグネチャと、カーネル検査済み六モデル逐次合成定理
- 共通対称モノイダル `flip ⊗ flip`、六モデル並列定理、厳密計算資源加算、全双圏 1-セルへ昇格した六つの正準異種自由 lift
- 線形理論の計算可能正規形、単元像表現、六解釈の絶対等号反映完全性
- expose–erase シグネチャと六モデルの消去・介入・意味損失・Landauer 支払定理
- 非薄菱形の厳密二経路像、分離完全性条件、六つの分離かつ完全な解釈
- 多生成元適応二分木の有限正履歴正規形、厳密経路予算、記録チャネル表現、観測完全性、六つの固有モデル実現
- 可変深度・生成元依存有限結果木、依存履歴、厳密上限予算、明示的履歴同値に沿う表現/完全性、保守的二分埋め込み
- 任意の有限正依存正規形に対する、確率、measurement–preparation 量子、タグ付き二節点因果、資源付きランダム計算、タスク文脈意味、誘導平衡熱過程の六モデル実現と等号反映完全性
- Blackwell 支配/同値に対する厳密有限意味順序と全タスク数値プロファイルの完全性、および実行可能な単一タスク不完全性証人
- Gibbs 保存チャネルの内在像定理と一意熱 lift、外部指定目標への依存正規形表現/完全性
- 固定 DAG soft/stochastic/hard 因果プログラムの計算可能な縮約正規形、厳密モデル/チャネル表現、等号反映完全性
- 依存分岐代数の圏、始木代数、一意 fold、絶対等式完全性、逐次接ぎ木モノイド、高さ/予算代数表現
- 分岐モデル代数の笛卡尔対称モノイダル圏、成分ごとの積 fold 表現、厳密同時等号、木項モデル共同完全性
- 二元木レベル独立並列プロトコルの厳密確率分解、レーン対称性、資源加算、共有境界接ぎ木、厳密交換則、並列観測完全性
- 任意型付き逐次シグネチャの自由項圏–経路圏同値、厳密コスト保存、経路忠実完全性
- 厳密延長型が可縮な通常・異種逐次初期性、解釈–自由源関手分類同値、六つの正準自由 lift とコスト境界
- `Fin 4 → Nat` 計算資源から `Nat` ステップへの実行可能射影と予算保存モデル 1-セル

次に必要な定理層は次です。

- 異種ノードキャリア、グラフ変更、またはポリシー依存因果介入、資源制約付き意味プロファイルまたはより豊かな/無限タスク言語、エネルギー分解された熱操作 dilation に対する拡張可能なモデル固有像特徴づけを構成する
- モデル固有の表現、保存性、完全性と、その後の真のモデル間比較を証明する
- 既に自然同型な完全座標/native Duskin nerve と相干ホモトピー付き局所 mapping nerve を大域 complete-Segal 2-space へ組み立て、全資源過程双圏のコスト厳密局所化を構成し、コンパイル済み高次局所 nerve 比較で両者を接続しつつ商代表選択を実行モデルへ流さない

パラメータ化 walking 局所化では、任意 lift の対象、1/2-セル、恒等、compositor、自然性、単位則、
前向き結合則に加え、inverse/retained/retained、retained/retained/inverse、
retained/inverse/retained、forward/retained/inverse、retained/forward/inverse、
forward/inverse/retained、inverse/forward/retained、inverse/retained/forward、retained/inverse/forward、forward/inverse/forward の完全な結合分岐がコンパイル済みです。
対偶の inverse/forward/inverse も target・source・transport・all-arrow の全層が完了し、
全十六端点列から一般の非薄対象に対する `generalLiftPseudofunctor` が構成済みです。
source 制限比較とその逆は随伴同値 `generalLiftFactorization` を成し、任意の標識を反転する
source 擬関手が completion を通して分解することも証明済みです。
forward/retained/inverse 分岐には direct-mate 輸送、源結合則、七端点輸送、分岐選択、
厳密な all-arrow oplax 結合則が含まれます。
`inclusion_isBicategoricalLocalization` は標識反転、本質的全射性、局所前合成同値をまとめ、
パラメータ化 walking 例の完全な双圏局所化を与えます。同じ三つの普遍性フィールドは、現在 `CostExactZigzag.inclusion_isBicategoricalLocalization` によって全資源過程表示にも証明されています。

`TotalModelWalkingLocalization` はこの普遍性を、六つの名前付きモデル対象を含む異種
`ResourceModel` 双圏へ特殊化します。ただし標識反転の前提は維持され、共有構文から出る六つの
解釈 one-cell を随伴同値とは主張しません。

## 明示的に未解決または範囲外

- 一般可測空間の因果モデルと do-calculus 完全性
- 形式ステップ数と実時間・ハードウェアコストの同一視
- 実行可能有限確率コアにおける無理実数確率
- 普遍的量子複製
- Lean 型に対する外部ユニバレンス
- 完成した弱同値・Quillen モデル API による Mathlib 標準 complete-Segal 空間
- 資源過程双圏の完全な Dwyer–Kan、単体的、Rezk、または双圏的局所化

未証明命題は Lean の公理ではなく[予想台帳](reference/CONJECTURES.md)へ置きます。

## 主張の確認場所

- モデル能力：[モデル能力行列](reference/MODEL_MATRIX.md)
- 定理型と依存関係：[形式化ブループリント](reference/BLUEPRINT.md)
- カーネル仮定：[公理一覧](reference/AXIOMS.md)
- 未解決研究：[予想台帳](reference/CONJECTURES.md)
- 実行動作：`Ript/Examples/` と `scripts/check-examples.sh`
- マージ準備：`./scripts/quality-gate.sh`
