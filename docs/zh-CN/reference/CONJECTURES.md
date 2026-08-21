# 猜想与未证明研究陈述

[English](../../en/reference/CONJECTURES.md) · [简体中文](CONJECTURES.md) ·
[日本語](../../ja/reference/CONJECTURES.md) · [Esperanto](../../eo/reference/CONJECTURES.md)

本登记册用于记录“陈述已经成为可编译 Lean 命题，但证明尚未由内核检查”的条目。活跃条目必须
带 `FORMALIZED_BUT_UNPROVED` 标记，并给出声明名。根目录
[`CONJECTURES.md`](../../../CONJECTURES.md)是机器规范记录。

## 当前登记

目前没有活跃的 `FORMALIZED_BUT_UNPROVED` 命题。这不意味着研究计划已经完成；尚未定式化为精确
Lean 命题的构造工作不能被静默当作假设或公理。

## 总研究目标与开放定理族

Ript 的目标是统一资源受限信息过程，使经典概率、量子、因果、计算、语义信息和热力学成为不同
模型，并证明表示与完备性定理。已编译的总资源模型双范畴允许不同资源代数之间的异质强辫态射和
单子 2-胞腔；公共单子语法也可以沿资源映射推前成本，具有可逆表达式翻译、解释表示等价和精确
自由模型预算。

第一个字面共享语法切片已经编译：一个布尔翻转生成元分别由精确概率、Pauli-X 量子、有限因果、
多维计算、任务语义和 Gibbs 保持热模型实现，六个可观察等式由 `sixModelFlipAgreement` 封装。

三接口两翻转的组合扩展也已证明，六类模型的复合律由 `sixModelCompositionAgreement` 封装。

对称单子扩展现在还把同一个 `flip ⊗ flip` 表达式解释到六类模型，证明独立并行行为与精确计算资源
相加，并给出六个规范强对称资源变换自由提升。单子推导翻译在证明论上保守，每个异质单子解释的
严格延拓类型可收缩。量子目标现为完整有限 Kraus 范畴：基等价给出带全部协调律的对称单子结构，
张量 Pauli-X 对任意乘积密度矩阵逐分量作用。
有限量子仪器现已作为归一化完全正分支族实现，具有后验态、串行与张量律、经典记录 CPTP 表示和按结果选择的保迹反馈；
相干测量例使用经典结果把两个后验都纠正到同一基态，并接入资源感知自由语法。
依赖 bind 允许后续仪器及其结果类型依赖当前结果，具有 Born 链式法则和 Sigma 树重结合结合律；三历史例已接入资源语法。
第一类归纳 `InstrumentTree` 现给出规范依赖历史、精确历史分支表示、有限归纳和可计算路径/树预算。
经典记录信道对有限仪器单射；沿显式历史等价，树求值相等、全部递归分支映射相等与记录信道相等现已证明等价。
Kraus 行切片还证明块对角经典结果信道恰好具有唯一仪器原像，并在历史重标记下由单步 instrument tree 实现。
单一四分之一交叉噪声生成元也已由六模型共享：量子实现为随机单位且在相干输入上与测量–制备可区分；随机化计算保留四资源，语义风险/价值精确。
对象宇宙提升还把公共语法与包含完整 Kraus 过程模型的六个目标封装到总资源模型双范畴中，使六种实现成为带已检查资源映射的
强辫 1-胞腔。

独立的 `expose ≫ erase` 语法现在还通过 `sixModelErasureAgreement` 连接经典擦除、量子 reset、
因果干预、计算、语义价值损失和电池支付的 Landauer 饱和。
有限硬干预程序现可计算地正规化为 last-write-wins 部分赋值，执行等于一次规范干预；在基底机制不退化为恒定 Dirac 强制机制时，局部机制语义对规范形完备。

线性比特理论的表示与完备性不再完全开放：六解释的规范路径精确像与等式反射已经证明；向非薄语言
的首个推广也已证明：有限菱形具有精确双路径像，并在独立路径分离证据下获得六模型完备性。可扩展
自由路径正规化、项范畴–路径范畴显式等价、精确成本保持、路径像表示和路径忠实完备性现已对任意
有类型顺序签名成立。普通与异质解释空间已分别由自由源资源单调函子和资源变换函子分类，严格延拓空间均可收缩；六个菱形模型已验证生成元一致和翻译成本界。仍
开放的是更丰富操作语言中可扩展的逐模型路径忠实性与像刻画。
自适应噪声的第二种推广也已编译：任意定深二叉树具有可执行正历史规范形、精确成本、记录信道表示和观察完备性；一个两层两生成元树具有六个原生模型实现与统一表示定理。
该边界又已推广到生成元依赖任意有限结果与变深分支：依赖 Sigma 历史、有限上确界预算、沿显式历史等价的精确记录表表示/观察完备性，以及定深二叉语言的保守嵌入均已编译。
每个有限正依赖规范形现也有六模型通用实现；概率、测量–制备量子、固定资源随机计算、结构化语义实验和热信道均反射规范形等式，带全支撑先验的双节点因果联合分布也具有该性质。
精确有限语义数值边界也已刻画：全体任务的非负语义价值等价于 Blackwell 支配；相对于规范无信息实验的全部精确任务价值相等，当且仅当两个实验 Blackwell 等价。布尔反例证明单个任务标量不是完备不变量。
热过程遗忘映射的内在像也已刻画：给定源/目标平衡态，一个有限随机通道存在唯一 Gibbs 保持提升，当且仅当它把源平衡态严格推到目标平衡态。该定理已专门化到任意依赖规范形与外部给定目标平衡态。
固定 DAG 因果边界现包含任意父赋值相关的软机制替换，随机干预与 Dirac 硬干预为其特例。有限程序先做 last-write-wins，再可计算地删除与基底机制等同的冗余写入；约化规范形对模型、信道和局部机制语义均具有表示/完备性。
总资源模型双范畴现具有双层单纯桥：Kan 对象核中的内部模型等价类与恒等边精确对应；每对总模型的完整局部映射神经保留全部 1/2-胞腔，垂直复合为 2-单形，水平复合为单纯映射。不可逆丢弃 2-胞腔在总模型解码后仍不可逆。
全局 2/3 维 Duskin 数据也已显式化：三角形保留任意复合比较 2-胞腔；四面体边界存在唯一 3-单形，当且仅当结合子修正的四面体协调方程成立。
这些数据现已推广到所有维数，形成真正的全局半单纯 Duskin 神经：每个严格保序嵌入都通过限制给出严格面映射，2/3 维分别精确恢复上述三角形和四面体数据。
退化边界现也已由原生完整 Duskin 神经闭合：`n`-单形是从局部离散有限序 `[n]` 到总资源模型双范畴的严格保单位 lax 函子。每个保序序数映射（包括退化）都通过正规 lax 预复合作用，恒等与复合律严格成立。首个退化复制顶点并产生恒等 1-胞腔，lax 结合律正是结合子修正的四面体方程。完整神经限制到面映射后，还有自然的坐标解码变换到上述半单纯神经。
逆向表示现已建立构造子正规基础：仅含恒等/严格箭头构造子的 `Ordinal n` 与 `Fin (n + 1)` 薄范畴显式等价，`fromFin` 与 finite-to-normal lax 核心无需选择伪逆。边、比较、八分支四面体相干及源端运输均已编译。坐标与原生 normal-lax 单形的两条完整结构回转组成逐维等价；运输后的坐标神经含全部面与退化，并与原生 Duskin 神经对全部序数映射自然同构。仅余 complete-Segal 2-空间组装及其高阶局部化比较。
该组装的第一层现已编译：总模型同伦范畴的 Rezk core 图具有逐层 Kan 性、到既有对象 core 的范畴等价，以及选定 Kan 等价箭头空间上的 categorical completeness witness。透明恒等箭头函子、与旧前向函子的自然同构及 selected core inclusion 也已编译；该复合显式自然同构于真实零退化，并连同等价、inclusion 与退化封装为机器可消费的范畴因子化。新的通用圆柱构造证明每个自然变换都诱导 nerve 映射间的 `SSet.Homotopy`，因而这里的中介 completeness 映射已与真实零退化单纯同伦。每条横向行现又自然同构于纵向等价串范畴的普通 nerve，所以真实外层 spine 在每个双次数都是等价；这些字段共同封装为 `SegalCompletenessCore`。选定等价范畴现还与真实外层可逆箭头的满子范畴显式等价，直接落入该真实子空间的 completeness 映射仍是范畴等价的 nerve，且经 inclusion 后与真实零退化单纯同伦。尚待的是高阶 Reedy matching 纤维化、非可逆局部 mapping nerve 接入与泛比较。
Reedy 的底层桥也已编译：`Functor.IsIsofibration` 记录严格对象/同构提升；一维使用该提升，二维使用群胚消去，高维使用范畴 nerve horn 唯一性，最终 `Functor.nerveMap_fibration` 证明群胚间 isofibration 的 nerve map 是 Kan fibration。
degree 1 的应用现已在字面 outer-zero 坐标中完成：真实 `d₁,d₀` 面映射对 `degreeOneMatchingFunctor : Core(ComposableArrows C 1) ⟶ Core(ComposableArrows C 0) × Core(ComposableArrows C 0)` 是严格 isofibration，其 nerve map 为 Kan fibration；两个投影等于真实外向面。显式范畴积极限同构与 nerve 保积同构进一步把它运输到 Mathlib 选定的单纯集合二元积；标准 matching map 严格等于 `⟨d₁,d₀⟩` 且为 Kan fibration。`DegreeOneReedyCore` 已把这些事实接入 `SegalCompletenessCore`。degree 2 现有独立保存三条边的 `TriangleBoundary C`；边界可扩张当且仅当长边等于两短边复合。其 maximal-core restriction 是严格 isofibration，nerve 为 Kan fibration，并封装为 `DegreeTwoMatchingCore`。仍需与抽象 degree-2 Reedy matching 极限比较并构造三维以上 matching 范畴。
度 2 还具有对任意测试范畴 `T` 的 hom-wise 表示 `(T ⥤ TriangleBoundary C) ≃ TriangleBoundary (T ⥤ C)`。任意单纯空间的抽象边界匹配图和真实边界限制锥也已由 `∂Δ[n]` 的元素范畴构造；matching map 按定义就是进入选定极限的 universal lift。
显式三角边界 nerve 到选定极限的 canonical comparison cone 与映射、以及所有 `fac` 方程均已编译；与显式边界 map 的复合严格等于抽象 universal matching map，因此仅余 comparison 的可逆性。
三个规范非退化面索引及投影严格解码为 `δ₀,δ₁,δ₂`，且 comparison 与三者均交换。
三个规范顶点与六条面–端点入射态射也已显式构造；匹配锥自然性证明抽象边投影的端点兼容。
每个 `TriangleBoundary C` 现还具有对全部面与退化自然的完整单纯编码 `∂Δ[2] ⟶ nerve C`。
反向 `ofBoundaryNerveMap` 解码器也已编译；它利用入射自然性把规范边运输到共享顶点。三条运输边等式及两个完整回转均已证明，任意非满射 `Δ[2]` 单形都分解经过规范余面，`boundaryNerveEquiv` 给出 `TriangleBoundary C ≃ (∂Δ[2] ⟶ nerve C)`。
canonical comparison 的逐纵向次数逆由 `degreeTwoAbstractMatchingBoundaryMap`、`triangleBoundaryEquivalenceStringEquiv` 与 `degreeTwoBoundaryComparisonInverseApp` 显式构造；两个逆律、逐次双射与 `degreeTwoBoundaryAbstractMatchingIso` 均已证明并由 `DegreeTwoReedyCore` 封装。仅余 degree 3 及以上 matching。
任意次数的 `abstractMatchingBoundaryMap`、全部极限投影保持及单射性也已编译；它把 universal matching map 严格化为范畴 nerve 边界限制。`boundaryRestriction_injective` 与 `boundaryRestriction_surjective` 分别闭合唯一性和高维存在性，故所有 `n ≥ 3` matching map 均为同构与 Kan fibration，并由 `HigherMatchingCore` 封装。正次数 Reedy 包已完整。
非可逆局部 mapping nerve 接入现已由 `HigherCompleteSegalCore` 完成：它把 Rezk 对象顶点、完整局部 nerve、任意 2-胞腔精确解码、非可逆性保持及单纯横向复合封装在同一接口中。
自由顺序代数层也已完成：分支代数形成范畴，树代数初始，形式同余健全且绝对完备，结合有单位的叶嫁接具有高度/预算 fold 与次可加界。
模型代数范畴还具有选定有限积和笛卡尔对称单子结构；乘积 fold 逐分量，双模型相等精确，树项模型与任意第二模型的乘积联合完备。
二元树级并行协议也已编译为显式独立通道；随机条目分解，对称保持概率/成本，逐通道嫁接满足严格张量–顺序交换律和高度/预算次可加界。

仍开放的核心族是：

1. 在更丰富的逐模型语言中建立内在像成员刻画：异质节点载体、改变图结构或策略依赖的因果干预、资源受限语义剖面或更丰富/无限任务语言、能量分辨的热操作膨胀及其比较定理；固定 DAG 软/随机/硬干预程序、有限相干量子 instrument tree、无资源上界的精确有限语义价值剖面与任意给定 Gibbs 保持目标平衡态现已有像/完备性定理；
2. 超出通用自由项范畴–路径范畴等价与已证明有限双路径像的逐模型表示与保守性定理；
3. 超出通用路径忠实准则与已证明有限路径分离菱形的可扩展相对或绝对完备性；
4. 把已自然同构的完整坐标/原生 Duskin 神经与局部映射神经组装为 complete-Segal 2-空间，并证明其外层 Segal/完备性协调与高阶局部化泛性质。

这些目标必须先细化为精确 Lean 类型，才能进入 `FORMALIZED_BUT_UNPROVED` 登记。

## 分类图边界

已证明的分类图结果包括：

- 整个外图与 `n ↦ Map(Δ[n], N(M.Object))` 的自然同构；
- `Map(∂Δ[n], N(M.Object))` 是真正的边界匹配极限；
- 边界限制等于泛极限提升，所有匹配映射都是纤维化；
- 每个水平行是群胚的 Kan 神经，具有严格外 Segal 数据；
- 实际完备性映射具有 `SSet.NerveEquivalenceWitness`；
- 上述数据封装为 `SSet.GroupoidalCompleteSegal`。

固定 Mathlib 版本尚无单纯集合弱等价类和完整 Quillen 模型结构，因此还不能表述 Mathlib 原生标准
complete-Segal 实例。这是基础设施边界，不是隐藏的假设。

## 双范畴局部化边界

精确目标由 `Bicategory.MorphismProperty.IsBicategoricalLocalization` 给出：标记 1-态射变成伴随等价；
每个逆化伪函子具有双本质因子分解；对强变换与 modification 的每个局部范畴，预复合是等价。
Ript 的特化为 `IsCostExactBicategoricalLocalization`。

已完成：

- 恒等伪函子满足泛性质，当且仅当所有标记箭头本已是伴随等价；
- 零成本离散嵌入不是伴随等价，所以非平凡情形必须添加逆元；
- `Fin 2` 行走箭头的自由群胚局部化显式给出反向箭头和两条逆律；
- 参数化乘积构造只局部化行走坐标，同时忠实保留源 2-胞腔和一个非可逆布尔丢弃 2-胞腔；
- 保留坐标族、群胚值局部化族、可分混合族及其伴随等价闭包均可因子分解；
- 自由群胚坐标具有端点正规形、thinness，并等价于 `Fin 2` 上余离散群胚；
- 强变换和 modification 可以跨自由逆元提升，局部预复合函子为等价；
- 对任意可能非可分的逆化源伪函子，目标对象、1/2-态射的 `PrelaxFunctor` 作用、恒等比较和全部八种
  端点正规化二元合成比较已经编译；
- 合成比较具有左右自然性；任意箭头的左右单位律、全前向三元结合律，以及第一个真正含逆元的
  `1→0→0→0` 结合律分支已经编译。

包括对偶逆/前向/逆在内的全部十六种端点结合序列现已通过 target、source、transport 与
all-arrow 层，并经端点/自由群胚规范化封装为不要求局部薄性的 `generalLiftPseudofunctor`；
它在包含箭头上恢复源作用。`generalLiftFactorization` 已给出源限制伴随等价，
`generalLiftFactorsThrough` 已覆盖任意非可分逆化源，
`inclusion_isBicategoricalLocalization` 因而填满全部三个泛性质字段。参数化行走例的双范畴局部化
现已完成；把构造推广到完整资源过程双范畴仍然开放。

## 已完成的普通局部化

- 内部接口群胚的恒等、骨架和受限 Yoneda 函子满足 Mathlib `Functor.IsLocalization`；源本已是群胚，
  不会逆化新的非可逆过程。
- 模型双范畴的同伦 1-范畴在成本反射类上具有 Gabriel–Zisman 局部化；代表元标记对可逆 2-胞腔饱和，
  `Pith` 的规范伪函子把标记箭头送到同构。
- 具体非可逆标记箭头证明该普通局部化确实添加逆元；另一个非可逆单子 2-胞腔说明局部离散目标无法
  保留完整二维信息。
- `CostExactRezkComparison.comparison` 把 universe-balanced 普通成本精确局部化提升为 Rezk 图自然变换；每个标记箭头的外层一阶顶点严格因子化经过目标实际等价箭头子空间。非可逆 2-胞腔仍留在独立完整局部 mapping nerves 中。
- 高阶局部比较现已扩展到不同 universe。`CostExactZigzagGlobalComparison.core` 由同一高阶局部化的同伦范畴函子构造外层 Rezk 映射，并打包外层与局部层；顶点、恒等与水平复合的粘合律已编译。现剩高阶全局相容性及 Complete-Segal/Rezk 弱等价。
- `MarkedZigzag.Word`/`Cell` 的关系闭包包含标记伴随三角式；`InversionData.factorization`、`LocalExtension` 和 `CostExactZigzag.inclusion_isBicategoricalLocalization` 已分别证明双本质分解、强变换/modification 延拓与完整双范畴局部化泛性质。

## 最近完成：有限随机 Blackwell 逆定理

`Ript.Models.Decision.RationalSeparation.finiteBlackwellShermanStein` 已由内核检查。对任意非空有限隐
状态，所有精确有限决策问题上的风险序推出精确随机混淆。非空条件由 `EmptyParameterBoundary`
反例证明必要。

证明桥梁包括：随机混淆的有理确定性单纯形表示；有理点从实凸包反射到有理凸包；Hahn–Banach
严格分离和有理稠密近似；把有符号分离子通过行平移与均匀先验转成非负有理决策证书。公理足迹为
`[propext, Classical.choice, Quot.sound]`，不声称提取了线性规划求解器。

## 算法边界

对独立指定的有限实能谱，项目证明：精确有理 Gibbs 概率存在，当且仅当相对某参考态的所有
Boltzmann 比均为正有理数。项目提供可执行有理权重示例和 `sqrt 2` 障碍证明，但不提供判定任意实
指数表达式相等的一般算法；该边界没有被登记为未证明 Lean 命题。
