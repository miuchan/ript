# 研究状态

[English](../en/RESEARCH_STATUS.md) · [简体中文](RESEARCH_STATUS.md) ·
[日本語](../ja/RESEARCH_STATUS.md) · [Esperanto](../eo/RESEARCH_STATUS.md)

本页是简明研究地图，不是定理台账。精确定理类型、依赖、源文件与假设见
[形式化蓝图](reference/BLUEPRINT.md)和[公理清单](reference/AXIOMS.md)。

## 状态词汇

蓝图只使用以下正式状态：

- `DEFINED`：接口或构造已经存在；
- `STATEMENT_FORMALIZED`：定理类型已形式化，但不声称已有证明；
- `PROVED`：Lean 在没有项目公理或占位符的情况下接受证明；
- `BLOCKED`：记录了明确的依赖或 API 缺口；
- `OPEN_RESEARCH`：陈述或正确表述仍属于研究问题。

README 和模型矩阵只概述已经实现并编译的工作。

## 已实现支柱

### 资源敏感语法与语义

顺序与对称单子核心包含可执行语法、语法成本、解释、显式推导、健全性、项模型、相对完备性和
单子初始性。成本函数与可达预算过滤在显式假设下具有已证明的往返定律。

同一单子语言现在可以沿有序加法资源映射推前，而不改变线型或生成元。表达式翻译可计算且可逆；
异质解释精确表示为推前签名的普通解释；求值服从翻译后的预算；推前自由模型具有相对完备性和
精确翻译成本。

第一个具体跨模型切片也已编译：同一个单位成本布尔翻转签名分别解释为精确概率非门、Pauli-X 量子
演化、有限因果机制、多维资源计算、任务相对语义信息实验和 Gibbs 保持热过程。六个可观察边界等式
由一个内核检查定理统一封装。计算模型保留原生向量资源；量子与热解析观察量则和该切片采用的零抽象
成本保持分离。

第二个共享签名已经从单步边界推进到真正串行复合：两个有类型翻转分别通过精确随机复合、Pauli-X
演化、归一化三节点因果链、精确两步两门计算资源、可逆语义后处理和闭合 Gibbs 保持热协议恢复输入。

首个共享对称单子切片也已编译。同一个 `flip ⊗ flip` 表达式在概率、完整有限 Kraus 量子模型、两个
因果机制、精确四坐标计算、语义实验和 Gibbs 保持热过程中独立作用。相应具体模型现在具有已检查
的对称单子结构；量子实例涵盖任意 Kraus 通道，张量 Pauli-X 对任意乘积密度矩阵逐分量作用。单子资源翻译在证明论上保守，每个异质单子解释都有直接的强对称自由提升，其严格
延拓类型可收缩。
公共语法与六个目标还被封装为总资源模型双范畴对象；六个提升成为携带各自原生资源映射的已检查强辫
1-胞腔。

该线性组合理论现在具有首批绝对完备性与表示结果：正规化计算每个可达端点对的唯一路径，项模型为
薄范畴，每个语义 hom 像精确等于规范单元素集合，资源翻译在证明论上保守，六个解释全部反射等式。
这些定理依赖当前语法没有竞争路径。

首个特征性不可逆管线也已编译。共享双坐标 `expose ≫ erase` 语法实现经典常量擦除、量子 reset、
硬因果机制替换、精确计算资源、语义价值销毁，以及带精确 Landauer 饱和的功辅助热擦除。热接口
显式包含电池，不会推断免费闭合擦除。

首个非薄公共理论也已编译。四资源菱形保留两条形式不同的平行路径，在不合并分支的情况下正规化
全部表达式，把输入–输出像精确表示为两个语义，并证明路径分离蕴含语义完备性。六个具体解释都用
独立模型证据满足路径分离，因此全部反射等式。

该机制现已从菱形推广为通用基础。对任意有类型顺序签名，`SequentialNormalForm` 计算生成元路径，
证明推导等价于路径相等，把每个异质语义像表示为路径像，并证明所有路径忠实解释完备；六个菱形
模型都满足这一通用接口。它还把 hom 等价提升为商项模型与类型化路径范畴的显式范畴等价，并精确
保持自由成本。
`SequentialFree` 与 `ResourceChangingSequentialFree` 分别证明普通解释及异质解释的唯一严格自由提升，
并保留翻译后的成本界；两类严格延拓空间均可收缩。整个普通/异质解释空间分别由自由源资源单调函子/
资源变换函子分类，六个菱形模型都已实例化这种异质自由提升。

### 精确有限概率与决策

归一化有理随机通道形成带张量、凸混合、复制和丢弃的范畴。有限分布 Kleisli 表示以及到
Mathlib `Stoch` 的忠实有限离散桥梁已经编译。决策层包含 Blackwell 前向单调性、具有必要非空
隐状态边界的有限逆定理，以及精确分离证书。在精确有限语义边界上，全体任务的非负语义价值等价于
Blackwell 支配；相对于规范无信息实验的全部精确任务价值相等，当且仅当两个实验 Blackwell 等价。
布尔零损失任务把完美实验与无信息实验映到同一个标量，证明单个任务价值不是完备不变量。

### 因果、计算与热模型

有限 DAG 因果模型具有归一化观测语义与硬干预。任意有限硬干预程序可计算地正规化为逐节点 last-write-wins 部分赋值；执行严格等于一次规范干预及其随机状态。在原机制并非恒定 Dirac 强制机制的明确条件下，局部机制语义对该规范形完备。固定 DAG 扩展现允许任意父赋值相关的软机制替换，随机干预与硬干预是特例。规范化先 last-write-wins，再删除与基底机制相同的冗余写入；结果对最终模型、精确联合状态信道和局部机制语义均具有表示/完备性，不再需要额外可识别前提。布尔见证产生独立公平子节点，并证明“随机化后恢复”正规化为空程序。全计算和 `Option` 偏计算模型跟踪形式步数、
查询、存储和门计数。有限 Gibbs 保持模型在明确解析假设下把精确有理操作连接到 KL、自由能、
相关、近似擦除与显式 Landauer 见证。在精确操作边界上，一个随机通道在任意给定源/目标平衡态之间
具有唯一 Gibbs 保持提升，当且仅当它把前者严格推到后者。依赖规范形继承此外部兼容目标判据及等式反射。

### 有限量子通道

有限 Kraus 族只有在正性与保迹性证明后才封装为通道。恒等、复合、张量、带自然性及全部协调律的完整对称单子结构、迹丢弃、有限放大下的
完全正性，以及忠实经典退相干嵌入均已编译；项目不声称存在通用量子复制操作。
有限仪器是总和保迹的完全正操作分支族，具有非负归一化结果概率、后验态、串行/张量律和显式经典
记录 CPTP 表示。相干 plus 态的计算基测量验证精确半/四分之一概率；`InstrumentSyntax` 给出一/二
单位资源界和规范自由提升。
按结果选择的 Pauli-X 反馈保留记录概率，并把两个后验态与忘记结果的总通道都重置为 `false`。
依赖 bind 现支持后续仪器和结果类型依赖当前结果的多轮仪器；联合概率遵循 Born 链式法则，嵌套 bind 在 Sigma 树重标记下结合，三历史例概率为 `1/2、1/2、0`。
`InstrumentTree` 使有限自适应树成为第一类归纳语法：依赖历史是规范形，求值具有精确分支表示，可计算路径成本受结构树预算界定。
经典记录信道现已证明对有限仪器单射；对任意依赖树，给定显式历史等价后，求值仪器相等、全部递归分支映射相等与记录信道相等三者等价。
Kraus 行切片进一步给出反向像定理：输出到 `Outcome × residual-system` 的信道当且仅当所有非对角结果块消失时，来自唯一有限仪器；等价地，它在历史重标记下来自一棵单步 instrument tree。

首个六模型共享噪声生成元已编译。四分之一交叉 BSC 分别成为精确概率、保留相干的随机单位量子噪声、含噪因果机制、四资源随机化计算、任务语义信息和 Gibbs 保持热过程；一致性、相干区分、语义风险/价值、并行资源和六自由提升均已证明。

共享噪声边界现已扩展为真正的自适应树。通用定深二叉语言可计算完整历史、严格正的有理分支表、
精确路径成本和最坏情形预算；记录随机信道表示是忠实的，因此得到观察完备性定理。一个两层
quarter/half-flip 树分别实现为概率、保留相干的随机酉量子仪器树、四节点因果 DAG、带资源随机化
计算、语义决策信息和 Gibbs 保持热过程。四个精确分支质量、六模型表示、量子相干区分、确定性
历史解码、零 Bayes 风险、语义价值 `1/2` 以及基于完备性的树区分均已编译。

通用随机语言现进一步支持变深的依赖有限分支。每个生成元拥有自己的有限结果类型，每个结果可选择
不同形状的后续树；依赖 Sigma 历史、高度、精确路径成本、最坏预算、记录表表示及沿显式历史等价的
观察完备性均已编译。定深二叉语言保守嵌入其中。`Bool`/`Fin 3` 实例计算出长度分别为一至三的五个
历史、高度 `3`、预算 `4`，概率为 `1/2、1/6、1/6、1/12、1/12`。

依赖语法现已有自由代数语义。分支代数与同态形成范畴，树代数是初始对象，结构 fold 是唯一解释；
生成的同余在所有代数中健全，并由树项模型给出绝对完备性。顺序叶嫁接形成结合且有单位的幺半群，
高度与预算是规范数值 fold，且对嫁接次可加。实例计算叶数 `5`、嫁接高度 `6`、嫁接预算 `8`。

分支模型代数现形成笛卡尔对称单子范畴。单点代数和逐点乘积满足真正的终对象/积泛性质，因此结合子、
单位子、辫、复制、丢弃及全部协调律均已编译。公共树在 `A ⊗ B` 中的 fold 精确等于两个 fold 的有序
对，相等性逐分量成立，树项模型与任意第二模型的乘积联合完备。实例的叶计数/预算并行观察为 `(5,4)`，
辫将其交换。

树级独立并行协议现显式保留两条异构通道。成对历史与状态有限，概率相乘并归一化，每个记录信道条目
分解为两条通道条目的乘积，资源成本相加；通道交换保持概率与成本。逐通道叶嫁接结合且有单位，并严格
满足张量—顺序交换律。公平/偏置实例计算 `25` 个历史、高度 `3`、预算 `8`、短历史质量 `3/8`、
双阶段预算 `16`，并行观察完备性区分公平/公平与公平/偏置。

### 作为高阶对象的模型

资源索引的对称单子过程模型、不增加资源的强辫单子函子和单子自然变换形成双范畴。
成本精确等价额外记录数值反射。普通同伦局部化与多个行走局部化测试用例均已编译。

普通局部化现已连接到 Rezk 外层：`CostExactRezkComparison.comparison` 在 universe-balanced 的源同伦范畴与成本精确局部化之间构造双单纯图自然变换。每个运输后的标记箭头都被证明可逆，其外层一阶顶点严格因子化经过目标的实际等价箭头子空间。该结论精确描述普通局部化的外层比较；非可逆 2-胞腔仍由独立的完整局部 mapping nerves 保留。

完整局部层现也有机器化高阶比较接口。伪函子的单位约束与复合器约束都已提升为所有单纯次数上的真实 nerve 同伦；支配这些同伦的结合子与左右单位子方程也已成为 common-universe 局部 nerve 中的精确 1-单形等式。`CostExactZigzagGlobalComparison.core` 由同一高阶局部化构造外层 Rezk 映射与完整局部层；局部顶点、恒等、水平复合、结合子与左右单位子都已满足严格外层/局部层粘合律，任意可逆局部 2-胞腔都解码为相应的外层等式。解码后的结合子粘贴显式满足五边形律，结合子/单位子粘贴满足三角形律。现剩将这些证书组装成全维单纯相容性，并证明 Complete-Segal/Rezk 弱等价定理。

源与实际目标的外层 completeness 映射现都有显式单纯同伦逆；`HomotopyEquivalenceWitness` 同时记录两个复合到恒等映射的真实 `SSet.Homotopy`。

正确的相对 Rezk 源现已编译：其外层 `n` 级包含全部源串，纵向变换必须逐点 cost-exact。实际局部化函子在所有内外单纯次数上自然地把它映入目标 Rezk core，并精确作用于每个表示箭头顶点。实际局部零单形和任意 2-胞腔边的映射/解码现也精确；每个可能不可逆的 2-胞腔都同时封装两个相对外层端点与目标局部边。纵向可复合的任意 2-胞腔对现又精确映为目标局部 2-单形，两条一骨架证书、完整三角形和依赖复合对角线被统一封装。任意两个可能不可逆 2-胞腔的同步水平复合现又精确通过 compositor 同伦的两侧映射；水平复合后的一骨架、两个外层复合端点和交换自然性方形也被统一封装。对于两层纵向可复合的水平 2-胞腔对，源与目标 interchange 现均精确成立，两侧共同 universe 的 pair 2-单形精确映射，两个方形粘贴成交换长方形，并封装全部因子与复合局部证书。实际 compositor 同伦现又给出剖分 degree-two 棱柱的三个目标局部 3-单形；十二个面全部被识别，两个外侧面精确化简为规范 pair 2-单形。该构造现已封装到任意次数：每个水平乘积单形都有索引化目标棱柱单形，一个全局成本精确 core 对每个模型三元组记录七族端面/侧面/共享面/退化律。首个相对外层桥现也精确成立：普通和 relative 两箭头顶点具有三面两恒等退化，relative comparison 精确保留它们，每个 degree-two 局部棱柱的三个水平 pair 顶点都与这些外层顶点粘合，目标中间面由实际映射局部复合解码。任意外层串顶点现沿每个单形映射精确限制且被 relative comparison 保留；每个 all-degree 局部棱柱的每个源顶点都解码成具有完整 two-arrow glue 的源 1-胞对。剩余问题是全部棱柱面投影粘合和 Dwyer–Kan/Rezk 弱等价。

该实际构造现已有可计算的呈示语法。`MarkedZigzag.Word` 由端点索引，任意源 1-胞腔可正向出现，只有携带标记证明的箭头才可反向出现。二叉弱复合使解释严格保持复合，而结合性保留为真实 2-胞腔。关系闭包现包含 whiskering、interchange、五边形、双范畴三角形以及标记 unit/counit 的两条伴随三角式。`InversionData.lift` 构造任意反演目标的提升，`InversionData.factorization` 给出伴随等价因子分解。`LocalExtension.extension` 对正向生成元保留自然性约束，对形式逆元取 mate，并递归处理空词与复合；modification 同样沿恒等、逆元和复合延拓。因此预复合忠实、满且本质满，`CostExactZigzag.inclusion_isBicategoricalLocalization` 已证明完整高阶局部化普遍性。

进一步地，源 pair 解码已经对每个水平乘积单形的任意单形范畴限制严格自然，每个受限顶点都再次携带完整 two-arrow glue；因此一个定理统一覆盖所有次数的面与退化。实际目标棱柱的每个面顶点现由范畴 nerve 的面投影逐字给出，并在 compositor 切换两侧精确分类为 `map(composite)` 或 `map(f) ≫ map(g)`；两种局部呈示都解码为同一个外层复合且携带完整 two-arrow glue。完整局部面/退化 core 仍被保留，不可逆局部胞腔不会被塞入 relative outer maximal core。源定义的 marked-zigzag 词/商 2-胞腔 nerve 现为每个模型对给出一个显式 relative mapping-space 呈示：它与实际目标局部 nerve 范畴等价，具有 `NerveEquivalenceWitness` 和显式单纯同伦逆，现有 local map 在所有次数上严格经过它，并精确作用于 forward word 与任意 2-胞腔；外层同伦函子也已本质满。尚未解决的是该呈示的模型无关 derived/hammock mapping-space 刻画、认可的弱等价封装以及 Dwyer–Kan/Rezk 定理。

底层商 mapping category 现还具有与具体目标无关的代数普遍性质：任意把 words 解释为目标对象、把 raw 2-胞腔解释为目标态射并保持全部关系、恒等和纵向复合的数据，都会下降为一个函子，在所有 raw 代表元上精确计算，而且是唯一的相容 lift。通用下降只依赖 `Quot.sound`；尚未完成的是把该代数普遍性质提升为 derived/hammock 同伦刻画。

该普遍性质现已提升到所有次数的 common-universe 范畴 nerve：任意相容 lift 都诱导同一个规范 nerve map，word 顶点、raw 2-胞腔边和任意 simplex 均精确计算，下降解释之间的自然变换或自然同构给出真实的单向或双向 `SSet.Homotopy`。仍缺独立 derived/hammock 构造的比较。

`PresentedDwyerKanCore` 现把 outer essential surjectivity 与全部 presented mapping-space 条件统一封装为一个经审计命题：nerve 等价、显式同伦逆、代数/单纯呈示普遍性、严格因子化和全维精确作用。`Presented` 限定不可删除；这仍不是独立 hammock 定理。

现已有受限但真正独立的右结合 linear hammock 对象模型：typed step 列表与二叉 words 相互转换和扁平化，精确保留长度，并给出等价 mapping category、nerve 显式同伦逆以及到实际 target local nerve 的直接比较。`LinearHammockDwyerKanCore` 将其与 outer essential surjectivity 组合。尚缺与经典任意网格 hammock 或其他认可 derived 构造的比较。

任意高度的纵向 grid 现也已显式化：`n`-grid 包含 `n + 1` 行 linear hammocks、`n` 条相邻商 2-胞腔边和全部端点方程，strict-Segal 重构将其与 linear hammock nerve 的 `n`-simplices 等价，并精确证明行、边、解码和双向 round trip。固定形状的横向多列片段也已形式化：等形行的每个公共列含一个原始原子 2-胞腔，宽度与可执行横向拼接精确，商解释通过 interchange 保持逐列恒等和纵向合成，任意高度 aligned grid 重构为具有精确行和解释边的真实 simplex。基本前向列细化也已可执行：恒等列可插入/删除，复合列可展开/收缩，move 可在任意公共前缀下提升并传递复合；带符号宽度变化精确，两个生成器对在商语义中双向抵消。marked reverse 结构现在也包含可执行的 unit pair `f ; f⁻¹` 与 counit pair `f⁻¹ ; f` 插入/删除，其带符号宽度为 `±2`，语义同构、双向 round trip 和任意前缀稳定性均已证明。每个 refinement 现有可执行逆向和统一语义同构；双腿 common-refinement span 构成等价关系及行商，商相等精确等价于可共同细化，并只推出语义同构而非对象相等。0-截断 mapping 层也已完成：包装行构成薄 common-refinement 群胚，并与离散行商范畴等价；nerve 比较具有显式单纯逆和双向同伦。非薄语义 refinement-path 群胚现保留按 quotient-cell 语义区分的路径；其 nerve map 到 linear mapping nerve 对态射 faithful、对行对象本质满、将全部路径映为同构并具有精确顶点/边公式，且到薄群胚的 0-截断 full 且本质满。实际商 2-胞腔连同“由可执行 refinement 生成”的存在见证现构成精确语义像群胚；路径群胚与其范畴等价，nerve 比较具有显式单纯同伦逆，像包含到完整 linear mapping category 忠实，原语义 nerve map 严格经过它。更大的非群胚生成路径范畴现可交替复合 refinement 与任意 aligned raw 2-胞腔；其语义及 refinement 嵌入均 faithful，旧 nerve map 严格经过它，并且每个源 2-胞腔都有一个规范单列边，其商语义是由左右规范 right-unitor 共轭的原 2-胞腔。规范左右 whiskering 与横向 append 现保持语义等价和像成员资格，并具有精确三模型 nerve 公式。正规化现已证明与 raw 左右 whiskering 自然相容；raw 恒等、original、source identity/逆、source composition/逆、transport 及纵向/whiskering 闭包分支均已完成。source composition 正反方向通过纯双范畴两原子协调公式精确对应 forward expand/contract；通用空 word/两原子闭环公式又将 marked unit/counit 及其逆精确对应 pair insert/delete。线性 append 的右单位/结合等式与可计算 equality path 已建立，left unitor 及其逆通过任意同构共轭精确正规化为恒等。递归终端空行路径精确正规化 right unitor 正反，递归结合路径也通过双范畴自然性、三角形与五边形协调精确正规化 associator 正反。全部 raw Cell 现无条件可正规化；任意 linear 商 2-胞腔都有生成路径代表，语义函子因而成为范畴等价，其 nerve 比较具有显式同伦逆。critical-pair 协调、约化 hammock 不变性、标准弱等价封装及最终全局 Dwyer--Kan/Rezk 定理仍开放。

模型比较不再要求全局使用同一资源代数。有序加法同态重索引串行、并行、结构和预算律；跨资源
代数的强辫模型态射随同态复合，并在每个固定资源映射上形成单子自然变换的局部范畴。四维计算
成本到 `Nat` 步数的投影可执行且有定理支持。

这些纤维已组成单个总双范畴：对象封装资源代数和过程模型，1-胞腔携带资源翻译和强模型态射，
2-胞腔携带资源翻译相等性和单子自然变换。水平复合、交换律、结合子、单位子、五边形和三角形
均已编译。向量值自由过程模型到步数重索引提供了一个可执行异质 1-胞腔。

总双范畴现还具有双层单纯语义：对象核是 Kan 且严格 Segal 的神经，显式取商的内部模型等价类与对象恒等边精确等价。每个局部 hom 范畴都有保留全部 1/2-胞腔的严格 Segal 映射神经；垂直复合是 2-单形，水平复合由交换律诱导为单纯映射。确定性丢弃 2-胞腔在总模型封装和神经解码后仍被证明不可逆。
全局二、三维 Duskin 数据也已显式化：三角形保留任意复合比较 2-胞腔，四面体保留六条边与四个面胞腔。边界存在唯一 3-单形当且仅当结合子修正的四面体方程成立；规范三重复合把真实双范畴结合子置于长面。
该构造现已扩展为全维全局 Duskin 半单纯神经：每个单形记录全部递增顶点/边/三角/四元组，任意严格单调序映射按字面限制数据。恒等与复合限制律均已证明，2/3 维精确恢复显式三角形/四面体。
退化层现也已原生实现：`n`-单形是从局部离散有限序 `[n]` 到总资源模型双范畴的严格保单位 lax 函子。每个保序序数映射通过预复合统一给出面和退化，并严格满足恒等/复合律。首个退化产生恒等边，lax 结合律暴露四面体方程，而一个自然变换把完整神经沿全部面映射解码到坐标半单纯神经。
逆向现有一个与 `Fin (n + 1)` 显式范畴等价的构造子正规有限序；`fromFin` 与 finite-to-normal lax 核心不再选择伪逆。恒等/严格边和左/右单位或严格比较胞腔都按构造子计算；八种构造子模式的异质四面体相干、源单位子、恒等运输与结合子均已适配到严格保单位 lax 函子核心。坐标与原生 normal-lax 单形的两条完整结构回转都已证明并组成逐维等价。沿此等价运输原生作用得到含全部面与退化的坐标单纯神经，且它与原生 Duskin 神经自然同构。尚待 complete-Segal 2-空间组装与高阶局部化比较。
complete-Segal 组装的第一层也已编译：总模型同伦范畴的 Rezk core 图在每个外层维度取有限串范畴的 maximal core，因而所有纵向层均为 Kan；外层对象空间与既有对象 core 范畴等价；选定的 Kan 等价箭头空间具有把对象送到恒等箭头的 `NerveEquivalenceWitness`。该 completeness 等价现已改用定义透明的恒等箭头函子，旧复合前向函子与之自然同构，且 selected core 到实际外层一阶空间的 inclusion 已编译。该复合显式自然同构于真实零退化，并与等价、inclusion、退化一起封装为可复用的范畴因子化。新的通用圆柱构造进一步把每个自然变换提升为 nerve 映射之间的 `SSet.Homotopy`；应用于此即证明中介 completeness 映射与真实零退化单纯同伦。每条横向行现还自然同构于纵向等价串范畴的普通 nerve，因而真实外层 spine 在每个双次数都是等价；`SegalCompletenessCore` 把这些字段与纵向 Kan 和 completeness 数据一起封装。选定等价范畴现又与真实外层可逆箭头的满子范畴显式等价；直接 completeness 映射仍是范畴等价的 nerve，且其 inclusion 与真实零退化单纯同伦。仍需完成高阶 Reedy matching 纤维化、非可逆局部 mapping nerves 接入及高阶局部化比较。

所有上述由范畴等价展示的 completeness 映射现都自动获得 `HomotopyEquivalenceWitness`。
Reedy 基础设施现已有严格 `Functor.IsIsofibration` 提升对象、恒等与 core inclusion 实例及正反向同构提升方程。全维 horn 定理也已完成：二维由群胚消去保证唯一，高维由范畴 nerve horn 唯一性恢复，`Functor.nerveMap_fibration` 因而给出 Kan fibration。
degree 1 matching 现已在字面 outer-zero 坐标中编译：`degreeOneMatchingFunctor` 是从 `Core(ComposableArrows C 1)` 到两个 `Core(ComposableArrows C 0)` 的真实 `d₁,d₀` 面映射对。端点共轭给出严格 isofibration，其 nerve 是 Kan fibration，且两个 nerve 投影分别证明等于真实外向面。显式的范畴积极限同构和 nerve 保积同构把它运输到 Mathlib 选定的单纯集合二元积；标准 matching map 严格等于 `⟨d₁,d₀⟩`，并仍是 Kan fibration。`DegreeOneReedyCore` 已把这些事实接入 `SegalCompletenessCore`。degree 2 现有显式 `TriangleBoundary C` 范畴，独立记录三条边；其严格像表示定理证明边界可扩张为 `ComposableArrows C 2` 当且仅当长边等于两短边复合。maximal core 上的限制是严格 isofibration，其 nerve 为 Kan fibration，并封装为 `DegreeTwoMatchingCore`。尚待把该边界 nerve 认同为抽象 degree-2 Reedy matching 极限及处理三维以上 matching restriction。

此外，度 2 包已证明对任意测试范畴 `T` 的 hom-wise 表示 `(T ⥤ TriangleBoundary C) ≃ TriangleBoundary (T ⥤ C)`。任意单纯空间的抽象 `simplicialSpaceBoundaryMatchingDiagram` 也已由 `∂Δ[n]` 的元素范畴定义；真实边界限制锥已编译，matching map 按定义就是进入选定极限的 universal lift。

显式三角边界 nerve 到选定抽象极限的 canonical comparison cone 与映射也已编译，所有 `fac` 方程均已证明；其与显式边界 map 的复合严格等于抽象 universal matching map，因此两种 degree-2 matching map 的相容性已经闭合，仅余证明该比较可逆。

三个规范非退化面索引及投影也已显式构造，严格解码为 `δ₀,δ₁,δ₂`，comparison 与三者均交换。

三个规范顶点与六条面–端点入射态射也已显式构造；匹配锥自然性证明所有抽象边投影具有正确且共享的端点投影。

每个 `TriangleBoundary C` 现还具有完整单纯编码 `∂Δ[2] ⟶ nerve C`，在全部非满射单形上计算，并对所有面与退化自然。

反向 `ofBoundaryNerveMap` 解码器也已编译：它提取规范顶点与边，并用入射自然性把三条边运输到共享端点。三条运输边等式与两个完整回转现均已证明；任意非满射 `Δ[2]` 单形都可分解经过一条规范余面，`boundaryNerveEquiv` 因而给出精确表示 `TriangleBoundary C ≃ (∂Δ[2] ⟶ nerve C)`。

与选定抽象 degree-2 Reedy 极限的同构现已完成：`degreeTwoAbstractMatchingBoundaryMap` 把抽象 matching 单形组装成 `nerve (EquivalenceString C k)` 中的完整边界，`triangleBoundaryEquivalenceStringEquiv` 交换三角边界与纵向可逆串，`degreeTwoBoundaryComparisonInverseApp` 再解码并提升回 maximal core。两个逆律、逐次双射与 `degreeTwoBoundaryAbstractMatchingIso` 均已证明，并由 `DegreeTwoReedyCore` 封装；仅余 degree 3 及以上 matching。

任意次数的统一桥梁也已编译：`abstractMatchingBoundaryMap` 对所有 `n` 组装完整边界映射、保留全部极限投影且为单射，并把 `abstractMatchingMap` 严格运输为普通范畴 nerve 的边界限制。`boundaryRestriction_injective` 已证明全部 `n ≥ 2` 的唯一性；`boundaryRestriction_surjective` 又通过内 horn 填充与余维二恢复证明全部 `n ≥ 3` 的存在性。因此所有高阶 matching map 都是单纯集合同构与 Kan fibration，并由 `HigherMatchingCore` 统一封装；正次数 Reedy matching 包现已完整。

上述非可逆局部 mapping nerve 接入现已由 `HigherCompleteSegalCore` 完成，不再属于待办：同一结构封装 Rezk 对象顶点、完整局部 nerve、任意 2-胞腔精确解码、非可逆性保持、局部 strict-Segal/quasicategory/2-coskeletal 证据及单纯横向复合。

### 有界内部单值层

深嵌入语法区分内部恒等与结构等价，并在不增加外部公理的前提下解释二者。已编译语义包括群胚、
对象商、骨架、Yoneda 包络、Kan 单纯神经，以及满足项目显式群胚完备 Segal 接口的分类图。

## 活跃前沿

总目标是构造一种可计算、机器可验证、单值化、高阶范畴化的资源受限信息过程理论，使经典概率、
量子过程、因果模型、计算、语义信息和热力学成为不同模型，并用已证明的表示与完备性定理连接。

跨可变资源代数的第一个总高阶范畴已经编译，其验证组成包括：

- 过程、并行、结构和携带证明的预算律的有序加法重索引；
- 资源变换函子、恒等资源兼容性、复合和预算传输；
- 重索引 `ProcessModel` 与资源翻译可复合的异质强辫模型态射；
- 每个固定资源翻译上的单子 2-胞腔和垂直局部范畴；
- 总资源模型对象、异质水平复合与加须、交换律、结合子、单位子、五边形和三角形；
- Kan 对象等价核、内部等价类–恒等边精确对应、完整局部映射神经、垂直 2-单形、水平复合单纯映射与被保留的不可逆 2-胞腔；
- 全局 Duskin 三角形/四面体，以及结合子修正边界存在唯一 3-单形的精确充填定理；
- 全维全局 Duskin 半单纯神经，对所有序嵌入具有严格限制律与精确低维恢复；
- 以严格保单位 lax 有限序图为单形的原生完整 Duskin 神经，包含全部退化、恒等边见证、四面体协调和到半单纯神经的自然坐标解码；
- 支持逆向坐标表示的构造子正规有限序等价，其全部边/比较正规化条款与全严格四面体分支已编译；
- 成本可翻译到各模型原生资源代数的公共单子语法，以及可逆表达式翻译、精确解释表示定理和
  翻译后的自由模型完备性；
- 同一个布尔翻转过程签名的六种模型特定解释，以及内核检查的跨模型一致性定理；
- 三接口两阶段签名及内核检查的六模型串行复合定理；
- 公共对称单子 `flip ⊗ flip` 签名、六模型并行定理、精确计算资源相加，以及升级为总双范畴 1-胞腔的六个规范异质自由提升；
- 该线性理论的可计算规范形、单元素精确像表示和六解释绝对等式反射完备性；
- expose–erase 签名及内核检查的六模型擦除、干预、语义损失和 Landauer 支付定理；
- 非薄菱形的精确双路径像、路径分离完备性准则及六个分离且完备的解释；
- 多生成元自适应二叉树的有限正历史规范形、精确路径预算、记录信道表示、观察完备性及六个原生模型实现；
- 变深且生成元依赖有限结果的树、依赖历史、精确上确界预算、沿显式历史等价的表示/完备性及保守二叉嵌入；
- 任意有限正依赖规范形的六模型通用实现：概率、测量–制备量子、带标签双节点因果、资源化随机计算、任务语境语义和诱导平衡热过程，并具有各自边界上的等式反射完备性；
- 精确有限语义序与全任务数值剖面对 Blackwell 支配/等价的完备性，以及可执行的单任务不完备见证；
- Gibbs 保持通道的内在像定理、唯一热提升，以及面向外部给定目标的依赖规范形表示/完备性；
- 固定 DAG 软/随机/硬因果程序的可计算约化规范形、精确模型/信道表示与等式反射完备性；
- 依赖分支代数范畴、初始树代数、唯一 fold、绝对等式完备性、顺序嫁接幺半群和高度/预算代数表示；
- 分支模型代数的笛卡尔对称单子范畴、逐分量乘积 fold 表示、精确联合相等性及树项模型联合完备性；
- 二元树级独立并行协议的精确随机分解、通道对称、资源相加、共享阶段嫁接、严格交换律和并行观察完备性；
- 任意有类型顺序签名的显式自由项范畴–路径范畴等价、精确成本保持与路径忠实完备性；
- 严格延拓空间可收缩的普通与异质顺序初始性、解释–自由源函子分类等价，以及六个规范自由提升和翻译成本界；
- 从 `Fin 4 → Nat` 计算资源到单个 `Nat` 步坐标的可执行投影，并提升为带已检查预算传输的
  模型级 1-胞腔。

接下来的定理层是：

- 为异质节点载体、改变图结构或策略依赖的因果干预、资源受限语义剖面或更丰富/无限任务语言，以及能量分辨的热操作膨胀建立可扩展逐模型像刻画；
- 表述并证明模型特定的表示、保守性与完备性定理，再建立真正的跨模型比较定理；
- 把已自然同构的完整坐标/原生 Duskin 神经与已有相干同伦的局部映射神经组装为全局 complete-Segal 2-空间，构造全资源过程双范畴的成本精确局部化，并用已编译的高阶局部 nerve 比较接口连接二者，同时保持商代表选择不进入可执行模型。

参数化行走局部化仍是活跃支线。其任意提升现已对任意目标双范畴封装为真正的
`generalLiftPseudofunctor`，不再需要局部薄假设。全部十六种端点序列的 target、source、
端点 transport 与 all-arrow 结合律均已编译；端点与自由群胚规范化给出任意三元箭头的总结合律，
合成子自然性和左右单位律也已闭合，并且限制到源箭头时严格恢复原伪函子。
生成元/保留与保留/生成元两种规范化顺序及其映射形式现已证明保持二元乘积，所需单位
子图因此已闭合。两种顺序还在正逆方向、映射前后显式分解为普通 compositor 加对应左右 unitor，
不再残留不透明的 `Unit × A` 运输。两个 forward factorization hom 已直接化为映射后的 unitor 逆元加
普通 normalized compositor；乘积上的左右 unitor 逆元也已在映射前后分解为因子 unitor 与 associator。
八条左右对称的 HEq 引理现已安全运输依赖类型中的单位端点，避免非法 rewrite motive。
显式的左、右单位规范源 compositor 都已证明经七端点运输的结合律，
两种 forward factorization 也都已证明对保留乘积具有乘法性。
两种分解的混合交换方块与由此得到的 forward sliding 乘法律也已证明；
mate 转移现已证明 inverse sliding 乘法律。显式 whisker exchange、规范源结合律、
七端点 transport 与目标规范化已进一步给出 all-arrow retained/retained/inverse 完整结合律。
混合目标方块、单次 sliding 交换、source 方块、端点 transport 与分支选择也已给出
retained/inverse/retained 完整结合律。forward/retained/inverse cancellation 序列也已端到端完成：
canonical 与映射后目标方块、identity-pseudofunctor 到 direct mate 的运输、unit-insertion/mate
相容性、source 结合律、七端点 transport、all-arrow 分支与精确 oplax 结合律均已编译。
retained/forward/inverse 序列的目标、source、端点 transport 和 all-arrow 分支也已全部闭合。
forward/inverse/retained 序列也已完成，其 source 方块归结为 unit-insertion 的右 whiskering 协调。
inverse/forward/retained 序列也已完成，并抽取了对偶的 counit-insertion 右 whiskering 引理。
inverse/retained/forward 的 target、source、端点 transport 与 all-arrow 分支现已全部编译；
其 source 证明使用显式 associator 桥闭合 retained-compositor conjugation。
retained/inverse/forward、forward/inverse/forward 与对偶 inverse/forward/inverse 均已通过
target、source、端点 transport 与 all-arrow 四层。源限制比较及其逆比较现已组成伴随等价
`generalLiftFactorization`；因此任意逆化标记的源伪函子都通过完成对象分解，
`inclusion_isBicategoricalLocalization` 已把标记逆化、本质满分解和局部预复合等价封装为完整的
双范畴局部化定理。该结论针对参数化行走例；完整资源过程双范畴上的对应构造仍然开放。

`TotalModelWalkingLocalization` 已把这一泛性质专门化到包含六个具名模型对象的异质
`ResourceModel` 双范畴。该桥仍诚实保留“源图必须逆化标记”的前提；从共享语法出发的六条解释
one-cell 并未被宣称为伴随等价。

## 明确开放或超出范围

- 一般可测空间因果模型与 do-calculus 完备性；
- 把形式步数等同于墙钟时间或硬件成本；
- 可执行有限随机核心中的无理实概率；
- 通用量子复制操作；
- Lean 类型的外部单值性；
- 基于完整弱等价或 Quillen 模型 API 的 Mathlib 原生标准完备 Segal 空间对象；
- 资源过程双范畴的完整 Dwyer–Kan、单纯、Rezk 或双范畴局部化定理。

开放陈述应写入[猜想登记册](reference/CONJECTURES.md)，而不是 Lean 公理或定理声明。

## 如何核验声明

- 模型操作或能力：[模型能力矩阵](reference/MODEL_MATRIX.md)
- 定理类型与依赖：[形式化蓝图](reference/BLUEPRINT.md)
- 内核假设：[公理清单](reference/AXIOMS.md)
- 开放研究陈述：[猜想登记册](reference/CONJECTURES.md)
- 可执行行为：`Ript/Examples/` 与 `scripts/check-examples.sh`
- 合并准备状态：`./scripts/quality-gate.sh`

这种分离让首页保持简洁，同时保存形式研究所需的完整可审计细节。
