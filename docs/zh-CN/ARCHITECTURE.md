# 架构

[English](../en/ARCHITECTURE.md) · [简体中文](ARCHITECTURE.md) ·
[日本語](../ja/ARCHITECTURE.md) · [Esperanto](../eo/ARCHITECTURE.md)

Ript 的组织原则是：可执行有限模型不依赖商类型、测度论、高阶范畴或内部单值机制。
每一层可以使用其下方接口，反向导入则由代码审查和根模块结构明确禁止。

## 依赖方向

```text
资源代数
    ↓
带成本的过程接口
    ↓
资源重索引与异质模型映射
    ↓
可执行语法 ──→ 语义与项模型
    ↓                 ↓
有限模型 ─────→ 通用语义桥梁
    ↓                 ↓
模型双范畴与局部化
    ↓
内部单值解释
```

最后一层解释深嵌入语法；它不会改变 Lean 的相等性，也不会向上层添加单值性公理。

## 资源与过程核心

`Ript/Resource/` 定义过程度量所用的代数：

- 有序加法资源；
- 预算与带预算态射；
- 单调传输和资源代数的有序加法变换；
- 成本诱导与可达过滤；
- 并行预算律。

`Ript/Core/` 把该代数连接到范畴和能力接口：

- 过程成本与串行次可加性；
- 可选的并行成本、结构成本、凸性、复制与丢弃；
- 模拟与单调映射；
- 不会自动推断额外结构的能力接口。

张量并不蕴含复制或丢弃；凸性、因果结构和热结构同样是显式能力，而不是全局默认值。

## 语法与语义

`Ript/Syntax/` 包含原始有类型语法、成本计算和显式推导；原始语法保持可执行。

`Ript/Semantics/` 包含：

- 到带成本范畴的解释；
- 求值与成本健全性；
- 等式健全性；
- 商项模型与相对完备性；
- 对称单子语义与初始性；
- 沿有序加法资源变换的公共语法解释、可逆表达式翻译，以及精确的成本推前自由模型完备性。

商结构只存在于证明层。只求值有限语法的使用者不需要执行商机制。

## 具体模型

`Ript/Models/` 及其子目录实现语义实例，而不是孤立的数据结构。

- `FiniteFunction` 提供确定性基线和显式笛卡尔复制/丢弃；
- `FiniteStochastic` 提供归一化精确有理随机通道、复合、张量、凸混合、复制与丢弃；
- `FiniteDistribution` 提供有限分布单子及 Kleisli 表示；
- 概率模块把有限精确通道连接到 Mathlib 的 `Stoch`；
- 决策模块实现 Blackwell 比较、精确风险、资源界与分离证书；
- 计算模块区分形式步数/查询/存储/门计数与真实运行时间；随机化计算把精确有限核与同一四维资源代数结合；
- 因果模块使用有限拓扑排序 DAG 与硬干预；
- 热模块区分精确操作通道和实值解析热力学；
- 量子模块使用有限 Kraus 族，并在封装通道前证明正性与保迹性；完整对称单子 Kraus 范畴之上有仪器、结果控反馈和依赖 bind；`InstrumentTree` 是归纳规范形与可计算预算层。
- `NoisyBitRealizations` 是首个六模型共享噪声语法，包含保留相干的随机单位量子和随机化计算目标。
- `Syntax.Branching` 计算定深自适应二叉历史、正分支表规范形、精确路径成本、最坏情形预算、记录随机表示与观察完备性；`AdaptiveNoiseRealizations` 给出六个原生模型实现。
- `Syntax.DependentBranching` 推广到变深、生成元依赖有限结果、显式历史等价及保守二叉嵌入；`Examples.DependentBranching` 是异构结果的可执行见证。
- `Syntax.DependentBranching.Free` 把分支代数组织成范畴，证明树代数初始性、等式健全/完备性和顺序嫁接幺半群，并把高度与预算表示为数值 fold。
- `Syntax.DependentBranching.Monoidal` 为模型代数范畴提供选定有限积、笛卡尔对称单子协调、逐分量乘积 fold 表示和联合模型完备性。
- `Syntax.DependentBranching.Parallel` 封装显式异构通道、精确独立随机分解、通道对称、资源相加、共享阶段嫁接和严格张量—顺序交换律。

[模型能力矩阵](reference/MODEL_MATRIX.md)是各模型可选结构的权威记录。

## 高阶组织

`Ript/Higher/` 把完整过程模型组织成双范畴：

- 0-胞腔是资源索引的对称单子过程模型；
- 1-胞腔是不增加资源的强辫单子函子；
- 2-胞腔是单子自然变换。

固定资源双范畴只是更广已编译结构的一根纤维。`ResourceChangeModelHom` 在有序加法映射
`R →+o S` 上把 `R` 模型连接到 `S` 模型；异质 1-胞腔随资源映射复合、传输已检查预算，
并在每个固定资源映射上形成单子 2-胞腔的局部范畴。`ResourceModel` 把资源代数与模型
封装为对象，`ResourceModelHom` 把资源映射与异质强模型态射封装为 1-胞腔，
`ResourceModelTransformation` 则保留平行资源映射的相等证明和单子自然变换。
它们共同形成具有异质加须、水平/垂直复合、交换律、结合子、单位子、五边形和三角形协调的
总双范畴。

这一层复用 Mathlib 的双范畴基础证明恒等、复合、结合子、单位子、交换律与协调。
双范畴等价不会自动蕴含数值成本相等；更强的 `CostExactModelEquivalence` 显式记录成本反射。

局部化工作按强度分层：

- 模型同伦范畴拥有普通 Gabriel–Zisman 局部化；
- 行走示例检验真正的逆元添加；
- 精确的双范畴泛性质谓词单独定义；
- 尚未证明的协调或本质满性字段绝不会以公理代替。

当前 mapping-space 栈具有三种显式呈示：二叉 marked-zigzag word/商 2-胞腔、独立右结合 linear
hammock 行，以及把可执行 refinement 与任意 aligned raw cell 组合起来的非群胚 generated hammock
path。三者均已与实际局部化目标的 local hom-category 建立范畴等价，nerve 比较具有显式单纯同伦逆，
generated 比较严格经过 linear 比较。一个终止 administrative reduction 会消去单位/嵌套、融合相邻
move 并抵消可执行 refinement 正逆对，同时保持商语义。raw critical-pair joinability、完整经典任意
网格 move 系统与标准弱等价封装仍是研究边界。

## 内部单值解释

`Ript/Univalent/` 位于普通过程理论下游，定义：

- 深嵌入接口码；
- 相互独立的内部结构等价与恒等语法；
- 群胚解释；
- 0-截断对象商与 1-截断骨架；
- 可表预层与 Yoneda 语义；
- 单纯神经与分类图。

这不是 Lean 的外部 HoTT。Ript 从不假设全局映射 `Equiv α β → α = β`；所有声明均局限于
内部解释语法及项目已编译的精确范畴接口。

## 可执行与解析边界

有限核心尽可能使用精确数据：自然数资源向量、有限类型、非负有理概率、可判定有限极小值和
显式见证。实分析、测度论、商构造、选择代表元和矩阵证明位于语义层，可能不可计算。
一个定理谈论有限对象，并不自动意味着它可执行；分类取决于 API 和假设。

## 公开状态记录

Ript 将项目沟通与形式状态分开：

- `README.md` 是简洁入口；
- `RESEARCH_STATUS.md` 提供适合阅读的研究摘要；
- `reference/MODEL_MATRIX.md` 记录已编译模型能力；
- `reference/BLUEPRINT.md` 记录依赖与定理级状态；
- `reference/CONJECTURES.md` 记录未证明陈述；
- `reference/AXIOMS.md` 记录实际内核假设。
- `GOVERNANCE.md` 记录决策权与稳定性策略；
- `SECURITY.md` 记录私密报告方式和支持的可信边界。

若这些文件不一致，以 Lean 声明和机器检查的审计输出为准；文档变更必须在同一个 PR 中恢复一致。

## 质量架构

`scripts/quality-gate.sh` 是稳定的本地入口并与 CI 对齐，它强制检查：

- 禁止 `sorry`、`admit`、项目自定义公理、信任逃逸和不安全库声明；
- 使用窄范围 Mathlib 导入和显式标识符；
- 根模块覆盖完整；
- 完整构建无警告且声明 lint 通过；
- 可执行示例稳定；
- 公理 allowlist 明确；
- 公共 Markdown 结构有效，入口页长度受控。

工作流使用固定 action 修订版本和只读仓库权限。变更策略见[贡献指南](CONTRIBUTING.md)。
