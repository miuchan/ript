# Conjectures and Unproved Research Statements

[English](docs/en/reference/CONJECTURES.md) ·
[简体中文](docs/zh-CN/reference/CONJECTURES.md) ·
[日本語](docs/ja/reference/CONJECTURES.md) ·
[Esperanto](docs/eo/reference/CONJECTURES.md)

This register contains exact Lean propositions whose statements compile but
whose proofs are not yet kernel checked. An active entry must carry the marker
`FORMALIZED_BUT_UNPROVED` and identify the declaration that states it.

## Current register

There are currently no active `FORMALIZED_BUT_UNPROVED` propositions. This
does not make the broader research program complete; open construction tracks
remain recorded below, in `BLUEPRINT.md`, and in the README without being
silently promoted to Lean propositions.

This does **not** mean that Ript's research program is complete. The open tracks
in the README and blueprint include broader measurable models, heterogeneous
causal systems, generic capability interfaces, richer cost models, and higher
localization. They are design and formalization work, not silently assumed
mathematical propositions.

## Governing research objective

Ript's objective is to construct a computable, machine-verifiable, univalent,
higher-categorical theory of resource-constrained information processes in
which classical probability, quantum processes, causal models, computation,
semantic information, and thermodynamics are distinct models, and to prove
the corresponding representation and completeness theorems.

This is a research program, not a theorem currently asserted by the library.
The compiled total resource-model bicategory removes one former obstruction:
models may use different ordered additive resource algebras, heterogeneous
strong braided morphisms compose over their resource translations, and
resource-equal monoidal 2-cells satisfy horizontal composition, interchange,
pentagon, and triangle coherence. A common monoidal syntax can now also push
its costs into any same-universe resource algebra without changing wires or
generators; the expression translation is computably invertible, its
heterogeneous interpretations have an exact representation by ordinary
interpretations, and the translated free model has relative completeness and
exact translated budgets. A first literal common-syntax slice is now compiled:
one Boolean-flip generator is realized by the exact probabilistic, Pauli-X
quantum, finite causal, multidimensional computational, task-semantic, and
Gibbs-preserving thermal models, with their six observable equations packaged
by `sixModelFlipAgreement`. A proved compositional extension now interprets a
three-interface two-flip syntax in all six models and packages its laws in
`sixModelCompositionAgreement`. A symmetric monoidal extension now interprets
one literal `flip ⊗ flip` expression in all six families, proves independent
parallel behavior and exact computation-resource addition, and supplies six
canonical strong symmetric resource-changing free lifts. Its quantum target is
now the full finite Kraus category: reversible basis changes provide a compiled
symmetric monoidal structure with all coherence laws, and tensor Pauli-X acts
componentwise on arbitrary product density matrices. Finite quantum instruments
are now present as normalized families of completely positive branches, with
posterior states, serial and tensor laws, a classical-record CPTP
representation, and outcome-controlled trace-preserving feedback. The coherent
measurement example uses its classical result to reset both posteriors to one
basis state. Dependent bind supports multi-round result trees, proves the Born
chain rule and Sigma-reassociation associativity, and a concrete three-history
tree is integrated into the resource-aware free syntax. A first-class inductive
`InstrumentTree` now supplies canonical dependent-history normal forms, exact
branch representation, finite induction, and computable path/tree budgets.
The classical-record channel is proved injective on arbitrary finite
instruments, and two dependent instrument trees are operationally equivalent
along an explicit history equivalence exactly when their corresponding branch
maps, equivalently their recorded channels, agree. The intrinsic image is now
characterized too: slicing a channel's Kraus operators extracts a canonical
instrument, and a channel is the recorded representation of a unique
instrument—equivalently of some finite instrument tree up to history
relabeling—exactly when its classical outcome register is block diagonal.
One exact quarter-crossover noise generator is also shared by all six model
families. Its quantum realization is random-unitary and demonstrably distinct
from measurement--preparation on coherent input; randomized computation keeps
four-resource costs; semantic risk/value are exact; all six free lifts compile.
Monoidal derivation
translation is proof-theoretically conservative and every heterogeneous
monoidal interpretation has a contractible strict extension type. A separate
object-universe lift now packages the common syntax and all six targets inside
the total resource-model bicategory, with the full Kraus process category as
the quantum target, where the six realizations are strong
braided one-cells with checked resource maps. A separate
`expose ≫ erase` syntax now also
connects classical erasure, quantum reset, causal intervention, computation,
semantic-value loss, and battery-paid Landauer saturation in
`sixModelErasureAgreement`. Finite hard-intervention programs now have a
computable last-write-wins normal form. Program execution is represented by
one normalized intervention and its exact `FinStoch` state; when no original
mechanism is already a parent-independent forced Dirac distribution,
extensional local-mechanism semantics reflects normal-form equality. The
following construction and theorem families
are no longer wholly open for the linear bit theory: its canonical-path image
representation and equality-reflection completeness are proved for all six
interpretations. Their first non-thin generalization is now proved for a
finite diamond: exact two-path image representation plus six-model completeness
under independently checked path separation. Generic free-path normalization,
an explicit term-category/path-category equivalence with exact free-cost
preservation, path-image representation, and
path-faithful completeness now hold for every typed sequential signature.
Every ordinary interpretation also has a unique strict resource-nonincreasing
free lift, and every heterogeneous interpretation has the corresponding
unique lift along its ordered additive resource map; both strict-extension
types are contractible. Globally, ordinary and heterogeneous interpretation
spaces are classified by the corresponding free-source resource functors.
The six diamond models
instantiate these lifts with checked generator agreement and translated cost
bounds. What remains open is scalable model-specific path faithfulness and
image characterization for richer operational languages. A second
generalization is now compiled for adaptive noise: arbitrary fixed-depth
binary trees have executable positive-history normal forms, exact costs,
recorded-channel representation, and observational completeness. One
depth-two two-generator tree has probability, coherent quantum, causal,
randomized-computation, semantic, and thermal realizations with an exact
cross-model representation package.
That boundary is now generalized again: generator-dependent arbitrary finite
outcome types and variable branch depths have dependent Sigma histories,
finite-supremum budgets, exact recorded-table representation, observational
completeness along explicit history equivalences, and a conservative embedding
of the fixed-depth binary language. The heterogeneous `Bool`/`Fin 3` witness
has five histories at three different lengths.
The free sequential algebraic layer is also discharged: branching algebras
form a category, the tree algebra is initial, formal congruence is sound and
absolutely complete, and associative unital leaf grafting has algebraic height
and budget folds with subadditive bounds.
The model-algebra category now also has chosen finite products and a cartesian
symmetric monoidal structure. Product fold is componentwise, simultaneous
two-model equality is exact, and pairing the term model with any second model
is jointly complete.
Binary tree-level parallel protocols are now compiled as explicit independent
lanes. Their stochastic entries factor, symmetry preserves probability and
cost, and componentwise grafting satisfies strict tensor–sequential
interchange with subadditive height and budget.
Arbitrary finite n-ary lane families are now compiled. Signatures, states,
histories, and semantics may depend on the lane; product normalization,
n-ary factorization, equivalence-based lane reindexing, simultaneous
history/state normal-form transport, strict interchange, and n-ary
observational completeness are proved.
Every finite positive dependent normal form now also has generic realizations
in all six model families. Equality reflection is proved for probability,
measurement–preparation quantum channels, fixed-resource randomized
computation, structured semantic experiments, and underlying thermal channels;
the tagged two-node causal joint is faithful under a full-support prior.
The exact finite semantic numeric boundary is also characterized. Universal
nonnegative task value is equivalent to Blackwell dominance, and equality of
all exact finite task values relative to the canonical no-information
experiment is equivalent to Blackwell equivalence. A Boolean counterexample
proves that one task-relative scalar value is not a complete invariant.
The thermal forgetful map is now characterized intrinsically as well: a
finite stochastic channel admits exactly one Gibbs-preserving lift between
specified source and target equilibria precisely when it pushes the former to
the latter. This specializes to arbitrary dependent normal forms and
externally supplied, rather than definitionally induced, target equilibria.
The fixed-DAG causal boundary now includes arbitrary parent-dependent soft
mechanism replacements, parent-independent stochastic interventions, and hard
Dirac interventions as one hierarchy. Finite programs normalize by last write,
then computably erase writes equal to the original mechanism; this reduced
form has exact model/channel representation and equality-reflection
completeness. The Boolean witness randomizes the child to an independent fair
coin and normalizes a subsequent explicit restore back to the empty program.
The total resource-model bicategory now has a two-level simplicial bridge.
Its Kan object core identifies single-valued internal equivalence classes with
object-identity edges exactly. For every pair of total models, the full local
hom-category nerve represents resource-changing 1-cells as vertices and all
monoidal 2-cells as edges; vertical composition is a 2-simplex and horizontal
composition is a simplicial map. A lifted deterministic discard edge decodes
to a proved noninvertible total-model 2-cell, so this bridge does not silently
truncate local 2-dimensional data. Global low-dimensional Duskin data are now
explicit as well: triangles carry arbitrary composite-comparison 2-cells, and
tetrahedra carry six edges, four face cells, and the associator-corrected
coherence equation. A tetrahedral boundary has a unique 3-simplex exactly when
that equation holds; the canonical composable triple uses the bicategorical
associator as its long comparison face.
These data now extend to every dimension as a genuine global semi-simplicial
Duskin nerve. An `n`-simplex stores a model at every vertex, a 1-cell on every
increasing edge, a comparison 2-cell on every increasing triangle, and the
tetrahedral equation on every increasing quadruple. Strictly monotone ordinal
maps act by literal restriction, with proved identity and composition laws;
dimensions two and three recover the explicit triangle and tetrahedron.
The degeneracy boundary is now closed by a native full Duskin nerve. Its
`n`-simplices are strictly unitary lax functors from the locally discrete
finite ordinal `[n]` into the total resource-model bicategory. Every monotone
ordinal map, including every degeneracy, acts by normal-lax precomposition;
identity and composition hold strictly. The first degeneracy duplicates its
vertex and creates an identity 1-cell, and the lax associativity law is exactly
the associator-corrected tetrahedral equation. A natural coordinate-decoding
map from the restriction of this simplicial nerve to the earlier
semi-simplicial nerve commutes with every face map.
The inverse representation now has a compiled constructor-normal foundation:
`Ordinal n` has only identity and strict-arrow constructors, is categorically
equivalent to Mathlib's thin category on `Fin (n + 1)`, and that equivalence is
lifted in both directions to strictly unitary lax functors. Coordinate
identity/strict edges and left/right/strict comparison cells compute by
constructor, while the three-strict-arrow coherence is exactly the stored
coordinate tetrahedron. All seven identity-containing equations now compile
as generic bicategory coherence/naturality theorems, and
`constructorTetrahedralCoherence` packages all eight constructor patterns as
one heterogeneous equality recording source associativity transport. The
source unitors, identity transports, and associator have now been adapted to
the exact `StrictlyUnitaryLaxFunctorCore` fields. The finite-to-normal direction
is now an explicit choice-free core, and `toNativeSimplex` constructs a native
Duskin simplex from every coordinate simplex. Both round trips are proved on
the full normal-lax structure, yielding `nativeCoordinateEquiv`. Transporting
the native action gives `coordinateNerve`, including every face and degeneracy,
and `coordinateNerveIsoNative` proves naturality under every ordinal map.
Global complete-Segal 2-space assembly and construction of the full
resource-process cost-exact localization remain.
The first exact layer of that assembly is compiled: the Rezk core diagram of
the total-model homotopy category has Kan vertical levels, an object-space
equivalence to the existing object core, and a selected Kan equivalence-arrow
space whose completeness map is the nerve of a category equivalence. What
is now added is a transparent identity-arrow forward functor, its natural
isomorphism with the original composite equivalence, and the selected core
inclusion into actual outer degree one. The composite is now explicitly
naturally isomorphic to the genuine outer zero-degeneracy, and the equivalence,
inclusion, degeneracy, and comparison are bundled as a machine-facing
categorical factorization. A new generic cylinder construction proves that
every natural transformation induces an `SSet.Homotopy` of nerve maps; hence
the mediated completeness map is now simplicially homotopic to actual outer
zero-degeneracy, and both categorical and nerve data are bundled together.
Every horizontal row is now naturally the nerve of the category of vertical
equivalence strings, so the actual outer spine map is an equivalence in every
bidegree; this is bundled with vertical Kan and completeness data as
`SegalCompletenessCore`. The selected equivalence category is now explicitly
equivalent to the actual full subcategory of invertible outer arrows; its
nerve inclusion commutes with the previous selected inclusion, and the direct
object-to-actual-equivalence map is again the nerve of a category equivalence
whose inclusion is homotopic to zero-degeneracy. All positive-degree Reedy
matching fibrations are now compiled. The formerly separate local layer is
attached by `HigherCompleteSegalCore`: the same total-model
indices determine Rezk object vertices and full non-groupoidal mapping nerves;
vertices decode to 1-cells, edges decode to arbitrary 2-cells, encoding is
exact, noninvertibility is retained, every local nerve is strict Segal,
quasicategorical, and 2-coskeletal, and horizontal composition is simplicial.
Its associator and both unitors are now natural isomorphisms whose nerve maps
carry genuine simplicial homotopies, with the pointwise pentagon and triangle
equations bundled in the same machine-facing core.
The first Reedy prerequisite is now compiled separately:
`Functor.IsIsofibration` records strict object/isomorphism lifts, including
forward and reverse edge formulas and their exact image under `nerveMap`.
The extension to every horn is now compiled: dimension one uses the strict
isofibration lift, dimension two uses groupoid cancellation, and higher
dimensions use categorical-nerve horn uniqueness. Consequently
`Functor.nerveMap_fibration` proves that the nerve map of an isofibration
between groupoids is a Kan fibration. The degree-one application now uses the
literal outer faces: `degreeOneMatchingFunctor` maps
`Core(ComposableArrows C 1)` to two copies of
`Core(ComposableArrows C 0)` by the actual `d₁` and `d₀` functors. It is a
strict isofibration by conjugating the represented arrow with the requested
zero-diagram endpoint isomorphisms, so its nerve is a Kan fibration. The two
nerve projections are proved equal to the genuine outer faces. The explicit
categorical-product limit and nerve-product preservation isomorphisms then
transport this map to Mathlib's selected simplicial-set binary product. The
resulting standard matching map is exactly `⟨d₁,d₀⟩` and is a Kan
fibration; `DegreeOneReedyCore` bundles it inside `SegalCompletenessCore`.
Degree two now has an explicit `TriangleBoundary C` category with three
independent edges. Its strict-image representation theorem says that a
boundary extends to `ComposableArrows C 2` exactly when the long edge equals
the composite of the two short edges. Restriction on maximal cores is a
strict isofibration, hence its nerve is a Kan fibration, and
`DegreeTwoMatchingCore` packages these facts. Its hom-wise universal layer is
also compiled: for every test category `T`, functors
`T ⥤ TriangleBoundary C` are equivalent to triangle boundaries internal to
`T ⥤ C`. Independently, `simplicialSpaceBoundaryMatchingDiagram` now defines
the abstract matching diagram of every simplicial space directly from the
elements of `∂Δ[n]`; the actual boundary-restriction cone is constructed, and
the matching map is definitionally its universal lift into the selected limit.
The explicit triangular-boundary nerve now has a canonical comparison cone
and map into that limit, with every `fac` equation proved.  Its composite with
the explicit boundary map is proved exactly equal to the abstract universal
matching map.  Thus only invertibility of this comparison remains at degree
two.  The three canonical nondegenerate face objects are now explicit in
the boundary index, decode exactly to `δ₀,δ₁,δ₂`, and the comparison
map's composites with their projections are proved.  The three canonical
vertices and all six face-to-endpoint incidence morphisms are explicit as
well; matching-cone naturality proves that every abstract edge projection has
the required endpoint projections.  Independently, every
`TriangleBoundary C` now has a complete simplicial encoding
`∂Δ[2] ⟶ nerve C`, defined on every non-surjective simplex and proved
natural under all faces and degeneracies.  The reverse decoder
`ofBoundaryNerveMap` is now compiled: incidence naturality supplies endpoint
equalities, and the three extracted edges are transported to the three shared
canonical vertices.  All three transported edge equalities are proved, every
non-surjective simplex of `Δ[2]` is factored through a canonical edge, and both
full round trips are compiled.  `boundaryNerveEquiv` therefore packages the
exact representation
`TriangleBoundary C ≃ (∂Δ[2] ⟶ nerve C)`.
The inverse of the canonical comparison is now constructed in every vertical
degree: an abstract matching simplex is assembled into a boundary map in the
nerve of `EquivalenceString C k`, decoded, commuted across
`triangleBoundaryEquivalenceStringEquiv`, and lifted back to the maximal core
by `degreeTwoBoundaryComparisonInverseApp`. Both inverse laws and degreewise
bijectivity are proved; `degreeTwoBoundaryAbstractMatchingIso` identifies this
boundary nerve with the abstract degree-two Reedy matching limit, and
`DegreeTwoReedyCore` packages the result. Matching categories in dimensions at
least three and the resulting full Reedy package remain. The arbitrary-degree
infrastructure is nevertheless compiled: `abstractMatchingBoundaryMap`
assembles any selected degree-`n` matching element as a boundary map in
`nerve (EquivalenceString C k)`, is injective, and carries the universal
matching map exactly to categorical-nerve boundary restriction.
`CategoryTheory.Nerve.boundaryRestriction_injective` proves uniqueness in all
dimensions at least two. High-dimensional existence is now also proved by
restricting a boundary to an inner horn, filling it via strict Segal, and
recovering the omitted face from codimension-two compatibility. Consequently
all matching maps in degrees `n ≥ 3` are simplicial-set isomorphisms and Kan
fibrations, packaged by `HigherMatchingCore`. The positive-degree Reedy
matching package is therefore complete.
The following construction and theorem families
are still open and therefore are not entered as axioms or placeholder Lean
declarations:

1. scalable intrinsic image-membership characterizations inside richer
   model-specific languages: heterogeneous-carrier, graph-changing, or
   policy-dependent causal interventions, resource-bounded semantic profiles
   or richer/infinite task languages, energy-resolved thermal-operation
   dilations, and comparison theorems connecting those algebraic
   interpretations (fixed-DAG soft/stochastic/hard intervention programs, the
   coherent finite quantum instrument-tree image, the unbounded exact finite
   semantic value profile, and arbitrary specified Gibbs-preserving target
   equilibria are now characterized);
2. model-specific representation and conservativity theorems beyond the
   generic free-category/path-category equivalence and the proved finite
   two-path image;
3. scalable relative and, where mathematically justified, absolute
   completeness beyond the generic path-faithfulness criterion and the proved
   finite path-separating diamond;
4. assemble the naturally isomorphic full coordinate/native Duskin nerve and
   locally coherent mapping nerves into a global complete-Segal 2-space,
   construct the cost-exact bicategorical localization of the entire
   resource-process bicategory, and instantiate the now-compiled higher
   local-nerve comparison for that construction.

Each item must be refined into exact Lean statements before it can acquire the
`FORMALIZED_BUT_UNPROVED` marker. Until then, the existing finite and higher
results are verified components of the objective, not evidence that the whole
unified theory has already been established.

The classifying-diagram track has discharged its former explicit matching
obligations. Ript proves a natural isomorphism of the whole outer diagram with
`n ↦ Map(Δ[n], N(M.Object))`, proves by presheaf density that
`Map(∂Δ[n], N(M.Object))` is the genuine boundary matching limit, identifies
boundary restriction with the universal limit lift, and proves every matching
map is a fibration. These facts are bundled in the project-local
`SSet.BoundaryReedyFibrant` interface. Ript now also proves every horizontal
row is the Kan nerve of a groupoid and packages both directions, strict outer
Segal data, genuine matching fibrations, and the actual completeness map's
`SSet.NerveEquivalenceWitness` in `SSet.GroupoidalCompleteSegal`. Every such
witness now constructs an explicit simplicial inverse and genuine homotopies
for both inverse laws through `SSet.HomotopyEquivalenceWitness`. Remaining
work is broader infrastructure: the pinned Mathlib release has neither a
simplicial-set weak-equivalence class nor a completed Quillen model structure,
so a Mathlib-native standard complete-Segal instance cannot yet be stated.
The exact localization target is no longer informal: the compiled predicate
`Bicategory.MorphismProperty.IsBicategoricalLocalization` requires marked
1-morphisms to become adjoint equivalences, biessential factorization of every
inverting pseudofunctor, and equivalence on the local categories of strong
transformations and modifications. Its Ript specialization is
`IsCostExactBicategoricalLocalization`.
`CostExactZigzag.inclusion_isBicategoricalLocalization` now supplies the
previously open existence theorem for the full resource-process bicategory.
`CostExactZigzagNerveComparison.core` now supplies its common-universe full
local-nerve action, including exact arbitrary 2-cell images, unit/compositor
simplicial homotopies, and associator/unitor compatibility.
`CostExactZigzagGlobalComparison.core` additionally
constructs the correct relative Rezk outer source: its objects are arbitrary
source strings and its vertical transformations are pointwise cost-exact.
The actual localization induces an all-dimensional bisimplicial map from this
source into the target Rezk core, acting exactly on represented arrow vertices.
The previous ordinary outer map remains auxiliary. Both maps are packaged
with the full local layer; marked arrows factor through the target equivalence
space, while source and target outer completeness maps have explicit
simplicial homotopy inverses. Local vertices, identities, horizontal
composites, associators, and both unitors satisfy exact outer/local gluing
laws. Actual local zero-simplices and arbitrary local 2-cell edges now map and
decode exactly. For every possibly noninvertible 2-cell, its two relative
outer endpoints and exact target local edge are packaged in one one-skeleton
gluing witness. Vertically composable pairs now map to exact target local
2-simplices, with both one-skeletons and the dependent composite diagonal
packaged together. Simultaneous horizontal pairs of arbitrary 2-cells now map
exactly through both sides of the common-universe compositor homotopy; the
horizontally composed one-skeleton, both outer composite endpoints, and the
commuting compositor naturality square are packaged together. For two
vertically composable horizontal pairs, source and target interchange are now
exact; both common-universe pair 2-simplices map exactly, and the two
compositor squares paste to a commuting rectangle together with all factor,
horizontal-composite, and vertical-composite local witnesses. The actual
`SSet.Homotopy` now supplies the three genuine target-local 3-simplices of the
degree-two compositor prism. Their twelve faces are identified: the first and
last are the exact target/source pair 2-simplices, adjacent tetrahedra share
their switching faces, and the other six are prisms on the source faces. The
construction is now packaged in every simplicial degree: every horizontal-
product simplex has its indexed target prism simplices, and one core records
both endpoint families, both side-face families, shared switching faces, and
both degeneracy families. The remaining problem is gluing this local all-
degree core to the localization-aware relative outer Rezk structure. The
first correct bridge is now compiled: generic and relative Rezk two-arrow
vertices have exact three-face/two-degeneracy laws, relative comparison maps
them exactly, and all three horizontal pair vertices of the degree-two local
prism glue to those outer vertices; their target middle faces decode from
actual mapped local composites. Arbitrary outer strings now also have
canonical vertices with exact restriction along every simplex-category map,
and both ordinary and relative comparisons preserve them. Every source vertex
of every all-degree local prism decodes to a source 1-cell pair with the full
two-arrow glue. This decoding is now strictly natural under every simplex-
category restriction of every horizontal-product simplex, and every restricted
vertex again carries the full two-arrow glue; hence one theorem covers every
face and degeneracy in every degree. Every actual target-prism face vertex is
now projected literally from its target simplex, classified before or after
the compositor switch as `map(composite)` or `map(f) ≫ map(g)`, decoded to the
same outer composite, and equipped with the full two-arrow glue. The complete
local face/degeneracy core remains attached without treating noninvertible
local cells as outer equalities. The source-defined marked-zigzag word/
quotient-2-cell nerve is now categorically equivalent to the actual target
local nerve for every object pair, with a `NerveEquivalenceWitness`, explicit
simplicial homotopy inverse, and strict all-degree factorization of the
existing local map; the outer homotopy functor is essentially surjective.
The underlying word/quotient-2-cell category now also has a target-independent
presentation universal property: every interpretation of words and raw cells
into an arbitrary category that respects all relations, identities, and
vertical composition descends to a functor, computes exactly on every raw
representative, and is the unique compatible lift. What remains is upgrading
this algebraic universal property to a derived or hammock characterization,
accepted weak-equivalence packaging, and the resulting Dwyer--Kan/Rezk
theorem. The intermediate simplicial step is now compiled: each interpretation
induces an all-degree common-universe nerve map, all compatible lifts induce
that same map, and natural transformations or natural isomorphisms of
descended interpretations induce genuine one-way or two-way simplicial
homotopies. What is still absent is the comparison with an independently
specified derived/hammock construction. Outer essential surjectivity and all
presented mapping-space conditions are now combined in the audited
`PresentedDwyerKanCore`; the qualifier is essential because its source
mapping spaces are the compiled word/quotient nerves themselves. An
independent right-associated typed linear hammock object model is now also
compiled. Conversion and flattening preserve length, every binary word is
canonically isomorphic to its linear normal form, and the induced linear
mapping category is equivalent to both the presented category and the actual
target local nerve. `LinearHammockDwyerKanCore` combines this mapping condition
with outer essential surjectivity. The generated non-groupoidal path category
now represents every linear quotient 2-cell; its common-universe replacement
is directly equivalent to the actual target local category, has a nerve map
with explicit homotopy inverse, factors strictly through the linear
comparison, and forms `GeneratedHammockDwyerKanCore` with outer essential
surjectivity. What remains is comparison with the classical reduced arbitrary-
grid hammock or another accepted derived construction.
The arbitrary-height vertical-grid part is now explicit: an `n`-grid consists
of `n + 1` linear rows, `n` adjacent quotient-cell edges, and endpoint
equations, and strict-Segal reconstruction identifies it with every
linear-hammock `n`-simplex. The fixed-shape horizontal fragment is now also
explicit: equal-shape rows carry one raw atomic 2-cell per common column,
widths and executable horizontal append are exact, quotient interpretation preserves
componentwise identities and vertical composition, and arbitrary-height
aligned grids reconstruct genuine simplices with exact rows and interpreted
edges. Elementary forward-column refinement is now executable: identity
columns insert/delete, composite columns expand/contract, moves lift under
arbitrary prefixes and compose, their signed width change is exact, and both
generator pairs cancel in the quotient semantics. Marked reverse structure is
now present through executable insertion/deletion of both `f ; f⁻¹` unit pairs
and `f⁻¹ ; f` counit pairs, with signed width `±2`, exact semantic isomorphisms,
both round trips, and arbitrary-prefix stability. Every composite refinement
now has an executable reverse and unified semantic isomorphism. Two-leg
common-refinement spans form an equivalence relation and a row quotient;
quotient equality is exactly common-refinability and soundly yields a semantic
isomorphism, not Lean object equality. A non-thin semantic refinement-path
groupoid is now compiled as well: paths are quotiented only by equality of
their quotient-cell interpretations, executable reversal gives inverses, and
the semantic functor into the linear mapping category is faithful and
essentially surjective on row objects with exact nerve edge action. Its exact
semantic image has now been internalized as the subgroupoid of actual quotient
2-cells carrying an executable-refinement witness: paths are equivalent to
this image, the image inclusion is faithful, the nerve equivalence has an
explicit simplicial homotopy inverse, and semantic interpretation factors
through it strictly. A larger non-groupoidal path category now alternates
refinements with arbitrary aligned raw 2-cells. Its semantics is faithful, the
refinement subsystem embeds faithfully and factors strictly, and every source
2-cell has a canonical one-column representative whose quotient semantics is
the original 2-cell conjugated by right-unitors. The path calculus is now
closed under normalized left/right whiskering and horizontal append, with
exact cost-exact three-model nerve formulas. Raw identities and original cells
are normalizable, and normalizability is closed under vertical composition.
Normalization naturality for both raw whiskerings is now proved by explicit
append-isomorphism exchange and cancellation; source identity and inverse plus
equality transport are normalizable too. Recursive `rightUnitPath` and
`rightUnitPathInv` delete and insert a terminal empty row beneath every atomic
prefix; their quotient interpretations are mutually inverse, and raw right
unitor/inverse normalize exactly to them. Recursive `associatorPath` and its
inverse similarly implement the two linear append bracketings; bicategorical
naturality, triangle, and pentagon coherence identify their exact quotient
semantics with raw associator/inverse normalization. Source
composition/inverse are normalized exactly by executable
forward expansion/contraction using the audited two-atomic-step coherence
formula; generic empty/two-atom formulas now normalize marked unit/counit and
inverses exactly by pair insertion/deletion. Computable linear append right-
unit/associativity equalities and equality paths are available; left unitor and
inverse normalize to identity by arbitrary-iso conjugation. Unconditional
structural induction now normalizes every raw cell. Conjugating an arbitrary
quotient representative before choosing a raw representative then proves that
every linear quotient 2-cell is denoted by a generated path; the semantic
functor is a categorical equivalence and its nerve map has an explicit
homotopy inverse. Smallifying the generated and linear categories now gives a
direct categorical equivalence from generated paths to the actual target
local hom-category. Its nerve comparison has an explicit homotopy inverse and
factors strictly through the independent linear comparison; outer essential
surjectivity packages this as `GeneratedHammockDwyerKanCore`. Competing
forward/marked moves now have a first terminating administrative reduction
layer: vertical units, left nesting, adjacent refinement/aligned/common-prefix
administration, and executable refinement inverse pairs reduce under every
path context. `nodeCount + leftWeight` strictly decreases, every path has an
irreducible reduct, and all finite reductions preserve quotient semantics;
every one-step critical pair is therefore semantically coherent. Raw
joinability/local confluence, the additional classical arbitrary-grid moves,
and their homotopical invariance remain open.
The 0-truncated layer is now compiled separately: wrapped rows form a thin
common-refinement groupoid categorically equivalent to the discrete row
quotient, and its nerve comparison has an explicit simplicial homotopy inverse.

The ordinary-localization/Rezk comparison is now compiled separately.
`RezkCore.diagramMap` is functorial in an ordinary functor, while
`CostExactRezkComparison.comparison` smallifies and applies the cost-exact
localization functor. Every transported marked arrow maps to a target Rezk
one-arrow vertex that factors strictly through the actual equivalence-arrow
subspace. This proves the outer inversion comparison but intentionally does
not identify the ordinary localization with the full noninvertible local
mapping nerves.

The full local comparison is now compiled conditionally on the genuine
bicategorical universal property. For every universe-balanced
bicategorical localization, `BicategoricalNerveComparison` constructs maps on
all full local nerves, proves exact action on arbitrary 2-cell edges, and
promotes pseudofunctor compositor naturality to a genuine simplicial
homotopy; marked vertices land at chosen target adjoint equivalences. The
complete two-dimensional walking localization instantiates this package, and
its Boolean discard remains noninvertible after mapping. The unresolved step
is not this comparison interface but construction of the cost-exact
bicategorical localization for the entire resource-process bicategory and its
global complete-Segal assembly.

That construction now has a compiled syntactic beginning.
`MarkedZigzag.Word` is an executable endpoint-indexed word with arbitrary
forward 1-cells and backward steps restricted to the marking;
`CostExactZigzag` specializes it to the saturated cost-exact arrows. Its raw
2-cell language already contains original 2-cells, source identity and
composition comparisons, marked unit/counit generators and their inverses,
vertical composition, both whiskerings, and equality transport. Every
marking-inverting pseudofunctor with chosen adjoint-equivalence witnesses has
a single recursive interpretation of words, compatible with concatenation
and both cancellation orders. The concrete zero-cost embedding that is not a
source equivalence now has an explicit one-step reverse word and raw unit and
counit cells. The relation closure now includes horizontal whiskering,
interchange, associator/unitor inverse laws, pentagon and triangle. The
quotient hom-categories assemble into an actual bicategory, the source maps by
a genuine pseudofunctor, and marked unit/counit isomorphisms satisfy explicit
adjunction triangle relations and form equivalences; every cost-exact arrow is
proved inverted. The concrete
zero-cost non-equivalence becomes an equivalence in this target. The
representation was
refactored to binary weak composition, making word composition evaluation
definitionally exact. `evalCell_respects` now proves quotient descent,
`InversionData.lift` constructs every marking-inverting target lift, and
`factorizationHom`/`factorizationInv` are coherent strong transformations in
both directions. Their objectwise unitors compile as invertible modifications,
so `InversionData.factorization` packages an adjoint equivalence and
`InversionData.factorsThrough` proves biessential factorization for every
marking-inverting pseudofunctor. Both marked adjunction triangles are imposed
in the quotient. `LocalExtension.extension` recursively extends every strong
transformation using mates on formal inverses, and modification naturality
extends across identities, inverses, and composites. Precomposition is thus
faithful, full, and essentially surjective. Therefore
`CostExactZigzag.inclusion_isBicategoricalLocalization` proves the complete
bicategorical localization universal property. The source and
word-presentation local nerves are now replaced by equivalent common-universe
`AsSmall` nerves, and the complete cost-exact local comparison is packaged in
`CostExactZigzagNerveComparison.core`. The outer Rezk direction induced by the
same actual higher localization is packaged with it in
`CostExactZigzagGlobalComparison.core`, with exact vertex, identity, and
horizontal-composition gluing plus associator and unitor gluing. Its
degree-one horizontal action now also contains the exact two-sided compositor
edge maps and naturality square for arbitrary 2-cells. Its degree-two action
now maps vertically composable pair 2-simplices exactly and proves the pasted
rectangle. Its three actual compositor-prism 3-simplices and all twelve faces
are now exposed as well. The generic formulas are now packaged at all degrees
and instantiated globally for every cost-exact model triple. Their remaining
outer-relative gluing is no longer empty: degree-two represented strings,
their faces/degeneracies, and all three prism pair vertices are compiled. The
arbitrary-string vertex/restriction extension and all-degree prism source-
vertex glue are now compiled too. Pair decoding and complete glue for every
restricted source vertex are also compiled, uniformly covering all faces and
degeneracies. Actual target-face vertices are now classified on both sides of
the compositor switch, identified with their exact local presentations, and
decoded to the same outer composites while retaining the full local face
core. The presented relative-zigzag mapping nerve now has an exact categorical
comparison with the actual target local nerve, a displayed simplicial
homotopy inverse, and strict factorization of the source local map in every
degree. Proving model-independent derived mapping-space correctness and the
complete-Segal/Rezk weak equivalence remains open. The target-independent
quotient-presentation descent and uniqueness theorem is now compiled, but a
hammock/derived homotopical comparison has not yet been deduced from it. The
all-dimensional nerve-map uniqueness and natural-transformation homotopy
invariance are now proved and available for that comparison. A project-local
presented Dwyer--Kan criterion is also proved; a standard Dwyer--Kan claim
now has both an independent linear hammock model and a full generated path
model with direct target comparisons, categorical-nerve equivalences, explicit
homotopy inverses, and strict generated-to-linear-to-target factorization.
`GeneratedHammockDwyerKanCore` packages this with outer essential surjectivity,
but a standard claim still requires comparison with the classical reduced
arbitrary-grid hammock (or another accepted derived model) and standard weak-
equivalence packaging. Arbitrary-height row grids and their exact nerve representation are
proved. Fixed-shape aligned multi-column cells and grids now have exact
quotient/nerve interpretation, and elementary executable forward-column
refinements plus marked unit/counit pair refinements have exact signed-width
and semantic inverse laws. Their object-level common-refinement quotient and
semantic-isomorphism soundness are now proved. A quotient mapping nerve,
in the precise 0-truncated sense, is also proved via the thin refinement
groupoid/discrete-quotient nerve equivalence. A non-thin refinement-path nerve,
with faithful exact semantic action, is now proved too. It is categorically
and simplicially equivalent to the exact subgroupoid of refinement-generated
quotient 2-cells, which includes faithfully in the full linear mapping
category and strictly factors the semantic nerve map. The aligned-cell-
augmented path category now adds arbitrary pointwise raw cells, contains every
source 2-cell in one-column form, strictly extends refinement paths, and is
closed under normalized left/right whiskering and horizontal append. Identity,
vertical-composite, original-cell, both whiskering, source-identity/inverse,
source-composition/inverse, and equality-transport normalization cases are
proved; all marked unit/counit, unitor, and associator cases are proved too.
Every raw cell is therefore normalizable, every quotient 2-cell between linear
rows is in the generated semantic image, and the generated path category is
equivalent to the full linear mapping category. Its first directed
administrative reduction is terminating by a strictly decreasing executable
complexity, preserves semantics for arbitrary finite sequences, and supplies
an irreducible reduct for every path. Competing one-step reductions agree in
quotient semantics. Raw critical-pair joinability/local confluence, the full
classical arbitrary-grid move system, and reduced-hammock invariance remain
open.

The first complete construction against that predicate is now kernel checked.
Identity precomposition is an adjoint equivalence of pseudofunctors and an
equivalence on each local category of strong transformations and
modifications. Consequently the identity pseudofunctor is a bicategorical
localization exactly when every marked arrow is already an adjoint
equivalence. This validates the full universal-property interface without
weakening it. It does not solve Ript's nontrivial case: the concrete zero-cost
discrete embedding is proved not to be an adjoint equivalence, and therefore
the identity pseudofunctor is proved not to be the cost-exact bicategorical
localization. A genuine construction must adjoin at least that missing
inverse while retaining noninvertible 2-cells.

The first genuinely inverse-adjoining slice is also kernel checked. The
walking arrow is represented by the preorder category `Fin 2`; its generator
is proved not to be a bicategorical equivalence in the locally discrete
source. Mathlib's free-groupoid localization supplies an explicit reverse
arrow, both inverse equations, and an ordinary `Functor.IsLocalization`
instance. Ript proves that ordinary inversion transports to
adjoint-equivalence inversion by the induced pseudofunctor.

The next parameterized slice removes the locally discrete target restriction.
Ript takes the product with the single-object bicategory of types and
functions, localizes only the walking coordinate, proves the resulting
pseudofunctor faithful on every source 2-cell, and proves a concrete Boolean
discard 2-cell remains noninvertible in the target. Thus genuine inverse
addition and noninvertible 2-cell retention now coexist in one compiled
bicategorical construction. The first universal-property fragments are now
also compiled. For every target bicategory, every pseudofunctor that depends
only on the retained coordinate inverts the marking and factors through the
localization target up to an adjoint equivalence. A complementary family now
handles the coordinate being localized: every functor from the walking arrow
to an arbitrary groupoid induces a marking-inverting pseudofunctor, factors
through the free-groupoid target, and sends the formally adjoined inverse to
the actual inverse of the generator's image. Precomposition is fully faithful
on every local category of strong transformations and modifications: object
surjectivity gives faithfulness, while a mate calculation, signed-path
induction, and product decomposition lift every modification across the free
inverse. These two families now combine: for an
arbitrary groupoid-valued localized component `K` and arbitrary
retained-coordinate pseudofunctor `H`, the paired pseudofunctor `K × H`
inverts the marking and factors componentwise, while its lift maps the formal
inverse correctly; with the identity retained component it still detects the
noninvertible Boolean discard. Marking inversion and factorization are now
proved invariant under adjoint equivalence of source pseudofunctors, so this
result covers the entire replete closure of the separable family rather than
only literal componentwise pairs. The free-groupoid coordinate now also has a
kernel-checked endpoint normal form: every signed path represents the unique
morphism between its endpoints, the completion is thin, and it is explicitly
equivalent to the codiscrete groupoid on `Fin 2`. This removes path-representative
ambiguity in the strong-transformation extension. That extension is now
packaged as a genuine target strong transformation: forward constraints reuse
source naturality, reverse constraints use invertible mates, both generator
cancellation orders are compiled, and endpoint thinness reduces all remaining
composition cases to those constructors. Modifications lift as well, the
restriction recovers the original source transformation up to an invertible
modification, and precomposition is an equivalence on every local category.

For an arbitrary (possibly nonseparable) marking-inverting source
pseudofunctor, chosen adjoint equivalences on the images of the marked walking
arrows now determine a compiled `PrelaxFunctor` action on every target object,
1-morphism, and 2-morphism. Its forward and genuinely reverse 1-/2-morphism
equations are explicit. Its identity comparison is compiled at every object,
and composition comparisons are compiled for all eight endpoint-normalized
pairs: the four forward/forward shapes, both retained/inverse orders, and both
inverse/forward cancellation orders with arbitrary retained coordinates.
Endpoint normalization now packages those branches as one comparison for every
composable target-arrow pair, and eight reduction theorems expose the selected
canonical comparison. The four endpoint hom-functors now also reduce to their
forward or reverse implementations by compiled equalities, and one canonical
endpoint 2-cell constructor covers retained-coordinate morphisms in every
direction. For the forward/forward branch, the canonical target and source
composition comparisons now satisfy compiled left and right naturality
squares, and those squares remain valid after applying the arbitrary target
action and the original source pseudofunctor. Those squares are now joined
across every equality-transport stage, so the full forward/forward comparison
satisfies compiled left and right naturality in its retained coordinates.
Both mixed branches now satisfy the same complete statement: inverse followed
by retained data and retained data followed by inverse data have compiled left
and right naturality through target normalization, source compositors,
equality transports, associators, and the mate-derived inverse sliding square.
Both cancellation branches now do as well: inverse followed by its matching
forward arrow uses the chosen counit, while forward followed by inverse uses
the chosen unit; both are natural in either retained coordinate through their
source factorizations and endpoint transports. These five compositor families
now assemble into left and right naturality for the unified endpoint
comparison across all eight walking-endpoint triples. Free-groupoid thinness
and local discreteness then lift those equations to the all-arrow comparison
for arbitrary target objects, 1-morphisms, and 2-morphisms. The complete left-
and right-unit laws are now compiled for arbitrary target arrows, including
the freely adjoined inverse. The canonical source and target three-fold
composition comparisons, the resulting source-normalized forward compositor,
the mapped target comparison square, and the endpoint-transport stage now
satisfy compiled associativity. Isomorphism normalization now composes those
layers into the exact oplax associativity equation for every triple of
canonical forward arrows. The first genuinely inverse endpoint sequence,
1-to-0-to-0-to-0, now has the exact equation too:
inverse/retained/retained composition is reduced through its target and
endpoint-transport associativity squares. The retained/retained/inverse target
normalization square is now compiled as well. For every locally thin
destination bicategory, all associativity, naturality, and unit equations are
unique, so the arbitrary action packages as a genuine pseudofunctor and agrees
with the source action on included 1-morphisms. For the same branch in a
general non-thin target, the source-normalized retained/inverse compositor is
now isolated and proved natural in both retained coordinates. Its missing
three-fold law is therefore precisely the multiplicative coherence of the
mate-derived inverse-sliding isomorphism, not an endpoint-transport ambiguity.
At the unmapped source boundary, generator/retained and retained/generator
normalization are now both proved multiplicative in `A × B`; their images
under every source pseudofunctor are compiled as four-stage vertical
equalities in both hom and inverse orientations. These eight equations are
the unit-normalization inputs needed for the forward
sliding multiplication proof. The two generator/retained orders now also
factor explicitly through the ordinary source compositor followed by the
appropriate left or right unitor, again in both orientations and before or
after applying the source pseudofunctor. Thus the remaining proof no longer
contains opaque `Unit × A` normalization. The two forward factorization homs
are now rewritten directly as mapped unitor inverses followed by ordinary
normalized compositors. Inverse left/right unitors on `A × B` also decompose
through the factor unitors and associator, before and after mapping.
The dependent walking-arrow endpoint equalities that defeated ordinary
rewriting are now compiled explicitly as heterogeneous equalities: the
three-fold source 2-cell, the mapped 2-cell, and both normalized compositor
positions transport across `f ≫ id = f` and `id ≫ id = id` without an
ill-typed rewrite motive. Eight symmetric HEq bridges now support explicit
left- and right-identity-normalized source compositors whose dependent
seven-endpoint associativity laws are proved. Consequently both forward
factorizations are proved multiplicative in `A × B` as exact normalized
squares. Their mixed interchange square and the resulting forward-sliding
multiplicativity law are now proved as well. Transferring that law through the
mate construction now proves inverse-sliding multiplicativity too. Explicit
whisker exchange, source normalization, seven-endpoint transport, and target
normalization now fold this law into the complete all-arrow
retained/retained/inverse associativity square. The mixed target square,
single-sliding whisker exchange, source law, seven-endpoint transport, and
branch selection now also prove retained/inverse/retained associativity.
The forward/retained/inverse cancellation sequence now compiles end to end:
its canonical and mapped target square, identity-pseudofunctor-to-direct-mate
transport, unit-insertion/mate compatibility, source-normalized associativity,
seven-endpoint transport, all-arrow branch selection, and exact oplax
associativity equation are proved. The retained/forward/inverse cancellation
sequence is also complete, using retained-prefix compositor coherence and the
same endpoint transport. Forward/inverse/retained now compiles as well; its
source law is the right-whiskering coherence of unit insertion.
Inverse/forward/retained is now complete too, supported by the corresponding
counit-insertion right-whiskering theorem. Inverse/retained/forward is now
complete through target, source, endpoint transport, and all-arrow branch
selection. Retained/inverse/forward is now complete as well; its source law
factors through reversed-adjunction mate inversion, counit insertion,
inverse-sliding tensor multiplicativity, and split-left whisker exchange.
Forward/inverse/forward and the dual inverse/forward/inverse sequence are now
complete through target, source, endpoint transport, and all-arrow selection.
Endpoint and free-groupoid normalization prove associativity for arbitrary
target triples, and the invertible comparisons are packaged as the genuine
`generalLiftPseudofunctor` without a local-thinness hypothesis. Its restriction
is now adjoint equivalent to every marking-inverting source pseudofunctor;
`generalLiftFactorsThrough` supplies arbitrary nonseparable biessential
factorization, and `inclusion_isBicategoricalLocalization` combines it with
marking inversion and local precomposition equivalence. Thus the parameterized
walking example is a complete bicategorical localization. The full
resource-process case is now independently completed by the generic
marked-zigzag presentation and
`CostExactZigzag.inclusion_isBicategoricalLocalization`.

Two ordinary localization slices are no longer open. First, the identity,
skeletal-completion, and restricted-Yoneda functors now satisfy Mathlib's
`Functor.IsLocalization` predicate at all internal identity morphisms, and
their functor-category universal properties are compiled. This does not
invert any previously noninvertible process; the source is already a
groupoid. Second, the model bicategory now has a compiled homotopy
1-category, obtained by identifying invertibly 2-isomorphic model morphisms,
and a Mathlib Gabriel--Zisman localization at all classes with a
cost-reflecting representative. The representative-level mark is now
explicitly saturated under invertible 2-cells, that saturation is proved to
descend exactly to the homotopy-category mark, and a canonical pseudofunctor
from Mathlib's `Pith` maps every saturated marked arrow to an isomorphism in
the localization. A concrete zero-cost discrete marked arrow is proved
noninvertible before localization, so this construction adds a genuine formal
inverse. Finite deterministic discard supplies a separate noninvertible
monoidal 2-cell whose endpoints remain distinct after homotopy truncation;
moreover, every pseudofunctor from the full model bicategory to a locally
discrete target is proved to identify the images of those endpoints. This
formally witnesses why the current bridge cannot retain the 2-cell as
nontrivial data. The open localization problem is specifically constructing
the higher or bicategorical localization satisfying the now-compiled
2-dimensional universal-property predicate.

## Recently discharged: exact finite stochastic Blackwell converse

Status: `PROVED`.

The universe-polymorphic theorem is kernel checked as
`Ript.Models.Decision.RationalSeparation.finiteBlackwellShermanStein`:

```lean
theorem finiteBlackwellShermanStein :
    FiniteBlackwellShermanStein.{u}
```

It proves that, for every **nonempty** finite hidden-state carrier, universal
order over exact finite decision problems implies exact stochastic garbling.
The nonempty hypothesis is necessary: the compiled `EmptyParameterBoundary`
example proves that with no hidden states the decision order is vacuous while a
garbling from a unit observation carrier to an empty one need not exist.

The completed proof has four explicit bridges:

1. `deterministicMixtureDominates_iff` represents every finite stochastic
   garbling as an exact rational simplex mixture of deterministic
   post-processings.
2. `mem_convexHull_of_ratCastVector_mem_convexHull` reflects a rational point
   from the real convex hull of finitely many rational vertices back into their
   rational convex hull. The proof uses a minimum-support Carathéodory
   representation, affine-span reflection, and uniqueness of barycentric
   coordinates.
3. `exists_rational_strictSeparator_of_not_mem_convexHull` applies real
   Hahn--Banach separation and then uses density of rational coefficient vectors
   to preserve all finitely many strict inequalities.
4. `rationalGarblingSeparator_nonempty_iff_certificate` converts the resulting
   signed rational separator into exact nonnegative-rational decision data by
   row shifts and a uniform prior.

The proof is proposition-level and uses standard classical infrastructure; it
does not claim an extracted linear-programming solver. The axiom audit for the
new geometric bridge, separation completeness, pairwise converse, and global
theorem reports exactly `[propext, Classical.choice, Quot.sound]`.

The deterministic finite Blackwell converse remains available as a more direct
constructive fragment: under any exact full-support prior, reconstruction risk
extracts a post-processing witness precisely when the target is constant on
every source fiber.

## Algorithmic boundary

For independently specified finite real energy spectra, the project proves
that exact rational Gibbs probabilities exist exactly when all Boltzmann ratios
to a reference state are positive rationals. It also supplies executable
rational-weight examples and a proved `sqrt 2` obstruction. What remains
unsupported is a general algorithm deciding equality of arbitrary real
exponential expressions; no unproved Lean proposition is registered for that
algorithmic boundary.
