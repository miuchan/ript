# Research status

[English](RESEARCH_STATUS.md) · [简体中文](../zh-CN/RESEARCH_STATUS.md) ·
[日本語](../ja/RESEARCH_STATUS.md) · [Esperanto](../eo/RESEARCH_STATUS.md)

This page is a concise research map, not the theorem ledger. Exact theorem
types, dependencies, source files, and assumptions live in
[`BLUEPRINT.md`](reference/BLUEPRINT.md) and [`AXIOMS.md`](reference/AXIOMS.md).

## Status vocabulary

Ript uses only these formal status labels in the blueprint:

- `DEFINED` — an interface or construction exists;
- `STATEMENT_FORMALIZED` — a theorem type exists but no proved declaration is
  claimed;
- `PROVED` — Lean accepts the proof without project axioms or placeholders;
- `BLOCKED` — a specific dependency or API gap is recorded;
- `OPEN_RESEARCH` — the statement or correct formulation remains research.

The README and model matrix summarize only implemented, compiled work.

## Implemented pillars

### Resource-sensitive syntax and semantics

The sequential and symmetric monoidal cores include executable syntax, syntax
cost, interpretations, explicit derivations, soundness, term models, relative
completeness, and monoidal initiality. Cost functions and attained budget
filtrations have proved round-trip laws under explicit hypotheses.
The same monoidal language can now be pushed along an ordered additive
resource map without changing its wires or generators. Expression translation
is computably invertible, heterogeneous interpretations are represented
exactly by ordinary interpretations of the pushed signature, evaluation obeys
the translated budget, and the pushed free model is relatively complete with
an exact translated cost.

The first concrete cross-model slice now compiles as well. One unit-cost
Boolean-flip signature is interpreted by exact probability, Pauli-X quantum
evolution, a finite causal mechanism, multidimensional computation,
task-relative semantic information, and a Gibbs-preserving thermal process.
The six observable boundary equations are packaged by one checked theorem.
Computation retains its native vector resource, while quantum and thermal
analytic observables remain separate from this slice's zero abstract cost.

A second shared signature now proves serial composition rather than only a
single boundary action. Two typed flips restore the input through exact
stochastic composition, Pauli-X evolution, a normalized three-node causal
chain, exact two-step/two-gate computation resources, reversible semantic
post-processing, and a closed Gibbs-preserving thermal protocol.

The first shared symmetric monoidal slice now compiles as well. One common
`flip ⊗ flip` expression acts independently in probability, the full
finite-Kraus quantum model, two causal mechanisms, exact
four-coordinate computation, semantic experiments, and Gibbs-preserving
thermodynamics. The relevant concrete models now carry checked symmetric
monoidal structures; the quantum instance includes arbitrary Kraus channels,
and tensor Pauli-X acts componentwise on arbitrary product density matrices.
Monoidal resource translation is proof-theoretically
conservative, and every heterogeneous monoidal interpretation has a direct
strong symmetric free lift with a contractible strict-extension type.
The common syntax and all six targets are also bundled as objects of the total
resource-model bicategory; the six lifts become checked strong braided
one-cells with their native resource maps.

That linear compositional theory now has its first absolute completeness and
representation results. Normalization computes the unique path at every
reachable interface pair, the term model is thin, each semantic hom-image is
exactly the canonical singleton, resource translation is proof-theoretically
conservative, and all six interpretations reflect equality. These theorems
depend on the current syntax having no competing paths.

The first characteristic irreversible pipeline now compiles too. A shared
two-coordinate `expose ≫ erase` syntax realizes classical constant erasure,
quantum reset, hard causal mechanism replacement, exact computation resources,
semantic-value destruction, and work-assisted thermal erasure with exact
Landauer saturation. The thermal interface explicitly includes the battery;
free closed erasure is not inferred.

The first non-thin common theory now compiles. A four-resource diamond retains
two formally distinct parallel paths, normalizes every expression without
collapsing the branch, represents the input-to-output image as exactly two
denotations, and proves that path separation implies semantic completeness.
All six concrete interpretations satisfy path separation by independent
model-specific witnesses and are therefore equality-reflecting.

The mechanism is now generic rather than diamond-specific. For every typed
sequential signature, `SequentialNormalForm` computes generator paths, proves
derivability equivalent to path equality, represents every heterogeneous
semantic image as a path image, and proves every path-faithful interpretation
complete. It also gives an explicit category equivalence between the quotient
term model and the typed path category, with exact free-cost preservation.
`SequentialFree` and
`ResourceChangingSequentialFree` prove unique strict free lifts for ordinary
and heterogeneous interpretations, including translated cost bounds; both
strict-extension types are contractible. The entire interpretation spaces are
classified by free-source resource-monotone or resource-changing functors.
All six diamond models satisfy the generic path interface and instantiate the
resource-changing lift.

### Exact finite probability and decisions

Normalized rational stochastic channels form a category with tensor, convex
mixtures, copy, and discard. The finite-distribution Kleisli representation and
a faithful finite-discrete bridge to Mathlib `Stoch` compile. The decision layer
contains forward Blackwell monotonicity and finite converse results with the
necessary nonempty hidden-state boundary, plus exact separator certificates.
At the exact finite semantic boundary, universal nonnegative task value is
equivalent to Blackwell dominance, and equality of every exact task value
relative to the canonical no-information experiment is equivalent to
Blackwell equivalence. A Boolean zero-loss task assigns the same scalar value
to perfect and uninformative experiments, proving that one task value is not a
complete invariant.

### Causal, computational, and thermal models

Finite DAG causal models have normalized observational semantics and hard
interventions. Finite hard-intervention programs normalize computably by
last-write-wins; execution equals one normalized intervention and its exact
stochastic state. Under the explicit condition that no base mechanism is
already a forced Dirac constant for every parent assignment, extensional
mechanism semantics is complete for this normal form. The fixed-DAG extension
allows arbitrary parent-dependent soft replacements, with stochastic and hard
interventions as special cases. Its normalizer performs last write wins and
then deletes writes equal to the base mechanism; the reduced form represents
both the final model and exact joint-state channel and is complete for local
mechanism semantics without an additional identifiability premise. A Boolean
example gives an independent fair child and shows that randomize-then-restore
canonicalizes to the empty program. Total and
`Option`-partial computation models track formal
steps, queries, storage, and gate counts. Finite Gibbs-preserving models connect
exact rational operations to KL, free-energy, correlation, approximate erasure,
and explicit Landauer witnesses under stated analytic hypotheses. At the exact
operational boundary, a stochastic channel has a unique Gibbs-preserving lift
between any specified source and target equilibria exactly when it pushes the
former to the latter. Dependent normal forms inherit this criterion and
equality reflection for externally supplied compatible target equilibria.

### Finite quantum channels

Finite Kraus families define channels only after positivity and trace
preservation are proved. Identity, composition, tensor, a full symmetric
monoidal structure with proved naturality and all coherence laws, trace discard,
complete positivity under finite amplification, and a faithful classical dephasing
embedding compile. No universal quantum copying operation is claimed.
Finite instruments are normalized families of completely positive operations.
They provide nonnegative normalized outcome probabilities, posterior states,
serial and tensor laws, and a CPTP representation with an explicit classical
record. Computational-basis measurement of a coherent plus state verifies
exact half/quarter probabilities, while `InstrumentSyntax` supplies checked
one-/two-unit resource bounds and the canonical free lift. Outcome-controlled
Pauli-X feedback preserves the recorded probabilities and resets both
posteriors and the forgotten-result total to `false`.
Dependent bind now supports multi-round instruments whose continuation and
result type depend on the current result. Joint probabilities obey Born's
chain rule, nested binds associate under Sigma-tree relabeling, and a compiled
three-history tree has probabilities `1/2`, `1/2`, and `0`.
`InstrumentTree` now makes finite adaptive trees first-class. Its dependent
histories are canonical normal forms, evaluation has exact branch
representation, and computable path costs are bounded by a structural tree
budget. The classical-record channel is injective on finite instruments, and
for arbitrary dependent trees an explicit history equivalence makes evaluated
instrument equality, equality of every recursive branch map, and recorded
channel equality equivalent. Kraus-row slicing now gives the converse image
theorem: a channel into `Outcome × residual-system` comes from a unique finite
instrument, equivalently from a one-step instrument tree up to history
relabeling, exactly when all off-diagonal outcome blocks vanish.

The first shared noisy generator now compiles across all six families. One
quarter-crossover BSC is exact probability, coherent random-unitary quantum
noise, a noisy causal mechanism, four-resource randomized computation,
task-semantic information, and Gibbs-preserving thermodynamics. The boundary
agreement, quantum coherence separation, exact semantic risk/value, parallel
resource addition, and six free lifts are proved.

The shared noise boundary now includes a genuine adaptive tree. The generic
fixed-depth binary language computes complete histories, positive rational
branch tables, exact path costs, and a worst-case budget. Its recorded
stochastic representation is faithful, giving an observational completeness
theorem. A depth-two quarter/half-flip tree is realized by probability, a
coherent random-unitary quantum instrument tree, a four-node causal DAG,
resource-accounted randomized computation, semantic decision information,
and Gibbs-preserving thermodynamics. The four branch masses, cross-model
representation, coherent quantum separation, deterministic history decoder,
zero Bayes risk, semantic value `1/2`, and a concrete completeness-based tree
distinction are all compiled.

The generic stochastic language now also supports variable-depth dependent
finite branching. Every generator has its own finite outcome type and every
result may choose a differently shaped continuation. Dependent Sigma histories,
height, exact path cost, worst-case budget, recorded-table representation, and
observational completeness along explicit history equivalences compile. The
fixed-depth binary language embeds conservatively. A `Bool`/`Fin 3` example
computes five histories of lengths one through three, height `3`, budget `4`,
and exact masses `1/2, 1/6, 1/6, 1/12, 1/12`.

The dependent syntax now has a free algebraic semantics. Branching algebras
and homomorphisms form a category; the tree algebra is initial and structural
fold is its unique interpretation. The generated congruence is sound in every
algebra and absolutely complete via the tree term model. Sequential leaf
grafting is an associative unital monoid, height and budget are canonical
numeric folds, and both are subadditive under grafting. The executable witness
computes leaf count `5`, grafted height `6`, and grafted budget `8`.

Branching model algebras now form a cartesian symmetric monoidal category.
The one-point algebra and pointwise products satisfy actual terminal/product
universal properties, so associators, unitors, braiding, copy, discard, and
all coherence laws compile. Folding a common tree into `A ⊗ B` is exactly the
pair of folds into `A` and `B`; equality is simultaneous component equality,
and the term-model/product interpretation is jointly complete. The executable
parallel leaf-count/budget observation is `(5, 4)` and braiding swaps it.

Tree-level independent parallel protocols now keep two heterogeneous lanes
explicit. Paired histories and states are finite, probabilities multiply and
normalize, every recorded channel entry factors into the two lane entries,
and resource costs add. Lane swap preserves probability and cost. Componentwise
leaf grafting is associative and unital and satisfies strict tensor–sequential
interchange. The fair/biased example computes `25` histories, height `3`,
budget `8`, short mass `3/8`, and two-phase budget `16`; parallel
observational completeness separates fair/fair from fair/biased.

The binary construction is generalized to arbitrary finite dependent lane
families. Lane-indexed signatures, state carriers, trees, histories, and
semantics have exact product normalization and n-ary channel factorization.
Explicit lane equivalences preserve budget and commute with residual-state
evaluation and the entire canonical normal form under dependent history/state
transport. Pointwise phase grafting gives strict n-ary interchange. The
three-lane witness computes `125` histories, budget `12`, short mass `3/16`,
a checked lane transposition, and two-phase budget `24`.

Every finite positive dependent normal form now has a generic six-model
realization. Its exact recorded channel becomes a probability process, a
faithful measurement--preparation quantum channel, the valid conditional
boundary of a tagged two-node causal model, a four-resource randomized
program, a structured experiment in a decision-task context, and a
Gibbs-preserving process into the induced equilibrium. Path cost and history
length have checked computation-resource bounds. Equality at each stated
boundary reflects normal-form equality; causal reflection uses an explicit
full-support prior. The heterogeneous `Bool`/`Fin 3` tree instantiates the
construction and six-model completeness separates its fair and biased roots.

### Models as higher objects

Resource-indexed symmetric monoidal process models, resource-nonincreasing
strong braided monoidal functors, and monoidal natural transformations form a
bicategory. Cost-exact equivalences add explicit numerical reflection. An
ordinary homotopy localization and multiple walking-localization test cases
compile.

The ordinary localization is now connected to the Rezk outer layer.
`RezkCore.diagramMap` functorially maps Rezk core diagrams, and
`CostExactRezkComparison.comparison` applies it to universe-balanced source
and localized homotopy categories. Every transported cost-exact arrow is
proved inverted, and its outer one-arrow vertex factors strictly through the
target's actual equivalence-arrow subspace. This is the exact outer
localization comparison; it does not claim that the ordinary localization
retains noninvertible 2-cells, which remain in the separate full local mapping
nerves.

The full local layer now has its own higher comparison interface.
`BicategoricalNerveComparison.higherLocalizationNerveCore` turns every
universe-balanced bicategorical localization into maps of all local mapping
nerves, proves the exact image of every arbitrary 2-cell edge, supplies
natural unit and compositor isomorphisms with genuine simplicial homotopies,
proves the exact associator and left/right-unitor compatibility equations
underlying those homotopies, and sends every marked 1-cell vertex to a chosen
target adjoint equivalence.
`WalkingLocalizationNerveComparison.core` instantiates this interface for the
complete two-dimensional walking localization: its marked generator acquires
an inverse while the mapped Boolean-discard edge still decodes to a
noninvertible 2-cell. The full cost-exact localization of the resource-process
bicategory is now constructed below. `UniverseLiftedNerve` replaces both local
hom-categories by equivalent common-universe `AsSmall` categories, and
`CostExactZigzagNerveComparison.core` instantiates the full local comparison:
arbitrary 2-cell images remain exact, and both the unit and compositor give
genuine simplicial homotopies; the lifted associator and unitor edges equal
their prescribed compositor/unit/target-coherence pastings. The canonical
pseudofunctor now also descends to a
functor on homotopy categories. `CostExactZigzagGlobalComparison.core` uses
that functor to construct the localization-aware relative Rezk map into the
actual presented target. In every outer degree its source contains all source
strings and only pointwise cost-exact vertical transformations; the induced
map is bisimplicially natural in every inner and outer degree and acts exactly
on represented arrow vertices. The earlier ordinary outer map remains an
auxiliary comparison. Marked outer arrows factor through the target's actual
equivalence space, and both outer directions are packaged with the full-local
layer. The source and actual target
outer completeness maps both have explicit simplicial homotopy inverses.
Local vertices decode exactly
to outer arrows, every invertible local 2-cell decodes to its outer equality,
and identity, horizontal composition, associators, and both unitors satisfy
strict gluing laws. The decoded associator pastings satisfy the pentagon and
the decoded associator/unitor pastings satisfy the triangle. Actual source
local zero-simplices and arbitrary 2-cell edges now map and decode exactly.
For each possibly noninvertible 2-cell, both relative outer endpoints and its
exact mapped target-local edge are bundled in one one-skeleton witness.
Vertically composable pairs now map to exact target local 2-simplices; the two
one-skeleton witnesses, full triangle, and dependent composite diagonal are
bundled together. Simultaneous horizontal pairs of arbitrary 2-cells now map
exactly through both sides of the compositor homotopy; their horizontally
composed one-skeleton, outer composite endpoints, and commuting naturality
square are bundled together. For two vertically composable horizontal pairs,
source and target interchange are exact, both common-universe pair
2-simplices map exactly, and the two squares paste to a commuting rectangle
with all factor/composite local witnesses. The actual compositor homotopy now
also gives the three target-local 3-simplices triangulating the degree-two
prism; all twelve faces are identified and both outer faces normalize to the
exact pair 2-simplices. The construction is now packaged in every degree:
each horizontal-product simplex has indexed target prism simplices, and one
global cost-exact core records all seven endpoint/side/shared/degeneracy law
families for every model triple. The first relative-outer bridge is now exact:
generic and relative two-arrow vertices have all three faces and both identity
degeneracies, relative comparison preserves them, and all three horizontal
pair vertices of each degree-two local prism glue to those outer vertices;
target middle faces decode from actual mapped local composites. Remaining work
has narrowed further: arbitrary outer string vertices restrict exactly along
every simplex map and relative comparison preserves them; every source vertex
of every all-degree local prism decodes to a source pair with complete two-
arrow glue. All-prism-face projection gluing and the global Dwyer--Kan/Rezk
weak-equivalence theorem remain.

The actual construction has now begun with a computable presented syntax.
`MarkedZigzag.Word` is endpoint-indexed, permits every source 1-cell forward,
and permits a reverse step only with a marking proof. Concatenation, length,
unit and associativity laws compile. Its raw 2-cell language contains source
2-cells, identity/composition comparisons, invertible marked unit/counit
generators, vertical composition, both whiskerings and equality transport.
`CostExactZigzag` specializes this to the saturated cost-exact marking. Every
marking-inverting pseudofunctor has a single recursive word interpretation,
up to the proof-level choice of adjoint-equivalence witnesses, with canonical
composition and both cancellation isomorphisms. The concrete noninvertible
zero-cost embedding now has a one-step formal reverse and raw unit/counit
generators. The full relation closure now includes vertical and horizontal
functoriality, interchange, associator/unitor inverse laws, pentagon and
triangle. Its quotient hom-categories assemble into the actual
`Presented.localizationBicategory`; `Presented.inclusion` is a pseudofunctor,
and marked unit/counit isomorphisms give explicit adjoint equivalences.
`CostExactZigzag.inclusion_inverts` proves inversion of every saturated
cost-exact arrow, while the concrete zero-cost source non-equivalence becomes
an equivalence in this target. The word representation
is now binary and weakly associative, so composition evaluation is
definitionally exact. `evalCell_respects` proves quotient descent,
`InversionData.lift` constructs the target lift, and coherent forward/reverse
strong transformations compare its restriction with the original
pseudofunctor. Their objectwise unitors compile as invertible modifications;
`InversionData.factorization` and `CostExactZigzag.factorsThrough` therefore
prove biessential factorization for every cost-exact-inverting pseudofunctor.
Both marked adjunction triangle relations are now part of the quotient.
`LocalExtension.extension` recursively extends strong transformations, using
mates on formal inverse steps, while modification naturality extends across
identities, inverses, and composites. This makes local precomposition
faithful, full, and essentially surjective. The theorem
`CostExactZigzag.inclusion_isBicategoricalLocalization` therefore proves the
complete higher cost-exact localization universal property.

Resource algebras no longer have to be globally identical merely to compare
models. Ordered additive homomorphisms reindex serial, parallel, structural,
and budget laws. Strong braided model morphisms across different resource
algebras compose together with those homomorphisms, and monoidal natural
transformations form the local categories over each fixed resource map. A
four-dimensional computation cost now has an executable, theorem-backed
projection to its `Nat` step count. These fibres are now assembled into a
single total bicategory: objects bundle their resource algebra and process
model, 1-cells carry the resource translation and strong model morphism, and
2-cells retain equality of the resource translation together with a monoidal
natural transformation. Horizontal composition, interchange, associators,
unitors, pentagon, and triangle compile. A vector-valued free process model
and its step-count reindexing provide an executable heterogeneous 1-cell.

The total bicategory now also has a two-level simplicial semantics. Its object
core is a Kan strict-Segal nerve in which explicitly quotiented internal model
equivalences are exactly object-identity edges. Every local hom-category has a
full strict-Segal mapping nerve whose vertices are resource-changing 1-cells
and whose edges retain all monoidal 2-cells. Vertical composition is exposed
as a 2-simplex, while interchange makes horizontal composition a simplicial
map. The deterministic discard witness remains noninvertible after total-model
packaging and exact nerve decoding.
Global dimensions two and three are explicit: Duskin triangles store arbitrary
composite-comparison 2-cells, while tetrahedra store six edges and four face
cells. A boundary has a unique 3-simplex exactly when the
associator-corrected tetrahedral equation holds; the canonical composable
triple uses the actual bicategorical associator as its long face.
The construction now extends to every dimension as a genuine global
semi-simplicial Duskin nerve. Each simplex records all increasing
vertices/edges/triangles/quadruples, and every strictly monotone ordinal map
acts by literal restriction. Identity and composition of restrictions are
proved, and dimensions two and three recover the explicit triangle and
tetrahedron structures.
The remaining degeneracy step is now implemented natively: an `n`-simplex is
a strictly unitary lax functor from the locally discrete finite ordinal `[n]`
to the total resource-model bicategory. Every monotone ordinal map acts by
precomposition, so faces and degeneracies obey strict identity/composition
laws. The first degeneracy creates an identity edge, lax associativity exposes
the tetrahedral equation, and a natural transformation decodes the full nerve
to the coordinate semi-simplicial nerve along all face maps.
The inverse direction now has a constructor-normal finite ordinal equivalent
to `Fin (n + 1)`, with bidirectional strictly-unitary-lax lifts, executable
identity/strict edge and unitor/strict-cell normalization, and the all-strict
tetrahedral branch. All seven identity-containing equations now compile as
generic bicategory coherence/naturality theorems, and all eight constructor
patterns are assembled into one heterogeneous tetrahedral-coherence theorem.
The source unitors, identity transports, and associator are now adapted to the
exact lax-functor core fields, yielding both a constructor-normal simplex and,
through the explicit choice-free `fromFin` core, a native Duskin simplex. Both
coordinate/native round trips now hold for the complete normal-lax structure,
giving a degreewise equivalence. Transporting the native action along it gives
a full coordinate simplicial nerve with every face and degeneracy; this nerve
is naturally isomorphic to the native Duskin nerve. Complete-Segal 2-space
assembly has now started with an honest Rezk core diagram of the total-model
homotopy category: every vertical level is the nerve of a maximal subgroupoid
and is Kan; the outer object space is categorically equivalent to the compiled
object core; and a selected Kan equivalence-arrow space carries a
`NerveEquivalenceWitness` for the object-to-identity-arrow comparison. The
new `HomotopyEquivalenceWitness` construction upgrades this to a displayed
simplicial inverse with genuine homotopies for both inverse laws. The
completeness equivalence now uses a definitionally transparent identity-arrow
functor, obtained from the original composite equivalence by an explicit
natural isomorphism, and the selected equivalence space has a compiled nerve
map into actual outer degree one. Its composite is now naturally isomorphic
to the actual zero-degeneracy, and this categorical factorization is packaged
as one reusable witness. A generic explicit cylinder now turns every natural
transformation into an `SSet.Homotopy`; applying it here proves that the
mediated completeness map is simplicially homotopic to actual outer
zero-degeneracy and packages both levels together. The actual-equivalence-
subspace identification remains, but outer Segal reconstruction is now exact:
each horizontal row is naturally the nerve of a category of vertical
equivalence strings, and the actual spine map is an equivalence in every
bidegree. `SegalCompletenessCore` bundles this with vertical Kan and
completeness data. The full resource-process bicategory's cost-exact higher
localization is now constructed by
`CostExactZigzag.inclusion_isBicategoricalLocalization`. Full
non-groupoidal local mapping nerves are attached by
`HigherCompleteSegalCore` over the same total-model indices: the package stores
Rezk object vertices, exact 1-cell/2-cell decoding, preservation of
noninvertibility, strict Segal, quasicategory and 2-coskeletal local structure,
exact simplicial horizontal composition, natural associator and left/right
unitor isomorphisms, their induced genuine simplicial homotopies, and the
pointwise pentagon and triangle equations. The
selected equivalence category is now also explicitly equivalent to the actual
full subcategory of invertible outer arrows. The comparison commutes with
outer-degree-one inclusion, and the direct completeness map into that actual
subspace is the nerve of a category equivalence whose included map is
simplicially homotopic to real zero-degeneracy. Reedy infrastructure has now
started with a strict `Functor.IsIsofibration` lift object, identity and core-
inclusion instances, forward/reverse isomorphism lifting equations, and an
exact theorem for the lifted one-simplex under `nerveMap`. The all-dimensional
theorem is now compiled as well: dimension two is unique by groupoid
cancellation, dimensions at least three by categorical-nerve horn uniqueness,
and `Functor.nerveMap_fibration` packages the resulting Kan fibration.
The degree-one matching application is now compiled in literal outer-zero
coordinates. `degreeOneMatchingFunctor` is the pair of actual outer faces
`d₁,d₀` from `Core(ComposableArrows C 1)` to two copies of
`Core(ComposableArrows C 0)`. Endpoint conjugation gives a strict
isofibration, its nerve map is a Kan fibration, and both projected maps are
proved equal to the genuine outer faces. Explicit categorical-product and
nerve-product isomorphisms transport it to Mathlib's selected simplicial-set
binary product; the standard matching map is exactly `⟨d₁,d₀⟩` and
remains a Kan fibration. `DegreeOneReedyCore` packages these facts inside
`SegalCompletenessCore`. Degree two now uses an explicit
`TriangleBoundary C` category of three independent edges. A boundary extends
to a composable two-arrow diagram exactly when its long edge is the composite
of its short edges; restriction on maximal cores is a strict isofibration and
its nerve a Kan fibration. `DegreeTwoMatchingCore` packages this strict-image
representation and fibration inside `SegalCompletenessCore`. It also records
the hom-wise equivalence
`(T ⥤ TriangleBoundary C) ≃ TriangleBoundary (T ⥤ C)` for every test
category `T`. Comparison with
the abstract degree-two Reedy matching limit and dimensions at least three
remain. The abstract target is no longer implicit:
`simplicialSpaceBoundaryMatchingDiagram` now constructs it for every
simplicial space from the elements of `∂Δ[n]`; the actual boundary-restriction
cone is compiled, and its matching map is definitionally the universal limit
lift. `degreeTwoAbstractMatchingMap_eq_limitLift` specializes that equation to
the Rezk core diagram. A canonical map
`degreeTwoBoundaryToAbstractMatching` from the explicit triangular-boundary
nerve to the selected limit is now compiled, together with every cone `fac`
equation. The exact factorization
`degreeTwoBoundaryMap ≫ degreeTwoBoundaryToAbstractMatching =
degreeTwoAbstractMatchingMap` is proved, so compatibility with the two
degree-two matching maps is closed; invertibility of the comparison remains.
The three canonical face-index objects and projections
are explicit; they decode exactly to `δ₀,δ₁,δ₂`, and the comparison
commutes with all three. Three canonical vertex objects and all six
face-to-endpoint incidence morphisms are also explicit; cone naturality proves
the corresponding endpoint compatibility equations. The map
`TriangleBoundary.toBoundaryNerveMap` now encodes every explicit triangular
boundary as a full simplicial map `∂Δ[2] ⟶ nerve C`, including all degenerate
simplices and naturality under every simplex morphism. The reverse
`ofBoundaryNerveMap` decoder is also compiled: it extracts canonical vertices
and edges and uses incidence naturality to transport the edges to shared
endpoints. All three transported edge equalities and both full round trips are
proved. Every boundary simplex is factored through a canonical coface, and
`boundaryNerveEquiv` packages the exact representation
`TriangleBoundary C ≃ (∂Δ[2] ⟶ nerve C)`. The explicit boundary nerve is now
identified with the selected abstract degree-two Reedy limit. For every
vertical degree `k`,
`degreeTwoAbstractMatchingBoundaryMap` turns a matching-limit simplex into a
full boundary map in `nerve (EquivalenceString C k)`;
`triangleBoundaryEquivalenceStringEquiv` commutes triangular boundaries with
vertical equivalence strings, and
`degreeTwoBoundaryComparisonInverseApp` decodes and lifts the result back to
`nerve (Core (TriangleBoundary C))`. Both inverse laws are proved, every
comparison component is bijective, and
`degreeTwoBoundaryAbstractMatchingIso` promotes the canonical comparison to
an isomorphism. `DegreeTwoReedyCore` packages this result; matching dimensions
at least three remain. The higher-dimensional route is now uniform rather
than degree-specific: `abstractMatchingBoundaryMap` assembles every selected
degree-`n` matching simplex into a map
`∂Δ[n] ⟶ nerve (EquivalenceString C k)`, retains all limit projections, and
is injective. Its composite with `abstractMatchingMap` is exactly ordinary
categorical-nerve boundary restriction. The latter is proved injective in all
dimensions at least two. For `n ≥ 3`, every boundary is now filled by first
restricting it to an inner horn, applying the strict-Segal horn filler, and
recovering the omitted face from codimension-two compatibility. Thus
categorical-nerve boundary restriction and every high Rezk matching map are
bijective; `abstractMatchingMapHighIso` promotes them to simplicial-set
isomorphisms, and `HigherMatchingCore` packages all degrees at least three as
isomorphisms and Kan fibrations. Together with the degree-one and degree-two
packages, `SegalCompletenessCore` now contains the complete positive-degree
Reedy matching presentation.

### A bounded internal univalent layer

Deep syntax distinguishes internal identity from structural equivalence and
interprets both without adding external axioms. The compiled semantics include
a groupoid, object quotient, skeleton, Yoneda envelope, Kan simplicial nerve,
and a classifying diagram satisfying the project's explicit groupoidal
complete-Segal interface.

## Active frontier

The governing objective is a computable, machine-verifiable, univalent,
higher-categorical theory of resource-constrained information processes whose
classical probabilistic, quantum, causal, computational, semantic, and
thermodynamic realizations are connected by proved representation and
completeness theorems.

The first total higher category over varying resource algebras now compiles.
Its verified components are:

- ordered-additive resource reindexing for process, parallel, structural, and
  proof-carrying budget laws;
- resource-changing functors, identity-resource compatibility, composition,
  and budget transport;
- reindexed `ProcessModel` objects and heterogeneous strong braided model
  morphisms whose resource translations compose;
- monoidal 2-cells and vertical local categories over each fixed resource
  translation;
- total resource-model objects, heterogeneous horizontal composition and
  whiskering, interchange, associators, unitors, pentagon, and triangle;
- a Kan object-equivalence core with exact internal-equivalence/identity-edge
  correspondence, plus full local mapping nerves, vertical 2-simplices,
  horizontal-composition simplicial maps, a retained noninvertible 2-cell, and
  global Duskin triangles/tetrahedra with exact coherent-boundary filling;
- an all-dimensional global semi-simplicial Duskin nerve with strict
  restriction along every order embedding and exact low-dimensional recovery;
- a native full Duskin nerve of strictly unitary lax finite-ordinal diagrams,
  with every degeneracy, an identity-edge witness, tetrahedral coherence, and
  a natural coordinate-decoding map to the semi-simplicial nerve;
- a constructor-normal ordinal equivalence supporting the inverse coordinate
  representation, with all normalization clauses and the all-strict
  tetrahedral branch compiled;
- a common monoidal syntax whose costs can be translated into each model's
  native resource algebra, with reversible expression translation, an exact
  interpretation representation theorem, and translated free-model
  completeness;
- one literal Boolean-flip process signature with six model-specific
  interpretations and a kernel-checked cross-model agreement theorem;
- one three-interface two-stage signature with a checked six-model serial
  composition theorem;
- one common symmetric monoidal `flip ⊗ flip` signature with a checked
  six-model parallel theorem, exact computation-resource addition, and six
  canonical strong symmetric resource-changing free lifts upgraded to
  one-cells of the total resource-model bicategory;
- computable normal forms, exact singleton image representation, and absolute
  equality-reflection completeness for all six interpretations of that linear
  theory;
- one expose--erase signature with a checked six-model operational erasure,
  intervention, semantic-loss, and Landauer-payment theorem;
- one non-thin diamond with exact two-path image representation, a separation
  completeness criterion, and six separating complete interpretations;
- one multi-generator adaptive binary tree with finite positive-history normal
  forms, exact path budgets, recorded-channel representation and
  observational completeness, plus six native model realizations;
- variable-depth generator-dependent finite trees with dependent histories,
  exact supremum budgets, representation/completeness along explicit history
  equivalences, and a conservative binary embedding;
- the category of dependent branching algebras, initial tree algebra, unique
  fold, absolute equational completeness, sequential graft monoid, and
  algebraic height/budget representations;
- the cartesian symmetric monoidal category of branching model algebras,
  componentwise product-fold representation, exact simultaneous equality, and
  joint term-model completeness;
- binary tree-level independent parallel protocols with exact stochastic
  factorization, lane symmetry, additive resources, shared-boundary grafting,
  strict interchange, and parallel observational completeness;
- arbitrary finite dependent lane families with product normalization, exact
  n-ary factorization, dependent normal-form permutation coherence, strict
  interchange, and n-ary observational completeness;
- generic six-model realizations for every finite positive dependent normal
  form, with exact resource bounds, a full-support causal representation, and
  equality-reflection completeness at each stated operational boundary;
- universal exact finite semantic-order and all-task numeric-profile
  completeness for Blackwell dominance/equivalence, together with an
  executable one-task incompleteness witness;
- an intrinsic Gibbs-preserving channel-image theorem, unique thermal lifts,
  and externally targeted dependent-normal-form representation/completeness;
- fixed-DAG soft/stochastic/hard causal programs with computable reduced
  normal forms, exact model/channel representation, and equality-reflection
  completeness;
- explicit free-term/path-category equivalence, exact free-cost preservation,
  and path-faithful completeness for arbitrary typed sequential signatures;
- ordinary and resource-changing sequential initiality with contractible
  strict-extension types and global interpretation/free-source-functor
  classification, plus six canonical free lifts and translated cost bounds;
- an executable projection from `Fin 4 → Nat` computation resources to the
  single `Nat` step coordinate, upgraded to a model-level 1-cell with checked
  budget transport.

The next theorem-bearing layers are:

- prove scalable image characterizations for heterogeneous-carrier,
  graph-changing, or policy-dependent causal interventions, resource-bounded
  semantic profiles or richer/infinite task languages, and energy-resolved
  thermal-operation dilations;
- formulate and prove model-specific representation, conservativity, and
  completeness theorems, followed by genuinely cross-model comparison
  theorems;
- finish assembling the naturally isomorphic full coordinate/native Duskin
  nerve and locally coherent mapping nerves into a global complete-Segal
  2-space, construct the cost-exact bicategorical localization of the entire
  resource-process bicategory, and compare it through the generic higher
  local-nerve interface while keeping quotient representative choices outside
  executable models.

The parameterized walking-localization construction remains an active
supporting track. Its arbitrary lift now compiles as the genuine
`generalLiftPseudofunctor` for every destination bicategory. All sixteen
endpoint sequences have target, source, endpoint-transport, and all-arrow
associativity laws; endpoint and free-groupoid normalization prove the general
associativity equation. Compositor naturality and both unit laws are also
compiled, and restriction maps included source arrows exactly as the original
pseudofunctor. The two generator/retained normalization orders and their
mapped forms now satisfy the required binary product laws, removing the unit
subdiagrams from that proof in both orientations. Both orders also have
explicit compositor-plus-unitor factorizations before and after mapping, so
no opaque `Unit × A` normalization remains. Both forward factorization homs
now have unitor-normalized expansions, and product inverse unitors decompose
through factor unitors and associators. Eight symmetric HEq transport lemmas
now handle dependent left- and right-identity endpoints safely. Explicit
left- and right-identity-normalized source compositors satisfy their
transported associativity laws, and both forward factorizations are proved
multiplicative in retained products. Their mixed interchange square and the
resulting forward-sliding multiplication law are also proved, and mate
transfer now proves inverse-sliding multiplication. Explicit whisker exchange,
source normalization, seven-endpoint transport, and target normalization now
give the complete all-arrow retained/retained/inverse associativity law. The
corresponding mixed target, source, transport, and branch equations now also
give retained/inverse/retained associativity. The forward/retained/inverse
cancellation sequence now likewise has its direct-mate bridge, source law,
endpoint transport, branch selection, and exact all-arrow associativity
equation. Retained/forward/inverse is now complete as well, through its target,
source, endpoint-transport, and branch equations. Forward/inverse/retained is
also complete; its source square reduces to unit-insertion right-whiskering
coherence. Inverse/forward/retained is complete as well, using the dual
counit-insertion right-whiskering theorem. Inverse/retained/forward now also
compiles through target, source, endpoint transport, and all-arrow selection.
Retained/inverse/forward now also compiles through all four layers, using
reversed-adjunction mate inversion and split-left counit exchange.
Forward/inverse/forward and dual inverse/forward/inverse now compile through
all four layers using the two unit/counit triangle orientations. The remaining
source comparison and its inverse now form the adjoint equivalence
`generalLiftFactorization`. Consequently every marking-inverting source
pseudofunctor factors through the completion, and
`inclusion_isBicategoricalLocalization` packages marking inversion,
biessential factorization, and the local precomposition equivalence as a
complete bicategorical localization. This theorem is specific to the
parameterized walking example; the same three universal-property fields are
now also proved for the full resource-process presentation by
`CostExactZigzag.inclusion_isBicategoricalLocalization`.

`TotalModelWalkingLocalization` specializes this universal property to the
heterogeneous `ResourceModel` bicategory containing the six named model
objects. It deliberately retains the marking-inversion premise: the six
interpretation one-cells from shared syntax are not claimed to be adjoint
equivalences.

## Explicitly open or out of scope

- general measurable-space causal models and do-calculus completeness;
- a claim that formal step counts equal wall-clock runtime or hardware cost;
- irrational real probabilities in the executable finite stochastic core;
- a universal quantum copy operation;
- external univalence for Lean types;
- a Mathlib-native standard complete-Segal-space object using a completed
  weak-equivalence or Quillen-model API;
- a full Dwyer–Kan, simplicial, Rezk, or bicategorical localization theorem for
  the resource-process bicategory.

Open statements belong in [`CONJECTURES.md`](reference/CONJECTURES.md), not in Lean as
axioms or theorem declarations.

## Where to verify a claim

- Model operation or capability: [`MODEL_MATRIX.md`](reference/MODEL_MATRIX.md)
- Theorem type and dependencies: [`BLUEPRINT.md`](reference/BLUEPRINT.md)
- Kernel assumptions: [`AXIOMS.md`](reference/AXIOMS.md)
- Open research statement: [`CONJECTURES.md`](reference/CONJECTURES.md)
- Executable behavior: `Ript/Examples/` and `scripts/check-examples.sh`
- Merge readiness: `./scripts/quality-gate.sh`

This separation keeps the repository homepage readable while preserving the
full, auditable detail needed for formal research.
