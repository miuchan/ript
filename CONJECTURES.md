# Conjectures and Unproved Research Statements

This register contains exact Lean propositions whose statements compile but
whose proofs are not yet kernel checked. An active entry must carry the marker
`FORMALIZED_BUT_UNPROVED` and identify the declaration that states it.

## Current register

There are currently no active `FORMALIZED_BUT_UNPROVED` propositions.

This does **not** mean that Ript's research program is complete. The open tracks
in the README and blueprint include broader measurable models, heterogeneous
causal systems, generic capability interfaces, richer cost models, and higher
localization. They are design and formalization work, not silently assumed
mathematical propositions.

The classifying-diagram track has discharged its former explicit matching
obligations. Ript proves a natural isomorphism of the whole outer diagram with
`n ↦ Map(Δ[n], N(M.Object))`, proves by presheaf density that
`Map(∂Δ[n], N(M.Object))` is the genuine boundary matching limit, identifies
boundary restriction with the universal limit lift, and proves every matching
map is a fibration. These facts are bundled in the project-local
`SSet.BoundaryReedyFibrant` interface. Ript now also proves every horizontal
row is the Kan nerve of a groupoid and packages both directions, strict outer
Segal data, genuine matching fibrations, and the actual completeness map's
`SSet.NerveEquivalenceWitness` in `SSet.GroupoidalCompleteSegal`. Remaining
work is broader infrastructure: the pinned Mathlib release has neither a
simplicial-set weak-equivalence class nor a completed Quillen model structure,
so a Mathlib-native standard complete-Segal instance cannot yet be stated.
The exact localization target is no longer informal: the compiled predicate
`Bicategory.MorphismProperty.IsBicategoricalLocalization` requires marked
1-morphisms to become adjoint equivalences, biessential factorization of every
inverting pseudofunctor, and equivalence on the local categories of strong
transformations and modifications. Its Ript specialization is
`IsCostExactBicategoricalLocalization`. What remains open is constructing a
pseudofunctor that satisfies this predicate for the full resource-process
bicategory; no existence proposition is silently assumed.

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
ambiguity for the next strong-transformation extension. That extension now
has explicit object components and a candidate strong-naturality isomorphism
for every target 1-morphism. Forward arrows reuse source naturality with an
arbitrary retained coordinate; reverse arrows compose an explicit invertible
mate with the retained-coordinate constraint; endpoint normal form covers all
target arrows. Naturality in every target 2-cell and the identity law are
compiled, as is composition coherence for every pair in the inclusion image
and hence every canonical forward-forward pair. A first mixed constructor is
also compiled: the inverse-generator mate followed by any retained-coordinate
constraint recovers the public constraint on its raw composite. The remaining
public-factor mixed compositions involving the freely adjoined inverse have
not yet been assembled; after those cases, the data can be packaged as a target
strong transformation. What also remains open is factorization of an
arbitrary nonseparable mixed-coordinate marking-inverting pseudofunctor outside
that closure, local essential surjectivity, and ultimately the
corresponding construction for the full resource-process bicategory.

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
