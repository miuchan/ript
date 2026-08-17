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
so a Mathlib-native standard complete-Segal instance cannot yet be stated. A
localization universal property that retains the full resource-process
bicategory's 2-cell data also remains open research rather than a silently
assumed proposition.

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
this formally witnesses why the current bridge cannot retain all 2-cells. The
open localization problem is specifically the higher or bicategorical
localization with a universal property that retains that full 2-cell
structure.

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
