import Ript.ForMathlib.AlgebraicTopology.GroupoidNerve
import Ript.ForMathlib.AlgebraicTopology.ReedyMatching
import Ript.ForMathlib.AlgebraicTopology.SSetHomotopyEquivalence
import Ript.ForMathlib.AlgebraicTopology.StrictSegalIso

/-!
# Groupoidal complete-Segal witnesses

The pinned Mathlib release defines cofibrations and Kan fibrations for
simplicial sets, but it does not yet define their weak equivalences or finish
the Quillen model structure.  Consequently the standard complete-Segal-space
predicate cannot honestly be stated with Mathlib's `WeakEquivalence` class.

This file records the strongest exact substitute needed by groupoidal
classifying diagrams. A completeness map has a `NerveEquivalenceWitness` when
it is, up to displayed isomorphisms, literally the nerve of an equivalence of
categories. Every such presentation now yields an explicit simplicial inverse
and genuine homotopies for both inverse laws.

`GroupoidalCompleteSegal` combines that evidence with genuine boundary
matching limits and fibrations, Kan vertical levels, and strict Segal/Kan
horizontal rows. No upstream weak-equivalence instance is assumed.
-/

set_option autoImplicit false

open CategoryTheory
open HomotopicalAlgebra
open Opposite
open Simplicial
open scoped SSet.modelCategoryQuillen

noncomputable section

universe u

namespace SSet

/-- A map of simplicial sets is presented, up to explicit isomorphisms, as the
nerve of an equivalence of categories.  This is stronger concrete evidence
than merely naming the map a weak equivalence. -/
structure NerveEquivalenceWitness {X Y : SSet.{u}} (f : X ⟶ Y) where
  /-- A categorical presentation of the source. -/
  source : Cat.{u, u}
  /-- A categorical presentation of the target. -/
  target : Cat.{u, u}
  /-- The equivalence whose nerve presents `f`. -/
  equivalence : source ≌ target
  /-- Identification of the displayed source with a categorical nerve. -/
  sourceIso : X ≅ CategoryTheory.nerve source
  /-- Identification of the displayed target with a categorical nerve. -/
  targetIso : Y ≅ CategoryTheory.nerve target
  /-- The actual map agrees with the nerve of the displayed equivalence. -/
  square : f ≫ targetIso.hom =
    sourceIso.hom ≫ CategoryTheory.nerveMap equivalence.functor

namespace NerveEquivalenceWitness

/-- The nerve of an equivalence carries its tautological categorical
equivalence witness. -/
def ofEquivalence {C D : Type u} [Category.{u} C] [Category.{u} D]
    (e : C ≌ D) : NerveEquivalenceWitness (CategoryTheory.nerveMap e.functor) where
  source := Cat.of C
  target := Cat.of D
  equivalence := e
  sourceIso := eqToIso (by rfl)
  targetIso := eqToIso (by rfl)
  square := by
    change CategoryTheory.nerveMap e.functor ≫ 𝟙 _ =
      𝟙 _ ≫ CategoryTheory.nerveMap e.functor
    rw [Category.comp_id, Category.id_comp]

/-- Every categorical nerve-equivalence presentation supplies an explicit
simplicial homotopy inverse, including both inverse laws as genuine
`SSet.Homotopy` values. -/
def homotopyEquivalence {X Y : SSet.{u}} {f : X ⟶ Y}
    (h : NerveEquivalenceWitness f) : HomotopyEquivalenceWitness f :=
  HomotopyEquivalenceWitness.transportIso
    (HomotopyEquivalenceWitness.ofCategoryEquivalence h.equivalence)
    h.sourceIso h.targetIso f h.square

end NerveEquivalenceWitness

/-- The horizontal simplicial set obtained from a simplicial space by fixing
the inner simplicial degree `k`. -/
abbrev horizontalRow (W : SimplicialObject SSet.{u}) (k : ℕ) : SSet.{u} :=
  W ⋙ SSet.evaluation.obj (op ⦋k⦌)

/-- Kan fibrancy transports backward along an isomorphism of simplicial sets. -/
theorem KanComplex.ofIso {X Y : SSet.{u}} (e : X ≅ Y) [KanComplex Y] :
    KanComplex X := by
  change Fibration (Limits.terminal.from X)
  have : Fibration (e.hom ≫ Limits.terminal.from Y) := inferInstance
  simpa using this

/-- Exact groupoidal complete-Segal data available without a simplicial weak
equivalence API. Boundary matching maps are genuine universal maps and
fibrations; every vertical level and horizontal row is a Kan complex; every
horizontal row is strict Segal; and the actual completeness map is presented
as the nerve of a category equivalence and hence has an explicit simplicial
homotopy inverse. -/
structure GroupoidalCompleteSegal (W : SimplicialObject SSet.{u}) where
  /-- Project-local Reedy fibrancy through genuine boundary matching limits. -/
  reedyFibrant : BoundaryReedyFibrant W
  /-- Each value of the simplicial space is a Kan complex. -/
  levelKan : ∀ Δ, KanComplex (W.obj Δ)
  /-- Every horizontal row satisfies the strict Segal condition. -/
  horizontalStrictSegal : ∀ k, StrictSegal (horizontalRow W k)
  /-- Every horizontal row is groupoidal, expressed by Kan fibrancy. -/
  horizontalKan : ∀ k, KanComplex (horizontalRow W k)
  /-- The actual outer zero-degeneracy is the nerve of a category equivalence. -/
  completeness : NerveEquivalenceWitness (W.σ (0 : Fin 1))

namespace GroupoidalCompleteSegal

variable {W : SimplicialObject SSet.{u}} (h : GroupoidalCompleteSegal W)

/-- The genuine degree-`n` matching cone supplied by the complete-Segal
witness. -/
abbrev matchingCone (n : ℕ) := h.reedyFibrant.matchingCone n

/-- The matching cone satisfies the categorical limit universal property. -/
def matchingConeIsLimit (n : ℕ) : Limits.IsLimit (h.matchingCone n) :=
  h.reedyFibrant.matchingConeIsLimit n

/-- Every matching map supplied by the complete-Segal witness is a
fibration. -/
theorem matchingMap_fibration (n : ℕ) :
    Fibration (h.reedyFibrant.matchingMap n) :=
  h.reedyFibrant.matchingMap_fibration n

/-- The displayed completeness map is not merely presented by a category
equivalence: it has an explicit simplicial homotopy inverse. -/
def completenessHomotopyEquivalence :
    HomotopyEquivalenceWitness (W.σ (0 : Fin 1)) :=
  h.completeness.homotopyEquivalence

end GroupoidalCompleteSegal

end SSet
