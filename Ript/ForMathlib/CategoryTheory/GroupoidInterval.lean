import Mathlib.CategoryTheory.ComposableArrows.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Products.Basic

/-!
# Finite ordered diagrams in a groupoid

For a groupoid `C`, the functor sending an object to the constant diagram on
any nonempty finite ordinal is an equivalence

`C ≌ (Fin (n + 1) ⥤ C)`.

An inverse evaluates a diagram at its initial vertex. The counit contracts the
diagram to that vertex by using the unique maps `0 ⟶ i`; these components are
invertible precisely because `C` is a groupoid. The walking-arrow case is the
categorical ingredient in the completeness comparison for Rezk's classifying
diagram of a groupoid.
-/

set_option autoImplicit false

namespace CategoryTheory

open Category

universe v u

namespace Groupoid

variable (C : Type u) [Category.{v} C] [IsGroupoid C]

/-- The constant `n`-simplex diagram on an object of `C`. -/
abbrev constantDiagramFunctor (n : ℕ) : C ⥤ ComposableArrows C n :=
  Functor.const (Fin (n + 1))

/-- Evaluate an `n`-simplex diagram at its initial vertex. -/
abbrev zeroEvaluationFunctor (n : ℕ) : ComposableArrows C n ⥤ C :=
  (evaluation (Fin (n + 1)) C).obj 0

/-- A finite nonempty linearly ordered diagram in a groupoid is naturally
isomorphic to the constant diagram at its initial vertex. -/
noncomputable def zeroConstantIso (n : ℕ) (F : ComposableArrows C n) :
    (constantDiagramFunctor C n).obj (F.obj 0) ≅ F :=
  NatIso.ofComponents
    (fun i ↦ asIso (F.map (homOfLE (Fin.zero_le i))))
    (fun {i j} f ↦ by
      dsimp
      rw [Category.id_comp, ← F.map_comp]
      congr)

/-- The initial-vertex contractions assemble naturally over the diagram
category. -/
noncomputable def zeroConstantNatIso (n : ℕ) :
    zeroEvaluationFunctor C n ⋙ constantDiagramFunctor C n ≅
      𝟭 (ComposableArrows C n) :=
  NatIso.ofComponents
    (zeroConstantIso C n)
    (fun η ↦ by
      apply NatTrans.ext
      funext i
      exact (η.naturality (homOfLE (Fin.zero_le i))).symm)

/-- Constant finite nonempty diagrams in a groupoid are equivalent to the
underlying groupoid, with initial-vertex evaluation as inverse. -/
noncomputable def constantDiagramEquivalence (n : ℕ) :
    C ≌ ComposableArrows C n :=
  Equivalence.mk
    (constantDiagramFunctor C n)
    (zeroEvaluationFunctor C n)
    (Functor.constCompEvaluationObj C (0 : Fin (n + 1))).symm
    (zeroConstantNatIso C n)

@[simp]
theorem constantDiagramEquivalence_functor (n : ℕ) :
    (constantDiagramEquivalence C n).functor = constantDiagramFunctor C n :=
  rfl

@[simp]
theorem constantDiagramEquivalence_inverse (n : ℕ) :
    (constantDiagramEquivalence C n).inverse = zeroEvaluationFunctor C n :=
  rfl

/-- The constant walking-arrow diagram on an object of `C`. -/
abbrev identityArrowFunctor : C ⥤ ComposableArrows C 1 :=
  constantDiagramFunctor C 1

/-- Evaluate a walking-arrow diagram at its source. -/
abbrev sourceEvaluationFunctor : ComposableArrows C 1 ⥤ C :=
  zeroEvaluationFunctor C 1

/-- A walking arrow in a groupoid is naturally isomorphic to the constant
walking arrow at its source. -/
noncomputable def sourceConstantIso (F : ComposableArrows C 1) :
    (identityArrowFunctor C).obj (F.obj 0) ≅ F :=
  zeroConstantIso C 1 F

/-- The source contractions assemble naturally over the category of walking
arrows. -/
noncomputable def sourceConstantNatIso :
    sourceEvaluationFunctor C ⋙ identityArrowFunctor C ≅
      𝟭 (ComposableArrows C 1) :=
  zeroConstantNatIso C 1

/-- Sending an object of a groupoid to its identity walking arrow is an
equivalence of categories, with source evaluation as inverse. -/
noncomputable def identityArrowEquivalence :
    C ≌ ComposableArrows C 1 :=
  constantDiagramEquivalence C 1

@[simp]
theorem identityArrowEquivalence_functor :
    (identityArrowEquivalence C).functor = identityArrowFunctor C :=
  rfl

@[simp]
theorem identityArrowEquivalence_inverse :
    (identityArrowEquivalence C).inverse = sourceEvaluationFunctor C :=
  rfl

end Groupoid

end CategoryTheory
