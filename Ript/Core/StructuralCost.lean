import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Ript.Core.ParallelCost

/-!
# Costs of monoidal structure morphisms

Resource accounting normally treats associators, unitors, and symmetry as
representation-level rewiring. `HasFreeStructuralCost` records that policy as
an optional capability instead of forcing it on every costed category.
-/

set_option autoImplicit false

namespace Ript.Core

open CategoryTheory
open MonoidalCategory

universe u v w

/-- A symmetric monoidal costed category has free structural rewiring when all
associators, unitors, and braidings have zero process cost. -/
class HasFreeStructuralCost (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] (R : Type w) [AddCommMonoid R] [Preorder R]
    [HasProcessCost C R] where
  /-- Forward associators cost zero. -/
  cost_associator : ∀ X Y Z : C,
    processCost (R := R) (α_ X Y Z).hom = 0
  /-- Inverse associators cost zero. -/
  cost_associator_inv : ∀ X Y Z : C,
    processCost (R := R) (α_ X Y Z).inv = 0
  /-- Forward left unitors cost zero. -/
  cost_leftUnitor : ∀ X : C, processCost (R := R) (λ_ X).hom = 0
  /-- Inverse left unitors cost zero. -/
  cost_leftUnitor_inv : ∀ X : C, processCost (R := R) (λ_ X).inv = 0
  /-- Forward right unitors cost zero. -/
  cost_rightUnitor : ∀ X : C, processCost (R := R) (ρ_ X).hom = 0
  /-- Inverse right unitors cost zero. -/
  cost_rightUnitor_inv : ∀ X : C, processCost (R := R) (ρ_ X).inv = 0
  /-- Symmetry morphisms cost zero. -/
  cost_braiding : ∀ X Y : C, processCost (R := R) (β_ X Y).hom = 0

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {R : Type w} [AddCommMonoid R] [Preorder R] [HasProcessCost C R]
variable [HasFreeStructuralCost C R]

/-- Forward associators have zero process cost. -/
@[simp]
theorem processCost_associator (X Y Z : C) :
    processCost (R := R) (α_ X Y Z).hom = 0 :=
  HasFreeStructuralCost.cost_associator X Y Z

/-- Inverse associators have zero process cost. -/
@[simp]
theorem processCost_associator_inv (X Y Z : C) :
    processCost (R := R) (α_ X Y Z).inv = 0 :=
  HasFreeStructuralCost.cost_associator_inv X Y Z

/-- Forward left unitors have zero process cost. -/
@[simp]
theorem processCost_leftUnitor (X : C) :
    processCost (R := R) (λ_ X).hom = 0 :=
  HasFreeStructuralCost.cost_leftUnitor X

/-- Inverse left unitors have zero process cost. -/
@[simp]
theorem processCost_leftUnitor_inv (X : C) :
    processCost (R := R) (λ_ X).inv = 0 :=
  HasFreeStructuralCost.cost_leftUnitor_inv X

/-- Forward right unitors have zero process cost. -/
@[simp]
theorem processCost_rightUnitor (X : C) :
    processCost (R := R) (ρ_ X).hom = 0 :=
  HasFreeStructuralCost.cost_rightUnitor X

/-- Inverse right unitors have zero process cost. -/
@[simp]
theorem processCost_rightUnitor_inv (X : C) :
    processCost (R := R) (ρ_ X).inv = 0 :=
  HasFreeStructuralCost.cost_rightUnitor_inv X

/-- Symmetry morphisms have zero process cost. -/
@[simp]
theorem processCost_braiding (X Y : C) :
    processCost (R := R) (β_ X Y).hom = 0 :=
  HasFreeStructuralCost.cost_braiding X Y

end Ript.Core
