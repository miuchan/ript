import Mathlib.Algebra.Order.Hom.Monoid
import Ript.Core.StructuralCost
import Ript.Resource.Budget

/-!
# Reindexing process costs along resource homomorphisms

Different process models need not measure resources in the same algebra.
An ordered additive homomorphism `φ : R →+o S` translates an `R`-valued cost
into an `S`-valued cost while preserving zero, addition, and resource bounds.
This file proves that sequential, parallel, structural, and budget laws all
survive that translation.
-/

set_option autoImplicit false

namespace Ript.Resource

open CategoryTheory
open MonoidalCategory
open Ript.Core

universe u v w₁ w₂

variable {C : Type u} [Category.{v} C]

section OrderedAdditive

variable {R : Type w₁} [AddCommMonoid R] [Preorder R]
variable {S : Type w₂} [AddCommMonoid S] [Preorder S]

/-- Push an `R`-valued process cost forward along an ordered additive
homomorphism.  This is executable whenever the original cost and resource
translation are executable. -/
@[instance_reducible]
def reindexProcessCost (φ : R →+o S) [HasProcessCost C R] :
    HasProcessCost C S where
  cost f := φ (processCost (R := R) f)
  cost_id X := by simp
  cost_comp f g := by
    calc
      φ (processCost (R := R) (f ≫ g)) ≤
          φ (processCost (R := R) f + processCost (R := R) g) :=
        OrderHomClass.monotone φ (processCost_comp f g)
      _ = φ (processCost (R := R) f) +
          φ (processCost (R := R) g) := by simp

/-- Reindexed process cost is pointwise application of the resource
homomorphism. -/
@[simp]
theorem reindexProcessCost_cost (φ : R →+o S) [HasProcessCost C R]
    {X Y : C} (f : X ⟶ Y) :
    (reindexProcessCost φ).cost f = φ (processCost (R := R) f) :=
  rfl

/-- Parallel subadditivity is stable under resource reindexing. -/
theorem reindexParallelProcessCost
    [MonoidalCategory C] (φ : R →+o S)
    [HasProcessCost C R] [HasParallelProcessCost C R] :
    @HasParallelProcessCost C _ _ S _ _
      (reindexProcessCost (C := C) (R := R) (S := S) φ) := by
  let _ : HasProcessCost C S :=
    reindexProcessCost (C := C) (R := R) (S := S) φ
  constructor
  intro X₁ Y₁ X₂ Y₂ f g
  change φ (processCost (R := R) (f ⊗ₘ g)) ≤
    φ (processCost (R := R) f) + φ (processCost (R := R) g)
  calc
    φ (processCost (R := R) (f ⊗ₘ g)) ≤
        φ (processCost (R := R) f + processCost (R := R) g) :=
      OrderHomClass.monotone φ (processCost_tensor f g)
    _ = φ (processCost (R := R) f) +
        φ (processCost (R := R) g) := by simp

/-- Zero-cost associators, unitors, and braidings remain free after resource
reindexing. -/
theorem reindexFreeStructuralCost
    [MonoidalCategory C] [SymmetricCategory C]
    (φ : R →+o S) [HasProcessCost C R] [HasFreeStructuralCost C R] :
    @HasFreeStructuralCost C _ _ _ S _ _
      (reindexProcessCost (C := C) (R := R) (S := S) φ) := by
  let _ : HasProcessCost C S :=
    reindexProcessCost (C := C) (R := R) (S := S) φ
  constructor
  · intro X Y Z
    change φ (processCost (R := R) (α_ X Y Z).hom) = 0
    simp
  · intro X Y Z
    change φ (processCost (R := R) (α_ X Y Z).inv) = 0
    simp
  · intro X
    change φ (processCost (R := R) (λ_ X).hom) = 0
    simp
  · intro X
    change φ (processCost (R := R) (λ_ X).inv) = 0
    simp
  · intro X
    change φ (processCost (R := R) (ρ_ X).hom) = 0
    simp
  · intro X
    change φ (processCost (R := R) (ρ_ X).inv) = 0
    simp
  · intro X Y
    change φ (processCost (R := R) (β_ X Y).hom) = 0
    simp

end OrderedAdditive

section Budgets

variable {R : Type w₁} [AddCommMonoid R] [PartialOrder R]
variable {S : Type w₂} [AddCommMonoid S] [PartialOrder S]
variable [HasProcessCost C R]

/-- A checked `R`-budget maps to a checked `S`-budget under resource
translation. -/
theorem withinBudget_reindex (φ : R →+o S)
    {X Y : C} {r : R} {f : X ⟶ Y}
    (hf : WithinBudget (R := R) r f) :
    @WithinBudget C _ S _ _ (reindexProcessCost φ) X Y (φ r) f :=
  OrderHomClass.monotone φ hf

/-- Reindex a packaged budgeted process together with its verified bound. -/
def reindexBudgetedHom (φ : R →+o S)
    {X Y : C} {r : R} (f : BudgetedHom (R := R) r X Y) :
    @BudgetedHom C _ S _ _ (reindexProcessCost φ) (φ r) X Y := by
  letI : HasProcessCost C S :=
    reindexProcessCost (C := C) (R := R) (S := S) φ
  exact
    { hom := f.hom
      within := OrderHomClass.monotone φ f.within }

@[simp]
theorem reindexBudgetedHom_hom (φ : R →+o S)
    {X Y : C} {r : R} (f : BudgetedHom (R := R) r X Y) :
    @BudgetedHom.hom C _ S _ _ (reindexProcessCost φ) (φ r) X Y
      (reindexBudgetedHom (C := C) (R := R) (S := S) φ f) = f.hom :=
  rfl

end Budgets

end Ript.Resource
