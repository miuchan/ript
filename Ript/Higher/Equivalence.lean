import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Ript.Higher.Coherence

/-!
# Cost-exact model equivalences

A model equivalence in the bicategorical sense need not preserve numerical
costs exactly: `ModelHom` only requires the forward inequality.  This file
makes the missing condition explicit.  A cost-reflecting model morphism is
both resource-nonincreasing and resource-nondecreasing, hence cost-exact.
Adding that property in both directions to a bicategorical equivalence yields
a model equivalence that preserves budgets and the serial/parallel core laws
with exactly the same resource values.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Higher

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.MonoidalCategory
open Ript.Core

universe u v w

variable {R : Type w} [AddCommMonoid R] [PartialOrder R]
variable {M N : ProcessModel.{u, v, w} R}

/-- A model morphism reflects costs when it cannot make a process appear
strictly cheaper.  Together with `ModelHom.map_cost_le`, this gives equality. -/
class CostReflecting (F : M ⟶ N) : Prop where
  /-- Source cost is bounded by the cost of the mapped process. -/
  map_cost_ge : ∀ {X Y : M} (f : X ⟶ Y),
    processCost (R := R) f ≤ processCost (R := R) (F.toFunctor.map f)

namespace ModelHom

variable {P : ProcessModel.{u, v, w} R}
variable (F : M ⟶ N)

/-- The identity model morphism reflects costs. -/
instance idCostReflecting (M : ProcessModel.{u, v, w} R) :
    CostReflecting (ModelHom.id M) :=
  ⟨fun _ ↦ le_rfl⟩

/-- Cost reflection is closed under composition. -/
instance compCostReflecting (F : M ⟶ N) (G : N ⟶ P)
    [CostReflecting F] [CostReflecting G] :
    CostReflecting (ModelHom.comp F G) where
  map_cost_ge f :=
    (CostReflecting.map_cost_ge (F := F) f).trans
      (CostReflecting.map_cost_ge (F := G) (F.toFunctor.map f))

/-- A resource-nonincreasing, cost-reflecting model morphism preserves every
process cost exactly. -/
theorem map_cost_eq [CostReflecting F] {X Y : M} (f : X ⟶ Y) :
    processCost (R := R) (F.toFunctor.map f) = processCost (R := R) f :=
  le_antisymm (F.map_cost_le f) (CostReflecting.map_cost_ge f)

/-- Exact model morphisms preserve every budget predicate. -/
theorem map_cost_le_iff [CostReflecting F] {X Y : M} (f : X ⟶ Y) (budget : R) :
    processCost (R := R) (F.toFunctor.map f) ≤ budget ↔
      processCost (R := R) f ≤ budget := by
  rw [F.map_cost_eq f]

/-- The serial core bound is transported with the original source costs. -/
theorem map_comp_cost_le [CostReflecting F] {X Y Z : M}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    processCost (R := R) (F.toFunctor.map (f ≫ g)) ≤
      processCost (R := R) f + processCost (R := R) g := by
  rw [F.map_cost_eq]
  exact processCost_comp f g

/-- The parallel core bound is transported with the original source costs. -/
theorem map_tensor_cost_le [CostReflecting F] {X₁ Y₁ X₂ Y₂ : M}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    processCost (R := R) (F.toFunctor.map (f ⊗ₘ g)) ≤
      processCost (R := R) f + processCost (R := R) g := by
  rw [F.map_cost_eq]
  exact processCost_tensor f g

end ModelHom

/-- A bicategorical model equivalence whose forward and inverse model
morphisms both reflect costs.  The additional hypotheses are explicit because
ordinary monoidal natural isomorphisms do not, by themselves, constrain the
cost assigned to their components. -/
structure CostExactModelEquivalence (M N : ProcessModel.{u, v, w} R)
    extends Bicategory.Equivalence M N where
  /-- The forward equivalence morphism reflects costs. -/
  hom_cost_reflecting : CostReflecting toEquivalence.hom
  /-- The inverse equivalence morphism reflects costs. -/
  inv_cost_reflecting : CostReflecting toEquivalence.inv

namespace CostExactModelEquivalence

instance (e : CostExactModelEquivalence M N) : CostReflecting e.toEquivalence.hom :=
  e.hom_cost_reflecting

instance (e : CostExactModelEquivalence M N) : CostReflecting e.toEquivalence.inv :=
  e.inv_cost_reflecting

/-- The forward direction of a cost-exact model equivalence preserves costs. -/
theorem hom_map_cost_eq (e : CostExactModelEquivalence M N) {X Y : M} (f : X ⟶ Y) :
    processCost (R := R) (e.toEquivalence.hom.toFunctor.map f) =
      processCost (R := R) f :=
  e.toEquivalence.hom.map_cost_eq f

/-- The inverse direction of a cost-exact model equivalence preserves costs. -/
theorem inv_map_cost_eq (e : CostExactModelEquivalence M N) {X Y : N} (f : X ⟶ Y) :
    processCost (R := R) (e.toEquivalence.inv.toFunctor.map f) =
      processCost (R := R) f :=
  e.toEquivalence.inv.map_cost_eq f

/-- Identity is a cost-exact model equivalence. -/
def id (M : ProcessModel.{u, v, w} R) : CostExactModelEquivalence M M where
  toEquivalence := Bicategory.Equivalence.id M
  hom_cost_reflecting := ⟨fun _ ↦ le_rfl⟩
  inv_cost_reflecting := ⟨fun _ ↦ le_rfl⟩

end CostExactModelEquivalence

end Ript.Higher
