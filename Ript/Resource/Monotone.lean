import Ript.Core.Monotone
import Ript.Resource.Budget

/-!
# Budget transport along resource-nonincreasing functors

A resource-nonincreasing functor preserves every advertised budget, both as a
proposition and as packaged `BudgetedHom` data.
-/

set_option autoImplicit false

namespace Ript.Core.ResourceMonotoneFunctor

open CategoryTheory
open Ript.Resource

universe u₁ v₁ u₂ v₂ w

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {R : Type w} [AddCommMonoid R] [PartialOrder R]
variable [Ript.Core.HasProcessCost C R] [Ript.Core.HasProcessCost D R]

/-- A resource-nonincreasing functor maps a process within budget `r` to a
process within the same budget. -/
theorem map_withinBudget
    (F : Ript.Core.ResourceMonotoneFunctor C D R) {X Y : C} {r : R} {f : X ⟶ Y}
    (hf : WithinBudget r f) : WithinBudget r (F.toFunctor.map f) :=
  (F.map_cost_le f).trans hf

/-- Map a packaged budgeted morphism without enlarging its budget. -/
def mapBudgetedHom
    (F : Ript.Core.ResourceMonotoneFunctor C D R) {X Y : C} {r : R}
    (f : BudgetedHom r X Y) :
    BudgetedHom r (F.toFunctor.obj X) (F.toFunctor.obj Y) :=
  ⟨F.toFunctor.map f.hom, F.map_withinBudget f.within⟩

@[simp]
theorem mapBudgetedHom_hom
    (F : Ript.Core.ResourceMonotoneFunctor C D R) {X Y : C} {r : R}
    (f : BudgetedHom r X Y) :
    (F.mapBudgetedHom f).hom = F.toFunctor.map f.hom :=
  rfl

end Ript.Core.ResourceMonotoneFunctor
