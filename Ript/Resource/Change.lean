import Ript.Core.ResourceChange
import Ript.Resource.Budget

/-!
# Budget transport across resource algebras

A resource-changing functor sends a checked source budget `r : R` to the
checked target budget `φ r : S`.  Thus comparison between heterogeneous models
preserves executable budget certificates rather than merely relating raw cost
values.
-/

set_option autoImplicit false

namespace Ript.Core.ResourceChangeFunctor

open CategoryTheory
open Ript.Resource

universe u₁ v₁ u₂ v₂ w₁ w₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {R : Type w₁} [AddCommMonoid R] [PartialOrder R]
variable {S : Type w₂} [AddCommMonoid S] [PartialOrder S]
variable [HasProcessCost C R] [HasProcessCost D S]

/-- Mapping a process transports its verified source budget through the
resource homomorphism. -/
theorem map_withinBudget {φ : R →+o S}
    (F : ResourceChangeFunctor C D R S φ)
    {X Y : C} {r : R} {f : X ⟶ Y}
    (hf : WithinBudget (R := R) r f) :
    WithinBudget (R := S) (φ r) (F.toFunctor.map f) :=
  (F.map_cost_le f).trans (OrderHomClass.monotone φ hf)

/-- Map a packaged process and its budget certificate across resource
algebras. -/
def mapBudgetedHom {φ : R →+o S}
    (F : ResourceChangeFunctor C D R S φ)
    {X Y : C} {r : R} (f : BudgetedHom (R := R) r X Y) :
    BudgetedHom (R := S) (φ r) (F.toFunctor.obj X) (F.toFunctor.obj Y) :=
  ⟨F.toFunctor.map f.hom, F.map_withinBudget f.within⟩

@[simp]
theorem mapBudgetedHom_hom {φ : R →+o S}
    (F : ResourceChangeFunctor C D R S φ)
    {X Y : C} {r : R} (f : BudgetedHom (R := R) r X Y) :
    (F.mapBudgetedHom f).hom = F.toFunctor.map f.hom :=
  rfl

end Ript.Core.ResourceChangeFunctor
