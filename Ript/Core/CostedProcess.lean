import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.CategoryTheory.Category.Basic

/-!
# Sequential processes with resource costs

`HasProcessCost` equips the morphisms of an ordinary category with a lax
additive cost. No tensor, copying, or discarding capability is assumed.
-/

set_option autoImplicit false

namespace Ript.Core

open CategoryTheory

universe u v w

/-- A category has process costs in `R` when identities cost zero and the cost
of sequential composition is bounded by the sum of component costs. -/
class HasProcessCost (C : Type u) [Category.{v} C] (R : Type w)
    [AddCommMonoid R] [Preorder R] where
  /-- The resource cost assigned to a process. -/
  cost : {X Y : C} → (X ⟶ Y) → R
  /-- Identity processes have zero cost. -/
  cost_id : ∀ X : C, cost (𝟙 X) = 0
  /-- Sequential composition is subadditive. -/
  cost_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    cost (f ≫ g) ≤ cost f + cost g

variable {C : Type u} [Category.{v} C]
variable {R : Type w} [AddCommMonoid R] [Preorder R]

/-- The cost of a morphism in a category carrying `HasProcessCost`. -/
def processCost [HasProcessCost C R] {X Y : C} (f : X ⟶ Y) : R :=
  HasProcessCost.cost f

variable [HasProcessCost C R]

/-- Unfolding the cost law for an identity process. -/
@[simp]
theorem processCost_id (X : C) : processCost (R := R) (𝟙 X) = 0 :=
  HasProcessCost.cost_id X

/-- Unfolding the subadditive cost law for sequential composition. -/
theorem processCost_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    processCost (R := R) (f ≫ g) ≤
      processCost (R := R) f + processCost (R := R) g :=
  HasProcessCost.cost_comp f g

end Ript.Core
