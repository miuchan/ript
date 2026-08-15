import Mathlib.CategoryTheory.Monoidal.Category
import Ript.Core.CostedProcess

/-!
# Parallel process costs

`HasParallelProcessCost` is an optional capability on top of sequential process
costs. It requires only that tensoring two processes costs no more than the sum
of their costs; no copying, discarding, or classical structure is implied.
-/

set_option autoImplicit false

namespace Ript.Core

open CategoryTheory
open MonoidalCategory

universe u v w

/-- A monoidal process category has subadditive parallel costs when tensoring
two morphisms costs at most the sum of their individual costs. -/
class HasParallelProcessCost (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (R : Type w) [AddCommMonoid R] [Preorder R] [HasProcessCost C R] where
  /-- Tensor product is subadditive with respect to process cost. -/
  cost_tensor : ∀ {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
    processCost (R := R) (f ⊗ₘ g) ≤
      processCost (R := R) f + processCost (R := R) g

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {R : Type w} [AddCommMonoid R] [Preorder R]
variable [HasProcessCost C R] [HasParallelProcessCost C R]

/-- Unfolding the subadditive law for parallel composition. -/
theorem processCost_tensor {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    processCost (R := R) (f ⊗ₘ g) ≤
      processCost (R := R) f + processCost (R := R) g :=
  HasParallelProcessCost.cost_tensor f g

end Ript.Core
