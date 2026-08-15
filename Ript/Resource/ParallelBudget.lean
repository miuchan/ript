import Ript.Core.ParallelCost
import Ript.Resource.Budget

/-!
# Parallel budget composition

Budgeted morphisms tensor in parallel by adding their advertised resource
bounds.
-/

set_option autoImplicit false

namespace Ript.Resource

open CategoryTheory
open MonoidalCategory
open Ript.Core

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {R : Type w} [AddCommMonoid R] [PartialOrder R] [ResourceAlgebra R]
variable [HasProcessCost C R] [HasParallelProcessCost C R]

/-- Parallel composition adds the budgets of its two component processes. -/
theorem budgeted_tensor {X₁ Y₁ X₂ Y₂ : C} {r s : R}
    {f : X₁ ⟶ Y₁} {g : X₂ ⟶ Y₂}
    (hf : WithinBudget r f) (hg : WithinBudget s g) :
    WithinBudget (r + s) (f ⊗ₘ g) := by
  exact (processCost_tensor f g).trans (add_le_add_resources hf hg)

/-- Tensor two packaged budgeted morphisms. -/
def BudgetedHom.tensor {X₁ Y₁ X₂ Y₂ : C} {r s : R}
    (f : BudgetedHom r X₁ Y₁) (g : BudgetedHom s X₂ Y₂) :
    BudgetedHom (r + s) (X₁ ⊗ X₂) (Y₁ ⊗ Y₂) :=
  ⟨f.hom ⊗ₘ g.hom, budgeted_tensor f.within g.within⟩

end Ript.Resource
