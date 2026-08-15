import Ript.Core.CostedProcess
import Ript.Resource.Basic

/-!
# Budgeted sequential morphisms

This file packages morphisms whose process cost is bounded by a resource
budget and proves the stage-1 identity, composition, and weakening laws.
-/

set_option autoImplicit false

namespace Ript.Resource

open CategoryTheory
open Ript.Core

universe u v w

variable {C : Type u} [Category.{v} C]
variable {R : Type w} [AddCommMonoid R] [PartialOrder R] [ResourceAlgebra R]
variable [HasProcessCost C R]

/-- `WithinBudget r f` means that process `f` costs at most `r`. -/
def WithinBudget {X Y : C} (r : R) (f : X ⟶ Y) : Prop :=
  processCost (R := R) f ≤ r

/-- A morphism together with a checked upper bound on its resource cost. -/
structure BudgetedHom (r : R) (X Y : C) where
  /-- The underlying process. -/
  hom : X ⟶ Y
  /-- Evidence that the process lies within the advertised budget. -/
  within : WithinBudget r hom

omit [ResourceAlgebra R] in
/-- Identity morphisms are available at zero budget. -/
theorem budgeted_id (X : C) : WithinBudget (0 : R) (𝟙 X) := by
  simp [WithinBudget]

/-- Budgets add when two budgeted processes are composed sequentially. -/
theorem budgeted_comp {X Y Z : C} {r s : R} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : WithinBudget r f) (hg : WithinBudget s g) :
    WithinBudget (r + s) (f ≫ g) := by
  exact (processCost_comp f g).trans (add_le_add_resources hf hg)

/-- The zero-budget identity as a packaged budgeted morphism. -/
def BudgetedHom.id (X : C) : BudgetedHom (0 : R) X X :=
  ⟨𝟙 X, budgeted_id X⟩

/-- Sequential composition of packaged budgeted morphisms. -/
def BudgetedHom.comp {X Y Z : C} {r s : R}
    (f : BudgetedHom r X Y) (g : BudgetedHom s Y Z) :
    BudgetedHom (r + s) X Z :=
  ⟨f.hom ≫ g.hom, budgeted_comp f.within g.within⟩

omit [ResourceAlgebra R] in
/-- A process remains available when its budget is enlarged. -/
theorem WithinBudget.mono {X Y : C} {r s : R} {f : X ⟶ Y}
    (hf : WithinBudget r f) (hrs : r ≤ s) : WithinBudget s f :=
  hf.trans hrs

/-- Enlarge the advertised budget of a packaged process. -/
def BudgetedHom.weaken {X Y : C} {r s : R} (f : BudgetedHom r X Y)
    (hrs : r ≤ s) : BudgetedHom s X Y :=
  ⟨f.hom, f.within.mono hrs⟩

end Ript.Resource
