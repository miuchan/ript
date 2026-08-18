import Ript.Higher.ResourceChange
import Ript.Models.Computation.Total

/-!
# Executable resource reindexing

This example starts with the four-dimensional resource vector used by total
computations and projects it to a single natural-number step count.  The
projection is not an informal reporting convention: it is an ordered additive
homomorphism, so generic process costs and proof-carrying budgets are reindexed
by the theorems in `Ript.Resource.Reindexing`.
-/

set_option autoImplicit false

namespace Ript.Examples.ResourceReindexing

open CategoryTheory
open Ript.Core
open Ript.Models.Computation
open Ript.Resource

/-- Boolean values regarded as objects of the executable total-computation
category. -/
abbrev bit : Ript.Models.Computation.Total.Object :=
  Ript.Models.Computation.Total.Object.of Bool

/-- An executable Boolean negation declaring three steps and one gate. -/
def countedNot : bit ⟶ bit :=
  Ript.Models.Computation.Total.mk (!·) (ComputationResource.of 3 0 0 1)

/-- The `Nat`-valued cost is obtained canonically by projecting the original
four-dimensional cost to its step coordinate. -/
local instance stepProcessCost :
    HasProcessCost Ript.Models.Computation.Total.Object Nat :=
  reindexProcessCost ComputationResource.stepsHom

@[simp]
theorem countedNot_step_cost :
    processCost (R := Nat) countedNot = 3 :=
  rfl

/-- Reindexed sequential composition remains exactly additive in this model. -/
@[simp]
theorem countedNot_twice_step_cost :
    processCost (R := Nat) (countedNot ≫ countedNot) = 6 :=
  rfl

/-- The original computation packaged with its complete vector budget. -/
def vectorBudgetedNot :
    BudgetedHom (R := ComputationResource)
      (ComputationResource.of 3 0 0 1) bit bit :=
  ⟨countedNot, le_rfl⟩

/-- The same process and proof are transported to the single-valued step
budget by generic resource reindexing. -/
def stepBudgetedNot : BudgetedHom (R := Nat) 3 bit bit :=
  reindexBudgetedHom ComputationResource.stepsHom vectorBudgetedNot

@[simp]
theorem stepBudgetedNot_hom : stepBudgetedNot.hom = countedNot :=
  rfl

/-- An executable decision procedure for the projected step budget. -/
def withinStepBudget {X Y : Ript.Models.Computation.Total.Object}
    (budget : Nat) (f : X ⟶ Y) : Bool :=
  decide (processCost (R := Nat) f ≤ budget)

/-- The declared three-step computation passes budget three. -/
example : withinStepBudget 3 countedNot = true := by
  native_decide

/-- The same computation fails the strictly smaller budget two. -/
example : withinStepBudget 2 countedNot = false := by
  native_decide

/-- Two sequential executions pass the additively transported budget six. -/
example : withinStepBudget 6 (countedNot ≫ countedNot) = true := by
  native_decide

#eval withinStepBudget 3 countedNot
#eval withinStepBudget 2 countedNot
#eval withinStepBudget 6 (countedNot ≫ countedNot)

end Ript.Examples.ResourceReindexing
