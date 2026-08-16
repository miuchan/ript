import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Order.Lattice.Nat
import Ript.Examples.BitProcesses
import Ript.Resource.Filtration

/-!
# Executable cost-filtration reconstruction

This example defines a natural-number filtration directly from the declared
units carried by metered finite functions.  It proves that attained-infimum
reconstruction returns those units exactly, packages the reconstruction as a
valid process cost, and checks the budget layers of double Boolean negation.
-/

set_option autoImplicit false

namespace Ript.Examples.CostFiltration

open CategoryTheory
open Ript.Core
open Ript.Models.FiniteFunction
open Ript.Resource
open Ript.Semantics

/-- The direct filtration in which a metered function is available precisely
when its declared units fit within the budget. -/
def declaredUnitsFiltration : AttainedHomFiltration Metered Nat where
  toHomFiltration := {
    Mem := fun r f ↦ f.units ≤ r
    mono := fun hf hrs ↦ hf.trans hrs
    id_mem := fun _ ↦ Nat.zero_le 0
    comp_mem := by
      intro X Y Z r s f g hf hg
      exact Nat.add_le_add hf hg
  }
  minimum f := f.units
  minimum_mem _ := le_rfl
  minimum_le _ _ h := h

/-- Every metered function has an attained least budget equal to its declared
number of units. -/
theorem declaredUnitsFiltration_attained {X Y : Metered} (f : X ⟶ Y) :
    IsLeast (declaredUnitsFiltration.toHomFiltration.budgets f)
      (declaredUnitsFiltration.minimum f) :=
  declaredUnitsFiltration.minimum_isLeast f

/-- Infimum reconstruction of the direct filtration recovers the declared
units exactly. -/
theorem declaredUnitsCost_eq_units {X Y : Metered} (f : X ⟶ Y) :
    filtrationToCost declaredUnitsFiltration f = f.units := by
  rfl

/-- The cost structure reconstructed from the direct filtration. -/
@[instance_reducible]
def reconstructedProcessCost : HasProcessCost Metered Nat :=
  filtrationToProcessCost declaredUnitsFiltration rfl

/-- The reconstructed process-cost structure reads exactly the stored units. -/
theorem reconstructedProcessCost_eq_units {X Y : Metered} (f : X ⟶ Y) :
    reconstructedProcessCost.cost f = f.units :=
  declaredUnitsCost_eq_units f

/-- Double Boolean negation evaluated in the metered finite-function model. -/
def doubleNegation :
    (BitProcesses.meteredInterpretation.obj .bit ⟶
      BitProcesses.meteredInterpretation.obj .bit) :=
  eval BitProcesses.meteredInterpretation BitProcesses.notNot

/-- Double negation is available at exactly two declared units. -/
theorem doubleNegation_units : doubleNegation.units = 2 := by
  decide

/-- Double negation belongs to the two-unit filtration layer. -/
theorem doubleNegation_within_two :
    declaredUnitsFiltration.Mem 2 doubleNegation := by
  change doubleNegation.units ≤ 2
  decide

/-- Double negation does not belong to the one-unit filtration layer. -/
theorem doubleNegation_not_within_one :
    ¬ declaredUnitsFiltration.Mem 1 doubleNegation := by
  change ¬ doubleNegation.units ≤ 1
  decide

-- Executable exact-layer check.
#eval decide (doubleNegation.units ≤ 2)

-- Executable rejection below the least budget.
#eval decide (¬ doubleNegation.units ≤ 1)

end Ript.Examples.CostFiltration
