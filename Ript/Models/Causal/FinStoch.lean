import Ript.Models.Causal.Intervention

/-!
# Exact finite stochastic semantics for causal models

Every local mechanism is an exact `FinStoch` channel from parent assignments
to the node value.  The normalized observational and interventional joint
distributions are exposed as stochastic states from the tensor unit.
-/

set_option autoImplicit false

namespace Ript.Models.Causal

open scoped BigOperators

open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic

universe u

namespace Mechanism

variable {n : Nat} {Value : Type u} [Fintype Value] [DecidableEq Value]
  {graph : FiniteDAG n} {node : Fin n}

/-- Interpret a local causal mechanism as an exact finite stochastic channel
from parent assignments to node values. -/
def toFinStoch (mechanism : Mechanism graph Value node) :
    FinStoch (Object.of (graph.ParentAssignment Value node)) (Object.of Value) where
  prob parents value := (mechanism.run parents).prob value
  normalized parents := (mechanism.run parents).normalized

/-- The local-channel entry is the conditional probability returned by the
mechanism. -/
@[simp]
theorem toFinStoch_apply (mechanism : Mechanism graph Value node)
    (parents : graph.ParentAssignment Value node) (value : Value) :
    mechanism.toFinStoch.prob parents value =
      (mechanism.run parents).prob value :=
  rfl

end Mechanism

namespace FiniteCausalModel

variable {n : Nat} {Value : Type u} [Fintype Value] [DecidableEq Value]

/-- Interpret the observational joint distribution as a stochastic state. -/
def jointChannel (model : FiniteCausalModel n Value) :
    FinStoch Object.unit (assignmentObject n Value) where
  prob _ assignment := model.joint.prob assignment
  normalized _ := model.joint.normalized

/-- The observational stochastic state exposes the exact joint mass. -/
@[simp]
theorem jointChannel_apply (model : FiniteCausalModel n Value)
    (input : Object.unit) (assignment : Assignment n Value) :
    model.jointChannel.prob input assignment = model.joint.prob assignment :=
  rfl

/-- Interpret a hard-intervened model as an exact finite stochastic state. -/
def interventionalChannel (model : FiniteCausalModel n Value)
    (intervention : Intervention n Value) :
    FinStoch Object.unit (assignmentObject n Value) :=
  (model.intervene intervention).jointChannel

/-- An interventional state factors into unchanged observational mechanisms
and Dirac factors at targeted nodes. -/
theorem interventional_factorization (model : FiniteCausalModel n Value)
    (intervention : Intervention n Value) (input : Object.unit)
    (assignment : Assignment n Value) :
    (model.interventionalChannel intervention).prob input assignment =
      ∏ node,
        match intervention.setting node with
        | none =>
            ((model.mechanism node).run
              (fun parent ↦ assignment parent.1)).prob (assignment node)
        | some forced => if forced = assignment node then 1 else 0 := by
  rw [interventionalChannel, jointChannel_apply,
    (model.intervene intervention).observational_factorization]
  apply Fintype.prod_congr
  intro node
  cases hsetting : intervention.setting node with
  | none => simp [intervene, hsetting]
  | some forced =>
      simp [intervene, hsetting]
      rfl

/-- A hard intervention assigns zero joint mass to every configuration that
disagrees with one of its forced values. -/
theorem interventional_zero_of_target_mismatch
    (model : FiniteCausalModel n Value)
    (intervention : Intervention n Value) (input : Object.unit)
    (assignment : Assignment n Value) (node : Fin n) (forced : Value)
    (hsetting : intervention.setting node = some forced)
    (hne : forced ≠ assignment node) :
    (model.interventionalChannel intervention).prob input assignment = 0 := by
  rw [model.interventional_factorization intervention input assignment]
  apply Finset.prod_eq_zero (Finset.mem_univ node)
  simp [hsetting, hne]

/-- The finite stochastic state produced after intervention is normalized. -/
theorem interventionalChannel_normalized
    (model : FiniteCausalModel n Value)
    (intervention : Intervention n Value) (input : Object.unit) :
    ∑ assignment,
      (model.interventionalChannel intervention).prob input assignment = 1 :=
  (model.interventionalChannel intervention).normalized input

end FiniteCausalModel

end Ript.Models.Causal
