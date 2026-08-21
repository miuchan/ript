import Ript.Models.Causal.SoftIntervention

/-!
# Exact finite stochastic semantics for causal models

Every local mechanism is an exact `FinStoch` channel from parent assignments
to the node value.  The normalized observational and interventional joint
distributions are exposed as stochastic states from the tensor unit. This
includes hard interventions and arbitrary fixed-DAG soft/stochastic mechanism
replacement programs; their program channels are represented by computable
reduced one-step normal forms.
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

/-- Interpret an arbitrary soft/stochastic intervention as an exact finite
stochastic state. -/
def softInterventionalChannel (model : FiniteCausalModel n Value)
    (intervention : SoftIntervention model.dag Value) :
    FinStoch Object.unit (assignmentObject n Value) :=
  (model.softIntervene intervention).jointChannel

/-- A soft-interventional state factors through the selected replacement
mechanism at each targeted node and the original mechanism elsewhere. -/
theorem softInterventional_factorization (model : FiniteCausalModel n Value)
    (intervention : SoftIntervention model.dag Value) (input : Object.unit)
    (assignment : Assignment n Value) :
    (model.softInterventionalChannel intervention).prob input assignment =
      ∏ node,
        match intervention.setting node with
        | none =>
            ((model.mechanism node).run
              (fun parent ↦ assignment parent.1)).prob (assignment node)
        | some replacement =>
            (replacement.run
              (fun parent ↦ assignment parent.1)).prob (assignment node) := by
  rw [softInterventionalChannel, jointChannel_apply,
    (model.softIntervene intervention).observational_factorization]
  apply Fintype.prod_congr
  intro node
  cases hsetting : intervention.setting node <;>
    simp [softIntervene, softIntervenedMechanism, hsetting]

/-- The soft-interventional stochastic state is normalized. -/
theorem softInterventionalChannel_normalized
    (model : FiniteCausalModel n Value)
    (intervention : SoftIntervention model.dag Value) (input : Object.unit) :
    ∑ assignment,
      (model.softInterventionalChannel intervention).prob input assignment = 1 :=
  (model.softInterventionalChannel intervention).normalized input

/-- Hard-intervention channels are the Dirac special case of the soft
intervention channel construction. -/
theorem softInterventionalChannel_ofHard
    (model : FiniteCausalModel n Value)
    (intervention : Intervention n Value) :
    model.softInterventionalChannel
        (SoftIntervention.ofHard model.dag intervention) =
      model.interventionalChannel intervention := by
  unfold softInterventionalChannel interventionalChannel
  rw [model.softIntervene_ofHard intervention]

end FiniteCausalModel

namespace InterventionProgram

variable {n : Nat} {Value : Type u} [Fintype Value] [DecidableEq Value]

/-- Exact stochastic state produced by executing a finite hard-intervention
program. -/
def programChannel (model : FiniteCausalModel n Value)
    (program : Program n Value) :
    FinStoch Object.unit (assignmentObject n Value) :=
  (run model program).jointChannel

/-- The stochastic semantics of a finite intervention program is represented
exactly by the single interventional channel of its computable normal form. -/
theorem programChannel_eq_interventionalChannel_normalize
    (model : FiniteCausalModel n Value) (program : Program n Value) :
    programChannel model program =
      model.interventionalChannel (normalize program) := by
  rw [programChannel, run_eq_intervene_normalize]
  rfl

end InterventionProgram

namespace SoftInterventionProgram

variable {n : Nat} {Value : Type u} [Fintype Value] [DecidableEq Value]

/-- Exact stochastic state produced by a finite soft/stochastic-intervention
program. -/
def programChannel (model : FiniteCausalModel n Value)
    (program : Program model.dag Value) :
    FinStoch Object.unit (assignmentObject n Value) :=
  (run model program).jointChannel

/-- **Stochastic program representation.** The program channel is exactly the
single soft-interventional channel of its computable reduced normal form. -/
theorem programChannel_eq_softInterventionalChannel_normalize
    (model : FiniteCausalModel n Value)
    (program : Program model.dag Value) :
    programChannel model program =
      model.softInterventionalChannel (normalize model program) := by
  rw [programChannel, run_eq_softIntervene_normalize]
  rfl

end SoftInterventionProgram

end Ript.Models.Causal
