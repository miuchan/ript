import Ript.Models.Causal.Model

/-!
# Finite causal interventions

An intervention is an executable partial assignment of forced node values.
Applying it to a causal model replaces each targeted local mechanism by the
corresponding Dirac distribution.  It does not condition the observational
joint distribution.
-/

set_option autoImplicit false

namespace Ript.Models.Causal

open scoped BigOperators

open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic

universe u

/-- A simultaneous hard intervention, represented as a partial node
assignment. -/
structure Intervention (n : Nat) (Value : Type u) where
  /-- `some value` replaces the node mechanism; `none` leaves it unchanged. -/
  setting : Fin n → Option Value

namespace Intervention

variable {n : Nat} {Value : Type u}

/-- The intervention that leaves every mechanism unchanged. -/
def empty : Intervention n Value where
  setting _ := none

/-- A single-node hard intervention `do(node = value)`. -/
def doAt (node : Fin n) (value : Value) : Intervention n Value where
  setting candidate := if candidate = node then some value else none

/-- The executable set of nodes targeted by an intervention. -/
def support (intervention : Intervention n Value) : Finset (Fin n) :=
  Finset.univ.filter fun node ↦ (intervention.setting node).isSome

/-- Membership in intervention support is exactly the presence of a forced
value. -/
@[simp]
theorem mem_support_iff (intervention : Intervention n Value) (node : Fin n) :
    node ∈ intervention.support ↔ (intervention.setting node).isSome := by
  simp [support]

/-- A node is in the support exactly when its setting is not `none`. -/
theorem mem_support_iff_ne_none (intervention : Intervention n Value)
    (node : Fin n) :
    node ∈ intervention.support ↔ intervention.setting node ≠ none := by
  rw [mem_support_iff]
  cases intervention.setting node <;> simp

/-- The intervention support of `do(node = value)` contains its target. -/
theorem mem_support_doAt (node : Fin n) (value : Value) :
    node ∈ (doAt node value).support := by
  simp [support, doAt]

end Intervention

namespace Mechanism

variable {n : Nat} {Value : Type u} [Fintype Value] [DecidableEq Value]
  {graph : FiniteDAG n} {node : Fin n}

/-- Local mechanisms are equal when they return the same distribution for
every parent assignment. -/
@[ext]
theorem ext (left right : Mechanism graph Value node)
    (h : ∀ parents, left.run parents = right.run parents) : left = right := by
  cases left
  cases right
  congr
  funext parents
  exact h parents

end Mechanism

namespace FiniteCausalModel

variable {n : Nat} {Value : Type u} [Fintype Value] [DecidableEq Value]

/-- Replace targeted local mechanisms by point distributions.  This is hard
intervention semantics, not conditioning. -/
def intervene (model : FiniteCausalModel n Value)
    (intervention : Intervention n Value) : FiniteCausalModel n Value where
  dag := model.dag
  mechanism node :=
    { run := fun parents ↦
        match intervention.setting node with
        | none => (model.mechanism node).run parents
        | some value => FinDist.pure value }

/-- The empty intervention changes no local mechanism. -/
@[simp]
theorem intervene_empty (model : FiniteCausalModel n Value) :
    model.intervene Intervention.empty = model := by
  cases model with
  | mk dag mechanisms =>
      unfold intervene
      congr

/-- At its target, `do(node = value)` replaces the original mechanism by the
Dirac distribution at `value`, independently of all parent values. -/
theorem intervene_same (model : FiniteCausalModel n Value)
    (node : Fin n) (value : Value)
    (parents : model.dag.ParentAssignment Value node) :
    (((model.intervene (Intervention.doAt node value)).mechanism node).run
      parents) = FinDist.pure value := by
  simp [intervene, Intervention.doAt]

/-- Applying the same hard intervention twice has no additional effect. -/
theorem intervene_idempotent (model : FiniteCausalModel n Value)
    (intervention : Intervention n Value) :
    (model.intervene intervention).intervene intervention =
      model.intervene intervention := by
  cases model with
  | mk dag mechanisms =>
      unfold intervene
      congr
      funext node
      apply Mechanism.ext
      intro parents
      cases hsetting : intervention.setting node <;>
        simp [hsetting]

/-- Hard interventions with disjoint target sets commute. -/
theorem intervene_comm_of_disjoint (model : FiniteCausalModel n Value)
    (first second : Intervention n Value)
    (hdisjoint : Disjoint first.support second.support) :
    (model.intervene first).intervene second =
      (model.intervene second).intervene first := by
  cases model with
  | mk dag mechanisms =>
      unfold intervene
      congr
      funext node
      apply Mechanism.ext
      intro parents
      cases hfirst : first.setting node with
      | none => simp [hfirst]
      | some firstValue =>
          cases hsecond : second.setting node with
          | none => simp [hfirst]
          | some secondValue =>
              have hFirstSupport : node ∈ first.support := by
                rw [Intervention.mem_support_iff]
                simp [hfirst]
              have hSecondSupport : node ∈ second.support := by
                rw [Intervention.mem_support_iff]
                simp [hsecond]
              exact False.elim
                (Finset.disjoint_left.mp hdisjoint hFirstSupport hSecondSupport)

/-- Every intervened joint distribution remains normalized. -/
theorem intervention_preserves_normalization
    (model : FiniteCausalModel n Value)
    (intervention : Intervention n Value) :
    ∑ assignment,
      (model.intervene intervention).joint.prob assignment = 1 :=
  (model.intervene intervention).joint.normalized

end FiniteCausalModel

end Ript.Models.Causal
