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

/-- Interventions are extensionally equal when they choose the same optional
forced value at every node. -/
@[ext]
theorem ext (first second : Intervention n Value)
    (equal : ∀ node, first.setting node = second.setting node) :
    first = second := by
  cases first
  cases second
  congr
  funext node
  exact equal node

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

/-- Sequential composition of simultaneous hard interventions.  The second
intervention wins at every node it targets. -/
def thenDo (first second : Intervention n Value) :
    Intervention n Value where
  setting node :=
    match second.setting node with
    | none => first.setting node
    | some value => some value

/-- Last-write-wins intervention composition is associative. -/
theorem thenDo_assoc (first second third : Intervention n Value) :
    (first.thenDo second).thenDo third =
      first.thenDo (second.thenDo third) := by
  apply Intervention.ext
  intro node
  cases hfirst : first.setting node <;>
    cases hsecond : second.setting node <;>
      cases hthird : third.setting node <;>
        simp [thenDo, hfirst, hsecond, hthird]

/-- The empty intervention is a left identity for sequential composition. -/
@[simp]
theorem empty_thenDo (intervention : Intervention n Value) :
    empty.thenDo intervention = intervention := by
  apply Intervention.ext
  intro node
  cases hsetting : intervention.setting node <;>
    simp [thenDo, empty, hsetting]

/-- The empty intervention is a right identity for sequential composition. -/
@[simp]
theorem thenDo_empty (intervention : Intervention n Value) :
    intervention.thenDo empty = intervention :=
  rfl

/-- Repeating an intervention does not change its last-write-wins normal
form. -/
@[simp]
theorem thenDo_self (intervention : Intervention n Value) :
    intervention.thenDo intervention = intervention := by
  apply Intervention.ext
  intro node
  cases hsetting : intervention.setting node <;>
    simp [thenDo, hsetting]

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

/-- Extensional local-mechanism semantics of a hard intervention, expressed
over the fixed DAG of the original model. -/
def interventionSemantics (model : FiniteCausalModel n Value)
    (intervention : Intervention n Value) :
    (node : Fin n) →
      model.dag.ParentAssignment Value node →
        FinDist (Object.of Value) :=
  fun node parents ↦
    match intervention.setting node with
    | none => (model.mechanism node).run parents
    | some value => FinDist.pure value

/-- Exact identifiability condition for hard interventions: no original local
mechanism is already the same forced Dirac distribution for every parent
assignment. -/
def HardInterventionIdentifiable
    (model : FiniteCausalModel n Value) : Prop :=
  ∀ (node : Fin n) (forced : Value),
    ∃ parents : model.dag.ParentAssignment Value node,
      (model.mechanism node).run parents ≠ FinDist.pure forced

/-- Under hard-intervention identifiability, extensional local-mechanism
semantics reflects the complete partial assignment. -/
theorem interventionSemantics_injective
    (model : FiniteCausalModel n Value)
    (identifiable : HardInterventionIdentifiable model) :
    Function.Injective (interventionSemantics model) := by
  intro first second equal
  apply Intervention.ext
  intro node
  cases hfirst : first.setting node with
  | none =>
      cases hsecond : second.setting node with
      | none => rfl
      | some secondValue =>
          obtain ⟨parents, notPure⟩ := identifiable node secondValue
          have atParents := congrArg
            (fun semantics ↦ semantics node parents) equal
          simp only [interventionSemantics, hfirst, hsecond] at atParents
          exact (notPure atParents).elim
  | some firstValue =>
      cases hsecond : second.setting node with
      | none =>
          obtain ⟨parents, notPure⟩ := identifiable node firstValue
          have atParents := congrArg
            (fun semantics ↦ semantics node parents) equal
          simp only [interventionSemantics, hfirst, hsecond] at atParents
          exact (notPure atParents.symm).elim
      | some secondValue =>
          obtain ⟨parents, notPure⟩ := identifiable node firstValue
          have atParents := congrArg
            (fun semantics ↦ semantics node parents) equal
          simp only [interventionSemantics, hfirst, hsecond] at atParents
          exact congrArg some (FinDist.pure_injective atParents)

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

/-- Sequential hard intervention is represented exactly by the
last-write-wins composite partial assignment. -/
theorem intervene_thenDo (model : FiniteCausalModel n Value)
    (first second : Intervention n Value) :
    (model.intervene first).intervene second =
      model.intervene (first.thenDo second) := by
  cases model with
  | mk dag mechanisms =>
      unfold intervene Intervention.thenDo
      congr
      funext node
      apply Mechanism.ext
      intro parents
      cases hfirst : first.setting node <;>
        cases hsecond : second.setting node <;>
          simp [hfirst, hsecond]

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

/-! ## Finite hard-intervention programs -/

namespace InterventionProgram

variable {n : Nat} {Value : Type u} [Fintype Value] [DecidableEq Value]

/-- A finite sequential program of simultaneous hard interventions. -/
abbrev Program (n : Nat) (Value : Type u) :=
  List (Intervention n Value)

/-- Computable last-write-wins normal form of a finite intervention program. -/
def normalize : Program n Value → Intervention n Value
  | [] => Intervention.empty
  | intervention :: rest =>
      intervention.thenDo (normalize rest)

/-- Execute a finite intervention program on a causal model. -/
def run (model : FiniteCausalModel n Value) :
    Program n Value → FiniteCausalModel n Value
  | [] => model
  | intervention :: rest => run (model.intervene intervention) rest

/-- **Program representation theorem.**  Every finite intervention program
executes exactly as its single last-write-wins normal form. -/
theorem run_eq_intervene_normalize
    (model : FiniteCausalModel n Value) (program : Program n Value) :
    run model program = model.intervene (normalize program) := by
  induction program generalizing model with
  | nil => simp [run, normalize]
  | cons intervention rest induction =>
      simp only [run, normalize]
      rw [induction, FiniteCausalModel.intervene_thenDo]

/-- Extensional equivalence of finite intervention programs in one base
causal model. -/
def SemanticallyEquivalent (model : FiniteCausalModel n Value)
    (first second : Program n Value) : Prop :=
  FiniteCausalModel.interventionSemantics model (normalize first) =
    FiniteCausalModel.interventionSemantics model (normalize second)

/-- **Hard-intervention completeness.**  In an identifiable base model, two
finite intervention programs have equal local-mechanism semantics exactly
when their computable last-write-wins normal forms are equal. -/
theorem semanticallyEquivalent_iff_normalize_eq
    (model : FiniteCausalModel n Value)
    (identifiable : FiniteCausalModel.HardInterventionIdentifiable model)
    (first second : Program n Value) :
    SemanticallyEquivalent model first second ↔
      normalize first = normalize second := by
  constructor
  · exact fun equal ↦
      FiniteCausalModel.interventionSemantics_injective
        model identifiable equal
  · exact congrArg (FiniteCausalModel.interventionSemantics model)

end InterventionProgram

end Ript.Models.Causal
