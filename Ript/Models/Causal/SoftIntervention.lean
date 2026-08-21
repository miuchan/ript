import Ript.Models.Causal.Intervention

/-!
# Finite soft and stochastic causal interventions

A soft intervention replaces selected local mechanisms by arbitrary exact
parent-dependent mechanisms on the same finite DAG. A stochastic intervention
is the parent-independent special case, and a hard intervention is the Dirac
special case.

Sequential programs use last-write-wins composition. Raw last-write-wins data
is not yet a single-valued semantic normal form: explicitly replacing a node
by its original mechanism has the same meaning as leaving the node untouched.
`reduceAgainst` computably removes exactly those redundant writes. The reduced
normal form represents every finite program, and extensional local-mechanism
semantics is injective on reduced forms.
-/

set_option autoImplicit false

namespace Ript.Models.Causal

open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic

universe u

namespace Mechanism

variable {n : Nat} {Value : Type u} [Fintype Value] [DecidableEq Value]
  {graph : FiniteDAG n} {node : Fin n}

/-- Executable entrywise equality of two local mechanisms. This formulation
exposes only finite probability-table data and therefore has a decidable
instance. -/
def EntrywiseEqual (left right : Mechanism graph Value node) : Prop :=
  ∀ parents value,
    (left.run parents).prob value = (right.run parents).prob value

instance entrywiseEqualDecidable (left right : Mechanism graph Value node) :
    Decidable (EntrywiseEqual left right) := by
  unfold EntrywiseEqual
  infer_instance

/-- Entrywise equality is exactly equality of local mechanisms. -/
theorem entrywiseEqual_iff_eq (left right : Mechanism graph Value node) :
    EntrywiseEqual left right ↔ left = right := by
  constructor
  · intro equal
    apply Mechanism.ext
    intro parents
    apply FinDist.ext
    intro value
    exact equal parents value
  · rintro rfl
    intro parents value
    rfl

end Mechanism

/-- A simultaneous soft intervention on one fixed DAG. Each selected node is
assigned an arbitrary replacement mechanism with the same parents and output
carrier. -/
structure SoftIntervention {n : Nat} (graph : FiniteDAG n) (Value : Type u)
    [Fintype Value] [DecidableEq Value] where
  /-- Optional replacement mechanism at each node; `none` retains the current
  mechanism. -/
  setting : (node : Fin n) → Option (Mechanism graph Value node)

namespace SoftIntervention

variable {n : Nat} {Value : Type u} [Fintype Value] [DecidableEq Value]
  {graph : FiniteDAG n}

/-- Soft interventions are equal when every dependent optional mechanism is
equal. -/
@[ext]
theorem ext (first second : SoftIntervention graph Value)
    (equal : ∀ node, first.setting node = second.setting node) :
    first = second := by
  cases first
  cases second
  congr
  funext node
  exact equal node

/-- Leave every local mechanism unchanged. -/
def empty : SoftIntervention graph Value where
  setting _ := none

/-- Replace exactly one node by a supplied parent-dependent mechanism. -/
def replaceAt (node : Fin n) (replacement : Mechanism graph Value node) :
    SoftIntervention graph Value where
  setting candidate :=
    if equal : candidate = node then
      some (equal.symm ▸ replacement)
    else
      none

/-- Replace one node by a parent-independent exact distribution. -/
def stochasticAt (node : Fin n) (distribution : FinDist (Object.of Value)) :
    SoftIntervention graph Value :=
  replaceAt (graph := graph) node { run := fun _ ↦ distribution }

/-- Hard intervention is the Dirac special case of stochastic intervention. -/
def hardAt (node : Fin n) (value : Value) :
    SoftIntervention graph Value :=
  stochasticAt node (FinDist.pure value)

/-- Embed a simultaneous hard intervention as parent-independent Dirac
mechanism replacements. -/
def ofHard (graph : FiniteDAG n) (intervention : Intervention n Value) :
    SoftIntervention graph Value where
  setting node :=
    match intervention.setting node with
    | none => none
    | some value => some { run := fun _ ↦ FinDist.pure value }

@[simp]
theorem replaceAt_same (node : Fin n)
    (replacement : Mechanism graph Value node) :
    (replaceAt node replacement).setting node = some replacement := by
  simp [replaceAt]

/-- Sequential soft-intervention composition. The second intervention wins
at every node it replaces. -/
def thenReplace (first second : SoftIntervention graph Value) :
    SoftIntervention graph Value where
  setting node :=
    match second.setting node with
    | none => first.setting node
    | some replacement => some replacement

/-- Last-write-wins soft-intervention composition is associative. -/
theorem thenReplace_assoc (first second third : SoftIntervention graph Value) :
    (first.thenReplace second).thenReplace third =
      first.thenReplace (second.thenReplace third) := by
  apply SoftIntervention.ext
  intro node
  cases hfirst : first.setting node <;>
    cases hsecond : second.setting node <;>
      cases hthird : third.setting node <;>
        simp [thenReplace, hfirst, hsecond, hthird]

@[simp]
theorem empty_thenReplace (intervention : SoftIntervention graph Value) :
    empty.thenReplace intervention = intervention := by
  apply SoftIntervention.ext
  intro node
  cases hsetting : intervention.setting node <;>
    simp [thenReplace, empty, hsetting]

@[simp]
theorem thenReplace_empty (intervention : SoftIntervention graph Value) :
    intervention.thenReplace empty = intervention :=
  rfl

/-- A soft intervention is reduced against a base model when none of its
explicit replacements is extensionally equal to that model's original local
mechanism. -/
def ReducedAgainst (model : FiniteCausalModel n Value)
    (intervention : SoftIntervention model.dag Value) : Prop :=
  ∀ node replacement, intervention.setting node = some replacement →
    ¬ Mechanism.EntrywiseEqual replacement (model.mechanism node)

/-- Computably erase all explicit writes that merely reinstall the base
model's original local mechanism. -/
def reduceAgainst (model : FiniteCausalModel n Value)
    (intervention : SoftIntervention model.dag Value) :
    SoftIntervention model.dag Value where
  setting node :=
    match intervention.setting node with
    | none => none
    | some replacement =>
        if Mechanism.EntrywiseEqual replacement (model.mechanism node) then
          none
        else
          some replacement

/-- The computable reduction always produces a reduced intervention. -/
theorem reduceAgainst_reduced (model : FiniteCausalModel n Value)
    (intervention : SoftIntervention model.dag Value) :
    ReducedAgainst model (reduceAgainst model intervention) := by
  intro node replacement hsetting
  cases horiginal : intervention.setting node with
  | none =>
      simp [reduceAgainst, horiginal] at hsetting
  | some original =>
      by_cases hequal :
          Mechanism.EntrywiseEqual original (model.mechanism node)
      · simp [reduceAgainst, horiginal, hequal] at hsetting
      · simp [reduceAgainst, horiginal, hequal] at hsetting
        subst replacement
        exact hequal

/-- Fixed points of reduction are exactly the interventions with no redundant
base-mechanism writes. -/
theorem reduceAgainst_eq_self_iff (model : FiniteCausalModel n Value)
    (intervention : SoftIntervention model.dag Value) :
    intervention.reduceAgainst model = intervention ↔
      intervention.ReducedAgainst model := by
  constructor
  · intro equality
    rw [← equality]
    exact reduceAgainst_reduced model intervention
  · intro reduced
    apply SoftIntervention.ext
    intro node
    cases hsetting : intervention.setting node with
    | none => simp [reduceAgainst, hsetting]
    | some replacement =>
        have notEqual := reduced node replacement hsetting
        simp [reduceAgainst, hsetting, notEqual]

/-- Canonicalization is idempotent. -/
@[simp]
theorem reduceAgainst_idempotent (model : FiniteCausalModel n Value)
    (intervention : SoftIntervention model.dag Value) :
    (intervention.reduceAgainst model).reduceAgainst model =
      intervention.reduceAgainst model :=
  (reduceAgainst_eq_self_iff model _).2
    (reduceAgainst_reduced model intervention)

end SoftIntervention

namespace FiniteCausalModel

variable {n : Nat} {Value : Type u} [Fintype Value] [DecidableEq Value]

/-- The local mechanism selected by a soft intervention, before evaluating it
on a parent assignment. -/
def softIntervenedMechanism (model : FiniteCausalModel n Value)
    (intervention : SoftIntervention model.dag Value) (node : Fin n) :
    Mechanism model.dag Value node :=
  match intervention.setting node with
  | none => model.mechanism node
  | some replacement => replacement

/-- Extensional local-mechanism semantics of a soft intervention. -/
def softInterventionSemantics (model : FiniteCausalModel n Value)
    (intervention : SoftIntervention model.dag Value) :
    (node : Fin n) →
      model.dag.ParentAssignment Value node → FinDist (Object.of Value) :=
  fun node parents ↦
    (model.softIntervenedMechanism intervention node).run parents

/-- Apply arbitrary local-mechanism replacements without changing the DAG. -/
def softIntervene (model : FiniteCausalModel n Value)
    (intervention : SoftIntervention model.dag Value) :
    FiniteCausalModel n Value where
  dag := model.dag
  mechanism node := model.softIntervenedMechanism intervention node

@[simp]
theorem softIntervene_empty (model : FiniteCausalModel n Value) :
    model.softIntervene SoftIntervention.empty = model := by
  cases model with
  | mk dag mechanisms =>
      unfold softIntervene softIntervenedMechanism
      congr

/-- The soft-intervention semantics conservatively extends hard
interventions. -/
theorem softIntervene_ofHard (model : FiniteCausalModel n Value)
    (intervention : Intervention n Value) :
    model.softIntervene (SoftIntervention.ofHard model.dag intervention) =
      model.intervene intervention := by
  cases model with
  | mk dag mechanisms =>
      unfold softIntervene softIntervenedMechanism SoftIntervention.ofHard
        intervene
      congr
      funext node
      cases hsetting : intervention.setting node <;>
        simp [hsetting]

/-- Sequential soft interventions are represented by their last-write-wins
composite. -/
theorem softIntervene_thenReplace (model : FiniteCausalModel n Value)
    (first second : SoftIntervention model.dag Value) :
    (model.softIntervene first).softIntervene second =
      model.softIntervene (first.thenReplace second) := by
  cases model with
  | mk dag mechanisms =>
      unfold softIntervene softIntervenedMechanism SoftIntervention.thenReplace
      congr
      funext node
      cases hfirst : first.setting node <;>
        cases hsecond : second.setting node <;>
          simp [hfirst, hsecond]

/-- Removing redundant writes preserves the complete intervened model. -/
theorem softIntervene_reduceAgainst (model : FiniteCausalModel n Value)
    (intervention : SoftIntervention model.dag Value) :
    model.softIntervene (intervention.reduceAgainst model) =
      model.softIntervene intervention := by
  cases model with
  | mk dag mechanisms =>
      unfold softIntervene softIntervenedMechanism
        SoftIntervention.reduceAgainst
      congr
      funext node
      cases hsetting : intervention.setting node with
      | none => simp [hsetting]
      | some replacement =>
          by_cases hequal : Mechanism.EntrywiseEqual replacement (mechanisms node)
          · have mechanismEqual : replacement = mechanisms node :=
              (Mechanism.entrywiseEqual_iff_eq _ _).1 hequal
            subst replacement
            simp [hsetting, hequal]
          · simp [hsetting, hequal]

/-- Extensional semantics is injective on interventions reduced against the
same base model. This is the precise identifiability boundary for arbitrary
soft replacements. -/
theorem softInterventionSemantics_injective_of_reduced
    (model : FiniteCausalModel n Value)
    {first second : SoftIntervention model.dag Value}
    (firstReduced : first.ReducedAgainst model)
    (secondReduced : second.ReducedAgainst model)
    (equal : model.softInterventionSemantics first =
      model.softInterventionSemantics second) :
    first = second := by
  apply SoftIntervention.ext
  intro node
  have mechanismEqual :
      model.softIntervenedMechanism first node =
        model.softIntervenedMechanism second node := by
    apply Mechanism.ext
    intro parents
    exact congrFun (congrArg (fun semantics ↦ semantics node) equal) parents
  cases hfirst : first.setting node with
  | none =>
      cases hsecond : second.setting node with
      | none => rfl
      | some secondReplacement =>
          have replacementEqual :
              secondReplacement = model.mechanism node := by
            simpa [softIntervenedMechanism, hfirst, hsecond] using
              mechanismEqual.symm
          have entrywise : Mechanism.EntrywiseEqual secondReplacement
              (model.mechanism node) :=
            (Mechanism.entrywiseEqual_iff_eq _ _).2 replacementEqual
          exact False.elim
            (secondReduced node secondReplacement hsecond entrywise)
  | some firstReplacement =>
      cases hsecond : second.setting node with
      | none =>
          have replacementEqual :
              firstReplacement = model.mechanism node := by
            simpa [softIntervenedMechanism, hfirst, hsecond] using
              mechanismEqual
          have entrywise : Mechanism.EntrywiseEqual firstReplacement
              (model.mechanism node) :=
            (Mechanism.entrywiseEqual_iff_eq _ _).2 replacementEqual
          exact False.elim
            (firstReduced node firstReplacement hfirst entrywise)
      | some secondReplacement =>
          have replacementEqual : firstReplacement = secondReplacement := by
            simpa [softIntervenedMechanism, hfirst, hsecond] using mechanismEqual
          exact congrArg some replacementEqual

/-- Every soft-intervened joint distribution remains normalized. -/
theorem softIntervention_preserves_normalization
    (model : FiniteCausalModel n Value)
    (intervention : SoftIntervention model.dag Value) :
    ∑ assignment,
      (model.softIntervene intervention).joint.prob assignment = 1 :=
  (model.softIntervene intervention).joint.normalized

end FiniteCausalModel

/-! ## Finite soft-intervention programs -/

namespace SoftInterventionProgram

variable {n : Nat} {Value : Type u} [Fintype Value] [DecidableEq Value]
  {graph : FiniteDAG n}

/-- A finite sequential program of arbitrary local-mechanism replacements. -/
abbrev Program (graph : FiniteDAG n) (Value : Type u)
    [Fintype Value] [DecidableEq Value] :=
  List (SoftIntervention graph Value)

/-- Raw last-write-wins composite before redundant base-mechanism writes are
deleted. -/
def rawNormalize : Program graph Value → SoftIntervention graph Value
  | [] => SoftIntervention.empty
  | intervention :: rest =>
      intervention.thenReplace (rawNormalize rest)

/-- Execute a finite soft-intervention program by its structural
last-write-wins fold. -/
def run (model : FiniteCausalModel n Value)
    (program : Program model.dag Value) : FiniteCausalModel n Value :=
  model.softIntervene (rawNormalize program)

@[simp]
theorem run_nil (model : FiniteCausalModel n Value) :
    run model [] = model := by
  simp [run, rawNormalize]

/-- The structural fold agrees with stepwise execution of the head
intervention followed by the remaining program. -/
theorem run_cons (model : FiniteCausalModel n Value)
    (intervention : SoftIntervention model.dag Value)
    (rest : Program model.dag Value) :
    run model (intervention :: rest) =
      run (model.softIntervene intervention) rest := by
  unfold run
  simp only [rawNormalize]
  rw [← FiniteCausalModel.softIntervene_thenReplace]
  rfl

/-- Every program executes as its raw last-write-wins composite. -/
theorem run_eq_softIntervene_rawNormalize
    (model : FiniteCausalModel n Value) (program : Program model.dag Value) :
    run model program = model.softIntervene (rawNormalize program) :=
  rfl

/-- Computable single-valued normal form: last write wins, and writes equal to
the original base mechanism are erased. -/
def normalize (model : FiniteCausalModel n Value)
    (program : Program model.dag Value) : SoftIntervention model.dag Value :=
  (rawNormalize program).reduceAgainst model

/-- Program normal forms are reduced by construction. -/
theorem normalize_reduced (model : FiniteCausalModel n Value)
    (program : Program model.dag Value) :
    (normalize model program).ReducedAgainst model :=
  SoftIntervention.reduceAgainst_reduced model (rawNormalize program)

/-- **Soft-program representation theorem.** Every finite soft/stochastic
intervention program executes exactly as its single reduced normal form. -/
theorem run_eq_softIntervene_normalize
    (model : FiniteCausalModel n Value) (program : Program model.dag Value) :
    run model program = model.softIntervene (normalize model program) := by
  rw [run_eq_softIntervene_rawNormalize]
  exact (model.softIntervene_reduceAgainst (rawNormalize program)).symm

/-- Equality of reduced local-mechanism semantics for two programs. -/
def SemanticallyEquivalent (model : FiniteCausalModel n Value)
    (first second : Program model.dag Value) : Prop :=
  model.softInterventionSemantics (normalize model first) =
    model.softInterventionSemantics (normalize model second)

/-- **Soft-intervention completeness.** Two finite programs have equal
extensional local-mechanism semantics exactly when their computable reduced
normal forms are equal. -/
theorem semanticallyEquivalent_iff_normalize_eq
    (model : FiniteCausalModel n Value)
    (first second : Program model.dag Value) :
    SemanticallyEquivalent model first second ↔
      normalize model first = normalize model second := by
  constructor
  · intro equal
    exact model.softInterventionSemantics_injective_of_reduced
      (normalize_reduced model first) (normalize_reduced model second) equal
  · exact congrArg (FiniteCausalModel.softInterventionSemantics model)

end SoftInterventionProgram

end Ript.Models.Causal
