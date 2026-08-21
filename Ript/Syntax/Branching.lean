import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.NNRat.BigOperators
import Ript.Models.FiniteStochastic

/-!
# Executable finite adaptive branching protocols

This file defines a small, model-independent language for finite binary
protocol trees.  Every branch has the same finite depth, but the generator at
the next node may depend on the complete history observed so far.  Thus the
language represents genuine adaptive decision trees rather than fixed words.

An exact branch semantics assigns a strictly positive rational probability
and a deterministic state update to each generator outcome.  Evaluation keeps
the complete outcome history.  Its canonical normal form is therefore a
finite table containing one branch probability and one final-state function
per history.  The representation and completeness theorems below say that
this table evaluates to the protocol channel and that two tables are equal
exactly when their recorded stochastic channels are equal.

The syntax, histories, costs, budgets, normal forms, and stochastic entries
are all executable.  Quotients and classical choice are not used in this
computational layer.
-/

set_option autoImplicit false

namespace Ript.Syntax.Branching

open scoped BigOperators

open Ript.Models.FiniteStochastic

universe u

/-- A finite binary adaptive protocol of a statically known depth. -/
inductive Tree (Generator : Type u) : Nat → Type u where
  /-- Terminate without another observation. -/
  | leaf : Tree Generator 0
  /-- Execute one generator and choose the remaining tree from its outcome. -/
  | node {depth : Nat} (generator : Generator)
      (next : Bool → Tree Generator depth) : Tree Generator (depth + 1)

/-- Complete binary histories of a fixed finite depth. -/
def History : Nat → Type
  | 0 => PUnit
  | depth + 1 => Σ _ : Bool, History depth

/-- Executable enumeration of complete histories. -/
@[instance_reducible]
def historyFintype : (depth : Nat) → Fintype (History depth)
  | 0 => by
      change Fintype PUnit
      infer_instance
  | depth + 1 => by
      letI : Fintype (History depth) := historyFintype depth
      change Fintype (Σ _ : Bool, History depth)
      infer_instance

instance (depth : Nat) : Fintype (History depth) := historyFintype depth

/-- Executable equality of complete histories. -/
def historyDecidableEq : (depth : Nat) → DecidableEq (History depth)
  | 0 => by
      change DecidableEq PUnit
      infer_instance
  | depth + 1 => by
      letI : DecidableEq (History depth) := historyDecidableEq depth
      change DecidableEq (Σ _ : Bool, History depth)
      infer_instance

instance (depth : Nat) : DecidableEq (History depth) :=
  historyDecidableEq depth

/-- Scalar resource charge of every primitive generator. -/
structure CostModel (Generator : Type u) where
  /-- Charge incurred when the generator is executed. -/
  cost : Generator → Nat

/-- Exact binary branch semantics on a finite state carrier.

Strict positivity makes recorded histories fully observable: no final-state
entry can hide behind a zero-probability branch.  This is precisely the
hypothesis needed by the completeness theorem. -/
structure Semantics (Generator : Type u) (State : Type u) where
  /-- Exact probability of one binary outcome. -/
  weight : Generator → Bool → ℚ≥0
  /-- Every generator gives a normalized binary distribution. -/
  normalized : ∀ generator, ∑ outcome, weight generator outcome = 1
  /-- Every recorded outcome is possible. -/
  positive : ∀ generator outcome, 0 < weight generator outcome
  /-- Deterministic residual-state update conditioned on the outcome. -/
  transition : Generator → Bool → State → State

namespace Tree

variable {Generator State : Type u} {depth : Nat}

/-- Probability of one complete protocol history. -/
def historyProbability (semantics : Semantics Generator State) :
    {depth : Nat} → Tree Generator depth → History depth → ℚ≥0
  | 0, .leaf, _ => 1
  | _ + 1, .node generator next, history =>
      semantics.weight generator history.1 *
        (next history.1).historyProbability semantics history.2

/-- Residual state obtained along one complete history. -/
def finalState (semantics : Semantics Generator State) :
    {depth : Nat} → Tree Generator depth → State → History depth → State
  | 0, .leaf, input, _ => input
  | _ + 1, .node generator next, input, history =>
      (next history.1).finalState semantics
        (semantics.transition generator history.1 input) history.2

/-- Exact cost incurred along one complete history. -/
def historyCost (costModel : CostModel Generator) :
    {depth : Nat} → Tree Generator depth → History depth → Nat
  | 0, .leaf, _ => 0
  | _ + 1, .node generator next, history =>
      costModel.cost generator +
        (next history.1).historyCost costModel history.2

/-- Worst-case executable resource budget of a binary protocol tree. -/
def budget (costModel : CostModel Generator) :
    {depth : Nat} → Tree Generator depth → Nat
  | 0, .leaf => 0
  | _ + 1, .node generator next =>
      costModel.cost generator +
        max ((next false).budget costModel) ((next true).budget costModel)

/-- Every realized history stays within the computed worst-case budget. -/
theorem historyCost_le_budget (costModel : CostModel Generator)
    (tree : Tree Generator depth) (history : History depth) :
    tree.historyCost costModel history ≤ tree.budget costModel := by
  induction tree with
  | leaf =>
      change (0 : Nat) ≤ 0
      exact le_rfl
  | @node depth generator next induction =>
      rcases history with ⟨outcome, history⟩
      simp only [budget]
      apply Nat.add_le_add_left
      cases outcome
      · exact (induction false history).trans (Nat.le_max_left _ _)
      · exact (induction true history).trans (Nat.le_max_right _ _)

/-- Complete-history probabilities are normalized. -/
theorem historyProbability_normalized
    (semantics : Semantics Generator State)
    (tree : Tree Generator depth) :
    ∑ history, tree.historyProbability semantics history = 1 := by
  induction tree with
  | leaf =>
      change (∑ _ : PUnit, (1 : ℚ≥0)) = 1
      simp
  | @node depth generator next induction =>
      change (∑ history : Σ _ : Bool, History depth,
        semantics.weight generator history.1 *
          (next history.1).historyProbability semantics history.2) = 1
      rw [Fintype.sum_sigma]
      simp_rw [← Finset.mul_sum, induction]
      simpa using semantics.normalized generator

/-- Strictly positive primitive branches give strictly positive histories. -/
theorem historyProbability_pos
    (semantics : Semantics Generator State)
    (tree : Tree Generator depth) (history : History depth) :
    0 < tree.historyProbability semantics history := by
  induction tree with
  | leaf => simp [historyProbability]
  | @node depth generator next induction =>
      rcases history with ⟨outcome, history⟩
      exact mul_pos (semantics.positive generator outcome)
        (induction outcome history)

end Tree

/-- Canonical finite branch table of an adaptive protocol. -/
@[ext]
structure NormalForm (State : Type u) [Fintype State] [DecidableEq State]
    (depth : Nat) where
  /-- Exact probability of every complete history. -/
  probability : History depth → ℚ≥0
  /-- Final state for every input and complete history. -/
  output : State → History depth → State
  /-- The branch table is normalized. -/
  normalized : ∑ history, probability history = 1
  /-- Every table row is operationally visible. -/
  positive : ∀ history, 0 < probability history

namespace NormalForm

variable {State : Type u} [Fintype State] [DecidableEq State]
  {depth : Nat}

/-- Recorded stochastic channel represented by a canonical branch table. -/
def toFinStoch (normalForm : NormalForm State depth) :
    FinStoch (Object.of State) (Object.of (History depth × State)) where
  prob input result :=
    if normalForm.output input result.1 = result.2
      then normalForm.probability result.1 else 0
  normalized input := by
    rw [Fintype.sum_prod_type]
    simpa using normalForm.normalized

@[simp]
theorem toFinStoch_apply (normalForm : NormalForm State depth)
    (input : State) (history : History depth) (output : State) :
    normalForm.toFinStoch.prob input (history, output) =
      if normalForm.output input history = output
        then normalForm.probability history else 0 :=
  rfl

/-- Summing over the residual state recovers the exact history probability. -/
theorem historyMarginal (normalForm : NormalForm State depth)
    (input : State) (history : History depth) :
    ∑ output, normalForm.toFinStoch.prob input (history, output) =
      normalForm.probability history := by
  simp [toFinStoch_apply]

/-- A branch table is visible at its recorded deterministic output. -/
theorem toFinStoch_output (normalForm : NormalForm State depth)
    (input : State) (history : History depth) :
    normalForm.toFinStoch.prob input
        (history, normalForm.output input history) =
      normalForm.probability history := by
  simp [toFinStoch_apply]

variable [Inhabited State]

/-- **Recorded-table faithfulness.**  The stochastic channel uniquely
determines every probability and final-state entry of a strictly positive
normal form. -/
theorem toFinStoch_injective :
    Function.Injective
      (toFinStoch : NormalForm State depth →
        FinStoch (Object.of State) (Object.of (History depth × State))) := by
  intro first second equalChannels
  have probabilityEqual : first.probability = second.probability := by
    funext history
    let input : State := first.output default history
    calc
      first.probability history =
          ∑ output, first.toFinStoch.prob input (history, output) :=
        (first.historyMarginal input history).symm
      _ = ∑ output, second.toFinStoch.prob input (history, output) := by
        rw [equalChannels]
      _ = second.probability history := second.historyMarginal input history
  have outputEqual : first.output = second.output := by
    funext input history
    by_contra unequal
    have entryEqual := congrArg
      (fun channel ↦ channel.prob input (history, first.output input history))
      equalChannels
    rw [first.toFinStoch_output, second.toFinStoch_apply,
      if_neg (Ne.symm unequal), probabilityEqual] at entryEqual
    exact (ne_of_gt (second.positive history)) entryEqual
  exact NormalForm.ext probabilityEqual outputEqual

/-- Equality of recorded stochastic behavior is equivalent to equality of
canonical branch normal forms. -/
theorem toFinStoch_eq_iff {first second : NormalForm State depth} :
    first.toFinStoch = second.toFinStoch ↔ first = second :=
  ⟨fun equalChannels ↦ toFinStoch_injective equalChannels,
    congrArg toFinStoch⟩

end NormalForm

namespace Tree

variable {Generator State : Type u} [Fintype State] [DecidableEq State]
  {depth : Nat}

/-- Compute the canonical branch table of a protocol tree. -/
def normalForm (semantics : Semantics Generator State)
    (tree : Tree Generator depth) : NormalForm State depth where
  probability := tree.historyProbability semantics
  output := tree.finalState semantics
  normalized := tree.historyProbability_normalized semantics
  positive := tree.historyProbability_pos semantics

/-- Execute a protocol as an exact history-recording stochastic channel. -/
def run (semantics : Semantics Generator State)
    (tree : Tree Generator depth) :
    FinStoch (Object.of State) (Object.of (History depth × State)) :=
  (tree.normalForm semantics).toFinStoch

@[simp]
theorem run_apply (semantics : Semantics Generator State)
    (tree : Tree Generator depth) (input : State)
    (history : History depth) (output : State) :
    (tree.run semantics).prob input (history, output) =
      if tree.finalState semantics input history = output
        then tree.historyProbability semantics history else 0 :=
  rfl

/-- A deterministic decoder that retracts every represented branch makes the
complete history-recording channel exactly reversible. -/
theorem run_comp_dirac_of_decode
    (semantics : Semantics Generator State)
    (tree : Tree Generator depth)
    (decode : History depth × State → State)
    (decode_output : ∀ input history,
      decode (history, tree.finalState semantics input history) = input) :
    FinStoch.comp (tree.run semantics) (FinStoch.dirac decode) =
      FinStoch.identity (Object.of State) := by
  apply FinStoch.ext
  intro input output
  change
    (∑ result : History depth × State,
      (if tree.finalState semantics input result.1 = result.2
        then tree.historyProbability semantics result.1 else 0) *
      (if decode result = output then 1 else 0)) =
        if input = output then 1 else 0
  rw [Fintype.sum_prod_type]
  calc
    (∑ history : History depth, ∑ state : State,
      (if tree.finalState semantics input history = state
        then tree.historyProbability semantics history else 0) *
      (if decode (history, state) = output then 1 else 0)) =
        ∑ history : History depth,
          tree.historyProbability semantics history *
            (if decode
                (history, tree.finalState semantics input history) = output
              then 1 else 0) := by
        apply Fintype.sum_congr
        intro history
        calc
          (∑ state : State,
            (if tree.finalState semantics input history = state
              then tree.historyProbability semantics history else 0) *
            (if decode (history, state) = output then 1 else 0)) =
              ∑ state : State,
                if tree.finalState semantics input history = state then
                  tree.historyProbability semantics history *
                    (if decode (history, state) = output then 1 else 0)
                else 0 := by
                  apply Fintype.sum_congr
                  intro state
                  by_cases equal :
                      tree.finalState semantics input history = state <;>
                    simp [equal]
          _ = tree.historyProbability semantics history *
                (if decode
                    (history, tree.finalState semantics input history) = output
                  then 1 else 0) :=
            Fintype.sum_ite_eq _ _
    _ = ∑ history : History depth,
          if input = output
            then tree.historyProbability semantics history else 0 := by
      apply Fintype.sum_congr
      intro history
      rw [decode_output]
      by_cases equal : input = output <;> simp [equal]
    _ = if input = output then 1 else 0 := by
      by_cases equal : input = output
      · simp [equal, tree.historyProbability_normalized semantics]
      · simp [equal]

/-- **Finite branch representation theorem.**  Evaluation is exactly the
recorded channel represented by the computed canonical normal form. -/
theorem representation (semantics : Semantics Generator State)
    (tree : Tree Generator depth) :
    tree.run semantics = (tree.normalForm semantics).toFinStoch :=
  rfl

variable [Inhabited State]

/-- **Observational completeness.**  Two adaptive protocols have identical
recorded stochastic behavior exactly when their canonical finite branch
tables agree. -/
theorem observationalCompleteness
    (semantics : Semantics Generator State)
    {first second : Tree Generator depth} :
    first.run semantics = second.run semantics ↔
      first.normalForm semantics = second.normalForm semantics :=
  NormalForm.toFinStoch_eq_iff

end Tree

end Ript.Syntax.Branching
