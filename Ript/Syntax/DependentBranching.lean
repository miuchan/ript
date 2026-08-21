import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.NNRat.BigOperators
import Ript.Models.FiniteStochastic
import Ript.Syntax.Branching

/-!
# Variable-depth dependent finite branching protocols

This module generalizes fixed-depth binary branching to genuinely dependent
finite trees.  Every generator carries its own finite outcome type, and every
outcome selects an arbitrary continuation tree, so different branches may
terminate at different depths.

Complete histories are dependent Sigma types computed from the tree itself.
Exact positive rational semantics produce a canonical finite branch table and
an exact history-recording stochastic channel.  Because different trees can
have different history types, observational comparison explicitly carries an
equivalence between those types.  The representation and completeness
theorems are stated along that equivalence rather than relying on an unsafe or
implicit identification.
-/

set_option autoImplicit false

namespace Ript.Syntax.DependentBranching

open scoped BigOperators

open Ript.Models.FiniteStochastic

universe u

/-- Generators with generator-dependent finite outcome carriers and scalar
resource costs. -/
structure Signature where
  /-- Primitive process labels. -/
  Generator : Type u
  /-- Finite result type exposed by each primitive. -/
  Outcome : Generator → Type u
  /-- Executable enumeration of every result type. -/
  outcomeFintype : (generator : Generator) → Fintype (Outcome generator)
  /-- Executable equality of every result type. -/
  outcomeDecidableEq : (generator : Generator) → DecidableEq (Outcome generator)
  /-- Scalar resource charge of every primitive. -/
  cost : Generator → Nat

namespace Signature

instance (signature : Signature.{u}) (generator : signature.Generator) :
    Fintype (signature.Outcome generator) :=
  signature.outcomeFintype generator

instance (signature : Signature.{u}) (generator : signature.Generator) :
    DecidableEq (signature.Outcome generator) :=
  signature.outcomeDecidableEq generator

end Signature

/-- A finite variable-depth dependent branching protocol. -/
inductive Tree (signature : Signature.{u}) : Type u where
  /-- Terminate without another observation. -/
  | leaf : Tree signature
  /-- Execute one generator and choose an arbitrary continuation from its
  generator-specific outcome. -/
  | node (generator : signature.Generator)
      (next : signature.Outcome generator → Tree signature) : Tree signature

namespace Tree

variable {signature : Signature.{u}}

/-- Canonical dependent complete-history type of one tree. -/
def History : Tree signature → Type u
  | .leaf => PUnit.{u + 1}
  | .node generator next =>
      Σ outcome : signature.Outcome generator, (next outcome).History

/-- Executable enumeration of dependent complete histories. -/
@[instance_reducible]
def historyFintype : (tree : Tree signature) → Fintype tree.History
  | .leaf => by
      change Fintype PUnit
      infer_instance
  | .node generator next => by
      letI : ∀ outcome, Fintype (next outcome).History :=
        fun outcome ↦ historyFintype (next outcome)
      change Fintype (Σ outcome : signature.Outcome generator,
        (next outcome).History)
      infer_instance

instance (tree : Tree signature) : Fintype tree.History :=
  tree.historyFintype

/-- Executable equality of dependent complete histories. -/
def historyDecidableEq : (tree : Tree signature) → DecidableEq tree.History
  | .leaf => by
      change DecidableEq PUnit
      infer_instance
  | .node generator next => by
      letI : ∀ outcome, DecidableEq (next outcome).History :=
        fun outcome ↦ historyDecidableEq (next outcome)
      change DecidableEq (Σ outcome : signature.Outcome generator,
        (next outcome).History)
      infer_instance

instance (tree : Tree signature) : DecidableEq tree.History :=
  tree.historyDecidableEq

/-- Number of generator observations in one concrete history. -/
def historyLength : (tree : Tree signature) → tree.History → Nat
  | .leaf, _ => 0
  | .node _ next, history =>
      1 + (next history.1).historyLength history.2

/-- Maximum depth of a finite dependent tree. -/
def height : Tree signature → Nat
  | .leaf => 0
  | .node _ next =>
      1 + Finset.univ.sup fun outcome ↦ (next outcome).height

/-- Exact resource cost accumulated along one dependent history. -/
def historyCost : (tree : Tree signature) → tree.History → Nat
  | .leaf, _ => 0
  | .node generator next, history =>
      signature.cost generator + (next history.1).historyCost history.2

/-- Worst-case resource cost, computed as a finite supremum over every
generator-specific continuation. -/
def budget : Tree signature → Nat
  | .leaf => 0
  | .node generator next =>
      signature.cost generator +
        Finset.univ.sup fun outcome ↦ (next outcome).budget

/-- Every concrete history length is bounded by the computed tree height. -/
theorem historyLength_le_height (tree : Tree signature)
    (history : tree.History) : tree.historyLength history ≤ tree.height := by
  induction tree with
  | leaf =>
      change (0 : Nat) ≤ 0
      exact le_rfl
  | node generator next induction =>
      rcases history with ⟨outcome, history⟩
      simp only [historyLength, height]
      apply Nat.add_le_add_left
      exact (induction outcome history).trans
        (Finset.le_sup (f := fun result ↦ (next result).height)
          (Finset.mem_univ outcome))

/-- Every concrete history cost is bounded by the exact worst-case budget. -/
theorem historyCost_le_budget (tree : Tree signature)
    (history : tree.History) : tree.historyCost history ≤ tree.budget := by
  induction tree with
  | leaf =>
      change (0 : Nat) ≤ 0
      exact le_rfl
  | node generator next induction =>
      rcases history with ⟨outcome, history⟩
      simp only [historyCost, budget]
      apply Nat.add_le_add_left
      exact (induction outcome history).trans
        (Finset.le_sup (f := fun result ↦ (next result).budget)
          (Finset.mem_univ outcome))

end Tree

/-- Exact positive semantics of a dependent finite branching signature. -/
structure Semantics (signature : Signature.{u}) (State : Type u) where
  /-- Exact probability of one generator-specific outcome. -/
  weight : (generator : signature.Generator) →
    signature.Outcome generator → ℚ≥0
  /-- Every generator-specific outcome distribution is normalized. -/
  normalized : ∀ generator,
    ∑ outcome, weight generator outcome = 1
  /-- Strict positivity makes every valid dependent history observable. -/
  positive : ∀ generator outcome, 0 < weight generator outcome
  /-- Deterministic residual-state update conditioned on an outcome. -/
  transition : (generator : signature.Generator) →
    signature.Outcome generator → State → State

namespace Tree

variable {signature : Signature.{u}} {State : Type u}

/-- Exact probability of one dependent complete history. -/
def historyProbability (semantics : Semantics signature State) :
    (tree : Tree signature) → tree.History → ℚ≥0
  | .leaf, _ => 1
  | .node generator next, history =>
      semantics.weight generator history.1 *
        (next history.1).historyProbability semantics history.2

/-- Residual state computed along one dependent complete history. -/
def finalState (semantics : Semantics signature State) :
    (tree : Tree signature) → State → tree.History → State
  | .leaf, input, _ => input
  | .node generator next, input, history =>
      (next history.1).finalState semantics
        (semantics.transition generator history.1 input) history.2

/-- Dependent complete-history probabilities normalize exactly. -/
theorem historyProbability_normalized
    (semantics : Semantics signature State) (tree : Tree signature) :
    ∑ history, tree.historyProbability semantics history = 1 := by
  induction tree with
  | leaf =>
      change (∑ _ : PUnit, (1 : ℚ≥0)) = 1
      simp
  | node generator next induction =>
      change (∑ history : Σ outcome : signature.Outcome generator,
        (next outcome).History,
          semantics.weight generator history.1 *
            (next history.1).historyProbability semantics history.2) = 1
      rw [Fintype.sum_sigma]
      simp_rw [← Finset.mul_sum, induction]
      simpa using semantics.normalized generator

/-- Strictly positive primitive outcomes give strictly positive valid
dependent histories. -/
theorem historyProbability_pos
    (semantics : Semantics signature State) (tree : Tree signature)
    (history : tree.History) :
    0 < tree.historyProbability semantics history := by
  induction tree with
  | leaf => simp [historyProbability]
  | node generator next induction =>
      rcases history with ⟨outcome, history⟩
      exact mul_pos (semantics.positive generator outcome)
        (induction outcome history)

end Tree

/-- Canonical finite table over an arbitrary dependent history carrier. -/
@[ext]
structure NormalForm (History State : Type u)
    [Fintype History] [DecidableEq History]
    [Fintype State] [DecidableEq State] where
  /-- Exact probability of every valid complete history. -/
  probability : History → ℚ≥0
  /-- Final state for every input and history. -/
  output : State → History → State
  /-- History probabilities are normalized. -/
  normalized : ∑ history, probability history = 1
  /-- Every table row is operationally visible. -/
  positive : ∀ history, 0 < probability history

namespace NormalForm

variable {History OtherHistory State OtherState : Type u}
  [Fintype History] [DecidableEq History]
  [Fintype OtherHistory] [DecidableEq OtherHistory]
  [Fintype State] [DecidableEq State]
  [Fintype OtherState] [DecidableEq OtherState]

/-- Exact history-recording stochastic channel represented by a dependent
normal-form table. -/
def toFinStoch (normalForm : NormalForm History State) :
    FinStoch (Object.of State) (Object.of (History × State)) where
  prob input result :=
    if normalForm.output input result.1 = result.2
      then normalForm.probability result.1 else 0
  normalized input := by
    rw [Fintype.sum_prod_type]
    simpa using normalForm.normalized

@[simp]
theorem toFinStoch_apply (normalForm : NormalForm History State)
    (input : State) (history : History) (output : State) :
    normalForm.toFinStoch.prob input (history, output) =
      if normalForm.output input history = output
        then normalForm.probability history else 0 :=
  rfl

/-- Summing out the residual state recovers a dependent history weight. -/
theorem historyMarginal (normalForm : NormalForm History State)
    (input : State) (history : History) :
    ∑ output, normalForm.toFinStoch.prob input (history, output) =
      normalForm.probability history := by
  simp [toFinStoch_apply]

/-- A table is visible at its deterministic represented output. -/
theorem toFinStoch_output (normalForm : NormalForm History State)
    (input : State) (history : History) :
    normalForm.toFinStoch.prob input
        (history, normalForm.output input history) =
      normalForm.probability history := by
  simp [toFinStoch_apply]

/-- Transport a normal form to an equivalent history carrier. -/
def reindexHistory (equivalence : History ≃ OtherHistory)
    (normalForm : NormalForm OtherHistory State) :
    NormalForm History State where
  probability history := normalForm.probability (equivalence history)
  output input history := normalForm.output input (equivalence history)
  normalized :=
    (equivalence.sum_comp normalForm.probability).trans normalForm.normalized
  positive history := normalForm.positive (equivalence history)

@[simp]
theorem reindexHistory_probability (equivalence : History ≃ OtherHistory)
    (normalForm : NormalForm OtherHistory State) (history : History) :
    (normalForm.reindexHistory equivalence).probability history =
      normalForm.probability (equivalence history) :=
  rfl

@[simp]
theorem reindexHistory_output (equivalence : History ≃ OtherHistory)
    (normalForm : NormalForm OtherHistory State)
    (input : State) (history : History) :
    (normalForm.reindexHistory equivalence).output input history =
      normalForm.output input (equivalence history) :=
  rfl

/-- Transport both the complete-history carrier and the residual-state
carrier along explicit equivalences.  State updates are conjugated, so this
operation changes only the chosen finite presentation of a normal form. -/
def reindex (historyEquivalence : History ≃ OtherHistory)
    (stateEquivalence : State ≃ OtherState)
    (normalForm : NormalForm OtherHistory OtherState) :
    NormalForm History State where
  probability history := normalForm.probability (historyEquivalence history)
  output input history := stateEquivalence.symm
    (normalForm.output (stateEquivalence input) (historyEquivalence history))
  normalized :=
    (historyEquivalence.sum_comp normalForm.probability).trans
      normalForm.normalized
  positive history := normalForm.positive (historyEquivalence history)

@[simp]
theorem reindex_probability (historyEquivalence : History ≃ OtherHistory)
    (stateEquivalence : State ≃ OtherState)
    (normalForm : NormalForm OtherHistory OtherState) (history : History) :
    (normalForm.reindex historyEquivalence stateEquivalence).probability
        history =
      normalForm.probability (historyEquivalence history) :=
  rfl

@[simp]
theorem reindex_output (historyEquivalence : History ≃ OtherHistory)
    (stateEquivalence : State ≃ OtherState)
    (normalForm : NormalForm OtherHistory OtherState)
    (input : State) (history : History) :
    (normalForm.reindex historyEquivalence stateEquivalence).output
        input history =
      stateEquivalence.symm
        (normalForm.output (stateEquivalence input)
          (historyEquivalence history)) :=
  rfl

variable [Inhabited State]

/-- **Dependent-table faithfulness.**  A recorded stochastic channel uniquely
determines every strictly positive branch-table entry. -/
theorem toFinStoch_injective :
    Function.Injective
      (toFinStoch : NormalForm History State →
        FinStoch (Object.of State) (Object.of (History × State))) := by
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

/-- Equality of dependent recorded behavior is equivalent to equality of the
canonical branch tables. -/
theorem toFinStoch_eq_iff {first second : NormalForm History State} :
    first.toFinStoch = second.toFinStoch ↔ first = second :=
  ⟨fun equalChannels ↦ toFinStoch_injective equalChannels,
    congrArg toFinStoch⟩

end NormalForm

namespace Tree

variable {signature : Signature.{u}} {State : Type u}
  [Fintype State] [DecidableEq State]

/-- Compute the canonical dependent branch table of a variable-depth tree. -/
def normalForm (semantics : Semantics signature State)
    (tree : Tree signature) : NormalForm tree.History State where
  probability := tree.historyProbability semantics
  output := tree.finalState semantics
  normalized := tree.historyProbability_normalized semantics
  positive := tree.historyProbability_pos semantics

/-- Execute a variable-depth dependent tree as an exact history-recording
stochastic channel. -/
def run (semantics : Semantics signature State) (tree : Tree signature) :
    FinStoch (Object.of State) (Object.of (tree.History × State)) :=
  (tree.normalForm semantics).toFinStoch

@[simp]
theorem run_apply (semantics : Semantics signature State)
    (tree : Tree signature) (input : State)
    (history : tree.History) (output : State) :
    (tree.run semantics).prob input (history, output) =
      if tree.finalState semantics input history = output
        then tree.historyProbability semantics history else 0 :=
  rfl

/-- **Dependent branch representation theorem.**  Evaluation is exactly the
recorded channel represented by the computed canonical table. -/
theorem representation (semantics : Semantics signature State)
    (tree : Tree signature) :
    tree.run semantics = (tree.normalForm semantics).toFinStoch :=
  rfl

variable [Inhabited State]

/-- **Observational completeness along a history equivalence.**  Two trees
with possibly different dependent history types have the same recorded
behavior after explicit history reindexing exactly when their canonical tables
agree after that same reindexing. -/
theorem observationalCompletenessAlong
    (semantics : Semantics signature State)
    (first second : Tree signature)
    (historyEquivalence : first.History ≃ second.History) :
    first.run semantics =
        ((second.normalForm semantics).reindexHistory
          historyEquivalence).toFinStoch ↔
      first.normalForm semantics =
        (second.normalForm semantics).reindexHistory historyEquivalence :=
  NormalForm.toFinStoch_eq_iff

end Tree

/-! ## Embedding of fixed-depth binary branching -/

namespace BinaryEmbedding

open Ript.Syntax.Branching

variable {Generator State : Type} {depth : Nat}

/-- Regard a fixed-depth binary cost signature as a dependent finite-outcome
signature. -/
def signature (costModel : Branching.CostModel Generator) : Signature where
  Generator := Generator
  Outcome _ := Bool
  outcomeFintype _ := inferInstance
  outcomeDecidableEq _ := inferInstance
  cost := costModel.cost

/-- Embed every fixed-depth binary tree into the variable-depth language. -/
def tree (costModel : Branching.CostModel Generator) :
    {depth : Nat} → Branching.Tree Generator depth →
      Tree (signature costModel)
  | 0, .leaf => .leaf
  | _ + 1, .node generator next =>
      .node generator fun outcome ↦ tree costModel (next outcome)

/-- Embed exact binary semantics without changing weights or transitions. -/
def semantics (costModel : Branching.CostModel Generator)
    (binary : Branching.Semantics Generator State) :
    Semantics (signature costModel) State where
  weight := binary.weight
  normalized := binary.normalized
  positive := binary.positive
  transition := binary.transition

/-- Canonical equivalence between dependent histories of an embedded tree and
the original fixed-depth binary history type. -/
def historyEquiv (costModel : Branching.CostModel Generator) :
    {depth : Nat} → (binaryTree : Branching.Tree Generator depth) →
      (tree costModel binaryTree).History ≃ Branching.History depth
  | 0, .leaf => Equiv.refl _
  | _ + 1, .node _ next =>
      { toFun := fun history ↦
          ⟨history.1,
            historyEquiv costModel (next history.1) history.2⟩
        invFun := fun history ↦
          ⟨history.1,
            (historyEquiv costModel (next history.1)).symm history.2⟩
        left_inv := by
          rintro ⟨outcome, history⟩
          simp
          rfl
        right_inv := by
          rintro ⟨outcome, history⟩
          simp
          rfl }

/-- Embedded dependent histories retain exact binary branch probabilities. -/
theorem historyProbability_tree
    (costModel : Branching.CostModel Generator)
    (binary : Branching.Semantics Generator State)
    (binaryTree : Branching.Tree Generator depth)
    (history : (tree costModel binaryTree).History) :
    (tree costModel binaryTree).historyProbability
        (semantics costModel binary) history =
      binaryTree.historyProbability binary
        (historyEquiv costModel binaryTree history) := by
  induction binaryTree with
  | leaf =>
      change (1 : ℚ≥0) = 1
      rfl
  | node generator next induction =>
      rcases history with ⟨outcome, history⟩
      change binary.weight generator outcome *
          (tree costModel (next outcome)).historyProbability
            (semantics costModel binary) history =
        binary.weight generator outcome *
          (next outcome).historyProbability binary
            (historyEquiv costModel (next outcome) history)
      rw [induction outcome history]

/-- Embedded dependent histories retain exact binary residual states. -/
theorem finalState_tree
    (costModel : Branching.CostModel Generator)
    (binary : Branching.Semantics Generator State)
    (binaryTree : Branching.Tree Generator depth)
    (input : State) (history : (tree costModel binaryTree).History) :
    (tree costModel binaryTree).finalState
        (semantics costModel binary) input history =
      binaryTree.finalState binary input
        (historyEquiv costModel binaryTree history) := by
  induction binaryTree generalizing input with
  | leaf => rfl
  | node generator next induction =>
      rcases history with ⟨outcome, history⟩
      exact induction outcome (binary.transition generator outcome input) history

/-- The embedding preserves exact realized path costs. -/
theorem historyCost_tree
    (costModel : Branching.CostModel Generator)
    (binaryTree : Branching.Tree Generator depth)
    (history : (tree costModel binaryTree).History) :
    (tree costModel binaryTree).historyCost history =
      binaryTree.historyCost costModel
        (historyEquiv costModel binaryTree history) := by
  induction binaryTree with
  | leaf => rfl
  | node generator next induction =>
      rcases history with ⟨outcome, history⟩
      change costModel.cost generator +
          (tree costModel (next outcome)).historyCost history =
        costModel.cost generator +
          (next outcome).historyCost costModel
            (historyEquiv costModel (next outcome) history)
      rw [induction outcome history]

/-- The dependent evaluator is exactly the binary evaluator after the
canonical history equivalence. -/
theorem run_tree_apply
    [Fintype State] [DecidableEq State]
    (costModel : Branching.CostModel Generator)
    (binary : Branching.Semantics Generator State)
    (binaryTree : Branching.Tree Generator depth)
    (input output : State)
    (history : (tree costModel binaryTree).History) :
    ((tree costModel binaryTree).run (semantics costModel binary)).prob
        input (history, output) =
      (binaryTree.run binary).prob input
        (historyEquiv costModel binaryTree history, output) := by
  rw [Tree.run_apply, Branching.Tree.run_apply,
    historyProbability_tree, finalState_tree]

end BinaryEmbedding

end Ript.Syntax.DependentBranching
