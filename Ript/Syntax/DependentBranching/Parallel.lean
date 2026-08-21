import Ript.Syntax.DependentBranching.Monoidal

/-!
# Independent parallel dependent-tree protocols

A parallel protocol keeps two dependent trees as explicit independent lanes.
Its complete history, state, probability, and resource cost are paired.  This
avoids forcing heterogeneous outcome types into one artificial generator and
preserves a real phase boundary for sequential composition.

Sequential leaf grafting acts componentwise.  Consequently tensor and graft
satisfy a strict interchange law: both lanes finish the first phase before
their second-phase continuations begin.  The stochastic representation
factors exactly into the two lane channels.
-/

set_option autoImplicit false

namespace Ript.Syntax.DependentBranching

open Ript.Models.FiniteStochastic
open Ript.Syntax.DependentBranching.Free

universe u

/-- Two explicit independent dependent-tree lanes. -/
@[ext]
structure ParallelProtocol (leftSignature rightSignature : Signature.{u}) where
  /-- Left protocol lane. -/
  left : Tree leftSignature
  /-- Right protocol lane. -/
  right : Tree rightSignature

namespace ParallelProtocol

variable {leftSignature rightSignature : Signature.{u}}
  {LeftState RightState : Type u}

/-- Construct an independent parallel protocol from two trees. -/
def tensor (left : Tree leftSignature) (right : Tree rightSignature) :
    ParallelProtocol leftSignature rightSignature :=
  ⟨left, right⟩

/-- Complete paired history of both lanes. -/
abbrev History (protocol : ParallelProtocol leftSignature rightSignature) :=
  protocol.left.History × protocol.right.History

/-- Maximum synchronized depth of the two lanes. -/
def height (protocol : ParallelProtocol leftSignature rightSignature) : Nat :=
  max protocol.left.height protocol.right.height

/-- Sum of the two lane worst-case budgets. -/
def budget (protocol : ParallelProtocol leftSignature rightSignature) : Nat :=
  protocol.left.budget + protocol.right.budget

/-- Exact cost of one paired history. -/
def historyCost (protocol : ParallelProtocol leftSignature rightSignature)
    (history : protocol.History) : Nat :=
  protocol.left.historyCost history.1 +
    protocol.right.historyCost history.2

/-- Every paired history cost stays within the summed parallel budget. -/
theorem historyCost_le_budget
    (protocol : ParallelProtocol leftSignature rightSignature)
    (history : protocol.History) :
    protocol.historyCost history ≤ protocol.budget :=
  Nat.add_le_add
    (protocol.left.historyCost_le_budget history.1)
    (protocol.right.historyCost_le_budget history.2)

/-- Exact probability of one independent paired history. -/
def historyProbability
    (protocol : ParallelProtocol leftSignature rightSignature)
    (leftSemantics : Semantics leftSignature LeftState)
    (rightSemantics : Semantics rightSignature RightState)
    (history : protocol.History) : ℚ≥0 :=
  protocol.left.historyProbability leftSemantics history.1 *
    protocol.right.historyProbability rightSemantics history.2

/-- Independent paired histories normalize exactly. -/
theorem historyProbability_normalized
    (protocol : ParallelProtocol leftSignature rightSignature)
    (leftSemantics : Semantics leftSignature LeftState)
    (rightSemantics : Semantics rightSignature RightState) :
    ∑ history, protocol.historyProbability
      leftSemantics rightSemantics history = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [historyProbability, ← Finset.mul_sum,
    protocol.right.historyProbability_normalized rightSemantics]
  simp [protocol.left.historyProbability_normalized leftSemantics]

/-- Residual paired state after both independent histories. -/
def finalState
    (protocol : ParallelProtocol leftSignature rightSignature)
    (leftSemantics : Semantics leftSignature LeftState)
    (rightSemantics : Semantics rightSignature RightState)
    (input : LeftState × RightState) (history : protocol.History) :
    LeftState × RightState :=
  (protocol.left.finalState leftSemantics input.1 history.1,
    protocol.right.finalState rightSemantics input.2 history.2)

/-- Canonical exact branch table of an independent parallel protocol. -/
def normalForm
    [Fintype LeftState] [DecidableEq LeftState]
    [Fintype RightState] [DecidableEq RightState]
    (protocol : ParallelProtocol leftSignature rightSignature)
    (leftSemantics : Semantics leftSignature LeftState)
    (rightSemantics : Semantics rightSignature RightState) :
    NormalForm protocol.History (LeftState × RightState) where
  probability := protocol.historyProbability leftSemantics rightSemantics
  output := protocol.finalState leftSemantics rightSemantics
  normalized := protocol.historyProbability_normalized
    leftSemantics rightSemantics
  positive history := mul_pos
    (protocol.left.historyProbability_pos leftSemantics history.1)
    (protocol.right.historyProbability_pos rightSemantics history.2)

/-- Exact history-recording stochastic channel of both lanes. -/
def run
    [Fintype LeftState] [DecidableEq LeftState]
    [Fintype RightState] [DecidableEq RightState]
    (protocol : ParallelProtocol leftSignature rightSignature)
    (leftSemantics : Semantics leftSignature LeftState)
    (rightSemantics : Semantics rightSignature RightState) :
    FinStoch (Object.of (LeftState × RightState))
      (Object.of (protocol.History × (LeftState × RightState))) :=
  (protocol.normalForm leftSemantics rightSemantics).toFinStoch

@[simp]
theorem run_apply
    [Fintype LeftState] [DecidableEq LeftState]
    [Fintype RightState] [DecidableEq RightState]
    (protocol : ParallelProtocol leftSignature rightSignature)
    (leftSemantics : Semantics leftSignature LeftState)
    (rightSemantics : Semantics rightSignature RightState)
    (input output : LeftState × RightState)
    (history : protocol.History) :
    (protocol.run leftSemantics rightSemantics).prob input (history, output) =
      if protocol.finalState leftSemantics rightSemantics input history = output
        then protocol.historyProbability leftSemantics rightSemantics history
        else 0 :=
  rfl

/-- **Independent-lane representation theorem.**  Every parallel channel entry
factors exactly into the two component tree-channel entries. -/
theorem run_factorization
    [Fintype LeftState] [DecidableEq LeftState]
    [Fintype RightState] [DecidableEq RightState]
    (protocol : ParallelProtocol leftSignature rightSignature)
    (leftSemantics : Semantics leftSignature LeftState)
    (rightSemantics : Semantics rightSignature RightState)
    (input output : LeftState × RightState)
    (history : protocol.History) :
    (protocol.run leftSemantics rightSemantics).prob input (history, output) =
      (protocol.left.run leftSemantics).prob input.1 (history.1, output.1) *
        (protocol.right.run rightSemantics).prob input.2
          (history.2, output.2) := by
  rw [run_apply, Tree.run_apply, Tree.run_apply]
  by_cases leftEqual :
      protocol.left.finalState leftSemantics input.1 history.1 = output.1 <;>
    by_cases rightEqual :
      protocol.right.finalState rightSemantics input.2 history.2 = output.2 <;>
    simp [ParallelProtocol.finalState, ParallelProtocol.historyProbability,
      leftEqual, rightEqual, Prod.ext_iff]

/-- Parallel evaluation is exactly its canonical branch-table representation. -/
theorem representation
    [Fintype LeftState] [DecidableEq LeftState]
    [Fintype RightState] [DecidableEq RightState]
    (protocol : ParallelProtocol leftSignature rightSignature)
    (leftSemantics : Semantics leftSignature LeftState)
    (rightSemantics : Semantics rightSignature RightState) :
    protocol.run leftSemantics rightSemantics =
      (protocol.normalForm leftSemantics rightSemantics).toFinStoch :=
  rfl

/-- Observational completeness after an explicit equivalence between paired
history types. -/
theorem observationalCompletenessAlong
    [Fintype LeftState] [DecidableEq LeftState] [Inhabited LeftState]
    [Fintype RightState] [DecidableEq RightState] [Inhabited RightState]
    (leftSemantics : Semantics leftSignature LeftState)
    (rightSemantics : Semantics rightSignature RightState)
    (first second : ParallelProtocol leftSignature rightSignature)
    (historyEquivalence : first.History ≃ second.History) :
    first.run leftSemantics rightSemantics =
        ((second.normalForm leftSemantics rightSemantics).reindexHistory
          historyEquivalence).toFinStoch ↔
      first.normalForm leftSemantics rightSemantics =
        (second.normalForm leftSemantics rightSemantics).reindexHistory
          historyEquivalence :=
  NormalForm.toFinStoch_eq_iff

/-! ## Symmetry -/

/-- Swap the two independent lanes. -/
def swap (protocol : ParallelProtocol leftSignature rightSignature) :
    ParallelProtocol rightSignature leftSignature :=
  ⟨protocol.right, protocol.left⟩

/-- Swapping lanes swaps complete histories. -/
def swapHistoryEquiv
    (protocol : ParallelProtocol leftSignature rightSignature) :
    protocol.History ≃ protocol.swap.History :=
  Equiv.prodComm _ _

@[simp]
theorem swap_swap (protocol : ParallelProtocol leftSignature rightSignature) :
    protocol.swap.swap = protocol :=
  rfl

@[simp]
theorem swap_budget (protocol : ParallelProtocol leftSignature rightSignature) :
    protocol.swap.budget = protocol.budget := by
  simp [ParallelProtocol.swap, ParallelProtocol.budget, Nat.add_comm]

theorem swap_historyCost
    (protocol : ParallelProtocol leftSignature rightSignature)
    (history : protocol.History) :
    protocol.swap.historyCost (protocol.swapHistoryEquiv history) =
      protocol.historyCost history := by
  change protocol.right.historyCost history.2 +
      protocol.left.historyCost history.1 =
    protocol.left.historyCost history.1 +
      protocol.right.historyCost history.2
  omega

theorem swap_historyProbability
    (protocol : ParallelProtocol leftSignature rightSignature)
    (leftSemantics : Semantics leftSignature LeftState)
    (rightSemantics : Semantics rightSignature RightState)
    (history : protocol.History) :
    protocol.swap.historyProbability rightSemantics leftSemantics
        (protocol.swapHistoryEquiv history) =
      protocol.historyProbability leftSemantics rightSemantics history := by
  change protocol.right.historyProbability rightSemantics history.2 *
      protocol.left.historyProbability leftSemantics history.1 =
    protocol.left.historyProbability leftSemantics history.1 *
      protocol.right.historyProbability rightSemantics history.2
  exact mul_comm _ _

/-! ## Sequential composition and interchange -/

/-- Empty two-lane protocol. -/
def empty (leftSignature rightSignature : Signature.{u}) :
    ParallelProtocol leftSignature rightSignature :=
  ⟨.leaf, .leaf⟩

/-- Sequentially graft both lanes at a shared phase boundary. -/
def graft (first second : ParallelProtocol leftSignature rightSignature) :
    ParallelProtocol leftSignature rightSignature :=
  ⟨Free.graft first.left second.left,
    Free.graft first.right second.right⟩

@[simp]
theorem empty_graft (protocol : ParallelProtocol leftSignature rightSignature) :
    graft (empty leftSignature rightSignature) protocol = protocol :=
  rfl

@[simp]
theorem graft_empty (protocol : ParallelProtocol leftSignature rightSignature) :
    graft protocol (empty leftSignature rightSignature) = protocol := by
  apply ParallelProtocol.ext
  · exact Free.graft_leaf protocol.left
  · exact Free.graft_leaf protocol.right

/-- Componentwise sequential composition is associative. -/
theorem graft_assoc (first second third :
    ParallelProtocol leftSignature rightSignature) :
    graft (graft first second) third = graft first (graft second third) := by
  apply ParallelProtocol.ext
  · exact Free.graft_assoc first.left second.left third.left
  · exact Free.graft_assoc first.right second.right third.right

/-- Parallel protocols form a monoid under shared-boundary grafting. -/
instance : Monoid (ParallelProtocol leftSignature rightSignature) where
  one := empty leftSignature rightSignature
  mul := graft
  one_mul := empty_graft
  mul_one := graft_empty
  mul_assoc := graft_assoc

/-- **Strict tensor--sequential interchange.**  Tensoring the two sequential
lanes equals sequentially composing the two parallel phases. -/
theorem tensor_graft_interchange
    (leftFirst leftSecond : Tree leftSignature)
    (rightFirst rightSecond : Tree rightSignature) :
    tensor (Free.graft leftFirst leftSecond)
        (Free.graft rightFirst rightSecond) =
      graft (tensor leftFirst rightFirst) (tensor leftSecond rightSecond) :=
  rfl

/-- Parallel worst-case budget remains subadditive under shared-boundary
sequential composition. -/
theorem budget_graft_le
    (first second : ParallelProtocol leftSignature rightSignature) :
    (graft first second).budget ≤ first.budget + second.budget := by
  calc
    (graft first second).budget =
        (Free.graft first.left second.left).budget +
          (Free.graft first.right second.right).budget := rfl
    _ ≤ (first.left.budget + second.left.budget) +
          (first.right.budget + second.right.budget) :=
      Nat.add_le_add
        (Free.budget_graft_le first.left second.left)
        (Free.budget_graft_le first.right second.right)
    _ = first.budget + second.budget := by
      change
        (first.left.budget + second.left.budget) +
            (first.right.budget + second.right.budget) =
          (first.left.budget + first.right.budget) +
            (second.left.budget + second.right.budget)
      ac_rfl

/-- Synchronized maximum height remains subadditive under shared-boundary
sequential composition. -/
theorem height_graft_le
    (first second : ParallelProtocol leftSignature rightSignature) :
    (graft first second).height ≤ first.height + second.height := by
  have leftBound := Free.height_graft_le first.left second.left
  have rightBound := Free.height_graft_le first.right second.right
  simp only [ParallelProtocol.graft, ParallelProtocol.height]
  apply max_le
  · exact leftBound.trans
      (Nat.add_le_add (Nat.le_max_left _ _) (Nat.le_max_left _ _))
  · exact rightBound.trans
      (Nat.add_le_add (Nat.le_max_right _ _) (Nat.le_max_right _ _))

end ParallelProtocol

end Ript.Syntax.DependentBranching
