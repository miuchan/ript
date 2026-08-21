import Mathlib.Algebra.BigOperators.Ring.Finset
import Ript.Syntax.DependentBranching.Parallel

/-!
# Finite n-ary independent dependent-tree protocols

An n-ary protocol is indexed by an executable finite lane type.  Signatures,
state carriers, trees, histories, and semantics may all depend on the lane.
Joint history probability is the finite product of lane probabilities; exact
normalization follows from the finite product-of-sums theorem.

Lane equivalences reindex protocols explicitly.  This supplies coherent
finite permutation symmetry without choosing an ordering of lanes.  Sequential
leaf grafting is pointwise and satisfies strict n-ary tensor--sequential
interchange.
-/

set_option autoImplicit false

namespace Ript.Syntax.DependentBranching

open scoped BigOperators

open Ript.Models.FiniteStochastic
open Ript.Syntax.DependentBranching.Free

universe u

/-- A finite family of independent dependent-tree lanes. -/
@[ext]
structure LaneProtocol (Lane : Type u) [Fintype Lane] [DecidableEq Lane]
    (signature : Lane → Signature.{u}) where
  /-- Protocol tree in every lane. -/
  tree : (lane : Lane) → Tree (signature lane)

namespace LaneProtocol

variable {Lane OtherLane : Type u}
  [Fintype Lane] [DecidableEq Lane]
  [Fintype OtherLane] [DecidableEq OtherLane]
  {signature : Lane → Signature.{u}}
  {State : Lane → Type u}

/-- Construct an n-ary protocol from its lane trees. -/
abbrev tensor (tree : (lane : Lane) → Tree (signature lane)) :
    LaneProtocol Lane signature :=
  ⟨tree⟩

/-- Complete dependent history assignment for every lane. -/
abbrev History (protocol : LaneProtocol Lane signature) :=
  (lane : Lane) → (protocol.tree lane).History

instance (protocol : LaneProtocol Lane signature) : Fintype protocol.History :=
  inferInstance

instance (protocol : LaneProtocol Lane signature) :
    DecidableEq protocol.History :=
  inferInstance

/-- Maximum synchronized lane depth. -/
def height (protocol : LaneProtocol Lane signature) : Nat :=
  Finset.univ.sup fun lane ↦ (protocol.tree lane).height

/-- Sum of worst-case lane budgets. -/
def budget (protocol : LaneProtocol Lane signature) : Nat :=
  ∑ lane, (protocol.tree lane).budget

/-- Exact total cost of one complete lane-history assignment. -/
def historyCost (protocol : LaneProtocol Lane signature)
    (history : protocol.History) : Nat :=
  ∑ lane, (protocol.tree lane).historyCost (history lane)

/-- Every n-ary history cost is bounded by the summed lane budget. -/
theorem historyCost_le_budget (protocol : LaneProtocol Lane signature)
    (history : protocol.History) :
    protocol.historyCost history ≤ protocol.budget := by
  apply Finset.sum_le_sum
  intro lane _
  exact (protocol.tree lane).historyCost_le_budget (history lane)

/-- Exact product probability of a complete lane-history assignment. -/
def historyProbability (protocol : LaneProtocol Lane signature)
    (semantics : (lane : Lane) → Semantics (signature lane) (State lane))
    (history : protocol.History) : ℚ≥0 :=
  ∏ lane, (protocol.tree lane).historyProbability
    (semantics lane) (history lane)

/-- Independent n-ary history probabilities normalize exactly. -/
theorem historyProbability_normalized
    (protocol : LaneProtocol Lane signature)
    (semantics : (lane : Lane) → Semantics (signature lane) (State lane)) :
    ∑ history, protocol.historyProbability semantics history = 1 := by
  change (∑ history : (lane : Lane) → (protocol.tree lane).History,
    ∏ lane, (protocol.tree lane).historyProbability
      (semantics lane) (history lane)) = 1
  rw [← Fintype.prod_sum]
  simp_rw [fun lane ↦
    (protocol.tree lane).historyProbability_normalized (semantics lane)]
  simp

/-- Pointwise residual state after every lane history. -/
def finalState (protocol : LaneProtocol Lane signature)
    (semantics : (lane : Lane) → Semantics (signature lane) (State lane))
    (input : (lane : Lane) → State lane) (history : protocol.History) :
    (lane : Lane) → State lane :=
  fun lane ↦ (protocol.tree lane).finalState
    (semantics lane) (input lane) (history lane)

/-- Canonical exact branch table of an n-ary protocol. -/
def normalForm
    [∀ lane, Fintype (State lane)] [∀ lane, DecidableEq (State lane)]
    (protocol : LaneProtocol Lane signature)
    (semantics : (lane : Lane) → Semantics (signature lane) (State lane)) :
    NormalForm protocol.History ((lane : Lane) → State lane) where
  probability := protocol.historyProbability semantics
  output := protocol.finalState semantics
  normalized := protocol.historyProbability_normalized semantics
  positive history := Finset.prod_pos fun lane _ ↦
    (protocol.tree lane).historyProbability_pos
      (semantics lane) (history lane)

/-- Exact history-recording stochastic channel of all lanes. -/
def run
    [∀ lane, Fintype (State lane)] [∀ lane, DecidableEq (State lane)]
    (protocol : LaneProtocol Lane signature)
    (semantics : (lane : Lane) → Semantics (signature lane) (State lane)) :
    FinStoch (Object.of ((lane : Lane) → State lane))
      (Object.of (protocol.History × ((lane : Lane) → State lane))) :=
  (protocol.normalForm semantics).toFinStoch

@[simp]
theorem run_apply
    [∀ lane, Fintype (State lane)] [∀ lane, DecidableEq (State lane)]
    (protocol : LaneProtocol Lane signature)
    (semantics : (lane : Lane) → Semantics (signature lane) (State lane))
    (input output : (lane : Lane) → State lane)
    (history : protocol.History) :
    (protocol.run semantics).prob input (history, output) =
      if protocol.finalState semantics input history = output
        then protocol.historyProbability semantics history else 0 :=
  rfl

/-- **N-ary independent-lane representation.**  Every recorded channel entry
is the finite product of the corresponding lane entries. -/
theorem run_factorization
    [∀ lane, Fintype (State lane)] [∀ lane, DecidableEq (State lane)]
    (protocol : LaneProtocol Lane signature)
    (semantics : (lane : Lane) → Semantics (signature lane) (State lane))
    (input output : (lane : Lane) → State lane)
    (history : protocol.History) :
    (protocol.run semantics).prob input (history, output) =
      ∏ lane, ((protocol.tree lane).run (semantics lane)).prob
        (input lane) (history lane, output lane) := by
  rw [run_apply]
  by_cases allEqual : protocol.finalState semantics input history = output
  · have componentEqual : ∀ lane,
        (protocol.tree lane).finalState (semantics lane)
            (input lane) (history lane) = output lane := by
      intro lane
      exact congrFun allEqual lane
    rw [if_pos allEqual]
    apply Finset.prod_congr rfl
    intro lane _
    rw [Tree.run_apply, if_pos (componentEqual lane)]
  · rw [if_neg allEqual]
    have notAllComponents : ¬ ∀ lane,
        (protocol.tree lane).finalState (semantics lane)
            (input lane) (history lane) = output lane := by
      intro equalComponents
      exact allEqual (funext equalComponents)
    obtain ⟨lane, unequal⟩ := Classical.not_forall.mp notAllComponents
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ lane)
    rw [Tree.run_apply, if_neg unequal]

/-- N-ary evaluation is exactly its canonical branch-table representation. -/
theorem representation
    [∀ lane, Fintype (State lane)] [∀ lane, DecidableEq (State lane)]
    (protocol : LaneProtocol Lane signature)
    (semantics : (lane : Lane) → Semantics (signature lane) (State lane)) :
    protocol.run semantics = (protocol.normalForm semantics).toFinStoch :=
  rfl

/-- N-ary observational completeness after an explicit equivalence between
dependent lane-history assignments. -/
theorem observationalCompletenessAlong
    [∀ lane, Fintype (State lane)] [∀ lane, DecidableEq (State lane)]
    [∀ lane, Inhabited (State lane)]
    (semantics : (lane : Lane) → Semantics (signature lane) (State lane))
    (first second : LaneProtocol Lane signature)
    (historyEquivalence : first.History ≃ second.History) :
    first.run semantics =
        ((second.normalForm semantics).reindexHistory
          historyEquivalence).toFinStoch ↔
      first.normalForm semantics =
        (second.normalForm semantics).reindexHistory historyEquivalence :=
  NormalForm.toFinStoch_eq_iff

/-! ## Lane equivalence and symmetry -/

/-- Reindex every lane along an explicit finite equivalence. -/
abbrev reindex (equivalence : OtherLane ≃ Lane)
    (protocol : LaneProtocol Lane signature) :
    LaneProtocol OtherLane (fun lane ↦ signature (equivalence lane)) where
  tree lane := protocol.tree (equivalence lane)

/-- Reindexing lanes transports complete history assignments by the same
equivalence. -/
abbrev reindexHistoryEquiv (equivalence : OtherLane ≃ Lane)
    (protocol : LaneProtocol Lane signature) :
    (protocol.reindex equivalence).History ≃ protocol.History :=
  Equiv.piCongrLeft (fun lane ↦ (protocol.tree lane).History) equivalence

/-- Reindex a dependent lane-state assignment along a lane equivalence. -/
abbrev reindexStateEquiv (equivalence : OtherLane ≃ Lane) :
    ((lane : OtherLane) → State (equivalence lane)) ≃
      ((lane : Lane) → State lane) :=
  Equiv.piCongrLeft State equivalence

/-- Reindexing preserves the summed worst-case budget exactly. -/
theorem reindex_budget (equivalence : OtherLane ≃ Lane)
    (protocol : LaneProtocol Lane signature) :
    (protocol.reindex equivalence).budget = protocol.budget := by
  exact equivalence.sum_comp fun lane ↦ (protocol.tree lane).budget

/-- Reindexing preserves exact joint history probability. -/
theorem reindex_historyProbability
    (equivalence : OtherLane ≃ Lane)
    (protocol : LaneProtocol Lane signature)
    (semantics : (lane : Lane) → Semantics (signature lane) (State lane))
    (history : (protocol.reindex equivalence).History) :
    (protocol.reindex equivalence).historyProbability
        (fun lane ↦ semantics (equivalence lane)) history =
      protocol.historyProbability semantics
        (protocol.reindexHistoryEquiv equivalence history) := by
  change (∏ lane,
      (protocol.tree (equivalence lane)).historyProbability
        (semantics (equivalence lane)) (history lane)) = _
  calc
    _ = ∏ lane,
        (protocol.tree (equivalence lane)).historyProbability
          (semantics (equivalence lane))
          (protocol.reindexHistoryEquiv equivalence history
            (equivalence lane)) := by
      apply Finset.prod_congr rfl
      intro lane _
      rw [reindexHistoryEquiv, Equiv.piCongrLeft_apply_apply]
    _ = ∏ lane,
        (protocol.tree lane).historyProbability
          (semantics lane)
          (protocol.reindexHistoryEquiv equivalence history lane) := by
      let laneWeight : Lane → ℚ≥0 := fun lane ↦
        (protocol.tree lane).historyProbability
          (semantics lane)
          (protocol.reindexHistoryEquiv equivalence history lane)
      change (∏ lane, laneWeight (equivalence lane)) = ∏ lane, laneWeight lane
      exact equivalence.prod_comp laneWeight

/-- Reindexing lanes commutes exactly with residual-state evaluation after
transporting the input, history, and output assignments by their canonical
dependent function equivalences. -/
theorem reindex_finalState
    (equivalence : OtherLane ≃ Lane)
    (protocol : LaneProtocol Lane signature)
    (semantics : (lane : Lane) → Semantics (signature lane) (State lane))
    (input : (lane : OtherLane) → State (equivalence lane))
    (history : (protocol.reindex equivalence).History) :
    reindexStateEquiv (State := State) equivalence
        ((protocol.reindex equivalence).finalState
          (fun lane ↦ semantics (equivalence lane)) input history) =
      protocol.finalState semantics
        (reindexStateEquiv (State := State) equivalence input)
        (protocol.reindexHistoryEquiv equivalence history) := by
  funext lane
  obtain ⟨otherLane, rfl⟩ := equivalence.surjective lane
  simp only [reindexStateEquiv, Equiv.piCongrLeft_apply_apply]
  change
    (protocol.tree (equivalence otherLane)).finalState
        (semantics (equivalence otherLane)) (input otherLane)
        (history otherLane) =
      (protocol.tree (equivalence otherLane)).finalState
        (semantics (equivalence otherLane))
        ((Equiv.piCongrLeft State equivalence) input
          (equivalence otherLane))
        ((Equiv.piCongrLeft
          (fun lane ↦ (protocol.tree lane).History) equivalence) history
            (equivalence otherLane))
  simp

/-- **Finite-lane permutation coherence.**  Reindexing an n-ary protocol and
then normalizing is exactly the simultaneous history/state reindexing of its
canonical normal form.  Thus lane names and finite lane order carry no
semantic information. -/
theorem reindex_normalForm
    [∀ lane, Fintype (State lane)] [∀ lane, DecidableEq (State lane)]
    (equivalence : OtherLane ≃ Lane)
    (protocol : LaneProtocol Lane signature)
    (semantics : (lane : Lane) → Semantics (signature lane) (State lane)) :
    (protocol.reindex equivalence).normalForm
        (fun lane ↦ semantics (equivalence lane)) =
      (protocol.normalForm semantics).reindex
        (protocol.reindexHistoryEquiv equivalence)
        (reindexStateEquiv (State := State) equivalence) := by
  apply NormalForm.ext
  · funext history
    exact protocol.reindex_historyProbability equivalence semantics history
  · funext input history
    change
      (protocol.reindex equivalence).finalState
          (fun lane ↦ semantics (equivalence lane)) input history =
        (reindexStateEquiv (State := State) equivalence).symm
          (protocol.finalState semantics
            (reindexStateEquiv (State := State) equivalence input)
            (protocol.reindexHistoryEquiv equivalence history))
    apply (reindexStateEquiv (State := State) equivalence).injective
    rw [Equiv.apply_symm_apply]
    exact protocol.reindex_finalState equivalence semantics input history

/-! ## N-ary sequential composition and interchange -/

/-- Empty protocol in every lane. -/
def empty (Lane : Type u) [Fintype Lane] [DecidableEq Lane]
    (signature : Lane → Signature.{u}) : LaneProtocol Lane signature :=
  ⟨fun _ ↦ .leaf⟩

/-- Pointwise sequential grafting at one shared n-lane phase boundary. -/
def graft (first second : LaneProtocol Lane signature) :
    LaneProtocol Lane signature :=
  ⟨fun lane ↦ Free.graft (first.tree lane) (second.tree lane)⟩

@[simp]
theorem empty_graft (protocol : LaneProtocol Lane signature) :
    graft (empty Lane signature) protocol = protocol :=
  rfl

@[simp]
theorem graft_empty (protocol : LaneProtocol Lane signature) :
    graft protocol (empty Lane signature) = protocol := by
  apply LaneProtocol.ext
  funext lane
  exact Free.graft_leaf (protocol.tree lane)

/-- Pointwise n-ary grafting is associative. -/
theorem graft_assoc (first second third : LaneProtocol Lane signature) :
    graft (graft first second) third = graft first (graft second third) := by
  apply LaneProtocol.ext
  funext lane
  exact Free.graft_assoc
    (first.tree lane) (second.tree lane) (third.tree lane)

/-- N-ary protocols form a monoid under shared-boundary grafting. -/
instance : Monoid (LaneProtocol Lane signature) where
  one := empty Lane signature
  mul := graft
  one_mul := empty_graft
  mul_one := graft_empty
  mul_assoc := graft_assoc

/-- **Strict n-ary tensor--sequential interchange.** -/
theorem tensor_graft_interchange
    (first second : (lane : Lane) → Tree (signature lane)) :
    tensor (fun lane ↦ Free.graft (first lane) (second lane)) =
      graft (tensor first) (tensor second) :=
  rfl

/-- N-ary summed budget is subadditive under shared-boundary grafting. -/
theorem budget_graft_le (first second : LaneProtocol Lane signature) :
    (graft first second).budget ≤ first.budget + second.budget := by
  calc
    (graft first second).budget =
        ∑ lane, (Free.graft (first.tree lane) (second.tree lane)).budget := rfl
    _ ≤ ∑ lane, ((first.tree lane).budget + (second.tree lane).budget) := by
      apply Finset.sum_le_sum
      intro lane _
      exact Free.budget_graft_le (first.tree lane) (second.tree lane)
    _ = first.budget + second.budget := by
      rw [Finset.sum_add_distrib]
      rfl

end LaneProtocol

end Ript.Syntax.DependentBranching
