import Ript.Models.Quantum.Instrument
import Ript.Models.Quantum.Monoidal

/-!
# Recursive finite quantum instrument trees

An `InstrumentTree X Y` is a first-class finite adaptive protocol.  A leaf is
an ordinary channel.  An internal node executes a finite instrument, records
its outcome, charges a declared resource cost, and selects a recursively
defined continuation.  The canonical history type is a dependent Sigma tree.

Evaluation uses dependent instrument bind.  The main representation theorem
identifies every evaluated outcome branch with the recursively composed branch
map indexed by its unique history normal form.  A computable structural budget
bounds the exact cost of every history.
-/

set_option autoImplicit false

namespace Ript.Models.Quantum

open Ript.Core

universe u

/-- Finite adaptive quantum-instrument protocol tree. -/
inductive InstrumentTree : Object.{u} → Object.{u} → Type (u + 1) where
  /-- Finish with one ordinary trace-preserving channel. -/
  | done {X Y : Object.{u}} (channel : KrausChannel X Y) : InstrumentTree X Y
  /-- Execute an instrument and choose the continuation from its outcome. -/
  | step {X Z Y : Object.{u}} {Outcome : Type u}
      [Fintype Outcome] [DecidableEq Outcome]
      (instrument : KrausInstrument Outcome X Z)
      (cost : Nat)
      (next : Outcome → InstrumentTree Z Y) : InstrumentTree X Y

namespace InstrumentTree

variable {X Y Z : Object.{u}}

/-- Canonical dependent history normal form of a protocol tree. -/
def History : {X Y : Object.{u}} → InstrumentTree X Y → Type u
  | _, _, .done _ => PUnit.{u + 1}
  | _, _, @InstrumentTree.step _ _ _ Outcome outcomeFintype _ _ _ next => by
      letI := outcomeFintype
      exact Σ outcome : Outcome, History (next outcome)

/-- Canonical finite enumeration of tree histories. -/
@[instance_reducible]
def historyFintype : {X Y : Object.{u}} →
    (tree : InstrumentTree X Y) → Fintype tree.History
  | _, _, .done _ => by
      change Fintype PUnit
      exact inferInstance
  | _, _, @InstrumentTree.step _ _ _ Outcome outcomeFintype _ _ _ next => by
      letI := outcomeFintype
      letI : ∀ outcome, Fintype (next outcome).History :=
        fun outcome ↦ historyFintype (next outcome)
      change Fintype (Σ outcome : Outcome, (next outcome).History)
      exact inferInstance

instance (tree : InstrumentTree X Y) : Fintype tree.History :=
  tree.historyFintype

/-- Decidable equality of canonical finite histories. -/
def historyDecidableEq : {X Y : Object.{u}} →
    (tree : InstrumentTree X Y) → DecidableEq tree.History
  | _, _, .done _ => by
      change DecidableEq PUnit
      exact inferInstance
  | _, _, @InstrumentTree.step _ _ _ Outcome outcomeFintype outcomeDecEq _ _ next => by
      letI := outcomeFintype
      letI := outcomeDecEq
      letI : ∀ outcome, DecidableEq (next outcome).History :=
        fun outcome ↦ historyDecidableEq (next outcome)
      change DecidableEq (Σ outcome : Outcome, (next outcome).History)
      exact inferInstance

instance (tree : InstrumentTree X Y) : DecidableEq tree.History :=
  tree.historyDecidableEq

/-- Evaluate a recursive tree as one normalized finite instrument whose
outcomes are complete dependent histories. -/
noncomputable def eval : {X Y : Object.{u}} →
    (tree : InstrumentTree X Y) →
    KrausInstrument tree.History X Y
  | _, _, .done channel => by
      change KrausInstrument PUnit _ _
      exact KrausInstrument.ofChannel channel
  | _, _, @InstrumentTree.step _ _ _ Outcome outcomeFintype outcomeDecEq
      instrument _ next => by
      letI := outcomeFintype
      letI := outcomeDecEq
      letI : ∀ outcome, Fintype (next outcome).History :=
        fun outcome ↦ historyFintype (next outcome)
      change KrausInstrument (Σ outcome : Outcome, (next outcome).History) _ _
      exact instrument.bind (fun outcome ↦ eval (next outcome))

/-- Recursive operational action of one canonical history. -/
def branchMap : {X Y : Object.{u}} →
    (tree : InstrumentTree X Y) → tree.History →
    Matrix X X ℂ → Matrix Y Y ℂ
  | _, _, .done channel, _ => channel.map
  | _, _, @InstrumentTree.step _ _ _ Outcome outcomeFintype outcomeDecEq
      instrument _ next, history => by
      letI := outcomeFintype
      letI := outcomeDecEq
      change (Σ outcome : Outcome, (next outcome).History) at history
      rcases history with ⟨outcome, history⟩
      exact fun ρ ↦ (next outcome).branchMap history
        ((instrument.branch outcome).map ρ)

/-- Exact resource cost accumulated along one history. -/
def historyCost : {X Y : Object.{u}} →
    (tree : InstrumentTree X Y) → tree.History → Nat
  | _, _, .done _, _ => 0
  | _, _, @InstrumentTree.step _ _ _ Outcome outcomeFintype outcomeDecEq
      _ cost next, history => by
      letI := outcomeFintype
      letI := outcomeDecEq
      change (Σ outcome : Outcome, (next outcome).History) at history
      rcases history with ⟨outcome, history⟩
      exact cost + (next outcome).historyCost history

/-- A computable structural budget for the whole tree.  It sums continuation
budgets across branches, so it is conservative even when branch depths
differ. -/
def budget : {X Y : Object.{u}} → InstrumentTree X Y → Nat
  | _, _, .done _ => 0
  | _, _, @InstrumentTree.step _ _ _ Outcome outcomeFintype _ _ cost next => by
      letI := outcomeFintype
      exact cost + ∑ outcome : Outcome, (next outcome).budget

/-- Every concrete history cost is bounded by the tree's structural budget. -/
theorem historyCost_le_budget (tree : InstrumentTree X Y)
    (history : tree.History) : tree.historyCost history ≤ tree.budget := by
  induction tree with
  | done channel => simp [historyCost, budget]
  | @step X Z Y Outcome outcomeFintype outcomeDecEq instrument cost next induction =>
      change (Σ outcome : Outcome, (next outcome).History) at history
      rcases history with ⟨outcome, history⟩
      simp only [historyCost, budget]
      apply Nat.add_le_add_left
      exact (induction outcome history).trans
        (Finset.single_le_sum
          (fun other _ ↦ Nat.zero_le (next other).budget)
          (Finset.mem_univ outcome))

/-- **History representation theorem.**  Evaluation of the branch indexed by
a history is exactly recursive serial composition along that history. -/
theorem eval_branch_map (tree : InstrumentTree X Y)
    (history : tree.History) (ρ : Matrix X X ℂ) :
    ((tree.eval.branch history).map ρ) = tree.branchMap history ρ := by
  induction tree with
  | done channel =>
      change PUnit at history
      cases history
      rfl
  | @step X Z Y Outcome outcomeFintype outcomeDecEq instrument cost next induction =>
      change (Σ outcome : Outcome, (next outcome).History) at history
      rcases history with ⟨outcome, history⟩
      change
        (((instrument.bind (fun result ↦ (next result).eval)).branch
          ⟨outcome, history⟩).map ρ) =
            (next outcome).branchMap history
              ((instrument.branch outcome).map ρ)
      rw [KrausInstrument.bind_branch_map]
      exact induction outcome history ((instrument.branch outcome).map ρ)

/-- Evaluation is a normalized instrument over the complete history space. -/
theorem eval_outcomeProbability_normalized (tree : InstrumentTree X Y)
    (state : DensityMatrix X) :
    ∑ history, tree.eval.outcomeProbability state history = 1 :=
  KrausInstrument.outcomeProbability_normalized tree.eval state

/-- The recorded-channel representation exposes exactly the recursively
represented history branch in each diagonal classical block. -/
theorem recordedChannel_history_block (tree : InstrumentTree X Y)
    (state : Matrix X X ℂ) (history history' : tree.History)
    (y y' : Y) :
    (tree.eval.recordedChannel.map state) (history, y) (history', y') =
      if history = history' then tree.branchMap history state y y' else 0 := by
  rw [KrausInstrument.recordedChannel_map_apply]
  split_ifs with equal
  · rw [tree.eval_branch_map]
  · rfl

/-- Operational equivalence of two adaptive trees after explicitly
identifying their dependent canonical history types. -/
def ObservationallyEquivalentAlong
    (first second : InstrumentTree X Y)
    (historyEquiv : first.History ≃ second.History) : Prop :=
  first.eval.relabel historyEquiv = second.eval

/-- **Coherent-tree completeness.**  Two arbitrary finite dependent quantum
instrument trees are operationally equivalent along a history equivalence
exactly when all corresponding recursively composed branch maps agree. -/
theorem observationallyEquivalentAlong_iff_branchMap
    (first second : InstrumentTree X Y)
    (historyEquiv : first.History ≃ second.History) :
    first.ObservationallyEquivalentAlong second historyEquiv ↔
      ∀ (history : second.History) (ρ : Matrix X X ℂ),
        first.branchMap (historyEquiv.symm history) ρ =
          second.branchMap history ρ := by
  constructor
  · intro equal history ρ
    have branchEqual := congrArg
      (fun instrument ↦ (instrument.branch history).map ρ) equal
    change
      ((first.eval.branch (historyEquiv.symm history)).map ρ) =
        ((second.eval.branch history).map ρ) at branchEqual
    simpa only [eval_branch_map] using branchEqual
  · intro branchEqual
    apply KrausInstrument.ext
    funext history
    apply KrausOperation.ext
    funext ρ
    change
      ((first.eval.branch (historyEquiv.symm history)).map ρ) =
        ((second.eval.branch history).map ρ)
    simpa only [eval_branch_map] using branchEqual history ρ

/-- The recorded quantum channel is a complete representation of adaptive
tree behavior after reindexing the classical history register. -/
theorem observationallyEquivalentAlong_iff_recordedChannel
    (first second : InstrumentTree X Y)
    (historyEquiv : first.History ≃ second.History) :
    first.ObservationallyEquivalentAlong second historyEquiv ↔
      (first.eval.relabel historyEquiv).recordedChannel =
        second.eval.recordedChannel := by
  rw [ObservationallyEquivalentAlong,
    KrausInstrument.recordedChannel_eq_iff]

/-! ## Intrinsic image of tree evaluation -/

variable {Outcome : Type u} [Fintype Outcome] [DecidableEq Outcome]

/-- Embed an arbitrary finite instrument as a one-step adaptive tree whose
continuations are identity channels. -/
def ofInstrument (instrument : KrausInstrument Outcome X Y)
    (cost : Nat := 0) : InstrumentTree X Y :=
  .step instrument cost (fun _ ↦ .done (KrausChannel.identity Y))

/-- The canonical histories of the one-step tree are equivalent to the
original instrument outcomes. -/
def ofInstrumentHistoryEquiv
    (instrument : KrausInstrument Outcome X Y) (cost : Nat := 0) :
    (ofInstrument instrument cost).History ≃ Outcome where
  toFun history := history.1
  invFun outcome := ⟨outcome, PUnit.unit⟩
  left_inv := by
    rintro ⟨outcome, history⟩
    cases history
    rfl
  right_inv := by
    intro outcome
    rfl

/-- Evaluating the one-step embedding and relabeling its histories recovers
the original finite instrument exactly. -/
theorem eval_ofInstrument_relabel
    (instrument : KrausInstrument Outcome X Y) (cost : Nat := 0) :
    (ofInstrument instrument cost).eval.relabel
      (ofInstrumentHistoryEquiv instrument cost) = instrument := by
  apply KrausInstrument.ext
  funext outcome
  apply KrausOperation.ext
  funext ρ
  change
    (KrausChannel.identity Y).map ((instrument.branch outcome).map ρ) =
      (instrument.branch outcome).map ρ
  rw [KrausChannel.identity_map]

/-- **Coherent tree image theorem.**  A channel with a finite classical
outcome register is represented by evaluation of a finite dependent
instrument tree, up to an explicit history equivalence, exactly when the
outcome register is intrinsically block diagonal. -/
theorem isClassicallyRecorded_iff_exists_instrumentTree
    (channel : KrausChannel X
      (Object.tensor (KrausInstrument.outcomeObject Outcome) Y)) :
    KrausInstrument.IsClassicallyRecorded channel ↔
      ∃ (tree : InstrumentTree X Y)
        (historyEquiv : tree.History ≃ Outcome),
        (tree.eval.relabel historyEquiv).recordedChannel = channel := by
  constructor
  · intro classical
    let instrument := KrausInstrument.extractInstrument channel
    let tree := ofInstrument instrument 0
    let historyEquiv := ofInstrumentHistoryEquiv instrument 0
    refine ⟨tree, historyEquiv, ?_⟩
    rw [show tree.eval.relabel historyEquiv = instrument by
      exact eval_ofInstrument_relabel instrument 0]
    exact
      (KrausInstrument.recordedChannel_extractInstrument_eq_iff channel).2
        classical
  · rintro ⟨tree, historyEquiv, equal⟩
    rw [← equal]
    exact KrausInstrument.recordedChannel_isClassicallyRecorded
      (tree.eval.relabel historyEquiv)

/-- The full-Kraus abstract process cost of a recorded tree is bounded by its
computable structural budget. -/
theorem recordedChannel_cost_le_budget (tree : InstrumentTree X Y) :
    processCost (C := Object) (R := Nat) tree.eval.recordedChannel ≤ tree.budget :=
  Nat.zero_le _

end InstrumentTree

end Ript.Models.Quantum
