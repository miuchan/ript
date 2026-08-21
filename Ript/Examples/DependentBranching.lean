import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Ript.Examples.SimpleDecision
import Ript.Semantics.DependentBranchingRealization
import Ript.Syntax.DependentBranching.Nary

/-!
# Executable variable-depth heterogeneous branching

This example uses three generators with two different finite outcome types.
The root exposes a Boolean outcome.  One branch terminates immediately; the
other executes a ternary generator, and only one ternary result executes a
final Boolean generator.  The resulting five dependent histories have lengths
one, two, or three.

A second root generator has the same Boolean outcome carrier but different
weights.  The explicit history equivalence lets observational completeness
separate the two trees by their canonical normal forms.
-/

set_option autoImplicit false

namespace Ript.Examples.DependentBranching

open scoped BigOperators

open CategoryTheory MonoidalCategory
open Ript.Models.FiniteStochastic
open Ript.Semantics.DependentBranchingRealization
open Ript.Syntax.DependentBranching
open Ript.Syntax.DependentBranching.Free

/-- Fair Boolean, biased Boolean, and ternary primitive generators. -/
inductive Generator where
  | fair
  | biased
  | ternary
  deriving DecidableEq, Repr

/-- Generator-dependent result carriers. -/
abbrev Outcome : Generator → Type
  | .fair => Bool
  | .biased => Bool
  | .ternary => Fin 3

/-- Heterogeneous finite-outcome signature with native scalar costs. -/
abbrev signature : Signature where
  Generator := Generator
  Outcome := Outcome
  outcomeFintype generator := by
    cases generator <;> simp [Outcome] <;> infer_instance
  outcomeDecidableEq generator := by
    cases generator <;> simp [Outcome] <;> infer_instance
  cost
    | .fair => 1
    | .biased => 1
    | .ternary => 2

/-- Exact positive outcome weights. -/
def weight : (generator : Generator) → Outcome generator → ℚ≥0
  | .fair, _ => 1 / 2
  | .biased, false => 3 / 4
  | .biased, true => 1 / 4
  | .ternary, _ => 1 / 3

/-- Outcome-conditioned residual-bit update. -/
def transition : (generator : Generator) → Outcome generator → Bool → Bool
  | .fair, outcome, input => xor input outcome
  | .biased, outcome, input => xor input outcome
  | .ternary, outcome, input => if outcome = 2 then !input else input

/-- Exact strictly positive semantics of the heterogeneous signature. -/
abbrev semantics : Semantics signature Bool where
  weight := weight
  normalized generator := by
    cases generator with
    | fair =>
        change (∑ outcome : Bool, weight .fair outcome) = 1
        rw [Fintype.sum_bool]
        norm_num [weight]
    | biased =>
        change (∑ outcome : Bool, weight .biased outcome) = 1
        rw [Fintype.sum_bool]
        norm_num [weight]
    | ternary =>
        change (∑ outcome : Fin 3, weight .ternary outcome) = 1
        rw [Fin.sum_univ_three]
        norm_num [weight]
  positive generator outcome := by
    cases generator with
    | fair =>
        cases outcome <;>
          exact_mod_cast (show (0 : ℚ) < 1 / 2 by norm_num)
    | biased =>
        cases outcome
        · change (0 : ℚ≥0) < 3 / 4
          exact_mod_cast (show (0 : ℚ) < 3 / 4 by norm_num)
        · change (0 : ℚ≥0) < 1 / 4
          exact_mod_cast (show (0 : ℚ) < 1 / 4 by norm_num)
    | ternary =>
        fin_cases outcome <;>
          exact_mod_cast (show (0 : ℚ) < 1 / 3 by norm_num)
  transition := transition

/-- Uniform full-support input prior shared by the generic causal and thermal
realizations. -/
def uniformBitPrior :
    Ript.Models.FiniteDistribution.FinDist (Object.of Bool) where
  prob _ := 1 / 2
  normalized := by
    rw [Fintype.sum_bool]
    norm_num

/-- The uniform input prior is strictly positive at every bit. -/
theorem uniformBitPrior_fullSupport (input : Bool) :
    0 < uniformBitPrior.prob input := by
  norm_num [uniformBitPrior]

/-- Boolean-guessing task context used by the structured semantic
realization. -/
abbrev bitSemanticContext : SemanticContext Bool Bool Bool where
  problem := Ript.Examples.SimpleDecision.bitGuessing
  baseline := Ript.Examples.SimpleDecision.uninformativeExperiment

/-- Outcome-dependent continuation shared by the fair and biased roots. -/
abbrev continuation (first : Bool) : Tree signature :=
  if first then
    .node .ternary fun ternaryOutcome ↦
      if ternaryOutcome = 2 then
        .node .fair fun _ ↦ .leaf
      else .leaf
  else .leaf

/-- Variable-depth tree with a fair Boolean root. -/
abbrev fairTree : Tree signature :=
  .node .fair continuation

/-- The same dependent shape with a biased Boolean root. -/
abbrev biasedTree : Tree signature :=
  .node .biased continuation

/-- The arbitrary-outcome, variable-depth fair tree has canonical
probability, quantum, causal, computation, semantic, and thermal
realizations. -/
theorem fairTree_sixModelRepresentation :
    RepresentedInAllModels bitSemanticContext uniformBitPrior
      (treeResource fairTree) (fairTree.normalForm semantics) :=
  sixModelRepresentation bitSemanticContext uniformBitPrior
    (treeResource fairTree) (fairTree.normalForm semantics)

/-- One-step terminating history. -/
abbrev shortHistory : fairTree.History :=
  ⟨false, PUnit.unit⟩

/-- Corresponding short history of the biased-root tree. -/
abbrev biasedShortHistory : biasedTree.History :=
  ⟨false, PUnit.unit⟩

/-- Two-step history terminating after ternary outcome zero. -/
abbrev middleHistoryZero : fairTree.History :=
  ⟨true, (0 : Fin 3), PUnit.unit⟩

/-- Two-step history terminating after ternary outcome one. -/
abbrev middleHistoryOne : fairTree.History :=
  ⟨true, (1 : Fin 3), PUnit.unit⟩

/-- Three-step history passing through ternary outcome two. -/
abbrev longHistory (last : Bool) : fairTree.History :=
  ⟨true, (2 : Fin 3), last, PUnit.unit⟩

/-- There are exactly five valid dependent complete histories. -/
theorem fairTree_history_card : Fintype.card fairTree.History = 5 := by
  decide

@[simp]
theorem fairTree_height : fairTree.height = 3 := by
  decide

@[simp]
theorem fairTree_budget : fairTree.budget = 4 := by
  decide

@[simp]
theorem shortHistory_length : fairTree.historyLength shortHistory = 1 :=
  rfl

@[simp]
theorem middleHistoryZero_length :
    fairTree.historyLength middleHistoryZero = 2 :=
  rfl

@[simp]
theorem longHistory_length (last : Bool) :
    fairTree.historyLength (longHistory last) = 3 :=
  rfl

@[simp]
theorem shortHistory_cost : fairTree.historyCost shortHistory = 1 :=
  rfl

@[simp]
theorem middleHistoryZero_cost :
    fairTree.historyCost middleHistoryZero = 3 :=
  rfl

@[simp]
theorem longHistory_cost (last : Bool) :
    fairTree.historyCost (longHistory last) = 4 :=
  rfl

@[simp]
theorem shortHistory_probability :
    fairTree.historyProbability semantics shortHistory = 1 / 2 := by
  change (1 / 2 : ℚ≥0) * 1 = 1 / 2
  norm_num

@[simp]
theorem biasedShortHistory_probability :
    biasedTree.historyProbability semantics biasedShortHistory = 3 / 4 := by
  change (3 / 4 : ℚ≥0) * 1 = 3 / 4
  norm_num

@[simp]
theorem middleHistoryZero_probability :
    fairTree.historyProbability semantics middleHistoryZero = 1 / 6 := by
  change (1 / 2 : ℚ≥0) * (1 / 3 * 1) = 1 / 6
  norm_num

@[simp]
theorem middleHistoryOne_probability :
    fairTree.historyProbability semantics middleHistoryOne = 1 / 6 := by
  change (1 / 2 : ℚ≥0) * (1 / 3 * 1) = 1 / 6
  norm_num

@[simp]
theorem longHistory_probability (last : Bool) :
    fairTree.historyProbability semantics (longHistory last) = 1 / 12 := by
  change (1 / 2 : ℚ≥0) * (1 / 3 * (1 / 2 * 1)) = 1 / 12
  norm_num

/-- The five heterogeneous dependent histories normalize exactly. -/
theorem fairTree_history_normalized :
    ∑ history, fairTree.historyProbability semantics history = 1 :=
  fairTree.historyProbability_normalized semantics

/-- Exact branch-table representation of the variable-depth tree. -/
theorem fairTree_representation :
    fairTree.run semantics = (fairTree.normalForm semantics).toFinStoch :=
  fairTree.representation semantics

/-- The fair and biased trees have definitionally the same dependent shape,
made explicit as a history equivalence. -/
def fairBiasedHistoryEquiv : fairTree.History ≃ biasedTree.History :=
  Equiv.refl _

/-- Reindexing the biased table exposes a different short-branch weight. -/
theorem fair_normalForm_ne_biased :
    fairTree.normalForm semantics ≠
      (biasedTree.normalForm semantics).reindexHistory
        fairBiasedHistoryEquiv := by
  intro equalNormalForms
  have entryEqual := congrArg
    (fun normalForm ↦ normalForm.probability shortHistory)
    equalNormalForms
  change fairTree.historyProbability semantics shortHistory =
    biasedTree.historyProbability semantics biasedShortHistory at entryEqual
  rw [shortHistory_probability, biasedShortHistory_probability] at entryEqual
  norm_num at entryEqual

/-- The fair and biased variable-depth trees cannot agree simultaneously in
the six generic model realizations. -/
theorem fair_biased_not_allModelsAgree :
    ¬ AllModelsAgree bitSemanticContext uniformBitPrior
      (treeResource fairTree)
      (fairTree.normalForm semantics)
      ((biasedTree.normalForm semantics).reindexHistory
        fairBiasedHistoryEquiv) := by
  intro agreement
  exact fair_normalForm_ne_biased
    ((allModelsAgree_iff bitSemanticContext uniformBitPrior
      uniformBitPrior_fullSupport (treeResource fairTree)).mp agreement)

/-- **Concrete dependent observational completeness.**  The recorded fair and
biased trees are distinct after the explicit common-history reindexing. -/
theorem fair_run_ne_biased_reindexed :
    fairTree.run semantics ≠
      ((biasedTree.normalForm semantics).reindexHistory
        fairBiasedHistoryEquiv).toFinStoch := by
  intro equalRuns
  exact fair_normalForm_ne_biased
    ((Tree.observationalCompletenessAlong semantics fairTree biasedTree
      fairBiasedHistoryEquiv).mp equalRuns)

/-! ## Free algebra and sequential grafting -/

/-- Algebra counting terminal leaves of a dependent tree. -/
abbrev leafCountAlgebra : Algebra signature where
  Carrier := Nat
  leaf := 1
  node generator continuations := by
    cases generator with
    | fair => exact ∑ outcome : Bool, continuations outcome
    | biased => exact ∑ outcome : Bool, continuations outcome
    | ternary => exact ∑ outcome : Fin 3, continuations outcome

/-- The heterogeneous tree has five terminal branches by algebraic fold. -/
theorem fairTree_leafCount : fold leafCountAlgebra fairTree = 5 := by
  decide

/-- The categorical initial morphism computes the same leaf-count fold. -/
theorem initial_leafCount :
    (treeAlgebraIsInitial.to leafCountAlgebra).toFun fairTree = 5 := by
  rw [hom_apply_eq_fold]
  exact fairTree_leafCount

/-- Associativity of sequential leaf substitution is formally derivable in
the free branching equational theory. -/
theorem graft_associativity_derives :
    Derives
      (graft (graft fairTree biasedTree) fairTree)
      (graft fairTree (graft biasedTree fairTree)) :=
  Derives.iff_eq.mpr (graft_assoc fairTree biasedTree fairTree)

/-- Specialization of absolute soundness/completeness to this heterogeneous
signature. -/
theorem heterogeneous_semanticCompleteness
    {first second : Tree signature} :
    Derives first second ↔
      ∀ algebra : Algebra signature,
        fold algebra first = fold algebra second :=
  Derives.semanticCompleteness

/-- Grafting two copies attains the generic subadditive height bound. -/
theorem fairTree_graft_height :
    (graft fairTree fairTree).height = 6 := by
  decide

/-- Grafting two copies attains the generic subadditive budget bound. -/
theorem fairTree_graft_budget :
    (graft fairTree fairTree).budget = 8 := by
  decide

/-! ## Parallel model interpretations -/

/-- The product of leaf-count and budget models evaluates both observations
in one symmetric monoidal interpretation. -/
theorem parallel_leafCount_budget :
    fold (leafCountAlgebra ⊗ budgetAlgebra signature) fairTree =
      (5, ULift.up 4) := by
  rw [fold_tensor]
  apply Prod.ext
  · exact fairTree_leafCount
  · apply ULift.ext
    exact fold_budget fairTree

/-- Braiding the product interpretation swaps the two model observations. -/
theorem parallel_interpretation_braiding :
    (β_ leafCountAlgebra (budgetAlgebra signature)).hom.toFun
        (fold (leafCountAlgebra ⊗ budgetAlgebra signature) fairTree) =
      fold (budgetAlgebra signature ⊗ leafCountAlgebra) fairTree := by
  rw [fold_tensor, fold_tensor]
  rfl

/-- The term-model/product interpretation gives a concrete jointly complete
pair for this heterogeneous branching signature. -/
theorem heterogeneous_jointSemanticCompleteness
    {first second : Tree signature} :
    Derives first second ↔
      fold (treeAlgebra signature ⊗ leafCountAlgebra) first =
        fold (treeAlgebra signature ⊗ leafCountAlgebra) second :=
  jointSemanticCompleteness leafCountAlgebra

/-! ## Tree-level independent parallel protocols -/

/-- Fair and biased trees running in independent lanes. -/
abbrev fairBiasedParallel : ParallelProtocol signature signature :=
  ParallelProtocol.tensor fairTree biasedTree

/-- Short paired history of the independent lanes. -/
abbrev parallelShortHistory : fairBiasedParallel.History :=
  (shortHistory, biasedShortHistory)

/-- The paired protocol has all `5 × 5 = 25` complete histories. -/
theorem fairBiasedParallel_history_card :
    Fintype.card fairBiasedParallel.History = 25 := by
  decide

@[simp]
theorem fairBiasedParallel_height : fairBiasedParallel.height = 3 := by
  decide

@[simp]
theorem fairBiasedParallel_budget : fairBiasedParallel.budget = 8 := by
  decide

@[simp]
theorem fairBiasedParallel_short_cost :
    fairBiasedParallel.historyCost parallelShortHistory = 2 :=
  rfl

/-- Independent short-history mass is `1/2 × 3/4 = 3/8`. -/
theorem fairBiasedParallel_short_probability :
    fairBiasedParallel.historyProbability semantics semantics
      parallelShortHistory = (3 : ℚ≥0) / 8 := by
  change fairTree.historyProbability semantics shortHistory *
      biasedTree.historyProbability semantics biasedShortHistory = _
  rw [shortHistory_probability, biasedShortHistory_probability]
  norm_num

/-- The generic independent-lane factorization specializes to this protocol. -/
theorem fairBiasedParallel_run_factorization
    (input output : Bool × Bool)
    (history : fairBiasedParallel.History) :
    (fairBiasedParallel.run semantics semantics).prob input (history, output) =
      (fairTree.run semantics).prob input.1 (history.1, output.1) *
        (biasedTree.run semantics).prob input.2
          (history.2, output.2) :=
  fairBiasedParallel.run_factorization semantics semantics input output history

/-- Strict tensor--sequential interchange for the concrete two-lane tree. -/
theorem fairBiasedParallel_interchange :
    ParallelProtocol.tensor
        (graft fairTree fairTree) (graft biasedTree biasedTree) =
      ParallelProtocol.graft fairBiasedParallel fairBiasedParallel :=
  ParallelProtocol.tensor_graft_interchange
    fairTree fairTree biasedTree biasedTree

/-- Two sequential parallel phases attain the summed budget. -/
theorem fairBiasedParallel_graft_budget :
    (ParallelProtocol.graft
      fairBiasedParallel fairBiasedParallel).budget = 16 := by
  decide

/-- Comparison protocol with a fair tree in both lanes. -/
abbrev fairFairParallel : ParallelProtocol signature signature :=
  ParallelProtocol.tensor fairTree fairTree

/-- The two paired history types have the same dependent shape. -/
def fairFairBiasedHistoryEquiv :
    fairFairParallel.History ≃ fairBiasedParallel.History :=
  Equiv.refl _

/-- Their parallel canonical tables differ at the short paired history. -/
theorem fairFair_normalForm_ne_fairBiased :
    fairFairParallel.normalForm semantics semantics ≠
      (fairBiasedParallel.normalForm semantics semantics).reindexHistory
        fairFairBiasedHistoryEquiv := by
  intro equalNormalForms
  have entryEqual := congrArg
    (fun normalForm ↦ normalForm.probability
      (shortHistory, shortHistory)) equalNormalForms
  change fairTree.historyProbability semantics shortHistory *
      fairTree.historyProbability semantics shortHistory =
    fairTree.historyProbability semantics shortHistory *
      biasedTree.historyProbability semantics biasedShortHistory at entryEqual
  rw [shortHistory_probability, biasedShortHistory_probability] at entryEqual
  norm_num at entryEqual

/-- Parallel observational completeness turns that table difference into a
recorded-channel difference. -/
theorem fairFair_run_ne_fairBiased :
    fairFairParallel.run semantics semantics ≠
      ((fairBiasedParallel.normalForm semantics semantics).reindexHistory
        fairFairBiasedHistoryEquiv).toFinStoch := by
  intro equalRuns
  exact fairFair_normalForm_ne_fairBiased
    ((ParallelProtocol.observationalCompletenessAlong semantics semantics
      fairFairParallel fairBiasedParallel fairFairBiasedHistoryEquiv).mp
        equalRuns)

/-! ## Finite n-ary lane families -/

/-- Three heterogeneous-semantics lanes over one shared signature. -/
abbrev tripleTree : Fin 3 → Tree signature :=
  Fin.cases fairTree
    (Fin.cases biasedTree fun _ : Fin 1 ↦ fairTree)

/-- Three-lane protocol. -/
abbrev tripleProtocol : LaneProtocol (Fin 3) (fun _ ↦ signature) :=
  LaneProtocol.tensor tripleTree

/-- Short history assignment in all three lanes. -/
abbrev tripleShortHistory : tripleProtocol.History :=
  Fin.cases shortHistory
    (Fin.cases biasedShortHistory fun _ : Fin 1 ↦ shortHistory)

@[simp]
theorem tripleTree_zero : tripleTree 0 = fairTree := rfl

@[simp]
theorem tripleTree_one : tripleTree 1 = biasedTree := rfl

@[simp]
theorem tripleTree_two : tripleTree 2 = fairTree := rfl

@[simp]
theorem tripleShortHistory_zero : tripleShortHistory 0 = shortHistory := rfl

@[simp]
theorem tripleShortHistory_one :
    tripleShortHistory 1 = biasedShortHistory := rfl

@[simp]
theorem tripleShortHistory_two : tripleShortHistory 2 = shortHistory := rfl

/-- The n-ary protocol has `5³ = 125` complete histories. -/
theorem tripleProtocol_history_card :
    Fintype.card tripleProtocol.History = 125 := by
  have biasedCard : Fintype.card biasedTree.History = 5 := by
    calc
      Fintype.card biasedTree.History = Fintype.card fairTree.History :=
        Fintype.card_congr fairBiasedHistoryEquiv.symm
      _ = 5 := fairTree_history_card
  rw [Fintype.card_pi, Fin.prod_univ_three]
  change Fintype.card fairTree.History *
      Fintype.card biasedTree.History * Fintype.card fairTree.History = 125
  rw [fairTree_history_card, biasedCard]

@[simp]
theorem tripleProtocol_height : tripleProtocol.height = 3 := by
  decide

@[simp]
theorem tripleProtocol_budget : tripleProtocol.budget = 12 := by
  decide

/-- Joint short-history mass is `1/2 × 3/4 × 1/2 = 3/16`. -/
theorem tripleProtocol_short_probability :
    tripleProtocol.historyProbability (fun _ ↦ semantics)
      tripleShortHistory = (3 : ℚ≥0) / 16 := by
  change (∏ lane : Fin 3,
    (tripleTree lane).historyProbability semantics
      (tripleShortHistory lane)) = _
  rw [Fin.prod_univ_three]
  change fairTree.historyProbability semantics shortHistory *
      biasedTree.historyProbability semantics biasedShortHistory *
        fairTree.historyProbability semantics shortHistory = _
  rw [shortHistory_probability, biasedShortHistory_probability]
  norm_num

/-- N-ary recorded behavior factors into all three lane entries. -/
theorem tripleProtocol_run_factorization
    (input output : Fin 3 → Bool)
    (history : tripleProtocol.History) :
    (tripleProtocol.run (fun _ ↦ semantics)).prob input (history, output) =
      ∏ lane, ((tripleTree lane).run semantics).prob
        (input lane) (history lane, output lane) :=
  tripleProtocol.run_factorization (fun _ ↦ semantics) input output history

/-- Strict three-lane tensor--sequential interchange. -/
theorem tripleProtocol_interchange :
    LaneProtocol.tensor
        (fun lane ↦ graft (tripleTree lane) (tripleTree lane)) =
      LaneProtocol.graft tripleProtocol tripleProtocol :=
  LaneProtocol.tensor_graft_interchange tripleTree tripleTree

/-- Two n-ary phases attain the summed budget. -/
theorem tripleProtocol_graft_budget :
    (LaneProtocol.graft tripleProtocol tripleProtocol).budget = 24 := by
  decide

/-- All-fair comparison family. -/
abbrev tripleAllFairTree : Fin 3 → Tree signature :=
  fun _ ↦ fairTree

/-- Three independent copies of the fair dependent protocol. -/
abbrev tripleAllFairProtocol : LaneProtocol (Fin 3) (fun _ ↦ signature) :=
  LaneProtocol.tensor tripleAllFairTree

/-- All-short history assignment of the all-fair family. -/
abbrev tripleAllFairShortHistory : tripleAllFairProtocol.History :=
  fun _ ↦ shortHistory

/-- Lane-wise history equivalence from the all-fair family to the family with
the biased middle lane. -/
def tripleHistoryEquiv :
    tripleAllFairProtocol.History ≃ tripleProtocol.History :=
  Equiv.piCongrRight <|
    Fin.cases (Equiv.refl _)
      (Fin.cases fairBiasedHistoryEquiv fun _ : Fin 1 ↦ Equiv.refl _)

/-- Executable transposition of the first two lanes in the three-lane
protocol. -/
abbrev tripleLaneSwap : Fin 3 ≃ Fin 3 :=
  Equiv.swap 0 1

/-- Swapping two lane names changes only the explicit history/state
presentation of the canonical three-lane normal form. -/
theorem tripleProtocol_swap_normalForm :
    (tripleProtocol.reindex tripleLaneSwap).normalForm
        (fun _ ↦ semantics) =
      (tripleProtocol.normalForm (fun _ ↦ semantics)).reindex
        (tripleProtocol.reindexHistoryEquiv tripleLaneSwap)
        (LaneProtocol.reindexStateEquiv (State := fun _ : Fin 3 ↦ Bool)
          tripleLaneSwap) :=
  tripleProtocol.reindex_normalForm tripleLaneSwap (fun _ ↦ semantics)

@[simp]
theorem tripleHistoryEquiv_short :
    tripleHistoryEquiv tripleAllFairShortHistory = tripleShortHistory := by
  funext lane
  refine Fin.cases ?_ (Fin.cases ?_ fun _ : Fin 1 ↦ ?_) lane <;> rfl

/-- The n-ary canonical tables differ at the all-short history. -/
theorem tripleAllFair_normalForm_ne_triple :
    tripleAllFairProtocol.normalForm (fun _ ↦ semantics) ≠
      (tripleProtocol.normalForm (fun _ ↦ semantics)).reindexHistory
        tripleHistoryEquiv := by
  intro equalNormalForms
  have entryEqual := congrArg
    (fun normalForm ↦ normalForm.probability
      tripleAllFairShortHistory) equalNormalForms
  change (∏ lane : Fin 3,
      (tripleAllFairTree lane).historyProbability semantics
        (tripleAllFairShortHistory lane)) =
    ∏ lane : Fin 3,
      (tripleTree lane).historyProbability semantics
        (tripleHistoryEquiv tripleAllFairShortHistory lane) at entryEqual
  rw [tripleHistoryEquiv_short] at entryEqual
  simp only [Fin.prod_univ_three, tripleAllFairTree,
    tripleAllFairShortHistory, tripleTree_zero, tripleTree_one,
    tripleTree_two, tripleShortHistory_zero, tripleShortHistory_one,
    tripleShortHistory_two] at entryEqual
  rw [shortHistory_probability, biasedShortHistory_probability] at entryEqual
  norm_num at entryEqual

/-- N-ary observational completeness exposes the biased middle lane. -/
theorem tripleAllFair_run_ne_triple :
    tripleAllFairProtocol.run (fun _ ↦ semantics) ≠
      ((tripleProtocol.normalForm (fun _ ↦ semantics)).reindexHistory
        tripleHistoryEquiv).toFinStoch := by
  intro equalRuns
  exact tripleAllFair_normalForm_ne_triple
    ((LaneProtocol.observationalCompletenessAlong (fun _ ↦ semantics)
      tripleAllFairProtocol tripleProtocol tripleHistoryEquiv).mp equalRuns)

#eval decide (Fintype.card fairTree.History = 5)
#eval fairTree.height
#eval fairTree.budget
#eval decide
  (fairTree.historyProbability semantics shortHistory = (1 : ℚ≥0) / 2)
#eval decide
  (fairTree.historyProbability semantics (longHistory true) =
    (1 : ℚ≥0) / 12)
#eval fold leafCountAlgebra fairTree
#eval (graft fairTree fairTree).height
#eval (graft fairTree fairTree).budget
#eval (fold (leafCountAlgebra ⊗ budgetAlgebra signature) fairTree).1
#eval (fold (leafCountAlgebra ⊗ budgetAlgebra signature) fairTree).2.down
#eval decide (Fintype.card fairBiasedParallel.History = 25)
#eval fairBiasedParallel.budget
#eval decide
  (fairBiasedParallel.historyProbability semantics semantics
    parallelShortHistory = (3 : ℚ≥0) / 8)
#eval (ParallelProtocol.graft
  fairBiasedParallel fairBiasedParallel).budget
#eval decide (Fintype.card tripleProtocol.History = 125)
#eval tripleProtocol.budget
#eval decide
  (tripleProtocol.historyProbability (fun _ ↦ semantics)
    tripleShortHistory = (3 : ℚ≥0) / 16)
#eval (LaneProtocol.graft tripleProtocol tripleProtocol).budget

end Ript.Examples.DependentBranching
