import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Ript.Models.Decision.DeterministicBlackwell

/-!
# Executable deterministic Blackwell converse

Four equiprobable hidden states are observed through a two-block deterministic
partition.  A target that is constant on those blocks is reconstructed with
zero risk and is an exact Blackwell garbling.  A crossing partition separates
each source block, has exact reconstruction risk `1/2`, and cannot be obtained
by any stochastic post-processing of the source.

The examples exercise both directions of the deterministic finite converse;
their risk values and fiber predicates reduce by ordinary kernel evaluation.
-/

set_option autoImplicit false

namespace Ript.Examples.DeterministicBlackwell

open Ript.Models.Decision.Blackwell
open Ript.Models.Decision.DeterministicBlackwell
open Ript.Models.Decision.FiniteRisk
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic

/-- Four executable hidden states. -/
abbrev fourState : Object :=
  ⟨Fin 4, inferInstance, inferInstance⟩

/-- Executable Boolean observation carrier. -/
abbrev observationBit : Object :=
  ⟨Bool, inferInstance, inferInstance⟩

/-- Exact full-support uniform prior on four hidden states. -/
def uniformFourPrior : FinDist fourState where
  prob _ := (1 : ℚ≥0) / 4
  normalized := by
    change (∑ _ : Fin 4, (1 : ℚ≥0) / 4) = 1
    norm_num [Fin.sum_univ_succ]

/-- Every hidden state has positive prior mass. -/
theorem uniformFourPrior_fullSupport (state : fourState) :
    0 < uniformFourPrior.prob state := by
  norm_num [uniformFourPrior]

/-- Source observation: distinguish the lower pair from the upper pair. -/
def blockObservation (state : fourState) : observationBit :=
  decide (state.val < 2)

/-- A target constant on each source block. -/
def alignedTarget (state : fourState) : observationBit :=
  !blockObservation state

/-- A target crossing both source blocks. -/
def crossingTarget (state : fourState) : observationBit :=
  decide (state.val % 2 = 0)

/-- Zero-one reconstruction task for the aligned target. -/
def alignedProblem : DecisionProblem fourState observationBit :=
  reconstructionProblem uniformFourPrior alignedTarget 0

/-- Zero-one reconstruction task for the crossing target. -/
def crossingProblem : DecisionProblem fourState observationBit :=
  reconstructionProblem uniformFourPrior crossingTarget 0

/-- The aligned target is reconstructed from the source blocks with zero
exact Bayes risk. -/
theorem aligned_reconstructionRisk_zero :
    finiteBayesRisk alignedProblem (FinStoch.dirac blockObservation) = 0 := by
  apply le_antisymm
  · calc
      finiteBayesRisk alignedProblem (FinStoch.dirac blockObservation) ≤
          deterministicDecisionRisk alignedProblem
            (FinStoch.dirac blockObservation) (fun bit ↦ !bit) :=
        finiteBayesRisk_le_deterministicDecisionRisk _ _ _
      _ = 0 := by
        change deterministicDecisionRisk
          (reconstructionProblem uniformFourPrior alignedTarget 0)
          (FinStoch.dirac blockObservation) (fun bit ↦ !bit) = 0
        rw [reconstruction_deterministicDecisionRisk]
        simp [alignedTarget]
  · exact zero_le

/-- Every action after either source-block observation has the same crossing
target loss mass `1/4`. -/
theorem crossing_actionRisk (observation action : observationBit) :
    actionRiskMass crossingProblem (FinStoch.dirac blockObservation)
      observation action = (1 : ℚ≥0) / 4 := by
  change Bool at observation action
  change (∑ state : Fin 4,
    (1 : ℚ≥0) / 4 *
      (if blockObservation state = observation then 1 else 0) *
      (if crossingTarget state = action then 0 else 1)) =
        (1 : ℚ≥0) / 4
  cases observation <;> cases action
  all_goals simp [blockObservation, crossingTarget, Fin.sum_univ_succ]

/-- The pointwise optimal crossing loss mass is `1/4` at either source
observation. -/
theorem crossing_optimalActionRisk (observation : observationBit) :
    optimalActionRisk crossingProblem (FinStoch.dirac blockObservation)
      observation = (1 : ℚ≥0) / 4 := by
  obtain ⟨action, haction⟩ :=
    exists_optimalAction crossingProblem (FinStoch.dirac blockObservation)
      observation
  calc
    optimalActionRisk crossingProblem (FinStoch.dirac blockObservation)
        observation =
        actionRiskMass crossingProblem (FinStoch.dirac blockObservation)
          observation action := haction.symm
    _ = (1 : ℚ≥0) / 4 := crossing_actionRisk observation action

/-- The crossing target retains exact error probability one half after the
source partition is observed. -/
theorem crossing_reconstructionRisk_half :
    finiteBayesRisk crossingProblem (FinStoch.dirac blockObservation) =
      (1 : ℚ≥0) / 2 := by
  rw [finiteBayesRisk]
  simp_rw [crossing_optimalActionRisk]
  change (∑ _ : Bool, (1 : ℚ≥0) / 4) = (1 : ℚ≥0) / 2
  rw [Fintype.sum_bool]
  norm_num

/-- The deterministic converse recovers an exact post-processing witness for
the aligned partition. -/
theorem block_dominates_aligned :
    BlackwellDominates (FinStoch.dirac blockObservation)
      (FinStoch.dirac alignedTarget) := by
  apply (deterministic_dominates_iff_reconstructionRisk_le uniformFourPrior
    uniformFourPrior_fullSupport blockObservation alignedTarget 0).2
  change finiteBayesRisk alignedProblem (FinStoch.dirac blockObservation) ≤
    finiteBayesRisk alignedProblem (FinStoch.dirac alignedTarget)
  have htarget :
      finiteBayesRisk alignedProblem (FinStoch.dirac alignedTarget) = 0 := by
    simpa [alignedProblem] using
      target_reconstructionRisk_zero uniformFourPrior alignedTarget 0
  rw [aligned_reconstructionRisk_zero, htarget]

/-- The positive crossing risk rules out every stochastic post-processing
from the source partition to the crossing target. -/
theorem block_not_dominates_crossing :
    ¬BlackwellDominates (FinStoch.dirac blockObservation)
      (FinStoch.dirac crossingTarget) := by
  intro hdominates
  have hrisk :=
    (deterministic_dominates_iff_reconstructionRisk_le uniformFourPrior
      uniformFourPrior_fullSupport blockObservation crossingTarget 0).1
      hdominates
  change finiteBayesRisk crossingProblem (FinStoch.dirac blockObservation) ≤
    finiteBayesRisk crossingProblem (FinStoch.dirac crossingTarget) at hrisk
  have htarget :
      finiteBayesRisk crossingProblem (FinStoch.dirac crossingTarget) = 0 := by
    simpa [crossingProblem] using
      target_reconstructionRisk_zero uniformFourPrior crossingTarget 0
  rw [crossing_reconstructionRisk_half, htarget] at hrisk
  norm_num at hrisk

-- The aligned reconstruction risk is exactly zero.
#eval decide
  (finiteBayesRisk alignedProblem (FinStoch.dirac blockObservation) = 0)

-- The crossing reconstruction risk is exactly one half.
#eval decide
  (finiteBayesRisk crossingProblem (FinStoch.dirac blockObservation) =
    (1 : ℚ≥0) / 2)

-- The aligned target is constant on every source fiber, while the crossing
-- target is not.
#eval decide
  ((∀ θ θ' : fourState,
      blockObservation θ = blockObservation θ' →
        alignedTarget θ = alignedTarget θ') ∧
    ¬(∀ θ θ' : fourState,
      blockObservation θ = blockObservation θ' →
        crossingTarget θ = crossingTarget θ'))

end Ript.Examples.DeterministicBlackwell
