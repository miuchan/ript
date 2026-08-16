import Mathlib.Tactic.NormNum
import Ript.Models.Decision.Separation

/-!
# Executable stochastic decision separation

This example supplies a concrete separation certificate between two genuinely
stochastic Boolean experiments.  The source observation is independent of a
uniform hidden bit.  The target reports the hidden bit correctly with
probability `3/4` and flips it with probability `1/4`.

Using the target observation directly therefore guesses the hidden state with
exact risk `1/4`, whereas every rule based on the uninformative source has
risk `1/2`.  The generic certificate theorem rules out every stochastic
garbling from the uninformative experiment to the noisy informative one.
-/

set_option autoImplicit false

namespace Ript.Examples.StochasticSeparation

open Ript.Models.Decision.Blackwell
open Ript.Models.Decision.FiniteRisk
open Ript.Models.Decision.Separation
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic

/-- Executable Boolean carrier for the stochastic separation example. -/
abbrev separationBit : Object :=
  ⟨Bool, inferInstance, inferInstance⟩

/-- Exact uniform prior on the hidden Boolean state. -/
def uniformPrior : FinDist separationBit where
  prob _ := (1 : ℚ≥0) / 2
  normalized := by
    change (∑ _ : Bool, (1 : ℚ≥0) / 2) = 1
    rw [Fintype.sum_bool]
    norm_num

/-- Guess the hidden bit under exact zero-one loss. -/
def guessingProblem : DecisionProblem separationBit separationBit where
  prior := uniformPrior
  loss state action := if state = action then 0 else 1
  defaultAction := false

/-- A Boolean observation independent of the hidden state. -/
def uninformativeExperiment : FinStoch separationBit separationBit where
  prob _ _ := (1 : ℚ≥0) / 2
  normalized := by
    intro state
    change Bool at state
    change (∑ _ : Bool, (1 : ℚ≥0) / 2) = 1
    rw [Fintype.sum_bool]
    norm_num

/-- A genuinely stochastic informative experiment: report the hidden bit
correctly with probability `3/4`. -/
def noisyExperiment : FinStoch separationBit separationBit where
  prob state observation :=
    if observation = state then (3 : ℚ≥0) / 4 else (1 : ℚ≥0) / 4
  normalized := by
    intro state
    change Bool at state
    cases state
    · change (∑ observation : Bool,
        if observation = false then (3 : ℚ≥0) / 4 else 1 / 4) = 1
      rw [Fintype.sum_bool]
      norm_num
    · change (∑ observation : Bool,
        if observation = true then (3 : ℚ≥0) / 4 else 1 / 4) = 1
      rw [Fintype.sum_bool]
      norm_num

/-- Under the independent source, every action at every observation has loss
mass exactly `1/4`. -/
theorem uninformative_actionRisk (observation action : separationBit) :
    actionRiskMass guessingProblem uninformativeExperiment observation action =
      (1 : ℚ≥0) / 4 := by
  change Bool at observation action
  cases observation <;> cases action
  all_goals
    change (∑ state : Bool, _) = _
    rw [Fintype.sum_bool]
    norm_num [guessingProblem, uninformativeExperiment, uniformPrior]
  all_goals simp

/-- Every deterministic rule based on the independent source has risk `1/2`. -/
theorem uninformative_decision_half_risk
    (decision : separationBit → separationBit) :
    deterministicDecisionRisk guessingProblem uninformativeExperiment
        decision = (1 : ℚ≥0) / 2 := by
  rw [deterministicDecisionRisk_eq_sum_actionRisk]
  simp_rw [uninformative_actionRisk]
  change (∑ _ : Bool, (1 : ℚ≥0) / 4) = (1 : ℚ≥0) / 2
  rw [Fintype.sum_bool]
  norm_num

/-- The uninformative source has exact Bayes risk `1/2`. -/
theorem uninformative_information_half_risk :
    finiteBayesRisk guessingProblem uninformativeExperiment =
      (1 : ℚ≥0) / 2 := by
  obtain ⟨decision, hdecision⟩ :=
    exists_optimalDecision guessingProblem uninformativeExperiment
  calc
    finiteBayesRisk guessingProblem uninformativeExperiment =
        deterministicDecisionRisk guessingProblem uninformativeExperiment
          decision := hdecision.symm
    _ = (1 : ℚ≥0) / 2 := uninformative_decision_half_risk decision

/-- For a noisy observation, the matching action has posterior loss mass
`1/8`; the other action has loss mass `3/8`. -/
theorem noisy_actionRisk (observation action : separationBit) :
    actionRiskMass guessingProblem noisyExperiment observation action =
      if action = observation then (1 : ℚ≥0) / 8 else (3 : ℚ≥0) / 8 := by
  change Bool at observation action
  cases observation <;> cases action
  all_goals
    change (∑ state : Bool, _) = _
    rw [Fintype.sum_bool]
    norm_num [guessingProblem, noisyExperiment, uniformPrior]
  all_goals simp

/-- The exact pointwise optimal posterior loss mass is `1/8`. -/
theorem noisy_optimalActionRisk (observation : separationBit) :
    optimalActionRisk guessingProblem noisyExperiment observation =
      (1 : ℚ≥0) / 8 := by
  apply le_antisymm
  · calc
      optimalActionRisk guessingProblem noisyExperiment observation ≤
          actionRiskMass guessingProblem noisyExperiment observation
            observation :=
        optimalActionRisk_le_actionRisk _ _ _ _
      _ = (1 : ℚ≥0) / 8 := by rw [noisy_actionRisk]; simp
  · obtain ⟨action, haction⟩ :=
      exists_optimalAction guessingProblem noisyExperiment observation
    rw [← haction, noisy_actionRisk]
    split
    · exact le_rfl
    · exact
        (div_le_div_iff_of_pos_right
          (by norm_num : (0 : ℚ≥0) < 8)).mpr (by norm_num)

/-- The noisy informative experiment has exact Bayes risk `1/4`. -/
theorem noisy_information_quarter_risk :
    finiteBayesRisk guessingProblem noisyExperiment = (1 : ℚ≥0) / 4 := by
  rw [finiteBayesRisk]
  simp_rw [noisy_optimalActionRisk]
  change (∑ _ : Bool, (1 : ℚ≥0) / 8) = (1 : ℚ≥0) / 4
  rw [Fintype.sum_bool]
  norm_num

/-- Using the noisy observation directly attains the exact risk `1/4`. -/
theorem noisy_identity_decision_quarter_risk :
    deterministicDecisionRisk guessingProblem noisyExperiment id =
      (1 : ℚ≥0) / 4 := by
  rw [deterministicDecisionRisk_eq_sum_actionRisk]
  simp_rw [noisy_actionRisk]
  change (∑ observation : Bool,
    if observation = observation then (1 : ℚ≥0) / 8 else 3 / 8) = 1 / 4
  rw [Fintype.sum_bool]
  norm_num

/-- Exact finite decision data separating the noisy informative experiment
from the uninformative source. -/
def noisyBeatsUninformativeCertificate :
    DecisionSeparationCertificate uninformativeExperiment noisyExperiment where
  action := separationBit
  problem := guessingProblem
  decision := id
  separates := by
    rw [noisy_identity_decision_quarter_risk,
      uninformative_information_half_risk]
    norm_num

/-- No stochastic post-processing of an observation independent of the state
can produce this noisy informative experiment. -/
theorem uninformative_not_dominates_noisy :
    ¬BlackwellDominates uninformativeExperiment noisyExperiment :=
  noisyBeatsUninformativeCertificate.not_dominates

-- The genuinely stochastic target has exact optimal risk one quarter.
#eval decide
  (finiteBayesRisk guessingProblem noisyExperiment = (1 : ℚ≥0) / 4)

-- The independent source retains exact risk one half.
#eval decide
  (finiteBayesRisk guessingProblem uninformativeExperiment =
    (1 : ℚ≥0) / 2)

-- The target's exact risk is strictly smaller than the source's.
#eval decide
  (finiteBayesRisk guessingProblem noisyExperiment <
    finiteBayesRisk guessingProblem uninformativeExperiment)

end Ript.Examples.StochasticSeparation
