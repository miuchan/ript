import Mathlib.Tactic.NormNum
import Ript.Examples.StochasticBits
import Ript.Models.Decision.SemanticValue

/-!
# Executable Boolean decision problem

A hidden fair bit must be guessed under exact zero-one loss.  Perfect
observation has Bayes risk zero; an observation independent of the state has
risk `1/2`.  A simple resource model charges one unit for using the observation
and zero for constant decisions, exposing the task value of one unit of
decision budget.
-/

set_option autoImplicit false

namespace Ript.Examples.SimpleDecision

open CategoryTheory
open Ript.Examples.StochasticBits
open Ript.Models.Decision.Blackwell
open Ript.Models.Decision.FiniteRisk
open Ript.Models.Decision.ResourceBounded
open Ript.Models.Decision.SemanticValue
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic
open Ript.Models.FiniteStochastic.FinStoch

/-- A reducible Boolean carrier for decision computations. -/
abbrev decisionBit : Object :=
  Object.of Bool

/-- Exact uniform prior on the hidden Boolean state. -/
def uniformBitPrior : FinDist decisionBit where
  prob _ := (1 : ℚ≥0) / 2
  normalized := by
    change (∑ state : Bool, (1 : ℚ≥0) / 2) = 1
    rw [Fintype.sum_bool]
    norm_num

/-- Guess the hidden bit with zero-one loss. -/
def bitGuessing : DecisionProblem decisionBit decisionBit where
  prior := uniformBitPrior
  loss state action := if state = action then 0 else 1
  defaultAction := false

/-- Perfect observation of the hidden bit. -/
def perfectExperiment : FinStoch decisionBit decisionBit :=
  FinStoch.identity decisionBit

/-- A Boolean observation independent of the hidden state. -/
def uninformativeExperiment : FinStoch decisionBit decisionBit where
  prob _ _ := (1 : ℚ≥0) / 2
  normalized state := by
    change Bool at state
    change (∑ observation : Bool, (1 : ℚ≥0) / 2) = 1
    rw [Fintype.sum_bool]
    norm_num

/-- The perfect experiment Blackwell-dominates the uninformative one. -/
theorem perfect_dominates_uninformative :
    BlackwellDominates perfectExperiment uninformativeExperiment := by
  refine ⟨uninformativeExperiment, ?_⟩
  apply FinStoch.ext
  intro state observation
  simp [perfectExperiment, FinStoch.identity, uninformativeExperiment]

/-- Under perfect observation, an action has loss mass `0` when it matches the
observation and `1/2` otherwise. -/
theorem perfect_actionRisk (observation action : decisionBit) :
    actionRiskMass bitGuessing perfectExperiment observation action =
      if observation = action then 0 else (1 : ℚ≥0) / 2 := by
  change Bool at observation action
  cases observation <;> cases action <;>
    norm_num [actionRiskMass, bitGuessing, perfectExperiment,
      uniformBitPrior, decisionBit, Object.of, FinStoch.identity,
      Fintype.sum_bool]
  all_goals
    change (∑ state : Bool, _) = _
    rw [Fintype.sum_bool]
    simp
    norm_num
  all_goals rfl

/-- Under an independent observation, every action at every observation has
loss mass exactly `1/4`. -/
theorem uninformative_actionRisk (observation action : decisionBit) :
    actionRiskMass bitGuessing uninformativeExperiment observation action =
      (1 : ℚ≥0) / 4 := by
  change Bool at observation action
  cases observation <;> cases action <;>
    norm_num [actionRiskMass, bitGuessing, uninformativeExperiment,
      uniformBitPrior, decisionBit, Object.of, Fintype.sum_bool]
  all_goals
    change (∑ state : Bool, _) = _
    rw [Fintype.sum_bool]
    simp
  all_goals rfl

/-- Acting on a perfect observation by the identity rule has zero risk. -/
theorem perfect_identity_decision_zero :
    deterministicDecisionRisk bitGuessing perfectExperiment id = 0 := by
  rw [deterministicDecisionRisk_eq_sum_actionRisk]
  simp_rw [perfect_actionRisk]
  change (∑ observation : Bool,
    if observation = observation then (0 : ℚ≥0) else 1 / 2) = 0
  rw [Fintype.sum_bool]
  simp

/-- Perfect observation gives exact zero Bayes risk. -/
theorem perfect_information_zero_risk :
    finiteBayesRisk bitGuessing perfectExperiment = 0 := by
  apply le_antisymm
  · calc
      finiteBayesRisk bitGuessing perfectExperiment ≤
          deterministicDecisionRisk bitGuessing perfectExperiment id :=
        finiteBayesRisk_le_deterministicDecisionRisk _ _ _
      _ = 0 := perfect_identity_decision_zero
  · exact zero_le

/-- Every deterministic rule has risk `1/2` when the observation is independent
of the hidden fair bit. -/
theorem uninformative_decision_half_risk
    (decision : decisionBit → decisionBit) :
    deterministicDecisionRisk bitGuessing uninformativeExperiment decision =
      (1 : ℚ≥0) / 2 := by
  rw [deterministicDecisionRisk_eq_sum_actionRisk]
  simp_rw [uninformative_actionRisk]
  change (∑ observation : Bool,
    (1 : ℚ≥0) / 4) = (1 : ℚ≥0) / 2
  rw [Fintype.sum_bool]
  norm_num

/-- An independent observation leaves exact Bayes risk `1/2`. -/
theorem uninformative_information_half_risk :
    finiteBayesRisk bitGuessing uninformativeExperiment =
      (1 : ℚ≥0) / 2 := by
  obtain ⟨decision, hdecision⟩ :=
    exists_optimalDecision bitGuessing uninformativeExperiment
  calc
    finiteBayesRisk bitGuessing uninformativeExperiment =
        deterministicDecisionRisk bitGuessing uninformativeExperiment
          decision := hdecision.symm
    _ = (1 : ℚ≥0) / 2 := uninformative_decision_half_risk decision

/-- The executable data-processing theorem orders the two risks without
recomputing either matrix. -/
theorem decision_data_processing :
    finiteBayesRisk bitGuessing perfectExperiment ≤
      finiteBayesRisk bitGuessing uninformativeExperiment :=
  finiteBayesRisk_mono perfect_dominates_uninformative bitGuessing

/-- Charge one unit exactly when a Boolean decision genuinely depends on its
observation. -/
def bitDecisionResources : DecisionResourceModel decisionBit decisionBit where
  cost decision := if decision false = decision true then 0 else 1
  fallback _ := false
  fallback_cost := rfl

/-- A perfect observation followed by a constant decision still has risk
`1/2`. -/
theorem perfect_constant_decision_half_risk
    (decision : decisionBit → decisionBit)
    (hconstant : decision false = decision true) :
    deterministicDecisionRisk bitGuessing perfectExperiment decision =
      (1 : ℚ≥0) / 2 := by
  rw [deterministicDecisionRisk_eq_sum_actionRisk]
  simp_rw [perfect_actionRisk]
  change Bool → Bool at decision
  change (∑ observation : Bool,
    if observation = decision observation then (0 : ℚ≥0) else 1 / 2) =
      (1 : ℚ≥0) / 2
  rw [Fintype.sum_bool]
  cases hfalse : decision false <;> cases htrue : decision true <;>
    simp_all

/-- With zero decision budget, even perfect observations cannot be used. -/
theorem zero_budget_half_risk :
    resourceBayesRisk bitGuessing perfectExperiment bitDecisionResources 0 =
      (1 : ℚ≥0) / 2 := by
  apply le_antisymm
  · calc
      resourceBayesRisk bitGuessing perfectExperiment
          bitDecisionResources 0 ≤
          deterministicDecisionRisk bitGuessing perfectExperiment
            bitDecisionResources.fallback :=
        resourceBayesRisk_le_decision _ _ _ _ (by rfl)
      _ = (1 : ℚ≥0) / 2 :=
        perfect_constant_decision_half_risk _ rfl
  · obtain ⟨decision, hcost, hrisk⟩ :=
      exists_optimalBudgetedDecision bitGuessing perfectExperiment
        bitDecisionResources 0
    have hconstant : decision false = decision true := by
      by_contra hne
      simp [bitDecisionResources, hne] at hcost
    rw [← hrisk, perfect_constant_decision_half_risk decision hconstant]

/-- One unit of budget allows the identity decision and recovers zero risk. -/
theorem one_budget_zero_risk :
    resourceBayesRisk bitGuessing perfectExperiment bitDecisionResources 1 =
      0 := by
  apply le_antisymm
  · calc
      resourceBayesRisk bitGuessing perfectExperiment
          bitDecisionResources 1 ≤
          deterministicDecisionRisk bitGuessing perfectExperiment id :=
        resourceBayesRisk_le_decision _ _ _ _ (by decide)
      _ = 0 := perfect_identity_decision_zero
  · exact zero_le

/-- The generic budget-antitonicity theorem explains the computed
improvement. -/
theorem more_budget_cannot_hurt :
    resourceBayesRisk bitGuessing perfectExperiment bitDecisionResources 1 ≤
      resourceBayesRisk bitGuessing perfectExperiment bitDecisionResources 0 :=
  resourceBayesRisk_antitone bitGuessing perfectExperiment
    bitDecisionResources (Nat.zero_le 1)

/-- Perfect observation has exact semantic value `1/2` for the guessing task,
relative to the independent-observation baseline. -/
theorem perfect_guessing_semantic_value :
    semanticValue bitGuessing uninformativeExperiment perfectExperiment =
      (1 : ℚ≥0) / 2 := by
  rw [semanticValue, uninformative_information_half_risk,
    perfect_information_zero_risk]
  norm_num

/-- A task whose loss is always zero, used to show task relativity. -/
def irrelevantTask : DecisionProblem decisionBit decisionBit where
  prior := uniformBitPrior
  loss _ _ := 0
  defaultAction := false

/-- The same perfect observation has zero value for an irrelevant task. -/
theorem perfect_irrelevant_semantic_value :
    semanticValue irrelevantTask uninformativeExperiment perfectExperiment =
      0 :=
  semanticValue_eq_zero_of_loss_eq_zero _ _ _ (fun _ _ ↦ rfl)

/-- Zero budget gives zero task value relative to the no-observation risk. -/
theorem zero_budget_zero_semantic_value :
    resourceSemanticValue ((1 : ℚ≥0) / 2) bitGuessing perfectExperiment
      bitDecisionResources 0 = 0 := by
  rw [resourceSemanticValue, zero_budget_half_risk]
  simp

/-- One unit of decision budget exposes the full `1/2` guessing value. -/
theorem one_budget_half_semantic_value :
    resourceSemanticValue ((1 : ℚ≥0) / 2) bitGuessing perfectExperiment
      bitDecisionResources 1 = (1 : ℚ≥0) / 2 := by
  rw [resourceSemanticValue, one_budget_zero_risk]
  simp

#eval decide (finiteBayesRisk bitGuessing perfectExperiment = 0)
#eval decide (finiteBayesRisk bitGuessing uninformativeExperiment = (1 : ℚ≥0) / 2)
#eval decide
  (resourceBayesRisk bitGuessing perfectExperiment bitDecisionResources 0 =
    (1 : ℚ≥0) / 2)
#eval decide
  (resourceBayesRisk bitGuessing perfectExperiment bitDecisionResources 1 = 0)
#eval decide
  (semanticValue bitGuessing uninformativeExperiment perfectExperiment =
    (1 : ℚ≥0) / 2)
#eval decide
  (semanticValue irrelevantTask uninformativeExperiment perfectExperiment = 0)

end Ript.Examples.SimpleDecision
