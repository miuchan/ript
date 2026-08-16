import Ript.Models.Decision.ResourceBounded

/-!
# Task-relative semantic information

Semantic value is defined by improvement in optimal decision risk relative to
an explicit baseline experiment.  It therefore depends on a hidden-state
prior, action space, loss function, observation channel, and—when requested—a
decision-resource budget.  No task-independent entropy is postulated.

The relational predicates are primary: a channel has value at least `v` when
its risk plus `v` is no larger than the baseline risk.  Exact numeric values use
truncated subtraction in `ℚ≥0`, where that operation is already well defined.
-/

set_option autoImplicit false

namespace Ript.Models.Decision.SemanticValue

open Ript.Models.Decision.Blackwell
open Ript.Models.Decision.FiniteRisk
open Ript.Models.Decision.ResourceBounded
open Ript.Models.FiniteStochastic

universe u

variable {Θ B X Y A : Object.{u}}

/-- Relational task value: `P` improves on `baseline` by at least `value` in
the specified finite decision problem. -/
def HasSemanticValueAtLeast (problem : DecisionProblem Θ A)
    (baseline : FinStoch Θ B) (P : FinStoch Θ X) (value : ℚ≥0) : Prop :=
  finiteBayesRisk problem P + value ≤ finiteBayesRisk problem baseline

/-- Exact task-relative semantic value when subtraction in `ℚ≥0` is desired. -/
def semanticValue (problem : DecisionProblem Θ A)
    (baseline : FinStoch Θ B) (P : FinStoch Θ X) : ℚ≥0 :=
  finiteBayesRisk problem baseline - finiteBayesRisk problem P

/-- Garbling monotonicity in relational form: every value guarantee for the
less informative experiment also holds for the dominating experiment. -/
theorem hasSemanticValueAtLeast_mono
    (problem : DecisionProblem Θ A) (baseline : FinStoch Θ B)
    {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    (hPQ : BlackwellDominates P Q) {value : ℚ≥0}
    (hvalue : HasSemanticValueAtLeast problem baseline Q value) :
    HasSemanticValueAtLeast problem baseline P value := by
  unfold HasSemanticValueAtLeast at hvalue ⊢
  exact (add_le_add (finiteBayesRisk_mono hPQ problem) le_rfl).trans hvalue

/-- Garbling cannot increase exact task-relative semantic value. -/
theorem semanticValue_mono
    (problem : DecisionProblem Θ A) (baseline : FinStoch Θ B)
    {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    (hPQ : BlackwellDominates P Q) :
    semanticValue problem baseline Q ≤ semanticValue problem baseline P :=
  tsub_le_tsub_left (finiteBayesRisk_mono hPQ problem)
    (finiteBayesRisk problem baseline)

/-- Information-equivalent experiments have identical task-relative value. -/
theorem semanticValue_eq_of_equivalent
    (problem : DecisionProblem Θ A) (baseline : FinStoch Θ B)
    {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    (hPQ : BlackwellEquivalent P Q) :
    semanticValue problem baseline P = semanticValue problem baseline Q := by
  unfold semanticValue
  rw [finiteBayesRisk_eq_of_equivalent hPQ problem]

/-- An experiment has zero semantic value relative to itself.  Choosing an
uninformative experiment as the baseline gives the usual no-information-zero
law. -/
@[simp]
theorem semanticValue_baseline (problem : DecisionProblem Θ A)
    (baseline : FinStoch Θ B) :
    semanticValue problem baseline baseline = 0 := by
  simp [semanticValue]

/-- If every action has zero loss in every hidden state, every experiment has
zero Bayes risk. -/
theorem finiteBayesRisk_eq_zero_of_loss_eq_zero
    (problem : DecisionProblem Θ A) (P : FinStoch Θ X)
    (hloss : ∀ θ a, problem.loss θ a = 0) :
    finiteBayesRisk problem P = 0 := by
  apply le_antisymm
  · calc
      finiteBayesRisk problem P ≤
          deterministicDecisionRisk problem P
            (fun _ ↦ problem.defaultAction) :=
        finiteBayesRisk_le_deterministicDecisionRisk _ _ _
      _ = 0 := by
        simp [deterministicDecisionRisk, randomizedDecisionRisk, hloss]
  · exact zero_le

/-- Task-irrelevant observations have zero semantic value for a zero-loss
task, independently of the channel. -/
theorem semanticValue_eq_zero_of_loss_eq_zero
    (problem : DecisionProblem Θ A) (baseline : FinStoch Θ B)
    (P : FinStoch Θ X) (hloss : ∀ θ a, problem.loss θ a = 0) :
    semanticValue problem baseline P = 0 := by
  rw [semanticValue,
    finiteBayesRisk_eq_zero_of_loss_eq_zero problem baseline hloss,
    finiteBayesRisk_eq_zero_of_loss_eq_zero problem P hloss]
  simp

/-- Relational semantic value with an explicit scalar baseline risk and a
decision-resource budget. -/
def HasResourceSemanticValueAtLeast (baselineRisk : ℚ≥0)
    (problem : DecisionProblem Θ A) (P : FinStoch Θ X)
    (resources : DecisionResourceModel X A) (budget : Nat)
    (value : ℚ≥0) : Prop :=
  resourceBayesRisk problem P resources budget + value ≤ baselineRisk

/-- Exact resource-bounded semantic value relative to an explicit baseline
risk. -/
def resourceSemanticValue (baselineRisk : ℚ≥0)
    (problem : DecisionProblem Θ A) (P : FinStoch Θ X)
    (resources : DecisionResourceModel X A) (budget : Nat) : ℚ≥0 :=
  baselineRisk - resourceBayesRisk problem P resources budget

/-- Increasing the decision budget cannot decrease semantic value. -/
theorem resourceSemanticValue_mono_budget (baselineRisk : ℚ≥0)
    (problem : DecisionProblem Θ A) (P : FinStoch Θ X)
    (resources : DecisionResourceModel X A) {small large : Nat}
    (hbudget : small ≤ large) :
    resourceSemanticValue baselineRisk problem P resources small ≤
      resourceSemanticValue baselineRisk problem P resources large :=
  tsub_le_tsub_left
    (resourceBayesRisk_antitone problem P resources hbudget) baselineRisk

/-- A certified decision reduction transports semantic value while paying its
explicit additive overhead. -/
theorem resourceSemanticValue_mono_reduction
    (baselineRisk : ℚ≥0) {problem : DecisionProblem Θ A}
    {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    {sourceResources : DecisionResourceModel X A}
    {targetResources : DecisionResourceModel Y A}
    {overhead budget : Nat}
    (reduction : DecisionReduction problem P Q sourceResources
      targetResources overhead) :
    resourceSemanticValue baselineRisk problem Q targetResources budget ≤
      resourceSemanticValue baselineRisk problem P sourceResources
        (budget + overhead) :=
  tsub_le_tsub_left (resourceBayesRisk_le_of_reduction reduction) baselineRisk

/-- In particular, free post-processing cannot create resource-bounded
semantic value. -/
theorem resourceSemanticValue_mono_free_reduction
    (baselineRisk : ℚ≥0) {problem : DecisionProblem Θ A}
    {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    {sourceResources : DecisionResourceModel X A}
    {targetResources : DecisionResourceModel Y A}
    {budget : Nat}
    (reduction : DecisionReduction problem P Q sourceResources
      targetResources 0) :
    resourceSemanticValue baselineRisk problem Q targetResources budget ≤
      resourceSemanticValue baselineRisk problem P sourceResources budget := by
  simpa using resourceSemanticValue_mono_reduction baselineRisk
    (budget := budget) reduction

end Ript.Models.Decision.SemanticValue
