import Ript.Models.Decision.ResourceBounded
import Ript.Models.Decision.RationalSeparation

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
open Ript.Models.Decision.Separation
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

/-! ## Universal semantic profiles -/

/-- The unique no-information experiment with one possible observation. -/
def noInformationExperiment (Θ : Object.{u}) : FinStoch Θ Object.unit :=
  FinStoch.discard Θ

/-- Every finite experiment Blackwell-dominates the no-information
experiment. -/
theorem dominates_noInformation (P : FinStoch Θ X) :
    BlackwellDominates P (noInformationExperiment Θ) := by
  have dominates := dominates_postprocess P (FinStoch.discard X)
  rw [FinStoch.comp_discard] at dominates
  exact dominates

/-- Universal relational semantic order: `P` has nonnegative value relative
to `Q` in every exact finite decision problem. -/
def UniversalSemanticOrder (P : FinStoch Θ X) (Q : FinStoch Θ Y) : Prop :=
  ∀ (A : Object.{u}) (problem : DecisionProblem Θ A),
    HasSemanticValueAtLeast problem Q P 0

/-- Universal semantic order is exactly the finite decision-risk order. -/
theorem universalSemanticOrder_iff_finiteDecisionOrder
    (P : FinStoch Θ X) (Q : FinStoch Θ Y) :
    UniversalSemanticOrder P Q ↔ FiniteDecisionOrder P Q := by
  constructor <;> intro order A problem <;>
    simpa [UniversalSemanticOrder, HasSemanticValueAtLeast] using
      order A problem

/-- **Relational semantic completeness.**  On a nonempty hidden-state
carrier, universal nonnegative task value relative to `Q` is equivalent to
exact Blackwell dominance over `Q`. -/
theorem blackwellDominates_iff_universalSemanticOrder
    [Nonempty Θ.carrier] (P : FinStoch Θ X) (Q : FinStoch Θ Y) :
    BlackwellDominates P Q ↔ UniversalSemanticOrder P Q := by
  constructor
  · intro dominates
    exact (universalSemanticOrder_iff_finiteDecisionOrder P Q).2
      (finiteDecisionOrder_of_dominates dominates)
  · intro order
    exact Ript.Models.Decision.RationalSeparation.blackwellShermanSteinConverse
      P Q ((universalSemanticOrder_iff_finiteDecisionOrder P Q).1 order)

/-- Exact numeric semantic value relative to the canonical no-information
baseline. -/
def noInformationSemanticValue (problem : DecisionProblem Θ A)
    (P : FinStoch Θ X) : ℚ≥0 :=
  semanticValue problem (noInformationExperiment Θ) P

/-- Equality of the entire exact finite task-value profile.  Unlike one
scalar task value, this family is a candidate complete invariant. -/
def UniversalSemanticValueProfileEqual
    (P : FinStoch Θ X) (Q : FinStoch Θ Y) : Prop :=
  ∀ (A : Object.{u}) (problem : DecisionProblem Θ A),
    noInformationSemanticValue problem P =
      noInformationSemanticValue problem Q

/-- Equality of no-information-relative semantic values for one task reflects
equality of its exact Bayes risks. -/
theorem finiteBayesRisk_eq_of_noInformationSemanticValue_eq
    (problem : DecisionProblem Θ A) (P : FinStoch Θ X)
    (Q : FinStoch Θ Y)
    (equal : noInformationSemanticValue problem P =
      noInformationSemanticValue problem Q) :
    finiteBayesRisk problem P = finiteBayesRisk problem Q := by
  have riskP : finiteBayesRisk problem P ≤
      finiteBayesRisk problem (noInformationExperiment Θ) :=
    finiteBayesRisk_mono (dominates_noInformation P) problem
  have riskQ : finiteBayesRisk problem Q ≤
      finiteBayesRisk problem (noInformationExperiment Θ) :=
    finiteBayesRisk_mono (dominates_noInformation Q) problem
  unfold noInformationSemanticValue semanticValue at equal
  exact (tsub_right_inj riskP riskQ).mp equal

/-- **Numeric semantic-value completeness.**  For a nonempty finite hidden
carrier, two experiments are Blackwell equivalent exactly when all exact
finite task-relative semantic values, measured from the canonical
no-information baseline, agree. -/
theorem blackwellEquivalent_iff_universalSemanticValueProfileEqual
    [Nonempty Θ.carrier] (P : FinStoch Θ X) (Q : FinStoch Θ Y) :
    BlackwellEquivalent P Q ↔ UniversalSemanticValueProfileEqual P Q := by
  constructor
  · intro equivalent A problem
    exact semanticValue_eq_of_equivalent problem
      (noInformationExperiment Θ) equivalent
  · intro profile
    have riskEqual : ∀ (A : Object.{u})
        (problem : DecisionProblem Θ A),
        finiteBayesRisk problem P = finiteBayesRisk problem Q :=
      fun A problem ↦
        finiteBayesRisk_eq_of_noInformationSemanticValue_eq
          problem P Q (profile A problem)
    have orderPQ : FiniteDecisionOrder P Q :=
      fun A problem ↦ (riskEqual A problem).le
    have orderQP : FiniteDecisionOrder Q P :=
      fun A problem ↦ (riskEqual A problem).ge
    exact ⟨
      Ript.Models.Decision.RationalSeparation.blackwellShermanSteinConverse
        P Q orderPQ,
      Ript.Models.Decision.RationalSeparation.blackwellShermanSteinConverse
        Q P orderQP⟩

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
