import Mathlib.Data.Finset.Max
import Ript.Models.Decision.Blackwell

/-!
# Executable finite decision risk

This module gives the computational counterpart of the measure-theoretic Bayes
risk used in `Ript.Models.Decision.Blackwell`.  Priors, experiments, losses,
and decision channels use exact nonnegative rationals.  Optimal risk is a sum
of genuine finite minima, rather than a nonconstructive `iInf`.

Randomized decision rules are retained in the comparison theorems.  The key
finite argument proves that no randomized rule beats the pointwise minimum;
this yields a direct exact-rational proof of Bayes-risk data processing under
arbitrary finite stochastic garblings.
-/

set_option autoImplicit false

namespace Ript.Models.Decision.FiniteRisk

open CategoryTheory
open scoped BigOperators
open Ript.Core
open Ript.Models.Decision.Blackwell
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic
open Ript.Models.FiniteStochastic.FinStoch

universe u

variable {Θ X Y A : Object.{u}}

/-- A finite decision problem with an exact prior and exact nonnegative loss.
`defaultAction` is computational data witnessing that the action carrier is
nonempty; it is used only to construct finite minima. -/
structure DecisionProblem (Θ A : Object.{u}) where
  /-- Exact prior distribution on the hidden parameter. -/
  prior : FinDist Θ
  /-- Loss incurred by taking an action in a hidden state. -/
  loss : Θ → A → ℚ≥0
  /-- A concrete action, ensuring that optimization ranges over a nonempty
  finite carrier. -/
  defaultAction : A

/-- Unnormalized posterior loss mass of choosing `a` after observing `x`. -/
def actionRiskMass (problem : DecisionProblem Θ A)
    (P : FinStoch Θ X) (x : X) (a : A) : ℚ≥0 :=
  ∑ θ, problem.prior.prob θ * P.prob θ x * problem.loss θ a

/-- The finite set of loss masses available at one observation. -/
def actionRiskSet (problem : DecisionProblem Θ A)
    (P : FinStoch Θ X) (x : X) : Finset ℚ≥0 :=
  Finset.univ.image (actionRiskMass problem P x)

/-- The action-risk set is nonempty because a decision problem supplies a
concrete default action. -/
theorem actionRiskSet_nonempty (problem : DecisionProblem Θ A)
    (P : FinStoch Θ X) (x : X) : (actionRiskSet problem P x).Nonempty := by
  refine ⟨actionRiskMass problem P x problem.defaultAction, ?_⟩
  exact Finset.mem_image.mpr
    ⟨problem.defaultAction, Finset.mem_univ _, rfl⟩

/-- Exact minimum loss mass at a single observation. -/
def optimalActionRisk (problem : DecisionProblem Θ A)
    (P : FinStoch Θ X) (x : X) : ℚ≥0 :=
  (actionRiskSet problem P x).min' (actionRiskSet_nonempty problem P x)

/-- The optimal action risk is below the risk of every concrete action. -/
theorem optimalActionRisk_le_actionRisk (problem : DecisionProblem Θ A)
    (P : FinStoch Θ X) (x : X) (a : A) :
    optimalActionRisk problem P x ≤ actionRiskMass problem P x a := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩

/-- At every observation, some action attains the computed finite minimum. -/
theorem exists_optimalAction (problem : DecisionProblem Θ A)
    (P : FinStoch Θ X) (x : X) :
    ∃ a : A, actionRiskMass problem P x a = optimalActionRisk problem P x := by
  have hmem := Finset.min'_mem (actionRiskSet problem P x)
    (actionRiskSet_nonempty problem P x)
  rcases Finset.mem_image.mp hmem with ⟨a, _, ha⟩
  exact ⟨a, ha⟩

/-- Executable Bayes risk: sum the finite minimum posterior loss mass over all
observations. -/
def finiteBayesRisk (problem : DecisionProblem Θ A)
    (P : FinStoch Θ X) : ℚ≥0 :=
  ∑ x, optimalActionRisk problem P x

/-- Expected loss of a randomized finite decision channel. -/
def randomizedDecisionRisk (problem : DecisionProblem Θ A)
    (P : FinStoch Θ X) (δ : FinStoch X A) : ℚ≥0 :=
  ∑ θ, ∑ a,
    problem.prior.prob θ * (FinStoch.comp P δ).prob θ a *
      problem.loss θ a

/-- Expected loss of a deterministic decision rule. -/
def deterministicDecisionRisk (problem : DecisionProblem Θ A)
    (P : FinStoch Θ X) (decision : X → A) : ℚ≥0 :=
  randomizedDecisionRisk problem P (FinStoch.dirac decision)

/-- Reorganize randomized expected loss by observation and action. -/
theorem randomizedDecisionRisk_eq_sum_actionRisk
    (problem : DecisionProblem Θ A) (P : FinStoch Θ X)
    (δ : FinStoch X A) :
    randomizedDecisionRisk problem P δ =
      ∑ x, ∑ a, δ.prob x a * actionRiskMass problem P x a := by
  calc
    randomizedDecisionRisk problem P δ =
        ∑ θ, ∑ a, ∑ x,
          problem.prior.prob θ * (P.prob θ x * δ.prob x a) *
            problem.loss θ a := by
      unfold randomizedDecisionRisk
      apply Fintype.sum_congr
      intro θ
      apply Fintype.sum_congr
      intro a
      change problem.prior.prob θ *
          (∑ x, P.prob θ x * δ.prob x a) * problem.loss θ a = _
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ θ, ∑ x, ∑ a,
          problem.prior.prob θ * (P.prob θ x * δ.prob x a) *
            problem.loss θ a := by
      apply Fintype.sum_congr
      intro θ
      rw [Finset.sum_comm]
    _ = ∑ x, ∑ θ, ∑ a,
          problem.prior.prob θ * (P.prob θ x * δ.prob x a) *
            problem.loss θ a := by
      rw [Finset.sum_comm]
    _ = ∑ x, ∑ a, ∑ θ,
          problem.prior.prob θ * (P.prob θ x * δ.prob x a) *
            problem.loss θ a := by
      apply Fintype.sum_congr
      intro x
      rw [Finset.sum_comm]
    _ = ∑ x, ∑ a, ∑ θ,
          δ.prob x a *
            (problem.prior.prob θ * P.prob θ x * problem.loss θ a) := by
      apply Fintype.sum_congr
      intro x
      apply Fintype.sum_congr
      intro a
      apply Fintype.sum_congr
      intro θ
      ac_rfl
    _ = ∑ x, ∑ a, δ.prob x a * actionRiskMass problem P x a := by
      apply Fintype.sum_congr
      intro x
      apply Fintype.sum_congr
      intro a
      rw [actionRiskMass, Finset.mul_sum]

/-- A deterministic rule's expected loss is the sum of the action-risk masses
selected at each observation. -/
theorem deterministicDecisionRisk_eq_sum_actionRisk
    (problem : DecisionProblem Θ A) (P : FinStoch Θ X)
    (decision : X → A) :
    deterministicDecisionRisk problem P decision =
      ∑ x, actionRiskMass problem P x (decision x) := by
  rw [deterministicDecisionRisk, randomizedDecisionRisk_eq_sum_actionRisk]
  apply Fintype.sum_congr
  intro x
  simp [FinStoch.dirac]

/-- No randomized finite decision channel can beat the executable finite Bayes
risk. -/
theorem finiteBayesRisk_le_randomizedDecisionRisk
    (problem : DecisionProblem Θ A) (P : FinStoch Θ X)
    (δ : FinStoch X A) :
    finiteBayesRisk problem P ≤ randomizedDecisionRisk problem P δ := by
  rw [finiteBayesRisk, randomizedDecisionRisk_eq_sum_actionRisk]
  apply Finset.sum_le_sum
  intro x _
  calc
    optimalActionRisk problem P x =
        (∑ a, δ.prob x a) * optimalActionRisk problem P x := by
      rw [δ.normalized, one_mul]
    _ = ∑ a, δ.prob x a * optimalActionRisk problem P x := by
      rw [Finset.sum_mul]
    _ ≤ ∑ a, δ.prob x a * actionRiskMass problem P x a := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left
        (optimalActionRisk_le_actionRisk problem P x a) zero_le

/-- The executable finite Bayes risk is below every deterministic rule. -/
theorem finiteBayesRisk_le_deterministicDecisionRisk
    (problem : DecisionProblem Θ A) (P : FinStoch Θ X)
    (decision : X → A) :
    finiteBayesRisk problem P ≤
      deterministicDecisionRisk problem P decision :=
  finiteBayesRisk_le_randomizedDecisionRisk problem P
    (FinStoch.dirac decision)

/-- A deterministic decision rule attains the executable finite Bayes risk. -/
theorem exists_optimalDecision (problem : DecisionProblem Θ A)
    (P : FinStoch Θ X) :
    ∃ decision : X → A,
      deterministicDecisionRisk problem P decision =
        finiteBayesRisk problem P := by
  classical
  choose decision hdecision using fun x ↦ exists_optimalAction problem P x
  refine ⟨decision, ?_⟩
  rw [deterministicDecisionRisk_eq_sum_actionRisk, finiteBayesRisk]
  apply Fintype.sum_congr
  exact hdecision

/-- Associativity of experiment and decision-channel composition is reflected
exactly by randomized expected loss. -/
theorem randomizedDecisionRisk_comp
    (problem : DecisionProblem Θ A) (P : FinStoch Θ X)
    (κ : FinStoch X Y) (δ : FinStoch Y A) :
    randomizedDecisionRisk problem P (FinStoch.comp κ δ) =
      randomizedDecisionRisk problem (FinStoch.comp P κ) δ := by
  unfold randomizedDecisionRisk
  have hcomp :
      FinStoch.comp P (FinStoch.comp κ δ) =
        FinStoch.comp (FinStoch.comp P κ) δ :=
    (@Category.assoc Object _ Θ X Y A P κ δ).symm
  rw [hcomp]

/-- **Executable Bayes-risk data processing.** If `P` Blackwell-dominates
`Q`, then `P` has no greater optimal risk in any exact finite decision
problem.  This proves the forward Blackwell implication using finite sums and
finite minima only. -/
theorem finiteBayesRisk_mono {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    (hPQ : BlackwellDominates P Q) (problem : DecisionProblem Θ A) :
    finiteBayesRisk problem P ≤ finiteBayesRisk problem Q := by
  rcases hPQ with ⟨κ, hκ⟩
  change FinStoch.comp P κ = Q at hκ
  obtain ⟨decision, hdecision⟩ := exists_optimalDecision problem Q
  calc
    finiteBayesRisk problem P ≤
        randomizedDecisionRisk problem P
          (FinStoch.comp κ (FinStoch.dirac decision)) :=
      finiteBayesRisk_le_randomizedDecisionRisk problem P _
    _ = randomizedDecisionRisk problem (FinStoch.comp P κ)
          (FinStoch.dirac decision) :=
      randomizedDecisionRisk_comp problem P κ (FinStoch.dirac decision)
    _ = randomizedDecisionRisk problem Q (FinStoch.dirac decision) := by
      rw [hκ]
    _ = deterministicDecisionRisk problem Q decision := rfl
    _ = finiteBayesRisk problem Q := hdecision

/-- Blackwell-equivalent experiments have the same executable Bayes risk in
every exact finite decision problem. -/
theorem finiteBayesRisk_eq_of_equivalent
    {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    (hPQ : BlackwellEquivalent P Q) (problem : DecisionProblem Θ A) :
    finiteBayesRisk problem P = finiteBayesRisk problem Q :=
  le_antisymm
    (finiteBayesRisk_mono hPQ.1 problem)
    (finiteBayesRisk_mono hPQ.2 problem)

end Ript.Models.Decision.FiniteRisk
