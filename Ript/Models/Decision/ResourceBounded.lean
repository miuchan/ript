import Ript.Models.Decision.FiniteRisk

/-!
# Resource-bounded finite decision value

A `DecisionResourceModel` assigns an executable natural-number cost to every
deterministic finite decision rule and supplies a zero-cost fallback.  The
optimal risk within a budget is therefore a minimum over a nonempty finite
set, not an `iInf`.

Cost transport across experiments is expressed by `DecisionReduction`.  Its
fields state exactly what a post-processing argument must establish: a way to
lift target decisions, a risk inequality, and an additive cost bound.  This
separation avoids assuming that an arbitrary stochastic garbling preserves an
unrelated user-supplied cost model.
-/

set_option autoImplicit false

namespace Ript.Models.Decision.ResourceBounded

open CategoryTheory
open Ript.Models.Decision.FiniteRisk
open Ript.Models.FiniteStochastic
open Ript.Models.FiniteStochastic.FinStoch

universe u

variable {Θ X Y Z A : Object.{u}}

/-- Executable resource costs for deterministic decisions on observations
`X`, together with a decision feasible at every natural-number budget. -/
structure DecisionResourceModel (X A : Object.{u}) where
  /-- Cost of a deterministic decision rule. -/
  cost : (X → A) → Nat
  /-- A fallback rule used to make every budget-feasible set nonempty. -/
  fallback : X → A
  /-- The fallback rule is free. -/
  fallback_cost : cost fallback = 0

/-- Deterministic rules available within budget `budget`. -/
def feasibleDecisions (resources : DecisionResourceModel X A)
    (budget : Nat) : Finset (X → A) :=
  Finset.univ.filter fun decision ↦ resources.cost decision ≤ budget

/-- The feasible decision set is nonempty at every budget. -/
theorem feasibleDecisions_nonempty (resources : DecisionResourceModel X A)
    (budget : Nat) : (feasibleDecisions resources budget).Nonempty := by
  refine ⟨resources.fallback, ?_⟩
  simp [feasibleDecisions, resources.fallback_cost]

/-- Exact risks attained by decisions within the resource budget. -/
def budgetedRiskSet (problem : DecisionProblem Θ A) (P : FinStoch Θ X)
    (resources : DecisionResourceModel X A) (budget : Nat) : Finset ℚ≥0 :=
  (feasibleDecisions resources budget).image
    (deterministicDecisionRisk problem P)

/-- The set of budget-feasible risks is nonempty. -/
theorem budgetedRiskSet_nonempty (problem : DecisionProblem Θ A)
    (P : FinStoch Θ X) (resources : DecisionResourceModel X A)
    (budget : Nat) : (budgetedRiskSet problem P resources budget).Nonempty := by
  have hfallback : resources.fallback ∈ feasibleDecisions resources budget := by
    simp [feasibleDecisions, resources.fallback_cost]
  refine ⟨deterministicDecisionRisk problem P resources.fallback, ?_⟩
  exact Finset.mem_image.mpr
    ⟨resources.fallback, hfallback, rfl⟩

/-- Minimum exact decision risk attainable within a natural-number budget. -/
def resourceBayesRisk (problem : DecisionProblem Θ A) (P : FinStoch Θ X)
    (resources : DecisionResourceModel X A) (budget : Nat) : ℚ≥0 :=
  (budgetedRiskSet problem P resources budget).min'
    (budgetedRiskSet_nonempty problem P resources budget)

/-- Resource-bounded Bayes risk is below every feasible rule's risk. -/
theorem resourceBayesRisk_le_decision (problem : DecisionProblem Θ A)
    (P : FinStoch Θ X) (resources : DecisionResourceModel X A)
    {budget : Nat} (decision : X → A)
    (hdecision : resources.cost decision ≤ budget) :
    resourceBayesRisk problem P resources budget ≤
      deterministicDecisionRisk problem P decision := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr
    ⟨decision, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdecision⟩, rfl⟩

/-- Some feasible deterministic rule attains the resource-bounded risk. -/
theorem exists_optimalBudgetedDecision (problem : DecisionProblem Θ A)
    (P : FinStoch Θ X) (resources : DecisionResourceModel X A)
    (budget : Nat) :
    ∃ decision : X → A,
      resources.cost decision ≤ budget ∧
      deterministicDecisionRisk problem P decision =
        resourceBayesRisk problem P resources budget := by
  have hmem := Finset.min'_mem (budgetedRiskSet problem P resources budget)
    (budgetedRiskSet_nonempty problem P resources budget)
  rcases Finset.mem_image.mp hmem with ⟨decision, hdecision, hrisk⟩
  have hcost : resources.cost decision ≤ budget :=
    (Finset.mem_filter.mp hdecision).2
  exact ⟨decision, hcost, hrisk⟩

/-- Increasing the decision budget cannot worsen optimal risk. -/
theorem resourceBayesRisk_antitone (problem : DecisionProblem Θ A)
    (P : FinStoch Θ X) (resources : DecisionResourceModel X A)
    {small large : Nat} (hbudget : small ≤ large) :
    resourceBayesRisk problem P resources large ≤
      resourceBayesRisk problem P resources small := by
  have hsubset :
      budgetedRiskSet problem P resources small ⊆
        budgetedRiskSet problem P resources large := by
    intro risk hrisk
    rcases Finset.mem_image.mp hrisk with ⟨decision, hdecision, rfl⟩
    refine Finset.mem_image.mpr ⟨decision, ?_, rfl⟩
    have hcost : resources.cost decision ≤ small :=
      (Finset.mem_filter.mp hdecision).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hcost.trans hbudget⟩
  unfold resourceBayesRisk
  exact Finset.min'_subset
    (budgetedRiskSet_nonempty problem P resources small) hsubset

/-- A certified reduction of decision-making on `Q` to decision-making on
`P`.  The lifted rule loses no decision quality and costs at most an additive
`overhead`. -/
structure DecisionReduction (problem : DecisionProblem Θ A)
    (P : FinStoch Θ X) (Q : FinStoch Θ Y)
    (sourceResources : DecisionResourceModel X A)
    (targetResources : DecisionResourceModel Y A) (overhead : Nat) where
  /-- Lift a target-observation decision to the source observations. -/
  lift : (Y → A) → (X → A)
  /-- Lifting cannot increase exact expected loss. -/
  risk_le : ∀ decision,
    deterministicDecisionRisk problem P (lift decision) ≤
      deterministicDecisionRisk problem Q decision
  /-- Lifting costs at most the target cost plus the advertised overhead. -/
  cost_le : ∀ decision,
    sourceResources.cost (lift decision) ≤
      targetResources.cost decision + overhead

namespace DecisionReduction

/-- Decision reductions compose and their overheads add. -/
def comp
    {problem : DecisionProblem Θ A}
    {P : FinStoch Θ X} {Q : FinStoch Θ Y} {S : FinStoch Θ Z}
    {resourcesX : DecisionResourceModel X A}
    {resourcesY : DecisionResourceModel Y A}
    {resourcesZ : DecisionResourceModel Z A}
    {firstOverhead secondOverhead : Nat}
    (first : DecisionReduction problem P Q resourcesX resourcesY firstOverhead)
    (second : DecisionReduction problem Q S resourcesY resourcesZ secondOverhead) :
    DecisionReduction problem P S resourcesX resourcesZ
      (firstOverhead + secondOverhead) where
  lift decision := first.lift (second.lift decision)
  risk_le decision := (first.risk_le _).trans (second.risk_le _)
  cost_le decision := by
    calc
      resourcesX.cost (first.lift (second.lift decision)) ≤
          resourcesY.cost (second.lift decision) + firstOverhead :=
        first.cost_le _
      _ ≤ (resourcesZ.cost decision + secondOverhead) + firstOverhead :=
        Nat.add_le_add_right (second.cost_le decision) firstOverhead
      _ = resourcesZ.cost decision + (firstOverhead + secondOverhead) := by
        omega

end DecisionReduction

/-- A decision reduction with overhead `overhead` transports a target budget
`budget` to source budget `budget + overhead`. -/
theorem resourceBayesRisk_le_of_reduction
    {problem : DecisionProblem Θ A}
    {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    {sourceResources : DecisionResourceModel X A}
    {targetResources : DecisionResourceModel Y A}
    {overhead budget : Nat}
    (reduction : DecisionReduction problem P Q sourceResources
      targetResources overhead) :
    resourceBayesRisk problem P sourceResources (budget + overhead) ≤
      resourceBayesRisk problem Q targetResources budget := by
  obtain ⟨decision, hcost, hrisk⟩ :=
    exists_optimalBudgetedDecision problem Q targetResources budget
  calc
    resourceBayesRisk problem P sourceResources (budget + overhead) ≤
        deterministicDecisionRisk problem P (reduction.lift decision) :=
      resourceBayesRisk_le_decision problem P sourceResources _
        ((reduction.cost_le decision).trans
          (Nat.add_le_add_right hcost overhead))
    _ ≤ deterministicDecisionRisk problem Q decision :=
      reduction.risk_le decision
    _ = resourceBayesRisk problem Q targetResources budget := hrisk

/-- A zero-overhead reduction proves that free post-processing cannot create
resource-bounded decision value. -/
theorem resourceBayesRisk_le_of_free_reduction
    {problem : DecisionProblem Θ A}
    {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    {sourceResources : DecisionResourceModel X A}
    {targetResources : DecisionResourceModel Y A}
    {budget : Nat}
    (reduction : DecisionReduction problem P Q sourceResources
      targetResources 0) :
    resourceBayesRisk problem P sourceResources budget ≤
      resourceBayesRisk problem Q targetResources budget := by
  simpa using
    (resourceBayesRisk_le_of_reduction (budget := budget) reduction)

/-- Deterministic post-processing followed by a deterministic decision is the
same composite decision rule. -/
theorem deterministicDecisionRisk_precomp
    (problem : DecisionProblem Θ A) (P : FinStoch Θ X)
    (garbling : X → Y) (decision : Y → A) :
    deterministicDecisionRisk problem P (fun x ↦ decision (garbling x)) =
      deterministicDecisionRisk problem
        (FinStoch.comp P (FinStoch.dirac garbling)) decision := by
  unfold deterministicDecisionRisk
  rw [FinStoch.dirac_comp]
  exact randomizedDecisionRisk_comp problem P
    (FinStoch.dirac garbling) (FinStoch.dirac decision)

/-- Build a resource-aware decision reduction from a deterministic garbling
and an explicit cost-composition bound. -/
def ofDeterministicGarbling
    {problem : DecisionProblem Θ A}
    {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    {sourceResources : DecisionResourceModel X A}
    {targetResources : DecisionResourceModel Y A}
    {overhead : Nat}
    (garbling : X → Y)
    (hQ : FinStoch.comp P (FinStoch.dirac garbling) = Q)
    (hcost : ∀ decision : Y → A,
      sourceResources.cost (fun x ↦ decision (garbling x)) ≤
        targetResources.cost decision + overhead) :
    DecisionReduction problem P Q sourceResources targetResources overhead where
  lift decision x := decision (garbling x)
  risk_le decision := by
    rw [deterministicDecisionRisk_precomp, hQ]
  cost_le := hcost

end Ript.Models.Decision.ResourceBounded
