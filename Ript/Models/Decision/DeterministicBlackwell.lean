import Ript.Models.Decision.FiniteRisk

/-!
# Deterministic finite Blackwell representation

The general finite Blackwell--Sherman--Stein converse is a convex-separation
theorem for stochastic matrices.  This module proves a complete, nontrivial
special case for deterministic finite experiments.

Given deterministic observations `source : Θ → X` and
`target : Θ → Y`, fix any exact full-support prior and the zero-one task of
reconstructing `target θ`.  The source experiment has no larger optimal risk
than direct observation of the target exactly when the target is an exact
stochastic post-processing of the source.  Equivalently, its value is the same
on every fiber of the source.

Thus decision-risk comparison recovers the Blackwell witness in this finite
deterministic fragment.  No finite-dimensional separation theorem, linear
programming oracle, or unproved converse for arbitrary stochastic experiments
is assumed.
-/

set_option autoImplicit false

namespace Ript.Models.Decision.DeterministicBlackwell

open scoped BigOperators
open Ript.Models.Decision.Blackwell
open Ript.Models.Decision.FiniteRisk
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic
open Ript.Models.FiniteStochastic.FinStoch

universe u

variable {Θ X Y : Object.{u}}

/-- The exact zero-one task of reconstructing a deterministic target
observation.  A reference hidden state supplies the required default action;
it has no mathematical effect on the optimum. -/
def reconstructionProblem (prior : FinDist Θ) (target : Θ → Y)
    (reference : Θ) : DecisionProblem Θ Y where
  prior := prior
  loss θ action := if target θ = action then 0 else 1
  defaultAction := target reference

/-- For deterministic observation and decision maps, reconstruction risk is
the prior-weighted zero-one error on hidden states. -/
theorem reconstruction_deterministicDecisionRisk
    (prior : FinDist Θ) (source : Θ → X) (target : Θ → Y)
    (reference : Θ) (decision : X → Y) :
    deterministicDecisionRisk (reconstructionProblem prior target reference)
        (FinStoch.dirac source) decision =
      ∑ θ, prior.prob θ *
        if target θ = decision (source θ) then 0 else 1 := by
  unfold deterministicDecisionRisk randomizedDecisionRisk reconstructionProblem
  rw [← FinStoch.dirac_comp]
  apply Fintype.sum_congr
  intro θ
  rw [Finset.sum_eq_single (decision (source θ))]
  · by_cases hcorrect : target θ = decision (source θ) <;>
      simp [FinStoch.dirac, hcorrect]
  · intro action _ hne
    by_cases htarget : target θ = action <;>
      simp [FinStoch.dirac, htarget, Ne.symm hne]
  · simp

/-- Direct deterministic observation of the reconstruction target has zero
exact finite Bayes risk. -/
theorem target_reconstructionRisk_zero
    (prior : FinDist Θ) (target : Θ → Y) (reference : Θ) :
    finiteBayesRisk (reconstructionProblem prior target reference)
        (FinStoch.dirac target) = 0 := by
  apply le_antisymm
  · calc
      finiteBayesRisk (reconstructionProblem prior target reference)
          (FinStoch.dirac target) ≤
          deterministicDecisionRisk
            (reconstructionProblem prior target reference)
            (FinStoch.dirac target) id :=
        finiteBayesRisk_le_deterministicDecisionRisk _ _ _
      _ = 0 := by
        rw [reconstruction_deterministicDecisionRisk]
        simp
  · exact zero_le

/-- Zero reconstruction risk under a full-support prior extracts a
deterministic post-processing witness, hence exact Blackwell dominance. -/
theorem dominates_of_reconstructionRisk_eq_zero
    (prior : FinDist Θ) (fullSupport : ∀ θ, 0 < prior.prob θ)
    (source : Θ → X) (target : Θ → Y) (reference : Θ)
    (hrisk : finiteBayesRisk (reconstructionProblem prior target reference)
      (FinStoch.dirac source) = 0) :
    BlackwellDominates (FinStoch.dirac source) (FinStoch.dirac target) := by
  obtain ⟨decision, hdecision⟩ :=
    exists_optimalDecision (reconstructionProblem prior target reference)
      (FinStoch.dirac source)
  have hdecisionRisk :
      deterministicDecisionRisk
          (reconstructionProblem prior target reference)
          (FinStoch.dirac source) decision = 0 :=
    hdecision.trans hrisk
  have hsum :
      (∑ θ, prior.prob θ *
        if target θ = decision (source θ) then 0 else 1) = 0 := by
    rw [← reconstruction_deterministicDecisionRisk]
    exact hdecisionRisk
  have hcorrect (θ : Θ) : target θ = decision (source θ) := by
    have hterm :
        prior.prob θ *
          (if target θ = decision (source θ) then 0 else 1) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ zero_le)).mp hsum θ
        (Finset.mem_univ θ)
    by_contra hne
    have hprior_zero : prior.prob θ = 0 := by
      simpa [hne] using hterm
    exact (ne_of_gt (fullSupport θ)) hprior_zero
  refine ⟨FinStoch.dirac decision, ?_⟩
  calc
    FinStoch.comp (FinStoch.dirac source) (FinStoch.dirac decision) =
        FinStoch.dirac (fun θ ↦ decision (source θ)) :=
      (FinStoch.dirac_comp source decision).symm
    _ = FinStoch.dirac target := by
      apply FinStoch.ext
      intro θ action
      simp [hcorrect θ]

/-- **Deterministic finite Blackwell converse.** Under any exact full-support
prior, the source has no larger risk in the target-reconstruction task than
direct target observation iff the target experiment is an exact Blackwell
garbling of the source. -/
theorem deterministic_dominates_iff_reconstructionRisk_le
    (prior : FinDist Θ) (fullSupport : ∀ θ, 0 < prior.prob θ)
    (source : Θ → X) (target : Θ → Y) (reference : Θ) :
    BlackwellDominates (FinStoch.dirac source) (FinStoch.dirac target) ↔
      finiteBayesRisk (reconstructionProblem prior target reference)
          (FinStoch.dirac source) ≤
        finiteBayesRisk (reconstructionProblem prior target reference)
          (FinStoch.dirac target) := by
  constructor
  · intro hdominates
    exact finiteBayesRisk_mono hdominates
      (reconstructionProblem prior target reference)
  · intro hrisk
    apply dominates_of_reconstructionRisk_eq_zero prior fullSupport source
      target reference
    apply le_antisymm
    · calc
        finiteBayesRisk (reconstructionProblem prior target reference)
            (FinStoch.dirac source) ≤
            finiteBayesRisk (reconstructionProblem prior target reference)
              (FinStoch.dirac target) := hrisk
        _ = 0 := target_reconstructionRisk_zero prior target reference
    · exact zero_le

/-- Two deterministic experiments are Blackwell ordered exactly when the
target observation is constant on every fiber of the source observation. -/
theorem deterministic_dominates_iff_fiber_refines
    (source : Θ → X) (target : Θ → Y) (reference : Θ) :
    BlackwellDominates (FinStoch.dirac source) (FinStoch.dirac target) ↔
      ∀ θ θ', source θ = source θ' → target θ = target θ' := by
  constructor
  · rintro ⟨garbling, hgarbling⟩ θ θ' hsource
    have hrow (action : Y) :
        (FinStoch.dirac target).prob θ action =
          (FinStoch.dirac target).prob θ' action := by
      rw [← hgarbling]
      change (∑ observation,
          (FinStoch.dirac source).prob θ observation *
            garbling.prob observation action) =
        ∑ observation,
          (FinStoch.dirac source).prob θ' observation *
            garbling.prob observation action
      apply Fintype.sum_congr
      intro observation
      simp [hsource]
    have htarget := hrow (target θ)
    have : target θ' = target θ := by simpa using htarget
    exact this.symm
  · intro hfiber
    classical
    let decision : X → Y := fun observation ↦
      if h : ∃ θ, source θ = observation then
        target (Classical.choose h)
      else target reference
    have hdecision (θ : Θ) : decision (source θ) = target θ := by
      have hexists : ∃ θ', source θ' = source θ := ⟨θ, rfl⟩
      simp only [decision, dif_pos hexists]
      exact hfiber _ _ (Classical.choose_spec hexists)
    refine ⟨FinStoch.dirac decision, ?_⟩
    calc
      FinStoch.comp (FinStoch.dirac source) (FinStoch.dirac decision) =
          FinStoch.dirac (fun θ ↦ decision (source θ)) :=
        (FinStoch.dirac_comp source decision).symm
      _ = FinStoch.dirac target := by
        apply FinStoch.ext
        intro θ action
        simp [hdecision θ]

end Ript.Models.Decision.DeterministicBlackwell
