import Mathlib.Tactic.Linarith
import Ript.ForMathlib.RationalConvexHull
import Ript.Models.Decision.GarblingPolytope

/-!
# Rational separation data for finite garbling polytopes

The exact garbling simplex has rational vertices.  This module constructs the
dual certificate: a signed rational linear score that places a target
experiment strictly below every deterministic post-processing of a source.

Signed scores are not yet decision losses, because losses must be
nonnegative.  On a nonempty hidden-state carrier we shift every hidden-state
row by a rational constant, use the uniform exact prior, and obtain a genuine
finite decision problem.  Row normalization makes the shifts cancel from all
strict comparisons.
-/

set_option autoImplicit false

namespace Ript.Models.Decision.RationalSeparation

open scoped BigOperators

open Ript.Models.Decision.Blackwell
open Ript.Models.Decision.FiniteRisk
open Ript.Models.Decision.GarblingPolytope
open Ript.Models.Decision.Separation
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic
open Ript.ForMathlib.RationalConvexHull

universe u

variable {Θ X Y Z : Object.{u}}

/-- Finite coordinate space for the entries of an experiment with hidden
state object `Θ` and observation object `Y`. -/
abbrev ExperimentCoordinate (Θ Y : Object.{u}) : Type u :=
  Θ.carrier × Y.carrier

/-- Exact rational coordinate vector of a finite stochastic experiment. -/
def channelVector (experiment : FinStoch Θ Y) :
    ExperimentCoordinate Θ Y → ℚ :=
  fun coordinate => experiment.prob coordinate.1 coordinate.2

/-- Channel coordinates determine a finite stochastic experiment. -/
theorem channelVector_injective :
    Function.Injective (channelVector : FinStoch Θ Y → ExperimentCoordinate Θ Y → ℚ) := by
  intro first second hequal
  apply FinStoch.ext
  intro θ y
  have hcoordinate := congrFun hequal (θ, y)
  change (first.prob θ y : ℚ) = (second.prob θ y : ℚ) at hcoordinate
  exact_mod_cast hcoordinate

/-- Blackwell dominance is exactly rational convex-hull membership of the
target channel vector in the deterministic post-processing vertices. -/
theorem channelVector_mem_convexHull_iff
    (P : FinStoch Θ X) (Q : FinStoch Θ Y) :
    channelVector Q ∈ convexHull ℚ
      (Set.range fun decision : X.carrier → Y.carrier =>
        channelVector (deterministicPostprocessing P decision)) ↔
      BlackwellDominates P Q := by
  classical
  constructor
  · intro hmem
    obtain ⟨weight, hweightNonnegative, hweightSum, hweightLinear⟩ :=
      (mem_convexHull_range_iff_exists_weights
        (fun decision : X.carrier → Y.carrier =>
          channelVector (deterministicPostprocessing P decision))
        (channelVector Q)).mp hmem
    let nonnegativeWeight : (X.carrier → Y.carrier) → ℚ≥0 :=
      fun decision => ⟨weight decision, hweightNonnegative decision⟩
    have hnonnegativeWeightSum :
        ∑ decision, nonnegativeWeight decision = 1 := by
      apply NNRat.coe_injective
      rw [NNRat.cast_sum]
      exact hweightSum
    let weights : FinDist (deterministicGarblingObject X Y) :=
      { prob := nonnegativeWeight
        normalized := hnonnegativeWeightSum }
    refine ⟨mixedGarbling weights, ?_⟩
    apply FinStoch.ext
    intro θ y
    change (FinStoch.comp P (mixedGarbling weights)).prob θ y = Q.prob θ y
    rw [comp_mixedGarbling_apply]
    apply NNRat.coe_injective
    rw [NNRat.cast_sum]
    push_cast
    have hcoordinate := congrFun hweightLinear (θ, y)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      channelVector] at hcoordinate
    change (∑ decision, weight decision *
      ((deterministicPostprocessing P decision).prob θ y : ℚ)) =
        (Q.prob θ y : ℚ)
    exact hcoordinate
  · intro hdominates
    obtain ⟨weights, hweights⟩ :=
      (deterministicMixtureDominates_iff P Q).mpr hdominates
    apply (mem_convexHull_range_iff_exists_weights
      (fun decision : X.carrier → Y.carrier =>
        channelVector (deterministicPostprocessing P decision))
      (channelVector Q)).mpr
    refine ⟨fun decision => (weights.prob decision : ℚ), ?_, ?_, ?_⟩
    · intro decision
      exact_mod_cast (weights.prob decision).property
    · change (∑ decision, (weights.prob decision : ℚ)) = 1
      rw [← NNRat.cast_sum, weights.normalized]
      simp
    · ext coordinate
      rcases coordinate with ⟨θ, y⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        channelVector]
      have hcoordinate := congrArg
        (fun experiment => (experiment.prob θ y : ℚ)) hweights
      rw [comp_mixedGarbling_apply, NNRat.cast_sum] at hcoordinate
      push_cast at hcoordinate
      exact hcoordinate

/-- Evaluation of a signed rational matrix score on a finite experiment. -/
def channelScore (score : Θ.carrier → Y.carrier → ℚ)
    (experiment : FinStoch Θ Y) : ℚ :=
  ∑ θ, ∑ y, score θ y * (experiment.prob θ y : ℚ)

/-- The same signed score evaluated after a concrete deterministic decision
rule, without first materializing its Dirac channel. -/
def decisionScore (score : Θ.carrier → Y.carrier → ℚ)
    (experiment : FinStoch Θ X) (decision : X.carrier → Y.carrier) : ℚ :=
  ∑ θ, ∑ x, (experiment.prob θ x : ℚ) * score θ (decision x)

/-- Flattened channel-vector scoring agrees with the matrix-shaped channel
score. -/
theorem rationalDot_channelVector
    (coefficient : ExperimentCoordinate Θ Y → ℚ)
    (experiment : FinStoch Θ Y) :
    rationalDot coefficient (channelVector experiment) =
      channelScore (fun θ y => coefficient (θ, y)) experiment := by
  rw [rationalDot, channelScore, Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro θ
  apply Fintype.sum_congr
  intro y
  simp only [channelVector]
  ring

/-- The identity decision rule evaluates the same score as the experiment
channel itself. -/
theorem decisionScore_id_eq_channelScore
    (score : Θ.carrier → Y.carrier → ℚ)
    (experiment : FinStoch Θ Y) :
    decisionScore score experiment id = channelScore score experiment := by
  unfold decisionScore channelScore
  apply Fintype.sum_congr
  intro θ
  apply Fintype.sum_congr
  intro y
  dsimp only [id_eq]
  ring

/-- Scoring a deterministic post-processing as a channel agrees with the
direct decision-rule formula. -/
theorem channelScore_deterministicPostprocessing
    (score : Θ.carrier → Y.carrier → ℚ) (experiment : FinStoch Θ X)
    (decision : X.carrier → Y.carrier) :
    channelScore score (deterministicPostprocessing experiment decision) =
      decisionScore score experiment decision := by
  unfold channelScore decisionScore deterministicPostprocessing
  apply Fintype.sum_congr
  intro θ
  calc
    (∑ y, score θ y *
      (↑(∑ x, experiment.prob θ x *
        (if decision x = y then 1 else 0)) : ℚ)) =
        ∑ y, ∑ x, score θ y *
          ((experiment.prob θ x : ℚ) *
            (if decision x = y then 1 else 0)) := by
      apply Fintype.sum_congr
      intro y
      rw [NNRat.cast_sum, Finset.mul_sum]
      apply Fintype.sum_congr
      intro x
      norm_cast
    _ = ∑ x, ∑ y, score θ y *
          ((experiment.prob θ x : ℚ) *
            (if decision x = y then 1 else 0)) := Finset.sum_comm
    _ = ∑ x, (experiment.prob θ x : ℚ) *
          score θ (decision x) := by
      apply Fintype.sum_congr
      intro x
      calc
        (∑ y, score θ y *
          ((experiment.prob θ x : ℚ) *
            (if decision x = y then 1 else 0))) =
            ∑ y, if decision x = y then
              (experiment.prob θ x : ℚ) * score θ y else 0 := by
          apply Fintype.sum_congr
          intro y
          by_cases h : decision x = y
          · simp [h]
            ring
          · simp [h]
        _ = (experiment.prob θ x : ℚ) * score θ (decision x) := by
          simp

/-- A signed rational hyperplane that strictly separates `Q` from every
deterministic post-processing vertex generated by `P`. -/
structure RationalGarblingSeparator
    (P : FinStoch Θ X) (Q : FinStoch Θ Y) where
  /-- Rational coefficient attached to every hidden-state/output pair. -/
  score : Θ.carrier → Y.carrier → ℚ
  /-- The target lies strictly below every deterministic garbling vertex. -/
  separates : ∀ decision : X.carrier → Y.carrier,
    decisionScore score Q id < decisionScore score P decision

/-- Exact uniform prior on an arbitrary nonempty executable finite carrier. -/
def uniformPrior (Θ : Object.{u}) [Nonempty Θ.carrier] : FinDist Θ where
  prob _ := (Fintype.card Θ : ℚ≥0)⁻¹
  normalized := by
    change (∑ _ : Θ, (Fintype.card Θ : ℚ≥0)⁻¹) = 1
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

/-- Per-hidden-state offset large enough to make every signed score
coefficient nonnegative. -/
def scoreOffset (score : Θ.carrier → Y.carrier → ℚ) (θ : Θ.carrier) : ℚ :=
  ∑ y, |score θ y|

/-- Every signed coefficient plus its row offset is nonnegative. -/
theorem score_add_offset_nonneg (score : Θ.carrier → Y.carrier → ℚ)
    (θ : Θ.carrier) (y : Y.carrier) :
    0 ≤ score θ y + scoreOffset score θ := by
  have habs_le : |score θ y| ≤ scoreOffset score θ := by
    exact Finset.single_le_sum (fun y' _ ↦ abs_nonneg (score θ y'))
      (Finset.mem_univ y)
  linarith [neg_le_abs (score θ y)]

/-- Nonnegative-rational loss obtained by shifting a signed separator within
each hidden-state row. -/
def shiftedLoss (score : Θ.carrier → Y.carrier → ℚ)
    (θ : Θ.carrier) (y : Y.carrier) : ℚ≥0 :=
  ⟨score θ y + scoreOffset score θ,
    score_add_offset_nonneg score θ y⟩

/-- Decision problem induced by a signed rational separator.  The explicit
default action keeps the construction computational; existence of such an
action will later be extracted from a target experiment. -/
def separatorDecisionProblem [Nonempty Θ.carrier]
    (score : Θ.carrier → Y.carrier → ℚ)
    (defaultAction : Y.carrier) : DecisionProblem Θ Y where
  prior := uniformPrior Θ
  loss := shiftedLoss score
  defaultAction := defaultAction

/-- Exact expected-loss formula for a shifted separator under the uniform
prior.  The added row offsets contribute the same constant for every
experiment and deterministic decision. -/
theorem separatorDecisionRisk_eq [Nonempty Θ.carrier]
    (score : Θ.carrier → Y.carrier → ℚ)
    (defaultAction : Y.carrier) (experiment : FinStoch Θ X)
    (decision : X.carrier → Y.carrier) :
    (deterministicDecisionRisk
      (separatorDecisionProblem score defaultAction) experiment decision : ℚ) =
      (Fintype.card Θ : ℚ)⁻¹ *
        (decisionScore score experiment decision +
          ∑ θ, scoreOffset score θ) := by
  rw [deterministicDecisionRisk_eq_sum_actionRisk, NNRat.cast_sum]
  simp only [actionRiskMass, separatorDecisionProblem, uniformPrior,
    shiftedLoss, NNRat.cast_sum]
  calc
    (∑ x, ∑ θ,
      (Fintype.card Θ : ℚ)⁻¹ * (experiment.prob θ x : ℚ) *
        (score θ (decision x) + scoreOffset score θ)) =
        (Fintype.card Θ : ℚ)⁻¹ *
          ∑ x, ∑ θ, (experiment.prob θ x : ℚ) *
            (score θ (decision x) + scoreOffset score θ) := by
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro x
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro θ
      ring
    _ = (Fintype.card Θ : ℚ)⁻¹ *
        ∑ θ, ∑ x, (experiment.prob θ x : ℚ) *
          (score θ (decision x) + scoreOffset score θ) := by
      rw [Finset.sum_comm]
    _ = (Fintype.card Θ : ℚ)⁻¹ *
        (decisionScore score experiment decision +
          ∑ θ, scoreOffset score θ) := by
      congr 1
      unfold decisionScore
      rw [← Finset.sum_add_distrib]
      apply Fintype.sum_congr
      intro θ
      calc
        (∑ x, (experiment.prob θ x : ℚ) *
          (score θ (decision x) + scoreOffset score θ)) =
            ∑ x, ((experiment.prob θ x : ℚ) *
              score θ (decision x) +
              (experiment.prob θ x : ℚ) * scoreOffset score θ) := by
          apply Fintype.sum_congr
          intro x
          ring
        _ = (∑ x, (experiment.prob θ x : ℚ) *
              score θ (decision x)) +
            ∑ x, (experiment.prob θ x : ℚ) *
              scoreOffset score θ := Finset.sum_add_distrib
        _ = (∑ x, (experiment.prob θ x : ℚ) *
              score θ (decision x)) + scoreOffset score θ := by
          congr 1
          calc
            (∑ x, (experiment.prob θ x : ℚ) * scoreOffset score θ) =
                (∑ x, (experiment.prob θ x : ℚ)) *
                  scoreOffset score θ := by rw [Finset.sum_mul]
            _ = scoreOffset score θ := by
              rw [← NNRat.cast_sum, experiment.normalized]
              simp

/-- Compare two exact nonnegative risks through a shared positive affine
rescaling of signed rational scores. -/
private theorem nnrat_lt_of_scaled_score_lt
    {risk₁ risk₂ : ℚ≥0} {scale score₁ score₂ offset : ℚ}
    (hscale : 0 < scale)
    (hrisk₁ : (risk₁ : ℚ) = scale * (score₁ + offset))
    (hrisk₂ : (risk₂ : ℚ) = scale * (score₂ + offset))
    (hscore : score₁ < score₂) : risk₁ < risk₂ := by
  apply NNRat.coe_lt_coe.mp
  rw [hrisk₁, hrisk₂]
  exact mul_lt_mul_of_pos_left
    (by simpa [add_comm] using add_lt_add_right hscore offset) hscale

/-- A nonempty hidden-state carrier and a normalized target experiment force
the target observation carrier to be nonempty. -/
theorem target_nonempty [Nonempty Θ.carrier] (Q : FinStoch Θ Y) :
    Nonempty Y.carrier := by
  classical
  let θ : Θ.carrier := Classical.choice inferInstance
  exact (channelToKleisli Q θ).carrier_nonempty

/-- Every signed rational separator yields a concrete finite decision
separation certificate.  The only classical choice selects default elements
needed by the proposition-level certificate; all probabilities and losses
remain exact rational data. -/
theorem RationalGarblingSeparator.toDecisionSeparationCertificate
    [Nonempty Θ.carrier] {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    (separator : RationalGarblingSeparator P Q) :
    Nonempty (DecisionSeparationCertificate P Q) := by
  classical
  let defaultAction : Y.carrier := Classical.choice (target_nonempty Q)
  let problem : DecisionProblem Θ Y :=
    separatorDecisionProblem separator.score defaultAction
  obtain ⟨bestDecision, hbestDecision⟩ :=
    exists_optimalDecision problem P
  refine ⟨
    { action := Y
      problem := problem
      decision := id
      separates := ?_ }⟩
  rw [← hbestDecision]
  have hcard : (0 : ℚ) < Fintype.card Θ.carrier := by
    exact_mod_cast Fintype.card_pos
  change
    deterministicDecisionRisk
        (separatorDecisionProblem separator.score defaultAction) Q id <
      deterministicDecisionRisk
        (separatorDecisionProblem separator.score defaultAction)
        P bestDecision
  exact nnrat_lt_of_scaled_score_lt
    (inv_pos.mpr hcard)
    (separatorDecisionRisk_eq separator.score defaultAction Q id)
    (separatorDecisionRisk_eq separator.score defaultAction P bestDecision)
    (separator.separates bestDecision)

/-- Completeness of rational hyperplane separation for a fixed experiment
pair. -/
def RationalSeparationComplete
    (P : FinStoch Θ X) (Q : FinStoch Θ Y) : Prop :=
  ¬BlackwellDominates P Q → Nonempty (RationalGarblingSeparator P Q)

/-- **Rational separation completeness for finite garbling polytopes.** Every
target outside the garbling polytope has an exact signed rational separator.
-/
theorem rationalSeparationComplete
    (P : FinStoch Θ X) (Q : FinStoch Θ Y) :
    RationalSeparationComplete P Q := by
  intro hnotDominates
  have hnotHull : channelVector Q ∉ convexHull ℚ
      (Set.range fun decision : X.carrier → Y.carrier =>
        channelVector (deterministicPostprocessing P decision)) := by
    intro hmem
    exact hnotDominates ((channelVector_mem_convexHull_iff P Q).mp hmem)
  obtain ⟨coefficient, hcoefficient⟩ :=
    exists_rational_strictSeparator_of_not_mem_convexHull
      (fun decision : X.carrier → Y.carrier =>
        channelVector (deterministicPostprocessing P decision))
      (channelVector Q) hnotHull
  let score : Θ.carrier → Y.carrier → ℚ :=
    fun θ y => coefficient (θ, y)
  refine ⟨
    { score := score
      separates := ?_ }⟩
  intro decision
  have hstrict := hcoefficient decision
  rw [rationalDot_channelVector, rationalDot_channelVector] at hstrict
  change decisionScore score Q id < decisionScore score P decision
  rw [decisionScore_id_eq_channelScore,
    ← channelScore_deterministicPostprocessing score P decision]
  exact hstrict

/-- Rational hyperplane completeness implies concrete decision-certificate
completeness. -/
theorem decisionSeparationComplete_of_rationalSeparationComplete
    [Nonempty Θ.carrier] {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    (hcomplete : RationalSeparationComplete P Q) :
    DecisionSeparationComplete P Q := by
  intro hnotDominates
  obtain ⟨separator⟩ := hcomplete hnotDominates
  exact separator.toDecisionSeparationCertificate

/-- Signed rational score read directly from an existing decision certificate:
prior mass times the loss of the certificate's chosen target action. -/
def DecisionSeparationCertificate.rationalScore
    {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    (certificate : DecisionSeparationCertificate P Q) :
    Θ.carrier → Y.carrier → ℚ :=
  fun θ y ↦
    (certificate.problem.prior.prob θ : ℚ) *
      (certificate.problem.loss θ (certificate.decision y) : ℚ)

/-- Direct evaluation of a certificate-derived score is exactly the expected
loss of composing a routing rule with the certificate's target decision. -/
theorem DecisionSeparationCertificate.decisionScore_rationalScore
    {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    (certificate : DecisionSeparationCertificate P Q)
    (experiment : FinStoch Θ Z) (routing : Z.carrier → Y.carrier) :
    decisionScore (rationalScore certificate) experiment routing =
      (deterministicDecisionRisk certificate.problem experiment
        (certificate.decision ∘ routing) : ℚ) := by
  rw [deterministicDecisionRisk_eq_sum_actionRisk, NNRat.cast_sum]
  simp only [actionRiskMass, NNRat.cast_sum]
  unfold decisionScore DecisionSeparationCertificate.rationalScore
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro z
  apply Fintype.sum_congr
  intro θ
  dsimp only [Function.comp_apply]
  push_cast
  ring

/-- Every concrete decision certificate determines a signed rational
hyperplane separating the target from all deterministic garbling vertices. -/
def DecisionSeparationCertificate.toRationalGarblingSeparator
    {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    (certificate : DecisionSeparationCertificate P Q) :
    RationalGarblingSeparator P Q where
  score := rationalScore certificate
  separates := by
    intro decision
    rw [decisionScore_rationalScore certificate Q id,
      decisionScore_rationalScore certificate P decision]
    have hrisk :
        deterministicDecisionRisk certificate.problem Q
            certificate.decision <
          deterministicDecisionRisk certificate.problem P
            (certificate.decision ∘ decision) :=
      certificate.separates.trans_le
        (finiteBayesRisk_le_deterministicDecisionRisk
          certificate.problem P (certificate.decision ∘ decision))
    simpa [Function.comp_def] using NNRat.coe_lt_coe.mpr hrisk

/-- On nonempty hidden-state carriers, rational hyperplane separators and
finite decision-separation certificates exist for exactly the same pairs. -/
theorem rationalGarblingSeparator_nonempty_iff_certificate
    [Nonempty Θ.carrier] (P : FinStoch Θ X) (Q : FinStoch Θ Y) :
    Nonempty (RationalGarblingSeparator P Q) ↔
      Nonempty (DecisionSeparationCertificate P Q) := by
  constructor
  · rintro ⟨separator⟩
    exact separator.toDecisionSeparationCertificate
  · rintro ⟨certificate⟩
    exact ⟨DecisionSeparationCertificate.toRationalGarblingSeparator certificate⟩

/-- Rational hyperplane completeness is exactly the previously isolated
decision-certificate completeness condition. -/
theorem rationalSeparationComplete_iff_decisionSeparationComplete
    [Nonempty Θ.carrier] (P : FinStoch Θ X) (Q : FinStoch Θ Y) :
    RationalSeparationComplete P Q ↔ DecisionSeparationComplete P Q := by
  unfold RationalSeparationComplete DecisionSeparationComplete
  constructor
  · intro hcomplete hnotDominates
    exact (rationalGarblingSeparator_nonempty_iff_certificate P Q).mp
      (hcomplete hnotDominates)
  · intro hcomplete hnotDominates
    exact (rationalGarblingSeparator_nonempty_iff_certificate P Q).mpr
      (hcomplete hnotDominates)

/-- The pairwise stochastic Blackwell converse is equivalent to rational
strict separation of the target from the finite deterministic garbling
simplex. -/
theorem blackwellShermanSteinConverse_iff_rationalSeparationComplete
    [Nonempty Θ.carrier] (P : FinStoch Θ X) (Q : FinStoch Θ Y) :
    BlackwellShermanSteinConverse P Q ↔ RationalSeparationComplete P Q :=
  (blackwellShermanSteinConverse_iff_separationComplete P Q).trans
    (rationalSeparationComplete_iff_decisionSeparationComplete P Q).symm

/-- **Finite Blackwell--Sherman--Stein converse for a fixed experiment
pair.** On a nonempty hidden-state carrier, universal finite decision order
forces exact stochastic garbling. -/
theorem blackwellShermanSteinConverse [Nonempty Θ.carrier]
    (P : FinStoch Θ X) (Q : FinStoch Θ Y) :
    BlackwellShermanSteinConverse P Q :=
  (blackwellShermanSteinConverse_iff_rationalSeparationComplete P Q).mpr
    (rationalSeparationComplete P Q)

/-- The corrected full finite stochastic converse is equivalent to uniform
completeness of signed rational separation for every nonempty hidden-state
carrier. -/
theorem finiteBlackwellShermanStein_iff_rationalSeparationComplete :
    FiniteBlackwellShermanStein.{u} ↔
      ∀ (Θ X Y : Object.{u}) (_ : Nonempty Θ.carrier)
        (P : FinStoch Θ X) (Q : FinStoch Θ Y),
        RationalSeparationComplete P Q := by
  constructor
  · intro hconverse Θ X Y hΘ P Q
    exact
      (blackwellShermanSteinConverse_iff_rationalSeparationComplete P Q).mp
        (hconverse Θ X Y hΘ P Q)
  · intro hcomplete Θ X Y hΘ P Q
    exact
      (blackwellShermanSteinConverse_iff_rationalSeparationComplete P Q).mpr
        (hcomplete Θ X Y hΘ P Q)

/-- **Finite Blackwell--Sherman--Stein theorem.** For every nonempty finite
hidden-state carrier, exact Blackwell dominance is characterized by
performance in all exact finite decision problems. -/
theorem finiteBlackwellShermanStein :
    FiniteBlackwellShermanStein.{u} := by
  intro Θ X Y hΘ P Q
  let _ : Nonempty Θ.carrier := hΘ
  exact blackwellShermanSteinConverse P Q

end Ript.Models.Decision.RationalSeparation
