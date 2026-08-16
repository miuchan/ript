import Mathlib.Probability.Decision.Risk.Basic
import Ript.Core.Simulation
import Ript.Models.FiniteStochastic.Kleisli
import Ript.Models.Probability.StochFunctor

/-!
# Blackwell simulation for exact finite experiments

An experiment is an exact finite stochastic channel from a hidden parameter
space to an observation space.  `BlackwellDominates P Q` means that `Q` is a
garbling of `P`: some stochastic post-processing of the observations of `P`
produces `Q` exactly.

The executable order lives entirely in `FinStoch`.  The final section reuses
Mathlib's measure-theoretic Bayes-risk data-processing theorem through the
faithful finite-to-`Stoch` bridge; no measure theory is reimplemented here.
-/

set_option autoImplicit false

namespace Ript.Models.Decision.Blackwell

open CategoryTheory MeasureTheory ProbabilityTheory
open scoped ENNReal
open Ript.Core
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic
open Ript.Models.FiniteStochastic.FinStoch
open Ript.Models.Probability.StochFunctor

universe u w

variable {Θ W X Y Z : Object.{u}}

/-- Blackwell's information order on finite experiments: `P` dominates `Q`
when `Q` is obtained from `P` by an exact finite stochastic garbling. -/
abbrev BlackwellDominates (P : FinStoch Θ X) (Q : FinStoch Θ Y) : Prop :=
  @Simulates Object _ Θ X Y P Q

/-- Mutual Blackwell dominance, allowing different observation carriers. -/
abbrev BlackwellEquivalent (P : FinStoch Θ X) (Q : FinStoch Θ Y) : Prop :=
  @InformationEquivalent Object _ Θ X Y P Q

/-- Every finite experiment Blackwell-dominates itself. -/
theorem dominates_refl (P : FinStoch Θ X) : BlackwellDominates P P :=
  @Simulates.refl Object _ Θ X P

/-- Blackwell dominance is transitive. -/
theorem dominates_trans {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    {S : FinStoch Θ Z} (hPQ : BlackwellDominates P Q)
    (hQS : BlackwellDominates Q S) : BlackwellDominates P S :=
  hPQ.trans hQS

/-- Every explicit stochastic post-processing is a Blackwell garbling. -/
theorem dominates_postprocess (P : FinStoch Θ X) (κ : FinStoch X Y) :
    BlackwellDominates P (FinStoch.comp P κ) :=
  ⟨κ, rfl⟩

/-- Applying the same preprocessing to the hidden parameter preserves
Blackwell dominance. -/
theorem dominates_precomp {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    (hPQ : BlackwellDominates P Q) (E : FinStoch W Θ) :
    BlackwellDominates (FinStoch.comp E P) (FinStoch.comp E Q) := by
  rcases hPQ with ⟨κ, hκ⟩
  refine ⟨κ, ?_⟩
  calc
    FinStoch.comp (FinStoch.comp E P) κ =
        FinStoch.comp E (FinStoch.comp P κ) := by
      apply FinStoch.ext
      intro w y
      simp only [FinStoch.comp]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp [mul_assoc]
    _ = FinStoch.comp E Q := congrArg (FinStoch.comp E) hκ

/-- Independent products preserve Blackwell dominance componentwise. -/
theorem dominates_tensor
    {Θ₁ X₁ Y₁ Θ₂ X₂ Y₂ : Object.{u}}
    {P₁ : FinStoch Θ₁ X₁} {Q₁ : FinStoch Θ₁ Y₁}
    {P₂ : FinStoch Θ₂ X₂} {Q₂ : FinStoch Θ₂ Y₂}
    (h₁ : BlackwellDominates P₁ Q₁)
    (h₂ : BlackwellDominates P₂ Q₂) :
    BlackwellDominates (tensor P₁ P₂) (tensor Q₁ Q₂) := by
  rcases h₁ with ⟨κ₁, hκ₁⟩
  rcases h₂ with ⟨κ₂, hκ₂⟩
  refine ⟨tensor κ₁ κ₂, ?_⟩
  calc
    FinStoch.comp (tensor P₁ P₂) (tensor κ₁ κ₂) =
        tensor (FinStoch.comp P₁ κ₁) (FinStoch.comp P₂ κ₂) :=
      (tensor_comp P₁ κ₁ P₂ κ₂).symm
    _ = tensor Q₁ Q₂ := congrArg₂ tensor hκ₁ hκ₂

/-- Blackwell equivalence is reflexive. -/
theorem equivalent_refl (P : FinStoch Θ X) : BlackwellEquivalent P P :=
  @InformationEquivalent.refl Object _ Θ X P

/-- Blackwell equivalence is symmetric. -/
theorem equivalent_symm {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    (h : BlackwellEquivalent P Q) : BlackwellEquivalent Q P :=
  h.symm

/-- Blackwell equivalence is transitive. -/
theorem equivalent_trans {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    {S : FinStoch Θ Z} (hPQ : BlackwellEquivalent P Q)
    (hQS : BlackwellEquivalent Q S) : BlackwellEquivalent P S :=
  hPQ.trans hQS

section ResourceBounded

variable {R : Type w} [AddCommMonoid R] [PartialOrder R]
variable [HasProcessCost Object.{u} R]

/-- Blackwell dominance whose garbling has a certified resource budget. -/
abbrev BlackwellDominatesWithin (r : R) (P : FinStoch Θ X)
    (Q : FinStoch Θ Y) : Prop :=
  @SimulatesWithin Object _ R _ _ _ Θ X Y r P Q

/-- Forgetting the resource certificate recovers ordinary Blackwell
dominance. -/
theorem dominates_of_dominatesWithin {r : R} {P : FinStoch Θ X}
    {Q : FinStoch Θ Y} (h : BlackwellDominatesWithin r P Q) :
    BlackwellDominates P Q :=
  h.simulates

end ResourceBounded

section BayesRisk

variable {A : Object.{u}}

/-- Regard an exact finite prior as a one-row stochastic channel. -/
def priorChannel (π : FinDist Θ) : FinStoch Object.unit Θ :=
  kleisliToChannel (fun _ ↦ π)

/-- The probability measure induced by an exact finite prior. -/
noncomputable def priorMeasure (π : FinDist Θ) : @Measure Θ ⊤ :=
  rowMeasure (priorChannel π) PUnit.unit

/-- Exact finite loss values embedded in Mathlib's extended nonnegative
reals. -/
def semanticLoss (loss : Θ → A → ℚ≥0) : Θ → A → ℝ≥0∞ :=
  fun θ a ↦ (loss θ a : ℝ≥0∞)

/-- Mathlib's Bayes risk for an exact finite experiment, prior, and loss.
This definition belongs to the noncomputable semantic layer. -/
noncomputable def semanticBayesRisk (loss : Θ → A → ℚ≥0)
    (π : FinDist Θ) (P : FinStoch Θ X) : ℝ≥0∞ :=
  @bayesRisk Θ X A ⊤ ⊤ ⊤
    (semanticLoss loss) (toKernel P) (priorMeasure π)

/-- **Bayes-risk data processing.** Garbling an exact finite experiment cannot
decrease its optimal Mathlib Bayes risk. -/
theorem semanticBayesRisk_le_postprocess (loss : Θ → A → ℚ≥0)
    (π : FinDist Θ) (P : FinStoch Θ X) (κ : FinStoch X Y) :
    semanticBayesRisk loss π P ≤
      semanticBayesRisk loss π (FinStoch.comp P κ) := by
  unfold semanticBayesRisk
  rw [toKernel_comp]
  exact @bayesRisk_le_bayesRisk_comp Θ X Y A ⊤ ⊤ ⊤ ⊤
    (semanticLoss loss) (toKernel P) (priorMeasure π) (toKernel κ) inferInstance

/-- Blackwell dominance implies the Bayes-risk order for every exact finite
prior and loss function.  This is the forward direction of the finite
Blackwell decision comparison, not the converse representation theorem. -/
theorem semanticBayesRisk_mono {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    (hPQ : BlackwellDominates P Q) (loss : Θ → A → ℚ≥0)
    (π : FinDist Θ) :
    semanticBayesRisk loss π P ≤ semanticBayesRisk loss π Q := by
  rcases hPQ with ⟨κ, hκ⟩
  rw [← hκ]
  exact semanticBayesRisk_le_postprocess loss π P κ

/-- Blackwell-equivalent finite experiments have equal Bayes risk in every
exact finite decision problem. -/
theorem semanticBayesRisk_eq_of_equivalent
    {P : FinStoch Θ X} {Q : FinStoch Θ Y}
    (hPQ : BlackwellEquivalent P Q) (loss : Θ → A → ℚ≥0)
    (π : FinDist Θ) :
    semanticBayesRisk loss π P = semanticBayesRisk loss π Q :=
  le_antisymm
    (semanticBayesRisk_mono hPQ.1 loss π)
    (semanticBayesRisk_mono hPQ.2 loss π)

end BayesRisk

end Ript.Models.Decision.Blackwell
