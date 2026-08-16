import Ript.Examples.StochasticBits
import Ript.Models.Probability.StochFunctor

/-!
# Finite Boolean channels inside Mathlib `Stoch`

These examples exercise the semantic bridge on the executable Boolean models:
singleton probabilities, categorical composition, deterministic kernels, and
independent tensor composition.
-/

set_option autoImplicit false

namespace Ript.Examples.StochBits

open CategoryTheory MeasureTheory
open scoped ENNReal MonoidalCategory
open Ript.Examples.StochasticBits
open Ript.Models.FiniteStochastic
open Ript.Models.FiniteStochastic.FinStoch
open Ript.Models.Probability.StochFunctor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The interpreted fair coin assigns its exact rational mass to `false`. -/
theorem fairCoin_false_mass :
    (toKernel fairCoin (PUnit.unit : Object.unit)) {false} =
      (((1 : ℚ≥0) / 2 : ℚ≥0) : ℝ≥0∞) := by
  rw [toKernel_apply, rowMeasure_singleton]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Functorial composition agrees with the executable proof that noisy
negation preserves the fair distribution. -/
theorem noisyNot_preserves_fair_in_stoch :
    toStoch.map fairCoin ≫ toStoch.map noisyNot = toStoch.map fairCoin := by
  rw [← toStoch.map_comp]
  change toStoch.map (FinStoch.comp fairCoin noisyNot) = toStoch.map fairCoin
  exact congrArg toStoch.map noisyNot_preserves_fair

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Deterministic Boolean negation is sent to Mathlib's deterministic kernel. -/
theorem deterministicNot_is_deterministic_kernel :
    toStoch.map deterministicNot =
      @discreteDeterministicHom bit bit Bool.not := by
  unfold deterministicNot
  exact @toStoch_map_dirac bit bit Bool.not

/-- Two independent fair coins satisfy the proved tensor comparison diagram
inside Mathlib `Stoch`. -/
theorem fairCoin_tensor_in_stoch :
    (toStoch.map fairCoin ⊗ₘ toStoch.map fairCoin) ≫
        (tensorComparison bit bit).hom =
      (tensorComparison Object.unit Object.unit).hom ≫
        toStoch.map (tensor fairCoin fairCoin) :=
  toStoch_map_tensor fairCoin fairCoin

end Ript.Examples.StochBits
