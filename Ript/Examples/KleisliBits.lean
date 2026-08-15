import Ript.Examples.StochasticBits
import Ript.Models.FiniteStochastic.Kleisli

/-!
# Executable Kleisli representation example

This example converts the exact fair-coin and noisy-negation matrices into
finite-distribution Kleisli morphisms, composes them with `FinDist.bind`, and
checks that conversion back yields Chapman--Kolmogorov composition.
-/

set_option autoImplicit false

namespace Ript.Examples.KleisliBits

open Ript.Examples.StochasticBits
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic
open Ript.Models.FiniteStochastic.FinStoch

/-- The fair coin represented as a finite-distribution Kleisli morphism. -/
def fairCoinKleisli : Object.unit → FinDist bit :=
  channelToKleisli fairCoin

/-- Noisy negation represented as a finite-distribution Kleisli morphism. -/
def noisyNotKleisli : bit → FinDist bit :=
  channelToKleisli noisyNot

/-- Kleisli composition of fair preparation and noisy negation. -/
def coinThenNoisyKleisli (input : Object.unit) : FinDist bit :=
  FinDist.bind (fairCoinKleisli input) noisyNotKleisli

/-- Converting Kleisli bind back to a matrix gives exact
Chapman--Kolmogorov composition. -/
theorem bind_matches_channel_composition :
    kleisliToChannel coinThenNoisyKleisli = comp fairCoin noisyNot := by
  apply FinStoch.ext
  intro input output
  rfl

-- Point distributions execute as exact zero-or-one mass functions.
#eval decide ((FinDist.pure true : FinDist bit).prob true = 1)

-- Kleisli bind executes the same noisy fair coin as matrix composition.
#eval decide ((coinThenNoisyKleisli PUnit.unit).prob true = (1 : ℚ≥0) / 2)

-- Matrix-to-Kleisli-to-matrix conversion preserves an exact channel entry.
#eval decide
  ((kleisliToChannel (channelToKleisli noisyNot)).prob false true = (3 : ℚ≥0) / 4)

-- The functors packaged by the categorical equivalence execute on morphisms.
#eval decide
  ((kleisliEquivalence.inverse.map
      (kleisliEquivalence.functor.map fairCoin)).prob PUnit.unit false =
    (1 : ℚ≥0) / 2)

end Ript.Examples.KleisliBits
