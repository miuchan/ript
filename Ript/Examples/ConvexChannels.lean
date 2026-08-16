import Mathlib.Tactic.NormNum
import Ript.Examples.StochasticBits
import Ript.Models.FiniteStochastic.Convex

/-!
# Executable exact convex-channel example

A fair external choice between the Boolean identity and Boolean negation
forgets the input and produces a fair bit.  The probabilities below compute as
exact nonnegative rationals, while the structural theorems are inherited from
the independent `ConvexProcess` capability.
-/

set_option autoImplicit false

namespace Ript.Examples.ConvexChannels

open CategoryTheory
open Ript.Core
open Ript.Models.FiniteStochastic
open Ript.Models.FiniteStochastic.FinStoch

/-- Reuse the executable Boolean object from the stochastic example. -/
abbrev bit : Object :=
  StochasticBits.bit

/-- Exact equal weights, represented without floating-point arithmetic. -/
def halfWeight : ConvexWeight ℚ≥0 where
  left := 1 / 2
  right := 1 / 2
  left_nonnegative := by norm_num
  right_nonnegative := by norm_num
  total := by norm_num

/-- Choose the Boolean identity or Boolean negation with equal probability. -/
def fairIdentityOrNot : FinStoch bit bit :=
  mix halfWeight (identity bit) StochasticBits.deterministicNot

/-- The fair choice erases its Boolean input: every output has probability
exactly one half. -/
theorem fairIdentityOrNot_apply (input output : Bool) :
    fairIdentityOrNot.prob input output = (1 : ℚ≥0) / 2 := by
  cases input with
  | false =>
      cases output with
      | false =>
          change ((1 : ℚ≥0) / 2) * 1 + ((1 : ℚ≥0) / 2) * 0 = 1 / 2
          norm_num
      | true =>
          change ((1 : ℚ≥0) / 2) * 0 + ((1 : ℚ≥0) / 2) * 1 = 1 / 2
          norm_num
  | true =>
      cases output with
      | false =>
          change ((1 : ℚ≥0) / 2) * 0 + ((1 : ℚ≥0) / 2) * 1 = 1 / 2
          norm_num
      | true =>
          change ((1 : ℚ≥0) / 2) * 1 + ((1 : ℚ≥0) / 2) * 0 = 1 / 2
          norm_num

/-- Postcomposition of the mixture is exactly the mixture of the
postcompositions. -/
theorem fairIdentityOrNot_postcomp :
    comp fairIdentityOrNot StochasticBits.deterministicNot =
      mix halfWeight
        (comp (identity bit) StochasticBits.deterministicNot)
        (comp StochasticBits.deterministicNot StochasticBits.deterministicNot) :=
  mix_postcomp halfWeight (identity bit) StochasticBits.deterministicNot
    StochasticBits.deterministicNot

/-- Tensoring the fair choice with deterministic negation distributes over
the two random branches. -/
theorem fairIdentityOrNot_tensor :
    tensor fairIdentityOrNot StochasticBits.deterministicNot =
      mix halfWeight
        (tensor (identity bit) StochasticBits.deterministicNot)
        (tensor StochasticBits.deterministicNot StochasticBits.deterministicNot) :=
  mix_tensor_left halfWeight (identity bit) StochasticBits.deterministicNot
    StochasticBits.deterministicNot

-- Both rows of the mixed channel are exactly uniform.
#eval decide (fairIdentityOrNot.prob false false = (1 : ℚ≥0) / 2)
#eval decide (fairIdentityOrNot.prob false true = (1 : ℚ≥0) / 2)
#eval decide (fairIdentityOrNot.prob true false = (1 : ℚ≥0) / 2)
#eval decide (fairIdentityOrNot.prob true true = (1 : ℚ≥0) / 2)

end Ript.Examples.ConvexChannels
