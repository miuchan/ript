import Mathlib.Tactic.NormNum
import Ript.Examples.StochasticBits
import Ript.Models.Quantum.ClassicalEmbedding

/-!
# A binary classical channel as a quantum measurement--preparation process

The exact `3/4` noisy Boolean negation channel is embedded into finite quantum
theory.  The examples verify both its action on a classical basis state and
the loss of off-diagonal coherence caused by the distinguished classical
measurement.
-/

set_option autoImplicit false

namespace Ript.Examples.ClassicalQuantum

open Matrix
open scoped ComplexOrder

open Ript.Models.FiniteDistribution
open Ript.Models.Quantum
open Ript.Models.Quantum.ClassicalEmbedding

/-- The classical noisy-not channel, interpreted as a CPTP
measurement--preparation channel. -/
noncomputable def quantumNoisyNot :
    KrausChannel
      (classicalObject StochasticBits.bit)
      (classicalObject StochasticBits.bit) :=
  measurementPreparation StochasticBits.noisyNot

/-- Applying the quantum realization to a diagonal basis state agrees with
exact finite-distribution evolution. -/
theorem quantumNoisyNot_false_state :
    quantumNoisyNot.applyDensity
        (diagonalDensity (FinDist.pure (X := StochasticBits.bit) false)) =
      diagonalDensity
        ((FinDist.pure (X := StochasticBits.bit) false).push
          StochasticBits.noisyNot) :=
  measurementPreparation_diagonalDensity _ _

/-- Starting from classical false, noisy negation outputs classical true with
exact probability `3/4`. -/
theorem quantumNoisyNot_false_to_true :
    (quantumNoisyNot.applyDensity
      (diagonalDensity (FinDist.pure (X := StochasticBits.bit) false))).matrix
        true true = ((3 : ℚ≥0) / 4 : ℂ) := by
  rw [quantumNoisyNot_false_state, diagonalDensity_matrix]
  change (((FinDist.pure (X := StochasticBits.bit) false).push
    StochasticBits.noisyNot).prob true : ℂ) = ((3 : ℚ≥0) / 4 : ℂ)
  simp only [FinDist.push, FinDist.bind, FinDist.pure,
    StochasticBits.noisyNot, StochasticBits.bit,
    Ript.Models.FiniteStochastic.Object.of]
  change ((((∑ x : Bool,
    (if false = x then (1 : ℚ≥0) else 0) *
      if true = !x then (3 : ℚ≥0) / 4 else (1 : ℚ≥0) / 4) : ℚ≥0) : ℂ) =
    ((3 : ℚ≥0) / 4 : ℂ))
  rw [Fintype.sum_bool]
  norm_num

/-- The stochastic identity becomes complete basis dephasing, so it removes
the Boolean off-diagonal matrix entry. -/
theorem dephase_bool_offDiagonal
    (ρ : Matrix
      (classicalObject StochasticBits.bit)
      (classicalObject StochasticBits.bit) ℂ) :
    (dephase StochasticBits.bit).map ρ false true = 0 := by
  have h := measurementPreparation_map_apply
    (Ript.Models.FiniteStochastic.FinStoch.identity StochasticBits.bit)
    ρ false true
  simpa only [dephase, StochasticBits.bit,
    Ript.Models.FiniteStochastic.Object.of, Bool.false_eq_true, if_false] using h

end Ript.Examples.ClassicalQuantum
