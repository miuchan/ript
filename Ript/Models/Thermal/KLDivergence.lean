import Ript.Models.Probability.FiniteKL
import Ript.Models.Thermal.Monotone

/-!
# KL athermality for finite thermal systems

The generic thermal monotonicity theorem becomes a concrete theorem here by
instantiating it with finite Kullback--Leibler divergence.  The analytic work
is not assumed: `FiniteKL.finiteKL_dataProcessing` derives the full stochastic
data-processing inequality from Mathlib's Markov-kernel theorem through Ript's
exact finite semantic bridge.
-/

set_option autoImplicit false

namespace Ript.Models.Thermal

open scoped ENNReal
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic
open Ript.Models.Probability.FiniteKL

universe u

/-- Finite Kullback--Leibler divergence packaged with its proved stochastic
data-processing law. -/
noncomputable def finiteKLDivergence : Divergence.{u, 0} ℝ≥0∞ where
  measure := fun p q ↦ finiteKL p q
  dataProcessing := finiteKL_dataProcessing

/-- KL athermality is divergence from the distinguished equilibrium state. -/
noncomputable def klAthermality (X : ThermalObject.{u})
    (state : FinDist X.system) : ℝ≥0∞ :=
  finiteKLDivergence.athermality X state

/-- The concrete KL athermality formula. -/
@[simp]
theorem klAthermality_eq (X : ThermalObject.{u})
    (state : FinDist X.system) :
    klAthermality X state = finiteKL state X.equilibrium :=
  rfl

/-- **KL athermality monotonicity.** Every exact finite Gibbs-preserving
stochastic process can only decrease divergence from equilibrium. -/
theorem klAthermality_monotone {X Y : ThermalObject.{u}}
    (process : GibbsPreserving X Y) (state : FinDist X.system) :
    klAthermality Y (state.push process.channel) ≤
      klAthermality X state :=
  finiteKLDivergence.athermality_monotone process state

/-- KL athermality packaged as a reusable thermal monotone. -/
noncomputable def klThermalMonotone : ThermalMonotone.{u, 0} ℝ≥0∞ :=
  finiteKLDivergence.toThermalMonotone

/-- The packaged thermal monotone evaluates to finite KL from equilibrium. -/
@[simp]
theorem klThermalMonotone_value (X : ThermalObject.{u})
    (state : FinDist X.system) :
    klThermalMonotone.value X state = finiteKL state X.equilibrium :=
  rfl

end Ript.Models.Thermal
