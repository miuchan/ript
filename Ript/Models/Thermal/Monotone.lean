import Ript.Models.Thermal.GibbsPreserving

/-!
# Generic thermodynamic monotones

The finite thermal layer deliberately does not assume a particular analytic
divergence.  Instead, `Divergence` records any family of state divergences that
satisfies the data-processing inequality for every exact finite stochastic
channel.  Distance from the distinguished equilibrium state is then a thermal
monotone for every Gibbs-preserving process.

This proves the structural monotonicity theorem without assuming an unproved
data-processing theorem for finite KL divergence.  Concrete divergences can be
added independently once their own data-processing proofs are available.
-/

set_option autoImplicit false

namespace Ript.Models.Thermal

open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic

universe u v

/-- A finite-state divergence valued in a preorder and satisfying stochastic
data processing.  No symmetry, separation, or numerical formula is assumed. -/
structure Divergence (Value : Type v) [Preorder Value] where
  /-- Compare two exact distributions on the same finite system. -/
  measure : {X : Object.{u}} → FinDist X → FinDist X → Value
  /-- Applying the same stochastic channel to both states cannot increase the
  divergence. -/
  dataProcessing : ∀ {X Y : Object.{u}} (channel : FinStoch X Y)
    (p q : FinDist X),
    measure (p.push channel) (q.push channel) ≤ measure p q

/-- A state functional that cannot increase under any Gibbs-preserving
process. -/
structure ThermalMonotone (Value : Type v) [Preorder Value] where
  /-- Resource value assigned to a state relative to its thermal system. -/
  value : (X : ThermalObject.{u}) → FinDist X.system → Value
  /-- Free thermodynamic evolution cannot increase the resource value. -/
  monotone : ∀ {X Y : ThermalObject.{u}} (process : GibbsPreserving X Y)
    (state : FinDist X.system),
    value Y (state.push process.channel) ≤ value X state

namespace Divergence

variable {Value : Type v} [Preorder Value]

/-- Divergence of a state from the distinguished equilibrium distribution. -/
def athermality (divergence : Divergence.{u, v} Value)
    (X : ThermalObject.{u}) (state : FinDist X.system) : Value :=
  divergence.measure state X.equilibrium

/-- **Generic thermodynamic data processing.** Divergence from equilibrium
cannot increase under a Gibbs-preserving finite stochastic process. -/
theorem athermality_monotone (divergence : Divergence.{u, v} Value)
    {X Y : ThermalObject.{u}} (process : GibbsPreserving X Y)
    (state : FinDist X.system) :
    divergence.athermality Y (state.push process.channel) ≤
      divergence.athermality X state := by
  unfold athermality
  rw [← process.preserves_equilibrium]
  exact divergence.dataProcessing process.channel state X.equilibrium

/-- Every stochastic divergence satisfying data processing canonically gives
a thermal monotone by measuring distance from equilibrium. -/
def toThermalMonotone (divergence : Divergence.{u, v} Value) :
    ThermalMonotone.{u, v} Value where
  value := divergence.athermality
  monotone := divergence.athermality_monotone

/-- The lifted thermal monotone is exactly divergence from equilibrium. -/
@[simp]
theorem toThermalMonotone_value (divergence : Divergence.{u, v} Value)
    (X : ThermalObject.{u}) (state : FinDist X.system) :
    divergence.toThermalMonotone.value X state =
      divergence.measure state X.equilibrium :=
  rfl

end Divergence

end Ript.Models.Thermal
