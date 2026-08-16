import Ript.Models.FiniteDistribution

/-!
# Finite equilibrium systems

This module uses the state-level operations supplied by the exact finite
distribution model.  A `ThermalObject` is a finite system together with one
distinguished normalized equilibrium state.

No energy function or analytic Gibbs formula is assumed at this layer: the
distinguished distribution is the operational datum that later free processes
must preserve.
-/

set_option autoImplicit false

namespace Ript.Models.Thermal

open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic

universe u

/-- An equilibrium state is an exact normalized distribution on a finite
system. -/
abbrev EquilibriumState (X : Object.{u}) := FinDist X

/-- A finite thermal system equipped with its distinguished equilibrium
distribution. -/
structure ThermalObject where
  /-- Underlying executable finite state space. -/
  system : Object.{u}
  /-- Distinguished normalized equilibrium distribution. -/
  equilibrium : EquilibriumState system

namespace ThermalObject

/-- Tensor unit with its unique equilibrium state. -/
def unit : ThermalObject.{u} where
  system := Object.unit
  equilibrium := FinDist.pure PUnit.unit

/-- Independent composite system with the product equilibrium state. -/
def tensor (X Y : ThermalObject.{u}) : ThermalObject.{u} where
  system := Object.tensor X.system Y.system
  equilibrium := X.equilibrium.tensor Y.equilibrium

/-- The composite equilibrium probability factors into its two marginal
equilibrium probabilities. -/
@[simp]
theorem tensor_equilibrium_apply (X Y : ThermalObject.{u})
    (outcome : X.system × Y.system) :
    (tensor X Y).equilibrium.prob outcome =
      X.equilibrium.prob outcome.1 * Y.equilibrium.prob outcome.2 :=
  rfl

end ThermalObject

end Ript.Models.Thermal
