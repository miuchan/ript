import Ript.Models.FiniteDistribution

/-!
# Finite equilibrium systems

This module supplies the state-level operations needed by the finite
thermodynamic model.  Exact finite distributions can be evolved through a
`FinStoch` channel and combined independently.  A `ThermalObject` is then a
finite system together with one distinguished normalized equilibrium state.

No energy function or analytic Gibbs formula is assumed at this layer: the
distinguished distribution is the operational datum that later free processes
must preserve.
-/

set_option autoImplicit false

namespace Ript.Models.FiniteDistribution

open scoped BigOperators

open Ript.Models.FiniteStochastic

universe u

namespace FinDist

variable {W X Y Z : Object.{u}}

/-- Evolve an exact finite distribution through a stochastic channel. -/
def push (p : FinDist X) (channel : FinStoch X Y) : FinDist Y :=
  bind p fun x ↦
    { prob := channel.prob x
      normalized := channel.normalized x }

/-- Entrywise formula for stochastic evolution of a finite distribution. -/
@[simp]
theorem push_apply (p : FinDist X) (channel : FinStoch X Y) (y : Y) :
    (p.push channel).prob y = ∑ x, p.prob x * channel.prob x y :=
  rfl

/-- Evolving through the identity channel leaves a distribution unchanged. -/
@[simp]
theorem push_identity (p : FinDist X) :
    p.push (FinStoch.identity X) = p := by
  apply ext
  intro y
  simp [push, FinStoch.identity]

/-- Stochastic evolution respects Chapman--Kolmogorov composition. -/
theorem push_comp (p : FinDist X) (f : FinStoch X Y) (g : FinStoch Y Z) :
    p.push (FinStoch.comp f g) = (p.push f).push g := by
  apply ext
  intro z
  change (∑ x, p.prob x * (∑ y, f.prob x y * g.prob y z)) =
    ∑ y, (∑ x, p.prob x * f.prob x y) * g.prob y z
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [mul_assoc]

/-- Independent product of two exact finite distributions. -/
def tensor (p : FinDist X) (q : FinDist Y) :
    FinDist (Object.tensor X Y) where
  prob outcome := p.prob outcome.1 * q.prob outcome.2
  normalized := by
    change (∑ outcome : X × Y, p.prob outcome.1 * q.prob outcome.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    simp [p.normalized, q.normalized]

/-- Entrywise formula for an independent product distribution. -/
@[simp]
theorem tensor_apply (p : FinDist X) (q : FinDist Y) (outcome : X × Y) :
    (p.tensor q).prob outcome = p.prob outcome.1 * q.prob outcome.2 :=
  rfl

/-- Independent stochastic evolution commutes with product distributions. -/
theorem push_tensor (p : FinDist W) (q : FinDist Y)
    (f : FinStoch W X) (g : FinStoch Y Z) :
    (p.tensor q).push (FinStoch.tensor f g) =
      (p.push f).tensor (q.push g) := by
  apply ext
  intro output
  change X × Z at output
  rcases output with ⟨x, z⟩
  change (∑ input : W × Y,
      (p.prob input.1 * q.prob input.2) *
        (f.prob input.1 x * g.prob input.2 z)) =
    (∑ w, p.prob w * f.prob w x) *
      ∑ y, q.prob y * g.prob y z
  rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]
  apply Fintype.sum_congr
  intro w
  apply Fintype.sum_congr
  intro y
  ac_rfl

/-- Regard a normalized finite distribution as a stochastic state from the
tensor unit. -/
def toState (p : FinDist X) : FinStoch Object.unit X where
  prob _ x := p.prob x
  normalized _ := p.normalized

/-- A stochastic state exposes the probability mass of its distribution. -/
@[simp]
theorem toState_apply (p : FinDist X) (input : Object.unit) (x : X) :
    p.toState.prob input x = p.prob x :=
  rfl

/-- Preparing a distribution from the unique unit state produces that
distribution. -/
@[simp]
theorem pure_unit_push_toState (p : FinDist X) :
    (pure PUnit.unit).push p.toState = p := by
  apply ext
  intro x
  change (∑ input : PUnit,
    (if PUnit.unit = input then 1 else 0) * p.prob x) = p.prob x
  rw [Fintype.sum_unique]
  simp

end FinDist

end Ript.Models.FiniteDistribution

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
