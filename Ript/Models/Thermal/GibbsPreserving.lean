import Mathlib.CategoryTheory.Products.Basic
import Ript.Models.Thermal.Equilibrium

/-!
# Gibbs-preserving finite processes

A free thermodynamic process is an exact finite stochastic channel that maps
the distinguished equilibrium state of its source to that of its target.
These processes contain identities, are closed under composition, and form a
category.  Independent tensor composition is a bifunctor, with product
equilibria supplied by `ThermalObject.tensor`.
-/

set_option autoImplicit false

namespace Ript.Models.Thermal

open CategoryTheory
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic

universe u

/-- An exact finite stochastic channel that preserves the specified
equilibrium distributions. -/
structure GibbsPreserving (X Y : ThermalObject.{u}) where
  /-- Underlying stochastic evolution. -/
  channel : FinStoch X.system Y.system
  /-- The source equilibrium evolves exactly to the target equilibrium. -/
  preserves_equilibrium : X.equilibrium.push channel = Y.equilibrium

namespace GibbsPreserving

variable {V W X Y Z : ThermalObject.{u}}

/-- Gibbs-preserving processes are equal when their underlying channels are
equal. -/
@[ext]
theorem ext (f g : GibbsPreserving X Y) (h : f.channel = g.channel) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The identity stochastic channel preserves every equilibrium state. -/
def identity (X : ThermalObject.{u}) : GibbsPreserving X X where
  channel := FinStoch.identity X.system
  preserves_equilibrium := FinDist.push_identity X.equilibrium

/-- Gibbs-preserving processes are closed under serial composition. -/
def comp (f : GibbsPreserving X Y) (g : GibbsPreserving Y Z) :
    GibbsPreserving X Z where
  channel := FinStoch.comp f.channel g.channel
  preserves_equilibrium := by
    rw [FinDist.push_comp, f.preserves_equilibrium, g.preserves_equilibrium]

/-- Finite thermal systems and Gibbs-preserving processes form a category. -/
instance category : Category.{u} ThermalObject.{u} where
  Hom := GibbsPreserving
  id := identity
  comp := comp
  id_comp := by
    intro X Y f
    apply ext
    apply FinStoch.ext
    intro x y
    simp [identity, comp, FinStoch.identity, FinStoch.comp]
  comp_id := by
    intro X Y f
    apply ext
    apply FinStoch.ext
    intro x y
    simp [identity, comp, FinStoch.identity, FinStoch.comp]
  assoc := by
    intro V W X Y f g h
    apply ext
    apply FinStoch.ext
    intro v y
    simp only [comp, FinStoch.comp]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp [mul_assoc]

/-- The underlying channel of a thermal identity is the stochastic identity. -/
@[simp]
theorem id_channel (X : ThermalObject.{u}) :
    (identity X).channel = FinStoch.identity X.system :=
  rfl

/-- The underlying channel of thermal composition is stochastic composition. -/
@[simp]
theorem comp_channel (f : GibbsPreserving X Y) (g : GibbsPreserving Y Z) :
    (comp f g).channel = FinStoch.comp f.channel g.channel :=
  rfl

/-- Independent tensor composition of two Gibbs-preserving processes is again
Gibbs-preserving. -/
def tensor (f : GibbsPreserving V W) (g : GibbsPreserving X Y) :
    GibbsPreserving (ThermalObject.tensor V X) (ThermalObject.tensor W Y) where
  channel := FinStoch.tensor f.channel g.channel
  preserves_equilibrium := by
    change (V.equilibrium.tensor X.equilibrium).push
      (FinStoch.tensor f.channel g.channel) =
        W.equilibrium.tensor Y.equilibrium
    rw [FinDist.push_tensor, f.preserves_equilibrium, g.preserves_equilibrium]

/-- Tensor preserves thermal identity processes. -/
theorem tensor_id (X Y : ThermalObject.{u}) :
    tensor (identity X) (identity Y) =
      identity (ThermalObject.tensor X Y) := by
  apply ext
  exact FinStoch.tensor_id X.system Y.system

/-- Tensor satisfies interchange for Gibbs-preserving processes. -/
theorem tensor_comp {A B C D E F : ThermalObject.{u}}
    (f : GibbsPreserving A B) (f' : GibbsPreserving B C)
    (g : GibbsPreserving D E) (g' : GibbsPreserving E F) :
    tensor (comp f f') (comp g g') = comp (tensor f g) (tensor f' g') := by
  apply ext
  exact FinStoch.tensor_comp f.channel f'.channel g.channel g'.channel

/-- Independent composition is a bifunctor on finite thermal systems. -/
def tensorFunctor :
    CategoryTheory.Functor (ThermalObject.{u} × ThermalObject.{u})
      ThermalObject.{u} where
  obj pair := ThermalObject.tensor pair.1 pair.2
  map pair := tensor pair.1 pair.2
  map_id pair := tensor_id pair.1 pair.2
  map_comp f g := tensor_comp f.1 g.1 f.2 g.2

/-- A free state is a Gibbs-preserving preparation from the thermal unit. -/
abbrev FreeState (X : ThermalObject.{u}) :=
  GibbsPreserving ThermalObject.unit X

/-- The distinguished equilibrium distribution is itself a free state. -/
def equilibriumFreeState (X : ThermalObject.{u}) : FreeState X where
  channel := X.equilibrium.toState
  preserves_equilibrium := FinDist.pure_unit_push_toState X.equilibrium

/-- Preparing the equilibrium free state returns exactly its equilibrium
probability mass. -/
@[simp]
theorem equilibriumFreeState_apply (X : ThermalObject.{u})
    (input : Object.unit) (x : X.system) :
    (equilibriumFreeState X).channel.prob input x = X.equilibrium.prob x :=
  rfl

/-- The equilibrium preparation satisfies the defining free-state law. -/
theorem equilibrium_is_free (X : ThermalObject.{u}) :
    ThermalObject.unit.equilibrium.push
      (equilibriumFreeState X).channel = X.equilibrium :=
  (equilibriumFreeState X).preserves_equilibrium

end GibbsPreserving

end Ript.Models.Thermal
