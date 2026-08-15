import Mathlib.CategoryTheory.Equivalence
import Ript.Models.FiniteDistribution

/-!
# Kleisli representation of exact finite stochastic channels

This module constructs the Kleisli category of `FinDist`, restricted to the
same executable finite carriers used by `FinStoch`. It then gives explicit
functors in both directions and proves a categorical equivalence.

The restriction is mathematically necessary: even over a nonempty finite
carrier, the type of all rational probability distributions is generally
infinite, so the finite carriers are not closed under the distribution object
mapping required by `CategoryTheory.Kleisli`. The hom formula remains the
ordinary Kleisli formula `X → FinDist Y`, and its category laws are the proved
`pure`/`bind` laws.
-/

set_option autoImplicit false

namespace Ript.Models.FiniteStochastic

open CategoryTheory
open Ript.Models.FiniteDistribution

universe u

/-- Objects of the finite-carrier Kleisli category for exact finite
distributions. -/
structure Kleisli where
  /-- The underlying executable finite carrier. -/
  object : Object.{u}

namespace Kleisli

/-- Regard an executable finite stochastic object as a Kleisli object. -/
def of (X : Object.{u}) : Kleisli :=
  ⟨X⟩

/-- Exact finite distributions form a Kleisli category on finite carriers. -/
instance category : Category.{u} Kleisli where
  Hom X Y := X.object → FinDist Y.object
  id _ := FinDist.pure
  comp f g x := FinDist.bind (f x) g
  id_comp := by
    intro X Y f
    funext x
    exact FinDist.pure_bind x f
  comp_id := by
    intro X Y f
    funext x
    exact FinDist.bind_pure (f x)
  assoc := by
    intro W X Y Z f g h
    funext w
    exact FinDist.bind_assoc (f w) g h

end Kleisli

variable {X Y Z : Object.{u}}
variable {K L : Kleisli.{u}}

/-- Convert a stochastic channel row into its exact output distribution. -/
def channelToKleisli (f : FinStoch X Y) : X → FinDist Y :=
  fun x ↦ ⟨f.prob x, f.normalized x⟩

/-- Convert a finite-carrier Kleisli morphism into a stochastic matrix. -/
def kleisliToChannel (f : X → FinDist Y) : FinStoch X Y where
  prob x y := (f x).prob y
  normalized x := (f x).normalized

/-- Reading a converted channel row recovers the original matrix entry. -/
@[simp]
theorem channelToKleisli_apply (f : FinStoch X Y) (x : X) (y : Y) :
    (channelToKleisli f x).prob y = f.prob x y :=
  rfl

/-- Reading a converted Kleisli morphism recovers the original distribution
entry. -/
@[simp]
theorem kleisliToChannel_apply (f : X → FinDist Y) (x : X) (y : Y) :
    (kleisliToChannel f).prob x y = (f x).prob y :=
  rfl

/-- Channel-to-Kleisli conversion followed by the reverse conversion is the
identity on stochastic channels. -/
@[simp]
theorem kleisliToChannel_channelToKleisli (f : FinStoch X Y) :
    kleisliToChannel (channelToKleisli f) = f := by
  apply FinStoch.ext
  intro x y
  rfl

/-- Kleisli-to-channel conversion followed by the reverse conversion is the
identity on finite-carrier Kleisli morphisms. -/
@[simp]
theorem channelToKleisli_kleisliToChannel (f : X → FinDist Y) :
    channelToKleisli (kleisliToChannel f) = f := by
  funext x
  apply FinDist.ext
  intro y
  rfl

/-- Convert exact finite stochastic channels into finite-carrier Kleisli
morphisms. -/
def toKleisli : Object.{u} ⥤ Kleisli.{u} where
  obj X := Kleisli.of X
  map f := channelToKleisli f
  map_id X := by
    funext x
    apply FinDist.ext
    intro y
    rfl
  map_comp f g := by
    funext x
    apply FinDist.ext
    intro z
    rfl

/-- Convert finite-carrier Kleisli morphisms into exact finite stochastic
channels. -/
def fromKleisli : Kleisli.{u} ⥤ Object.{u} where
  obj X := X.object
  map f := kleisliToChannel f
  map_id X := by
    apply FinStoch.ext
    intro x y
    rfl
  map_comp f g := by
    apply FinStoch.ext
    intro x z
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The forward and reverse conversions are naturally inverse on stochastic
objects and channels. -/
def unitIso : 𝟭 Object.{u} ≅ toKleisli ⋙ fromKleisli :=
  NatIso.ofComponents (fun X ↦ Iso.refl X) fun f ↦ by
    calc
      _ = f := Category.comp_id f
      _ = kleisliToChannel (channelToKleisli f) :=
        (kleisliToChannel_channelToKleisli f).symm
      _ = (toKleisli ⋙ fromKleisli).map f := rfl
      _ = _ := (Category.id_comp ((toKleisli ⋙ fromKleisli).map f)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The reverse and forward conversions are naturally inverse on
finite-carrier Kleisli objects and morphisms. -/
def counitIso : fromKleisli ⋙ toKleisli ≅ 𝟭 Kleisli.{u} :=
  NatIso.ofComponents (fun X ↦ Iso.refl X) fun f ↦ by
    calc
      _ = (fromKleisli ⋙ toKleisli).map f := Category.comp_id _
      _ = channelToKleisli (kleisliToChannel f) := rfl
      _ = f := channelToKleisli_kleisliToChannel f
      _ = (𝟭 Kleisli).map f := rfl
      _ = _ := (Category.id_comp ((𝟭 Kleisli).map f)).symm

/-- Exact finite stochastic channels are categorically equivalent to the
finite-carrier Kleisli category of exact finite distributions. -/
def kleisliEquivalence : Object.{u} ≌ Kleisli.{u} :=
  CategoryTheory.Equivalence.mk toKleisli fromKleisli unitIso counitIso

end Ript.Models.FiniteStochastic
