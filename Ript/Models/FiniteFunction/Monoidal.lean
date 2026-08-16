import Mathlib.CategoryTheory.CopyDiscardCategory.Cartesian
import Mathlib.CategoryTheory.FintypeCat
import Ript.Core.Capabilities
import Ript.Core.ParallelCost
import Ript.Models.FiniteFunction

/-!
# Cartesian structure on finite deterministic processes

This module equips Mathlib's `FintypeCat` with an explicit cartesian monoidal
structure.  The chosen terminal object is `PUnit` and the chosen binary product
is the ordinary product type, so tensor, copy, and discard retain their direct
computational meaning.  Mathlib's cartesian-to-copy-discard construction then
supplies the coherent classical comonoid laws.
-/

set_option autoImplicit false

namespace Ript.Models.FiniteFunction

open CategoryTheory
open CategoryTheory.Limits
open MonoidalCategory
open ComonObj
open Ript.Core

universe u

namespace FintypeCartesian

/-- The explicit terminal finite type used as the tensor unit. -/
abbrev unit : FintypeCat.{u} := FintypeCat.of PUnit

/-- `PUnit` is terminal among finite types. -/
def isTerminalUnit : IsTerminal (unit : FintypeCat.{u}) :=
  letI (X : FintypeCat.{u}) : Unique (X ⟶ unit) := {
    default := FintypeCat.homMk fun _ ↦ PUnit.unit
    uniq f := FintypeCat.hom_ext f _ fun _ ↦ Subsingleton.elim _ _
  }
  .ofUnique _

/-- The explicit terminal limit cone used to build the monoidal structure. -/
def terminalLimitCone : LimitCone (Functor.empty FintypeCat.{u}) :=
  ⟨_, isTerminalUnit⟩

/-- The ordinary product type, with its projections, as a binary fan in
`FintypeCat`. -/
def binaryProductCone (X Y : FintypeCat.{u}) : BinaryFan X Y :=
  BinaryFan.mk
    (FintypeCat.homMk
      (X := FintypeCat.of (X × Y)) (Y := X) fun pair ↦ pair.1)
    (FintypeCat.homMk
      (X := FintypeCat.of (X × Y)) (Y := Y) fun pair ↦ pair.2)

/-- The ordinary product type satisfies the binary-product universal
property in `FintypeCat`. -/
def binaryProductLimit (X Y : FintypeCat.{u}) :
    IsLimit (binaryProductCone X Y) where
  lift cone := FintypeCat.homMk fun value ↦
    (BinaryFan.fst cone value, BinaryFan.snd cone value)
  fac cone index := Discrete.recOn index fun index ↦
    WalkingPair.casesOn index rfl rfl
  uniq cone morphism equations := by
    apply FintypeCat.hom_ext
    intro value
    apply Prod.ext
    · exact ConcreteCategory.congr_hom (equations ⟨WalkingPair.left⟩) value
    · exact ConcreteCategory.congr_hom (equations ⟨WalkingPair.right⟩) value

/-- The explicit binary-product limit cone used to build the monoidal
structure. -/
def binaryProductLimitCone (X Y : FintypeCat.{u}) :
    LimitCone (pair X Y) :=
  ⟨_, binaryProductLimit X Y⟩

end FintypeCartesian

/-- The cartesian tensor on finite types is the ordinary product type, with
`PUnit` as unit. -/
instance cartesianMonoidalCategory :
    CartesianMonoidalCategory FintypeCat.{u} where
  tensorObj X Y := FintypeCat.of (X × Y)
  tensorUnit := FintypeCartesian.unit
  __ := CartesianMonoidalCategory.ofChosenFiniteProducts
    FintypeCartesian.terminalLimitCone
    FintypeCartesian.binaryProductLimitCone

/-- Cartesian products supply the canonical braiding on finite types. -/
instance braidedCategory : BraidedCategory FintypeCat.{u} :=
  .ofCartesianMonoidalCategory

/-- Finite deterministic processes have coherent classical copy and discard
operations inherited from their cartesian structure. -/
@[instance_reducible]
instance copyDiscardCategory : CopyDiscardCategory FintypeCat.{u} :=
  CartesianCopyDiscard.ofCartesianMonoidalCategory

/-- Every finite deterministic function preserves classical copy and
discard. -/
instance deterministic {X Y : FintypeCat.{u}} (f : X ⟶ Y) : Deterministic f :=
  CartesianCopyDiscard.instDeterministic f

/-- Tensoring two zero-cost deterministic functions remains zero-cost. -/
instance zeroParallelCost : HasParallelProcessCost FintypeCat.{u} Nat where
  cost_tensor _ _ := Nat.zero_le 0

/-- The tensor product object is definitionally the ordinary product type. -/
theorem tensorObj_eq (X Y : FintypeCat.{u}) : X ⊗ Y = FintypeCat.of (X × Y) :=
  rfl

/-- Tensoring deterministic functions applies them componentwise. -/
@[simp]
theorem tensor_apply {W X Y Z : FintypeCat.{u}}
    (f : W ⟶ X) (g : Y ⟶ Z) (value : W × Y) :
    (f ⊗ₘ g) value = (f value.1, g value.2) :=
  rfl

/-- Classical copy duplicates its input. -/
@[simp]
theorem copy_apply (X : FintypeCat.{u}) (value : X) :
    Δ[X] value = (value, value) :=
  rfl

/-- Classical discard returns the sole point of the tensor unit. -/
@[simp]
theorem discard_apply (X : FintypeCat.{u}) (value : X) :
    ε[X] value = PUnit.unit :=
  rfl

/-- Every finite deterministic function commutes with copying. -/
theorem copy_natural {X Y : FintypeCat.{u}} (f : X ⟶ Y) :
    f ≫ Δ[Y] = Δ[X] ≫ (f ⊗ₘ f) :=
  Deterministic.copy_natural f

/-- Every finite deterministic function commutes with discarding. -/
theorem discard_natural {X Y : FintypeCat.{u}} (f : X ⟶ Y) :
    f ≫ ε[Y] = ε[X] :=
  Deterministic.discard_natural f

/-- Copying is coassociative, with the monoidal associator exposing the two
parenthesizations. -/
theorem copy_coassociative (X : FintypeCat.{u}) :
    Δ[X] ≫ X ◁ Δ[X] =
      Δ[X] ≫ (Δ[X] ▷ X) ≫ (α_ X X X).hom :=
  ComonObj.comul_assoc X

/-- Discarding the first output of copy is the left-unitor insertion. -/
theorem copy_discard_left (X : FintypeCat.{u}) :
    Δ[X] ≫ ε[X] ▷ X = (λ_ X).inv :=
  ComonObj.counit_comul X

/-- Discarding the second output of copy is the right-unitor insertion. -/
theorem copy_discard_right (X : FintypeCat.{u}) :
    Δ[X] ≫ X ◁ ε[X] = (ρ_ X).inv :=
  ComonObj.comul_counit X

/-- Classical copy is invariant under swapping its two outputs. -/
theorem copy_commutative (X : FintypeCat.{u}) :
    Δ[X] ≫ (β_ X X).hom = Δ[X] :=
  IsCommComonObj.comul_comm X

/-- Every finite deterministic function is causal. -/
theorem causal {X Y : FintypeCat.{u}} (f : X ⟶ Y) : CausalProcess f :=
  causal_of_deterministic f

end Ript.Models.FiniteFunction
