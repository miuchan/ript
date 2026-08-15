import Mathlib.CategoryTheory.FintypeCat
import Ript.Core.CostedProcess

/-!
# Finite deterministic process models

The baseline model reuses mathlib's `FintypeCat` and assigns zero cost to every
function. `Metered` is a thin proof-relevant wrapper that records an explicit
natural-number cost and adds costs under composition.
-/

set_option autoImplicit false

namespace Ript.Models.FiniteFunction

open CategoryTheory
open Ript.Core

universe u

/-- The zero-cost baseline process model on mathlib's category of finite types. -/
instance zeroCost : HasProcessCost FintypeCat Nat where
  cost _ := 0
  cost_id _ := rfl
  cost_comp _ _ := Nat.zero_le 0

/-- A finite type object whose morphisms will carry explicit additive costs. -/
structure Metered where
  /-- The underlying object of mathlib's finite-type category. -/
  obj : FintypeCat

namespace Metered

/-- Construct a metered object from a type carrying a `Finite` instance. -/
def of (X : Type) [Finite X] : Metered :=
  ⟨FintypeCat.of X⟩

/-- A deterministic function paired with its declared execution cost. -/
@[ext]
structure Hom (X Y : Metered) where
  /-- The executable finite function. -/
  toFun : X.obj ⟶ Y.obj
  /-- The abstract execution cost in natural-number units. -/
  units : Nat

/-- Metered finite functions form a category with additive serial costs. -/
instance category : Category.{0} Metered where
  Hom := Hom
  id X := ⟨𝟙 X.obj, 0⟩
  comp f g := ⟨f.toFun ≫ g.toFun, f.units + g.units⟩
  id_comp := by
    intro X Y f
    cases f with
    | mk fn units =>
        apply Hom.ext
        · rfl
        · simp
  comp_id := by
    intro X Y f
    cases f with
    | mk fn units =>
        apply Hom.ext
        · rfl
        · simp
  assoc := by
    intro W X Y Z f g h
    cases f with
    | mk fn fUnits =>
      cases g with
      | mk gn gUnits =>
        cases h with
        | mk hn hUnits =>
          apply Hom.ext
          · rfl
          · simp [Nat.add_assoc]

/-- Construct a metered morphism from a finite function and a cost. -/
def homMk {X Y : Metered} (f : X.obj.obj → Y.obj.obj) (units : Nat) : X ⟶ Y :=
  ⟨FintypeCat.homMk f, units⟩

/-- Apply the executable function underlying a metered morphism. -/
def apply {X Y : Metered} (f : X ⟶ Y) (x : X.obj.obj) : Y.obj.obj :=
  f.toFun x

/-- The process-cost instance reads the explicit units stored in each morphism. -/
instance processCost : HasProcessCost Metered Nat where
  cost f := f.units
  cost_id _ := rfl
  cost_comp _ _ := le_rfl

/-- A constructed metered function has exactly its advertised cost. -/
@[simp]
theorem homMk_units {X Y : Metered} (f : X.obj.obj → Y.obj.obj) (units : Nat) :
    (homMk f units).units = units :=
  rfl

/-- Composition adds the stored costs exactly. -/
@[simp]
theorem comp_units {X Y Z : Metered} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).units = f.units + g.units :=
  rfl

end Metered

end Ript.Models.FiniteFunction
