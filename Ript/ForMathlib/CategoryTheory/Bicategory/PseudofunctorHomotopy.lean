import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Ript.ForMathlib.CategoryTheory.Bicategory.HomotopyCategory

/-!
# Pseudofunctors on bicategorical homotopy categories

A pseudofunctor maps invertible 2-cells to invertible 2-cells, so it descends
to an ordinary functor between the homotopy categories of its source and
target bicategories. This file constructs that functor and records its exact
action on represented 1-cells.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace CategoryTheory.Pseudofunctor

open CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory

universe u₁ v₁ w₁ u₂ v₂ w₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]
variable {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- A pseudofunctor induces an ordinary functor on bicategorical homotopy
categories. -/
noncomputable def homotopyFunctor (Q : B ⥤ᵖ C) :
    HomotopyCategory B ⥤ HomotopyCategory C where
  obj X := HomotopyCategory.of (Q.obj X.as)
  map {X Y} arrow := Quotient.liftOn arrow
    (fun f : X.as ⟶ Y.as => HomotopyCategory.homMk (Q.map f))
    (fun f g h => by
      apply (HomotopyCategory.homMk_eq_iff (Q.map f) (Q.map g)).2
      obtain ⟨e⟩ := h
      exact ⟨Q.map₂Iso e⟩)
  map_id X :=
    (HomotopyCategory.homMk_eq_iff _ _).2 ⟨Q.mapId X.as⟩
  map_comp := by
    rintro X Y Z ⟨f⟩ ⟨g⟩
    exact (HomotopyCategory.homMk_eq_iff _ _).2 ⟨Q.mapComp f g⟩

@[simp]
theorem homotopyFunctor_obj (Q : B ⥤ᵖ C) (X : B) :
    (homotopyFunctor Q).obj (HomotopyCategory.of X) =
      HomotopyCategory.of (Q.obj X) :=
  rfl

@[simp]
theorem homotopyFunctor_map_homMk (Q : B ⥤ᵖ C)
    {X Y : B} (f : X ⟶ Y) :
    (homotopyFunctor Q).map (HomotopyCategory.homMk f) =
      HomotopyCategory.homMk (Q.map f) :=
  rfl

end CategoryTheory.Pseudofunctor
