import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Product

/-!
# Products of pseudofunctors and adjoint equivalences

Mathlib equips a product of bicategories with a bicategory structure and
provides its projections, but does not currently package componentwise
products of pseudofunctors or adjoint equivalences.  This file supplies those
two constructions.  They are used by Ript's parameterized localization
examples, where one coordinate is localized while a genuinely
two-dimensional coordinate is retained unchanged.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace CategoryTheory

open Bicategory

universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃ u₄ v₄ w₄

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]
variable {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable {D : Type u₃} [Bicategory.{w₃, v₃} D]
variable {E : Type u₄} [Bicategory.{w₄, v₄} E]

namespace Pseudofunctor

/-- The componentwise cartesian product of two pseudofunctors. -/
@[simps]
def prod (F : B ⥤ᵖ C) (G : D ⥤ᵖ E) : (B × D) ⥤ᵖ (C × E) where
  obj X := (F.obj X.1, G.obj X.2)
  map f := (F.map f.1, G.map f.2)
  map₂ η := (F.map₂ η.1, G.map₂ η.2)
  mapId X := Iso.prod (F.mapId X.1) (G.mapId X.2)
  mapComp f g := Iso.prod (F.mapComp f.1 g.1) (G.mapComp f.2 g.2)
  map₂_id f := by apply Prod.ext <;> simp
  map₂_comp η θ := by apply Prod.ext <;> simp
  map₂_whisker_left f g h η := by apply Prod.ext <;> simp
  map₂_whisker_right η h := by apply Prod.ext <;> simp
  map₂_associator f g h := by apply Prod.ext <;> simp
  map₂_left_unitor f := by apply Prod.ext <;> simp
  map₂_right_unitor f := by apply Prod.ext <;> simp

end Pseudofunctor

namespace Bicategory.Equivalence

/-- The componentwise cartesian product of two adjoint equivalences. -/
def prod {X Y : B} {X' Y' : D} (e : X ≌ Y) (e' : X' ≌ Y') :
    (X, X') ≌ (Y, Y') :=
  Bicategory.Equivalence.mkOfAdjointifyCounit
    (f := (e.hom, e'.hom)) (g := (e.inv, e'.inv))
    (Iso.prod e.unit e'.unit) (Iso.prod e.counit e'.counit)

@[simp]
theorem prod_hom {X Y : B} {X' Y' : D} (e : X ≌ Y) (e' : X' ≌ Y') :
    (prod e e').hom = (e.hom, e'.hom) :=
  rfl

end Bicategory.Equivalence

end CategoryTheory
