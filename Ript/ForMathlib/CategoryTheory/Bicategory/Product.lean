import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
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
open scoped Pseudofunctor.StrongTrans

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

/-- Pair two pseudofunctors with a common source into the product of their
targets. -/
@[simps]
def pair (F : B ⥤ᵖ C) (G : B ⥤ᵖ D) : B ⥤ᵖ (C × D) where
  obj X := (F.obj X, G.obj X)
  map f := (F.map f, G.map f)
  map₂ η := (F.map₂ η, G.map₂ η)
  mapId X := Iso.prod (F.mapId X) (G.mapId X)
  mapComp f g := Iso.prod (F.mapComp f g) (G.mapComp f g)
  map₂_id f := by
    apply Prod.ext
    · exact F.map₂_id f
    · exact G.map₂_id f
  map₂_comp η θ := by
    apply Prod.ext
    · exact F.map₂_comp η θ
    · exact G.map₂_comp η θ
  map₂_whisker_left f g h η := by apply Prod.ext <;> simp
  map₂_whisker_right η h := by apply Prod.ext <;> simp
  map₂_associator f g h := by apply Prod.ext <;> simp
  map₂_left_unitor f := by apply Prod.ext <;> simp
  map₂_right_unitor f := by apply Prod.ext <;> simp

namespace StrongTrans

variable {F F' : B ⥤ᵖ C} {G G' : B ⥤ᵖ D}

/-- Pair strong transformations with a common source into a strong
transformation between paired pseudofunctors. -/
@[simps]
def pair (η : F ⟶ F') (θ : G ⟶ G') : F.pair G ⟶ F'.pair G' where
  app X := (η.app X, θ.app X)
  naturality f := Iso.prod (η.naturality f) (θ.naturality f)
  naturality_naturality μ := by
    apply Prod.ext
    · exact η.naturality_naturality μ
    · exact θ.naturality_naturality μ
  naturality_id X := by
    apply Prod.ext
    · exact η.naturality_id X
    · exact θ.naturality_id X
  naturality_comp f g := by
    apply Prod.ext
    · exact η.naturality_comp f g
    · exact θ.naturality_comp f g

/-- Evaluate an isomorphism of strong transformations at one source
object. -/
def isoApp {η θ : F ⟶ F'} (e : η ≅ θ) (X : B) : η.app X ≅ θ.app X where
  hom := e.hom.as.app X
  inv := e.inv.as.app X
  hom_inv_id := congrArg (fun k => k.as.app X) e.hom_inv_id
  inv_hom_id := congrArg (fun k => k.as.app X) e.inv_hom_id

end StrongTrans

/-- Pair adjoint equivalences between pseudofunctors with a common source. -/
noncomputable def pairEquivalence {F F' : B ⥤ᵖ C} {G G' : B ⥤ᵖ D}
    (e : F ≌ F') (e' : G ≌ G') : F.pair G ≌ F'.pair G' :=
  Bicategory.Equivalence.mkOfAdjointifyCounit
    (Pseudofunctor.StrongTrans.isoMk
      (η := 𝟙 (F.pair G))
      (θ := e.hom.pair e'.hom ≫ e.inv.pair e'.inv)
      (fun X => Iso.prod
        (Pseudofunctor.StrongTrans.isoApp e.unit X)
        (Pseudofunctor.StrongTrans.isoApp e'.unit X))
      (by
        intro a b f
        apply Prod.ext
        · exact e.unit.hom.as.naturality f
        · exact e'.unit.hom.as.naturality f))
    (Pseudofunctor.StrongTrans.isoMk
      (η := e.inv.pair e'.inv ≫ e.hom.pair e'.hom)
      (θ := 𝟙 (F'.pair G'))
      (fun X => Iso.prod
        (Pseudofunctor.StrongTrans.isoApp e.counit X)
        (Pseudofunctor.StrongTrans.isoApp e'.counit X))
      (by
        intro a b f
        apply Prod.ext
        · exact e.counit.hom.as.naturality f
        · exact e'.counit.hom.as.naturality f))

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

namespace Pseudofunctor

/-- Postcompose the strict first projection from a product bicategory with a
pseudofunctor.  This packages pseudofunctors which depend only on the first
coordinate. -/
noncomputable def fstComp (D : Type u₃) [Bicategory.{w₃, v₃} D]
    (H : B ⥤ᵖ C) : (B × D) ⥤ᵖ C :=
  (Bicategory.Prod.fst B D).toPseudofunctor.comp H

/-- Postcompose the strict second projection from a product bicategory with a
pseudofunctor.  This packages pseudofunctors which depend only on the retained
second coordinate. -/
noncomputable def sndComp (B : Type u₁) [Bicategory.{w₁, v₁} B]
    (H : D ⥤ᵖ E) : (B × D) ⥤ᵖ E :=
  (Bicategory.Prod.snd B D).toPseudofunctor.comp H

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The forward strong transformation exhibiting that a product
pseudofunctor of the form `Q × id` leaves every second-coordinate
pseudofunctor unchanged up to equivalence. -/
noncomputable def prodIdSndCompHom (Q : B ⥤ᵖ C) (H : D ⥤ᵖ E) :
    (Q.prod (Pseudofunctor.id D)).comp (sndComp C H) ⟶
      sndComp B H where
  app X := 𝟙 (H.obj X.2)
  naturality f := (ρ_ (H.map f.2)) ≪≫ (λ_ (H.map f.2)).symm
  naturality_naturality η := by simp [sndComp]
  naturality_id X := by simp [sndComp]
  naturality_comp f g := by simp [sndComp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse strong transformation for `prodIdSndCompHom`. -/
noncomputable def prodIdSndCompInv (Q : B ⥤ᵖ C) (H : D ⥤ᵖ E) :
    sndComp B H ⟶
      (Q.prod (Pseudofunctor.id D)).comp (sndComp C H) where
  app X := 𝟙 (H.obj X.2)
  naturality f := (ρ_ (H.map f.2)) ≪≫ (λ_ (H.map f.2)).symm
  naturality_naturality η := by simp [sndComp]
  naturality_id X := by simp [sndComp]
  naturality_comp f g := by simp [sndComp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A product pseudofunctor `Q × id` preserves every pseudofunctor depending
only on the second coordinate, up to an adjoint equivalence of
pseudofunctors. -/
noncomputable def prodIdSndCompEquivalence (Q : B ⥤ᵖ C) (H : D ⥤ᵖ E) :
    (Q.prod (Pseudofunctor.id D)).comp (sndComp C H) ≌
      sndComp B H :=
  Bicategory.Equivalence.mkOfAdjointifyCounit
    (Pseudofunctor.StrongTrans.isoMk
      (η := 𝟙 ((Q.prod (Pseudofunctor.id D)).comp (sndComp C H)))
      (θ := prodIdSndCompHom Q H ≫ prodIdSndCompInv Q H)
      (fun X => (ρ_ (𝟙 (H.obj X.2))).symm)
      (by
        intro a b f
        dsimp [prodIdSndCompHom, prodIdSndCompInv, sndComp]
        bicategory))
    (Pseudofunctor.StrongTrans.isoMk
      (η := prodIdSndCompInv Q H ≫ prodIdSndCompHom Q H)
      (θ := 𝟙 (sndComp B H))
      (fun X => ρ_ (𝟙 (H.obj X.2)))
      (by
        intro a b f
        dsimp [prodIdSndCompHom, prodIdSndCompInv, sndComp]
        bicategory))

end Pseudofunctor

end CategoryTheory
