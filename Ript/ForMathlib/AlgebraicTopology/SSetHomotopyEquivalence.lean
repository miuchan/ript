import Ript.ForMathlib.AlgebraicTopology.NerveHomotopy

/-!
# Explicit simplicial homotopy-equivalence witnesses

The pinned Mathlib toolchain does not expose a completed weak-equivalence
structure for simplicial sets. This file records stronger concrete data: a
displayed inverse together with simplicial homotopies for both composites.

The construction is deliberately independent of a model-category API. It
also proves that the nerve map of every equivalence of categories carries
such a witness and that witnesses transport across displayed source and
target isomorphisms.
-/

set_option autoImplicit false

open CategoryTheory

noncomputable section

universe u

namespace SSet

variable {W X Y Z : SSet.{u}}

namespace Homotopy

/-- Equal simplicial maps are simplicially homotopic. -/
def ofEq {f g : X ⟶ Y} (h : f = g) : Homotopy f g := by
  subst g
  exact RelativeMorphism.Homotopy.refl
    (RelativeMorphism.botEquiv.symm f)

/-- Change both displayed endpoints of a simplicial homotopy along equalities. -/
def congr {f g f' g' : X ⟶ Y} (H : Homotopy f g)
    (hf : f' = f) (hg : g' = g) : Homotopy f' g' := by
  subst f'
  subst g'
  exact H

/-- Postcomposition preserves simplicial homotopies. -/
def postcomp {f g : X ⟶ Y} (H : Homotopy f g) (k : Y ⟶ Z) :
    Homotopy (f ≫ k) (g ≫ k) :=
  RelativeMorphism.Homotopy.postcomp H
    (RelativeMorphism.botEquiv.symm k) rfl

/-- Precomposition preserves simplicial homotopies. -/
def precomp {f g : X ⟶ Y} (H : Homotopy f g) (k : W ⟶ X) :
    Homotopy (k ≫ f) (k ≫ g) :=
  RelativeMorphism.Homotopy.precomp H
    (RelativeMorphism.botEquiv.symm k) rfl

end Homotopy

/-- Strong project-local evidence that a simplicial map is a weak
equivalence: an explicit inverse and simplicial homotopies for both composite
maps. -/
structure HomotopyEquivalenceWitness (f : X ⟶ Y) where
  /-- Displayed homotopy inverse. -/
  inverse : Y ⟶ X
  /-- The forward map followed by the inverse is homotopic to the identity. -/
  homInv : Homotopy (f ≫ inverse) (𝟙 X)
  /-- The inverse followed by the forward map is homotopic to the identity. -/
  invHom : Homotopy (inverse ≫ f) (𝟙 Y)

namespace HomotopyEquivalenceWitness

/-- An isomorphism of simplicial sets is a simplicial homotopy equivalence. -/
def ofIso (e : X ≅ Y) : HomotopyEquivalenceWitness e.hom where
  inverse := e.inv
  homInv := Homotopy.ofEq e.hom_inv_id
  invHom := Homotopy.ofEq e.inv_hom_id

/-- The nerve map induced by an equivalence of categories is a simplicial
homotopy equivalence. -/
def ofCategoryEquivalence {C D : Type u} [Category.{u} C] [Category.{u} D]
    (e : C ≌ D) :
    HomotopyEquivalenceWitness (CategoryTheory.nerveMap e.functor) where
  inverse := CategoryTheory.nerveMap e.inverse
  homInv := by
    change Homotopy
      (CategoryTheory.nerveMap (e.functor ⋙ e.inverse))
      (CategoryTheory.nerveMap (𝟭 C))
    exact CategoryTheory.NerveHomotopy.ofNatTrans e.unitIso.inv
  invHom := by
    change Homotopy
      (CategoryTheory.nerveMap (e.inverse ⋙ e.functor))
      (CategoryTheory.nerveMap (𝟭 D))
    exact CategoryTheory.NerveHomotopy.ofNatTrans e.counitIso.hom

/-- Transport a simplicial homotopy equivalence across displayed source and
target isomorphisms. The square is oriented exactly as a naturality square
for the displayed forward map. -/
def transportIso {X' Y' : SSet.{u}} {f : X ⟶ Y}
    (h : HomotopyEquivalenceWitness f)
    (sourceIso : X' ≅ X) (targetIso : Y' ≅ Y)
    (f' : X' ⟶ Y')
    (square : f' ≫ targetIso.hom = sourceIso.hom ≫ f) :
    HomotopyEquivalenceWitness f' where
  inverse := targetIso.hom ≫ h.inverse ≫ sourceIso.inv
  homInv := by
    have H := (h.homInv.precomp sourceIso.hom).postcomp sourceIso.inv
    have H' : Homotopy
        (sourceIso.hom ≫ f ≫ h.inverse ≫ sourceIso.inv)
        (𝟙 X') := by
      simpa only [Category.assoc, Category.comp_id,
        Iso.hom_inv_id] using H
    refine Homotopy.congr H' ?_ rfl
    rw [← Category.assoc, square]
    simp only [Category.assoc]
  invHom := by
    have inverseSquare : sourceIso.inv ≫ f' = f ≫ targetIso.inv := by
      rw [← cancel_mono targetIso.hom]
      simp only [Category.assoc, square, Iso.inv_hom_id_assoc,
        Iso.inv_hom_id, Category.comp_id]
    have H := (h.invHom.precomp targetIso.hom).postcomp targetIso.inv
    simpa only [Category.assoc, inverseSquare, Category.comp_id,
      Iso.hom_inv_id] using H

end HomotopyEquivalenceWitness

end SSet
