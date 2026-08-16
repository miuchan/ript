import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# The homotopy category of a bicategory

This file constructs the ordinary category obtained from a bicategory by
identifying parallel 1-morphisms whenever they are related by an invertible
2-morphism.  Composition descends because whiskering preserves
2-isomorphisms; the bicategorical unitors and associator become the ordinary
category laws after quotienting.

The construction deliberately retains the objects of the bicategory.  Only
the local categories of 1-morphisms are truncated to their isomorphism
classes.  It is therefore a homotopy 1-category, not a bicategorical or
`(∞,1)`-categorical localization.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace CategoryTheory.Bicategory

open CategoryTheory

universe u v w

/-- The homotopy 1-category of a bicategory has the same objects as the
bicategory and 1-morphisms modulo invertible 2-morphisms. -/
@[ext]
structure HomotopyCategory (B : Type u) where
  /-- The underlying bicategory object. -/
  as : B

namespace HomotopyCategory

variable {B : Type u} [Bicategory.{w, v} B]

/-- Regard a bicategory object as an object of its homotopy category. -/
def of (X : B) : HomotopyCategory B :=
  ⟨X⟩

private theorem comp_respects {X Y Z : B} (f f' : X ⟶ Y)
    (hf : IsIsomorphic f f') (g g' : Y ⟶ Z) (hg : IsIsomorphic g g') :
    IsIsomorphic (f ≫ g) (f' ≫ g') := by
  obtain ⟨ef⟩ := hf
  obtain ⟨eg⟩ := hg
  exact ⟨whiskerRightIso ef g ≪≫ whiskerLeftIso f' eg⟩

/-- Quotienting each local hom-category by 2-isomorphism turns the weak
bicategorical laws into strict categorical laws. -/
instance category : Category.{v} (HomotopyCategory B) where
  Hom X Y := Quotient (isIsomorphicSetoid (X.as ⟶ Y.as))
  id X := ⟦𝟙 X.as⟧
  comp := Quotient.map₂ (fun f g ↦ f ≫ g) comp_respects
  id_comp := by
    rintro X Y ⟨f⟩
    exact Quotient.sound ⟨λ_ f⟩
  comp_id := by
    rintro X Y ⟨f⟩
    exact Quotient.sound ⟨ρ_ f⟩
  assoc := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact Quotient.sound ⟨α_ f g h⟩

/-- The quotient class of a 1-morphism. -/
def homMk {X Y : B} (f : X ⟶ Y) : of X ⟶ of Y :=
  Quotient.mk (isIsomorphicSetoid (X ⟶ Y)) f

@[simp]
theorem homMk_id (X : B) : homMk (𝟙 X) = 𝟙 (of X) :=
  rfl

@[simp]
theorem homMk_comp {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homMk (f ≫ g) = homMk f ≫ homMk g :=
  rfl

/-- Two represented 1-morphisms agree precisely when an invertible 2-cell
relates them. -/
theorem homMk_eq_iff {X Y : B} (f g : X ⟶ Y) :
    homMk f = homMk g ↔ Nonempty (f ≅ g) :=
  Quotient.eq

/-- A bicategorical equivalence becomes an ordinary isomorphism after passing
to the homotopy category. -/
def isoOfEquivalence {X Y : B} (e : X ≌ Y) : of X ≅ of Y where
  hom := homMk e.hom
  inv := homMk e.inv
  hom_inv_id := (homMk_eq_iff _ _).2 ⟨e.unit.symm⟩
  inv_hom_id := (homMk_eq_iff _ _).2 ⟨e.counit⟩

@[simp]
theorem isoOfEquivalence_hom {X Y : B} (e : X ≌ Y) :
    (isoOfEquivalence e).hom = homMk e.hom :=
  rfl

@[simp]
theorem isoOfEquivalence_inv {X Y : B} (e : X ≌ Y) :
    (isoOfEquivalence e).inv = homMk e.inv :=
  rfl

/-- If the class of a represented 1-morphism is invertible in the homotopy
category, then that 1-morphism is a bicategorical equivalence.  A
representative for the inverse class is chosen, and the two inverse equations
decode to invertible 2-cells. -/
noncomputable def equivalenceOfIsIso {X Y : B} (f : X ⟶ Y)
    [IsIso (homMk f)] : X ≌ Y := by
  let g : Y ⟶ X := Quotient.out (inv (homMk f))
  have hg : homMk g = inv (homMk f) :=
    Quotient.out_eq _
  have hunit : Nonempty (𝟙 X ≅ f ≫ g) := by
    apply (homMk_eq_iff (𝟙 X) (f ≫ g)).1
    rw [homMk_comp, hg, IsIso.hom_inv_id]
    rfl
  have hcounit : Nonempty (g ≫ f ≅ 𝟙 Y) := by
    apply (homMk_eq_iff (g ≫ f) (𝟙 Y)).1
    rw [homMk_comp, hg, IsIso.inv_hom_id]
    rfl
  exact Equivalence.mkOfAdjointifyCounit
    (Classical.choice hunit) (Classical.choice hcounit)

@[simp]
theorem equivalenceOfIsIso_hom {X Y : B} (f : X ⟶ Y)
    [IsIso (homMk f)] : (equivalenceOfIsIso f).hom = f :=
  rfl

end HomotopyCategory

end CategoryTheory.Bicategory
