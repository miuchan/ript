import Mathlib.CategoryTheory.MorphismProperty.Composition
import Ript.ForMathlib.CategoryTheory.Bicategory.HomotopyCategory

/-!
# Properties of 1-morphisms in a bicategory

This file provides the small amount of marked-bicategory infrastructure needed
to compare a property of bicategorical 1-morphisms with a property in the
ordinary homotopy category.  A raw property need not be invariant under
invertible 2-cells, so `saturate` makes that closure explicit.

The construction `toHomotopy` then marks a quotient class when it has a marked
representative.  Its value on a represented 1-morphism is exactly the
2-isomorphism saturation of the original property.  This is a bridge to an
ordinary Gabriel--Zisman localization; it is not itself a bicategorical
localization and it retains no noninvertible 2-cells.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace CategoryTheory.Bicategory

open CategoryTheory

universe u v w

/-- A property of 1-morphisms in a bicategory. -/
def MorphismProperty (B : Type u) [Bicategory.{w, v} B] :=
  ∀ ⦃X Y : B⦄ (_ : X ⟶ Y), Prop

namespace MorphismProperty

variable {B : Type u} [Bicategory.{w, v} B]

/-- A bicategorical morphism property contains all identity 1-morphisms. -/
class ContainsIdentities (W : MorphismProperty B) : Prop where
  /-- Every identity 1-morphism has the property. -/
  id_mem (X : B) : W (𝟙 X)

/-- A bicategorical morphism property is closed under composition of
1-morphisms. -/
class IsStableUnderComposition (W : MorphismProperty B) : Prop where
  /-- Composites of marked 1-morphisms are marked. -/
  comp_mem {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    W f → W g → W (f ≫ g)

/-- A bicategorical morphism property is multiplicative when it contains
identities and is closed under composition. -/
class IsMultiplicative (W : MorphismProperty B) : Prop
    extends ContainsIdentities W, IsStableUnderComposition W

/-- A property respects invertible 2-cells when it can be transported across
an isomorphism in every local hom-category. -/
class RespectsIso (W : MorphismProperty B) : Prop where
  /-- Transport membership along an invertible 2-cell. -/
  of_iso {X Y : B} {f g : X ⟶ Y} (e : f ≅ g) : W f → W g

namespace RespectsIso

/-- Membership in an isomorphism-invariant property is equivalent on the two
ends of an invertible 2-cell. -/
theorem iff_of_iso (W : MorphismProperty B) [RespectsIso W]
    {X Y : B} {f g : X ⟶ Y} (e : f ≅ g) : W f ↔ W g :=
  ⟨RespectsIso.of_iso e, RespectsIso.of_iso e.symm⟩

end RespectsIso

/-- The closure of a property of 1-morphisms under invertible 2-cells. -/
def saturate (W : MorphismProperty B) : MorphismProperty B :=
  fun {X Y} f ↦ ∃ g : X ⟶ Y, W g ∧ Nonempty (g ≅ f)

/-- Every marked 1-morphism belongs to the saturation. -/
theorem mem_saturate (W : MorphismProperty B) {X Y : B} {f : X ⟶ Y}
    (hf : W f) : W.saturate f :=
  ⟨f, hf, ⟨Iso.refl f⟩⟩

/-- Saturation is invariant under invertible 2-cells, whether or not the
original property is. -/
instance saturate_respectsIso (W : MorphismProperty B) : RespectsIso W.saturate where
  of_iso e := by
    rintro ⟨g, hg, ⟨i⟩⟩
    exact ⟨g, hg, ⟨i ≪≫ e⟩⟩

/-- Saturation does nothing to a property that already respects invertible
2-cells. -/
theorem saturate_iff (W : MorphismProperty B) [RespectsIso W]
    {X Y : B} (f : X ⟶ Y) : W.saturate f ↔ W f := by
  constructor
  · rintro ⟨g, hg, ⟨e⟩⟩
    exact RespectsIso.of_iso e hg
  · exact W.mem_saturate

/-- The 2-isomorphism saturation of a multiplicative property is
multiplicative. -/
instance saturate_isMultiplicative (W : MorphismProperty B) [IsMultiplicative W] :
    IsMultiplicative W.saturate where
  id_mem X := W.mem_saturate (ContainsIdentities.id_mem X)
  comp_mem f g hf hg := by
    obtain ⟨f', hf', ⟨ef⟩⟩ := hf
    obtain ⟨g', hg', ⟨eg⟩⟩ := hg
    exact ⟨f' ≫ g', IsStableUnderComposition.comp_mem f' g' hf' hg',
      ⟨whiskerRightIso ef g' ≪≫ whiskerLeftIso f eg⟩⟩

/-- A property of bicategorical 1-morphisms descends to the ordinary homotopy
category by asking for a marked representative of a quotient class. -/
def toHomotopy (W : MorphismProperty B) :
    CategoryTheory.MorphismProperty (HomotopyCategory B) :=
  fun X Y q ↦ ∃ f : X.as ⟶ Y.as,
    W f ∧ HomotopyCategory.homMk f = q

/-- A represented arrow is marked after descent precisely when the original
arrow belongs to the 2-isomorphism saturation. -/
theorem toHomotopy_homMk_iff (W : MorphismProperty B)
    {X Y : B} (f : X ⟶ Y) :
    W.toHomotopy (HomotopyCategory.homMk f) ↔ W.saturate f := by
  constructor
  · rintro ⟨g, hg, hgf⟩
    exact ⟨g, hg, (HomotopyCategory.homMk_eq_iff g f).1 hgf⟩
  · rintro ⟨g, hg, hgf⟩
    exact ⟨g, hg, (HomotopyCategory.homMk_eq_iff g f).2 hgf⟩

/-- If the original property already respects invertible 2-cells, descent
preserves membership on every represented arrow. -/
theorem toHomotopy_homMk_iff_of_respectsIso (W : MorphismProperty B)
    [RespectsIso W] {X Y : B} (f : X ⟶ Y) :
    W.toHomotopy (HomotopyCategory.homMk f) ↔ W f :=
  (W.toHomotopy_homMk_iff f).trans (W.saturate_iff f)

/-- Descent sends multiplicative bicategorical markings to multiplicative
ordinary morphism properties. -/
instance toHomotopy_isMultiplicative (W : MorphismProperty B) [IsMultiplicative W] :
    CategoryTheory.MorphismProperty.IsMultiplicative W.toHomotopy where
  id_mem X :=
    ⟨𝟙 X.as, ContainsIdentities.id_mem X.as, HomotopyCategory.homMk_id X.as⟩
  comp_mem f g hf hg := by
    obtain ⟨f', hf', rfl⟩ := hf
    obtain ⟨g', hg', rfl⟩ := hg
    exact ⟨f' ≫ g', IsStableUnderComposition.comp_mem f' g' hf' hg', rfl⟩

end MorphismProperty

end CategoryTheory.Bicategory
