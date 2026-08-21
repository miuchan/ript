import Ript.Higher.LocalizationCompleteSegal
import Mathlib.CategoryTheory.Category.ULift
/-!
# Universe-lifted full local nerves for bicategorical localizations

The ordinary categorical nerve requires source and target categories to share
universe levels. Presented bicategorical localizations generally enlarge their
local hom universes, so their exact local nerve maps cannot use that interface
directly.

This module replaces both local categories by equivalent `AsSmall` categories
in one common universe. It constructs the induced nerve maps, proves exact
1-cell and 2-cell action, transports compositor natural isomorphisms, and
retains the resulting genuine simplicial homotopies. The construction works for
source, localization target, and semantic test targets in independent
universes. Unit and compositor homotopies retain exact associator and
left/right-unitor edge coherence.
-/


set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Higher.UniverseLiftedNerve

open CategoryTheory
open Opposite Simplicial

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- A functor between common-universe small replacements. -/
def commonAsSmallFunctor (F : C ⥤ D) :
    AsSmall.{max u₂ v₂} C ⥤ AsSmall.{max u₁ v₁} D :=
  AsSmall.down ⋙ F ⋙ AsSmall.up

/-- The nerve map of a functor after lifting both categories to a common
object-and-morphism universe. -/
def commonNerveMap (F : C ⥤ D) :
    CategoryTheory.nerve (AsSmall.{max u₂ v₂} C) ⟶
      CategoryTheory.nerve (AsSmall.{max u₁ v₁} D) :=
  CategoryTheory.nerveMap (commonAsSmallFunctor F)

@[simp]
theorem commonNerveMap_vertex (F : C ⥤ D) (X : C) :
    (commonNerveMap F).app (op ⦋0⦌)
        (ComposableArrows.mk₀
          ((AsSmall.up : C ⥤ AsSmall.{max u₂ v₂} C).obj X)) =
      ComposableArrows.mk₀
        ((AsSmall.up : D ⥤ AsSmall.{max u₁ v₁} D).obj (F.obj X)) := by
  apply ComposableArrows.ext₀
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem commonNerveMap_edge (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    (commonNerveMap F).app (op ⦋1⦌)
        (ComposableArrows.mk₁
          ((AsSmall.up : C ⥤ AsSmall.{max u₂ v₂} C).map f)) =
      ComposableArrows.mk₁
        ((AsSmall.up : D ⥤ AsSmall.{max u₁ v₁} D).map (F.map f)) := by
  unfold commonNerveMap
  rw [CategoryTheory.nerveMap_app_mk₁]
  rfl

/-- Exact action of a common-universe nerve map on a canonical
2-simplex of two composable arrows. -/
@[simp]
theorem commonNerveMap_twoSimplex (F : C ⥤ D)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (commonNerveMap F).app (op ⦋2⦌)
        (ComposableArrows.mk₂
          ((AsSmall.up : C ⥤ AsSmall.{max u₂ v₂} C).map f)
          ((AsSmall.up : C ⥤ AsSmall.{max u₂ v₂} C).map g)) =
      ComposableArrows.mk₂
        ((AsSmall.up : D ⥤ AsSmall.{max u₁ v₁} D).map (F.map f))
        ((AsSmall.up : D ⥤ AsSmall.{max u₁ v₁} D).map (F.map g)) := by
  apply CategoryTheory.nerveMap_app_mk₂

variable {F G : C ⥤ D}

/-- A natural transformation transported to the common-universe small
replacements. -/
def commonAsSmallNatTrans (α : F ⟶ G) :
    commonAsSmallFunctor F ⟶ commonAsSmallFunctor G :=
  Functor.whiskerRight (Functor.whiskerLeft AsSmall.down α) AsSmall.up

/-- A natural transformation between arbitrary-universe categories induces
a homotopy between their common-universe nerve maps. -/
noncomputable def commonNerveHomotopy (α : F ⟶ G) :
    SSet.Homotopy (commonNerveMap F) (commonNerveMap G) :=
  CategoryTheory.NerveHomotopy.ofNatTrans (commonAsSmallNatTrans α)

open CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory

universe u₃ v₃ w₃ u₄ v₄ w₄

variable {B : Type u₃} [Bicategory.{w₃, v₃} B]
variable {E : Type u₄} [Bicategory.{w₄, v₄} E]
variable (Q : B ⥤ᵖ E)

/-- Source local hom-category lifted to the common local universe shared with
the target bicategory. -/
abbrev CommonSourceHom (_Q : B ⥤ᵖ E) (X Y : B) :=
  AsSmall.{max v₄ w₄} (X ⟶ Y)

/-- Target local hom-category lifted to the same common local universe. -/
abbrev CommonTargetHom (X Y : B) :=
  AsSmall.{max v₃ w₃} (Q.obj X ⟶ Q.obj Y)

/-- Full local mapping nerve after common-universe replacement. -/
abbrev CommonLocalMappingNerve (X Y : B) :=
  CategoryTheory.nerve (CommonSourceHom (_Q := Q) X Y)

/-- Target full local mapping nerve in the same simplicial-set universe. -/
abbrev CommonTargetMappingNerve (X Y : B) :=
  CategoryTheory.nerve (CommonTargetHom (Q := Q) X Y)

/-- Common-universe local nerve map induced by an arbitrary pseudofunctor. -/
def commonLocalMap (X Y : B) :
    CommonLocalMappingNerve (Q := Q) X Y ⟶
      CommonTargetMappingNerve (Q := Q) X Y :=
  commonNerveMap (Q.mapFunctor X Y)

@[simp]
theorem commonLocalMap_vertex {X Y : B} (f : X ⟶ Y) :
    (commonLocalMap Q X Y).app (op ⦋0⦌)
        (ComposableArrows.mk₀ ((AsSmall.up :
          (X ⟶ Y) ⥤ CommonSourceHom (_Q := Q) X Y).obj f)) =
      ComposableArrows.mk₀ ((AsSmall.up :
        (Q.obj X ⟶ Q.obj Y) ⥤
          CommonTargetHom (Q := Q) X Y).obj (Q.map f)) :=
  commonNerveMap_vertex (Q.mapFunctor X Y) f

@[simp]
theorem commonLocalMap_twoCell {X Y : B} {f g : X ⟶ Y} (α : f ⟶ g) :
    (commonLocalMap Q X Y).app (op ⦋1⦌)
        (ComposableArrows.mk₁ ((AsSmall.up :
          (X ⟶ Y) ⥤ CommonSourceHom (_Q := Q) X Y).map α)) =
      ComposableArrows.mk₁ ((AsSmall.up :
        (Q.obj X ⟶ Q.obj Y) ⥤
          CommonTargetHom (Q := Q) X Y).map (Q.map₂ α)) :=
  commonNerveMap_edge (Q.mapFunctor X Y) α

/-- Exact action of the lifted local comparison on the canonical 2-simplex
of two vertically composable source 2-cells. -/
@[simp]
theorem commonLocalMap_twoSimplex
    {X Y : B} {f g h : X ⟶ Y} (α : f ⟶ g) (β : g ⟶ h) :
    (commonLocalMap Q X Y).app (op ⦋2⦌)
        (ComposableArrows.mk₂
          ((AsSmall.up :
            (X ⟶ Y) ⥤ CommonSourceHom (_Q := Q) X Y).map α)
          ((AsSmall.up :
            (X ⟶ Y) ⥤ CommonSourceHom (_Q := Q) X Y).map β)) =
      ComposableArrows.mk₂
        ((AsSmall.up :
          (Q.obj X ⟶ Q.obj Y) ⥤ CommonTargetHom (Q := Q) X Y).map
            (Q.map₂ α))
        ((AsSmall.up :
          (Q.obj X ⟶ Q.obj Y) ⥤ CommonTargetHom (Q := Q) X Y).map
            (Q.map₂ β)) :=
  commonNerveMap_twoSimplex (Q.mapFunctor X Y) α β

/-- Arbitrary-universe constant diagram selecting the image of a source
identity. -/
def mappedIdentityFunctor (X : B) :
    (X ⟶ X) ⥤ (Q.obj X ⟶ Q.obj X) :=
  (Functor.const (X ⟶ X)).obj (Q.map (𝟙 X))

/-- Arbitrary-universe constant diagram selecting the target identity. -/
def targetIdentityFunctor (X : B) :
    (X ⟶ X) ⥤ (Q.obj X ⟶ Q.obj X) :=
  (Functor.const (X ⟶ X)).obj (𝟙 (Q.obj X))

/-- Arbitrary-universe pseudofunctor unit natural isomorphism. -/
noncomputable def identityComparisonNatIso (X : B) :
    mappedIdentityFunctor Q X ≅ targetIdentityFunctor Q X :=
  (Functor.const (X ⟶ X)).mapIso (Q.mapId X)

/-- Common-universe form of the pseudofunctor unit natural isomorphism. -/
noncomputable def commonIdentityComparisonNatIso (X : B) :
    commonAsSmallFunctor
        (mappedIdentityFunctor Q X) ≅
      commonAsSmallFunctor
        (targetIdentityFunctor Q X) :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft AsSmall.down
      (identityComparisonNatIso Q X))
    AsSmall.up

/-- Genuine common-universe simplicial homotopy induced by the pseudofunctor
unit constraint. -/
noncomputable def commonIdentityComparisonHomotopy (X : B) :
    SSet.Homotopy
      (commonNerveMap
        (mappedIdentityFunctor Q X))
      (commonNerveMap
        (targetIdentityFunctor Q X)) :=
  CategoryTheory.NerveHomotopy.ofNatTrans
    (commonIdentityComparisonNatIso Q X).hom

/-- Horizontal composition for an arbitrary bicategory, without any universe
balance assumption. -/
def horizontalCompositionFunctor (X Y Z : B) :
    ((X ⟶ Y) × (Y ⟶ Z)) ⥤ (X ⟶ Z) where
  obj pair := pair.1 ≫ pair.2
  map := @fun first second transformation =>
    first.1 ◁ transformation.2 ≫ transformation.1 ▷ second.2
  map_id pair := by simp
  map_comp := @fun first second third firstTransformation
      secondTransformation => by
    change
      first.1 ◁ (firstTransformation.2 ≫ secondTransformation.2) ≫
          (firstTransformation.1 ≫ secondTransformation.1) ▷ third.2 =
        (first.1 ◁ firstTransformation.2 ≫
            firstTransformation.1 ▷ second.2) ≫
          (second.1 ◁ secondTransformation.2 ≫
            secondTransformation.1 ▷ third.2)
    symm
    simp only [Category.assoc]
    rw [← whisker_exchange_assoc firstTransformation.1 secondTransformation.2,
      ← whiskerLeft_comp_assoc, ← comp_whiskerRight]

/-- Simultaneous horizontal composition of two arbitrary 2-cells. -/
def horizontalTwoCell
    {X Y Z : B} {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z}
    (α : f₀ ⟶ f₁) (β : g₀ ⟶ g₁) :
    f₀ ≫ g₀ ⟶ f₁ ≫ g₁ :=
  f₀ ◁ β ≫ α ▷ g₁

/-- Interchange for simultaneous horizontal composition of vertically
composable 2-cell pairs. -/
theorem horizontalTwoCell_comp
    {X Y Z : B}
    {f₀ f₁ f₂ : X ⟶ Y} {g₀ g₁ g₂ : Y ⟶ Z}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) :
    horizontalTwoCell (α₀ ≫ α₁) (β₀ ≫ β₁) =
      horizontalTwoCell α₀ β₀ ≫ horizontalTwoCell α₁ β₁ := by
  exact (horizontalCompositionFunctor X Y Z).map_comp
    (show (f₀, g₀) ⟶ (f₁, g₁) from ⟨α₀, β₀⟩)
    (show (f₁, g₁) ⟶ (f₂, g₂) from ⟨α₁, β₁⟩)

/-- First compose in the source bicategory and then apply the
pseudofunctor. -/
def composeThenMapFunctor (X Y Z : B) :
    ((X ⟶ Y) × (Y ⟶ Z)) ⥤ (Q.obj X ⟶ Q.obj Z) :=
  horizontalCompositionFunctor X Y Z ⋙ Q.mapFunctor X Z

/-- First apply the pseudofunctor locally and then compose in the target
bicategory. -/
def mapThenComposeFunctor (X Y Z : B) :
    ((X ⟶ Y) × (Y ⟶ Z)) ⥤ (Q.obj X ⟶ Q.obj Z) :=
  (Q.mapFunctor X Y).prod (Q.mapFunctor Y Z) ⋙
    horizontalCompositionFunctor (Q.obj X) (Q.obj Y) (Q.obj Z)

/-- The pseudofunctor compositor as a natural isomorphism between the two
raw horizontal-composition functors. -/
noncomputable def compositionComparisonNatIso (X Y Z : B) :
    composeThenMapFunctor Q X Y Z ≅ mapThenComposeFunctor Q X Y Z :=
  NatIso.ofComponents
    (fun pair => Q.mapComp pair.1 pair.2)
    (fun {first second} transformation => by
      rcases transformation with ⟨left, right⟩
      change Q.map₂ (first.1 ◁ right ≫ left ▷ second.2) ≫
          (Q.mapComp second.1 second.2).hom =
        (Q.mapComp first.1 first.2).hom ≫
          (Q.map first.1 ◁ Q.map₂ right ≫
            Q.map₂ left ▷ Q.map second.2)
      simp only [PrelaxFunctor.map₂_comp, Category.assoc,
        Q.map₂_whisker_left, Q.map₂_whisker_right]
      simp)

/-- Naturality square of the pseudofunctor compositor at a simultaneous
horizontal pair of 2-cells. -/
def HorizontalCompositionSquare
    {X Y Z : B} {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z}
    (α : f₀ ⟶ f₁) (β : g₀ ⟶ g₁) : Prop :=
  Q.map₂ (horizontalTwoCell α β) ≫ (Q.mapComp f₁ g₁).hom =
    (Q.mapComp f₀ g₀).hom ≫
      horizontalTwoCell (Q.map₂ α) (Q.map₂ β)

/-- The compositor square commutes for arbitrary, possibly noninvertible,
2-cells in both horizontal factors. -/
theorem horizontalCompositionSquare
    {X Y Z : B} {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z}
    (α : f₀ ⟶ f₁) (β : g₀ ⟶ g₁) :
    HorizontalCompositionSquare Q α β := by
  exact (compositionComparisonNatIso Q X Y Z).hom.naturality
    (show (f₀, g₀) ⟶ (f₁, g₁) from ⟨α, β⟩)

/-- Vertical pasting of two adjacent compositor naturality squares. -/
def HorizontalCompositionPastedSquare
    {X Y Z : B}
    {f₀ f₁ f₂ : X ⟶ Y} {g₀ g₁ g₂ : Y ⟶ Z}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) : Prop :=
  (Q.map₂ (horizontalTwoCell α₀ β₀) ≫
      Q.map₂ (horizontalTwoCell α₁ β₁)) ≫
      (Q.mapComp f₂ g₂).hom =
    (Q.mapComp f₀ g₀).hom ≫
      (horizontalTwoCell (Q.map₂ α₀) (Q.map₂ β₀) ≫
        horizontalTwoCell (Q.map₂ α₁) (Q.map₂ β₁))

/-- The vertically pasted compositor rectangle commutes. -/
theorem horizontalCompositionPastedSquare
    {X Y Z : B}
    {f₀ f₁ f₂ : X ⟶ Y} {g₀ g₁ g₂ : Y ⟶ Z}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) :
    HorizontalCompositionPastedSquare Q α₀ α₁ β₀ β₁ := by
  unfold HorizontalCompositionPastedSquare
  rw [Category.assoc]
  rw [horizontalCompositionSquare Q α₁ β₁]
  rw [← Category.assoc]
  rw [horizontalCompositionSquare Q α₀ β₀]
  simp only [Category.assoc]

/-- Interchange and vertical-pasting coherence before common-universe
replacement. -/
def HorizontalCompositionPastingCoherence
    {X Y Z : B}
    {f₀ f₁ f₂ : X ⟶ Y} {g₀ g₁ g₂ : Y ⟶ Z}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) : Prop :=
  Q.map₂ (horizontalTwoCell (α₀ ≫ α₁) (β₀ ≫ β₁)) =
      Q.map₂ (horizontalTwoCell α₀ β₀) ≫
        Q.map₂ (horizontalTwoCell α₁ β₁) ∧
  horizontalTwoCell (Q.map₂ (α₀ ≫ α₁)) (Q.map₂ (β₀ ≫ β₁)) =
      horizontalTwoCell (Q.map₂ α₀) (Q.map₂ β₀) ≫
        horizontalTwoCell (Q.map₂ α₁) (Q.map₂ β₁) ∧
  HorizontalCompositionPastedSquare Q α₀ α₁ β₀ β₁

/-- Every vertically composable horizontal pair satisfies the complete
interchange-and-pasting package. -/
theorem horizontalCompositionPastingCoherence
    {X Y Z : B}
    {f₀ f₁ f₂ : X ⟶ Y} {g₀ g₁ g₂ : Y ⟶ Z}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) :
    HorizontalCompositionPastingCoherence Q α₀ α₁ β₀ β₁ := by
  refine ⟨?_, ?_, horizontalCompositionPastedSquare Q α₀ α₁ β₀ β₁⟩
  · rw [horizontalTwoCell_comp, PrelaxFunctor.map₂_comp]
  · rw [PrelaxFunctor.map₂_comp, PrelaxFunctor.map₂_comp,
      horizontalTwoCell_comp]

/-- Common-universe form of the compositor natural isomorphism. -/
noncomputable def commonCompositionComparisonNatIso (X Y Z : B) :
    commonAsSmallFunctor (composeThenMapFunctor Q X Y Z) ≅
      commonAsSmallFunctor (mapThenComposeFunctor Q X Y Z) :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft AsSmall.down
      (compositionComparisonNatIso Q X Y Z)) AsSmall.up

/-- Common-universe replacement of the product of two source local
hom-categories used by horizontal composition. -/
abbrev CommonHorizontalSource (_Q : B ⥤ᵖ E) (X Y Z : B) :=
  AsSmall.{max v₄ w₄} ((X ⟶ Y) × (Y ⟶ Z))

/-- A pair of arbitrary source 2-cells as one degree-one simplex of the
common-universe product local nerve. -/
def commonHorizontalPairEdge
    {X Y Z : B} {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z}
    (α : f₀ ⟶ f₁) (β : g₀ ⟶ g₁) :
    (CategoryTheory.nerve
      (CommonHorizontalSource (_Q := Q) X Y Z)).obj
        (op ⦋1⦌) :=
  ComposableArrows.mk₁
    ((AsSmall.up :
      ((X ⟶ Y) × (Y ⟶ Z)) ⥤
        CommonHorizontalSource (_Q := Q) X Y Z).map
      (show (f₀, g₀) ⟶ (f₁, g₁) from ⟨α, β⟩))

/-- Two vertically composable pairs of source 2-cells as the canonical
degree-two simplex of the common-universe product local nerve. -/
def commonHorizontalPairTwoSimplex
    {X Y Z : B}
    {f₀ f₁ f₂ : X ⟶ Y} {g₀ g₁ g₂ : Y ⟶ Z}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) :
    (CategoryTheory.nerve
      (CommonHorizontalSource (_Q := Q) X Y Z)).obj (op ⦋2⦌) :=
  ComposableArrows.mk₂
    ((AsSmall.up :
      ((X ⟶ Y) × (Y ⟶ Z)) ⥤
        CommonHorizontalSource (_Q := Q) X Y Z).map
      (show (f₀, g₀) ⟶ (f₁, g₁) from ⟨α₀, β₀⟩))
    ((AsSmall.up :
      ((X ⟶ Y) × (Y ⟶ Z)) ⥤
        CommonHorizontalSource (_Q := Q) X Y Z).map
      (show (f₁, g₁) ⟶ (f₂, g₂) from ⟨α₁, β₁⟩))

/-- The compose-then-map nerve sends a horizontal pair edge to the exact
lifted image of the horizontally composed source 2-cell. -/
@[simp]
theorem commonComposeThenMap_edge
    {X Y Z : B} {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z}
    (α : f₀ ⟶ f₁) (β : g₀ ⟶ g₁) :
    (commonNerveMap (composeThenMapFunctor Q X Y Z)).app
        (op ⦋1⦌) (commonHorizontalPairEdge Q α β) =
      ComposableArrows.mk₁
        ((AsSmall.up :
          (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
            (Q.map₂ (horizontalTwoCell α β))) := by
  unfold commonHorizontalPairEdge
  rw [commonNerveMap_edge]
  rfl

/-- The map-then-compose nerve sends the same pair edge to the exact lifted
horizontal composite of the two mapped 2-cells. -/
@[simp]
theorem commonMapThenCompose_edge
    {X Y Z : B} {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z}
    (α : f₀ ⟶ f₁) (β : g₀ ⟶ g₁) :
    (commonNerveMap (mapThenComposeFunctor Q X Y Z)).app
        (op ⦋1⦌) (commonHorizontalPairEdge Q α β) =
      ComposableArrows.mk₁
        ((AsSmall.up :
          (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
            (horizontalTwoCell (Q.map₂ α) (Q.map₂ β))) := by
  unfold commonHorizontalPairEdge
  rw [commonNerveMap_edge]
  rfl

/-- The compose-then-map nerve sends the canonical horizontal pair
2-simplex to the two exact mapped horizontal source 2-cells. -/
@[simp]
theorem commonComposeThenMap_twoSimplex
    {X Y Z : B}
    {f₀ f₁ f₂ : X ⟶ Y} {g₀ g₁ g₂ : Y ⟶ Z}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) :
    (commonNerveMap (composeThenMapFunctor Q X Y Z)).app
        (op ⦋2⦌)
        (commonHorizontalPairTwoSimplex Q α₀ α₁ β₀ β₁) =
      ComposableArrows.mk₂
        ((AsSmall.up :
          (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
          (Q.map₂ (horizontalTwoCell α₀ β₀)))
        ((AsSmall.up :
          (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
          (Q.map₂ (horizontalTwoCell α₁ β₁))) := by
  unfold commonHorizontalPairTwoSimplex
  rw [commonNerveMap_twoSimplex]
  rfl

/-- The map-then-compose nerve sends the same horizontal pair 2-simplex to
the two exact horizontal composites of mapped 2-cells. -/
@[simp]
theorem commonMapThenCompose_twoSimplex
    {X Y Z : B}
    {f₀ f₁ f₂ : X ⟶ Y} {g₀ g₁ g₂ : Y ⟶ Z}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) :
    (commonNerveMap (mapThenComposeFunctor Q X Y Z)).app
        (op ⦋2⦌)
        (commonHorizontalPairTwoSimplex Q α₀ α₁ β₀ β₁) =
      ComposableArrows.mk₂
        ((AsSmall.up :
          (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
          (horizontalTwoCell (Q.map₂ α₀) (Q.map₂ β₀)))
        ((AsSmall.up :
          (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
          (horizontalTwoCell (Q.map₂ α₁) (Q.map₂ β₁))) := by
  unfold commonHorizontalPairTwoSimplex
  rw [commonNerveMap_twoSimplex]
  rfl

/-- Common-universe edge equality expressing the exact diagonal of the
compositor naturality square. -/
def CommonHorizontalCompositionSquare
    {X Y Z : B} {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z}
    (α : f₀ ⟶ f₁) (β : g₀ ⟶ g₁) : Prop :=
  ComposableArrows.mk₁
      ((AsSmall.up :
        (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
          (Q.map₂ (horizontalTwoCell α β) ≫ (Q.mapComp f₁ g₁).hom)) =
    ComposableArrows.mk₁
      ((AsSmall.up :
        (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
          ((Q.mapComp f₀ g₀).hom ≫
            horizontalTwoCell (Q.map₂ α) (Q.map₂ β)))

/-- The two lifted paths around the compositor square are the same target
local-nerve edge. -/
theorem commonHorizontalCompositionSquare
    {X Y Z : B} {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z}
    (α : f₀ ⟶ f₁) (β : g₀ ⟶ g₁) :
    CommonHorizontalCompositionSquare Q α β := by
  unfold CommonHorizontalCompositionSquare
  rw [horizontalCompositionSquare]

/-- Degree-one horizontal gluing package: exact action of both sides of the
compositor homotopy together with its commuting naturality square. -/
def CommonHorizontalCompositionGlue
    {X Y Z : B} {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z}
    (α : f₀ ⟶ f₁) (β : g₀ ⟶ g₁) : Prop :=
  (commonNerveMap (composeThenMapFunctor Q X Y Z)).app
      (op ⦋1⦌) (commonHorizontalPairEdge Q α β) =
    ComposableArrows.mk₁
      ((AsSmall.up :
        (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
          (Q.map₂ (horizontalTwoCell α β))) ∧
  (commonNerveMap (mapThenComposeFunctor Q X Y Z)).app
      (op ⦋1⦌) (commonHorizontalPairEdge Q α β) =
    ComposableArrows.mk₁
      ((AsSmall.up :
        (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
          (horizontalTwoCell (Q.map₂ α) (Q.map₂ β))) ∧
  CommonHorizontalCompositionSquare Q α β

/-- Every pair of arbitrary source 2-cells satisfies the complete
degree-one horizontal gluing package. -/
theorem commonHorizontalCompositionGlue
    {X Y Z : B} {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z}
    (α : f₀ ⟶ f₁) (β : g₀ ⟶ g₁) :
    CommonHorizontalCompositionGlue Q α β :=
  ⟨commonComposeThenMap_edge Q α β,
    commonMapThenCompose_edge Q α β,
    commonHorizontalCompositionSquare Q α β⟩

/-- Common-universe equality of the two composite edges around the vertically
pasted compositor rectangle. -/
def CommonHorizontalCompositionPastedSquare
    {X Y Z : B}
    {f₀ f₁ f₂ : X ⟶ Y} {g₀ g₁ g₂ : Y ⟶ Z}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) : Prop :=
  ComposableArrows.mk₁
      ((AsSmall.up :
        (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
        (((Q.map₂ (horizontalTwoCell α₀ β₀)) ≫
            Q.map₂ (horizontalTwoCell α₁ β₁)) ≫
          (Q.mapComp f₂ g₂).hom)) =
    ComposableArrows.mk₁
      ((AsSmall.up :
        (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
        ((Q.mapComp f₀ g₀).hom ≫
          (horizontalTwoCell (Q.map₂ α₀) (Q.map₂ β₀) ≫
            horizontalTwoCell (Q.map₂ α₁) (Q.map₂ β₁))))

/-- The common-universe long edges of the vertically pasted compositor
rectangle agree exactly. -/
theorem commonHorizontalCompositionPastedSquare
    {X Y Z : B}
    {f₀ f₁ f₂ : X ⟶ Y} {g₀ g₁ g₂ : Y ⟶ Z}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) :
    CommonHorizontalCompositionPastedSquare Q α₀ α₁ β₀ β₁ := by
  unfold CommonHorizontalCompositionPastedSquare
  rw [horizontalCompositionPastedSquare]

/-- Degree-two mixed horizontal/vertical gluing package. It records exact
action on the two horizontal pair 2-simplices, source and target interchange,
and the vertically pasted common-universe compositor rectangle. -/
def CommonHorizontalCompositionPastingGlue
    {X Y Z : B}
    {f₀ f₁ f₂ : X ⟶ Y} {g₀ g₁ g₂ : Y ⟶ Z}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) : Prop :=
  (commonNerveMap (composeThenMapFunctor Q X Y Z)).app
      (op ⦋2⦌)
      (commonHorizontalPairTwoSimplex Q α₀ α₁ β₀ β₁) =
    ComposableArrows.mk₂
      ((AsSmall.up :
        (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
        (Q.map₂ (horizontalTwoCell α₀ β₀)))
      ((AsSmall.up :
        (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
        (Q.map₂ (horizontalTwoCell α₁ β₁))) ∧
  (commonNerveMap (mapThenComposeFunctor Q X Y Z)).app
      (op ⦋2⦌)
      (commonHorizontalPairTwoSimplex Q α₀ α₁ β₀ β₁) =
    ComposableArrows.mk₂
      ((AsSmall.up :
        (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
        (horizontalTwoCell (Q.map₂ α₀) (Q.map₂ β₀)))
      ((AsSmall.up :
        (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
        (horizontalTwoCell (Q.map₂ α₁) (Q.map₂ β₁))) ∧
  HorizontalCompositionPastingCoherence Q α₀ α₁ β₀ β₁ ∧
  CommonHorizontalCompositionPastedSquare Q α₀ α₁ β₀ β₁

/-- Every vertically composable pair of horizontal 2-cell pairs satisfies
the complete common-universe degree-two pasting package. -/
theorem commonHorizontalCompositionPastingGlue
    {X Y Z : B}
    {f₀ f₁ f₂ : X ⟶ Y} {g₀ g₁ g₂ : Y ⟶ Z}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) :
    CommonHorizontalCompositionPastingGlue Q α₀ α₁ β₀ β₁ :=
  ⟨commonComposeThenMap_twoSimplex Q α₀ α₁ β₀ β₁,
    commonMapThenCompose_twoSimplex Q α₀ α₁ β₀ β₁,
    horizontalCompositionPastingCoherence Q α₀ α₁ β₀ β₁,
    commonHorizontalCompositionPastedSquare Q α₀ α₁ β₀ β₁⟩

/-- Genuine simplicial homotopy between the common-universe horizontal
composition maps. -/
noncomputable def commonCompositionComparisonHomotopy (X Y Z : B) :
    SSet.Homotopy
      (commonNerveMap (composeThenMapFunctor Q X Y Z))
      (commonNerveMap (mapThenComposeFunctor Q X Y Z)) :=
  CategoryTheory.NerveHomotopy.ofNatTrans
    (commonCompositionComparisonNatIso Q X Y Z).hom

/-- An arbitrary-degree target simplex in the common-universe compositor
prism. For every source horizontal-product `n`-simplex there are `n + 1`
canonical target `(n + 1)`-simplices. -/
noncomputable def commonCompositionPrismSimplexAt
    (X Y Z : B) {n : ℕ}
    (x : (CategoryTheory.nerve
      (CommonHorizontalSource (_Q := Q) X Y Z)).obj (op ⦋n⦌))
    (i : Fin (n + 1)) :
    (CategoryTheory.nerve (CommonTargetHom (Q := Q) X Z)).obj
      (op ⦋n + 1⦌) :=
  SSet.Homotopy.prismSimplex
    (commonCompositionComparisonHomotopy Q X Y Z) x i

/-- Before the switching vertex, an arbitrary common-universe compositor
prism has exactly the compose-then-map target object at the corresponding
source vertex. -/
theorem commonCompositionPrismSimplexAt_obj_castSucc_of_le
    (X Y Z : B) {n : ℕ}
    (x : (CategoryTheory.nerve
      (CommonHorizontalSource (_Q := Q) X Y Z)).obj (op ⦋n⦌))
    (i j : Fin (n + 1)) (hji : j ≤ i) :
    (commonCompositionPrismSimplexAt Q X Y Z x i).obj j.castSucc =
      (commonAsSmallFunctor (composeThenMapFunctor Q X Y Z)).obj
        (x.obj j) := by
  unfold commonCompositionPrismSimplexAt commonCompositionComparisonHomotopy
  exact CategoryTheory.NerveHomotopy.ofNatTrans_prismSimplex_obj_castSucc_of_le
    _ x i j hji

/-- After the switching vertex, an arbitrary common-universe compositor
prism has exactly the map-then-compose target object at the corresponding
source vertex. -/
theorem commonCompositionPrismSimplexAt_obj_succ_of_le
    (X Y Z : B) {n : ℕ}
    (x : (CategoryTheory.nerve
      (CommonHorizontalSource (_Q := Q) X Y Z)).obj (op ⦋n⦌))
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    (commonCompositionPrismSimplexAt Q X Y Z x i).obj j.succ =
      (commonAsSmallFunctor (mapThenComposeFunctor Q X Y Z)).obj
        (x.obj j) := by
  unfold commonCompositionPrismSimplexAt commonCompositionComparisonHomotopy
  exact CategoryTheory.NerveHomotopy.ofNatTrans_prismSimplex_obj_succ_of_le
    _ x i j hij

/-- Complete arbitrary-degree compositor-prism coherence for a fixed triple
of bicategory objects. -/
def CommonCompositionPrismCore (X Y Z : B) : Prop :=
  SSet.Homotopy.AllPrismCoherence
    (commonCompositionComparisonHomotopy Q X Y Z)

/-- The common-universe compositor homotopy satisfies all endpoint,
side-face, shared-face, and degeneracy equations in every degree. -/
theorem commonCompositionPrismCore (X Y Z : B) :
    CommonCompositionPrismCore Q X Y Z :=
  SSet.Homotopy.allPrismCoherence _

/-- One of the three genuine target 3-simplices triangulating the compositor
homotopy prism over a common-universe horizontal pair 2-simplex. -/
noncomputable def commonCompositionPrismSimplex
    {X Y Z : B}
    {f₀ f₁ f₂ : X ⟶ Y} {g₀ g₁ g₂ : Y ⟶ Z}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂)
    (i : Fin 3) :
    (CategoryTheory.nerve (CommonTargetHom (Q := Q) X Z)).obj
      (op ⦋3⦌) :=
  commonCompositionPrismSimplexAt Q X Y Z
    (commonHorizontalPairTwoSimplex Q α₀ α₁ β₀ β₁) i

/-- The first face of the first compositor-prism tetrahedron is exactly the
canonical map-then-compose target 2-simplex. -/
@[simp]
theorem commonCompositionPrism_zeroFace
    {X Y Z : B}
    {f₀ f₁ f₂ : X ⟶ Y} {g₀ g₁ g₂ : Y ⟶ Z}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) :
    ((CategoryTheory.nerve
      (CommonTargetHom (Q := Q) X Z)).δ 0).hom'
        (commonCompositionPrismSimplex Q α₀ α₁ β₀ β₁ 0) =
      ComposableArrows.mk₂
        ((AsSmall.up :
          (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
          (horizontalTwoCell (Q.map₂ α₀) (Q.map₂ β₀)))
        ((AsSmall.up :
          (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
          (horizontalTwoCell (Q.map₂ α₁) (Q.map₂ β₁))) := by
  unfold commonCompositionPrismSimplex commonCompositionPrismSimplexAt
  rw [SSet.Homotopy.prismSimplex_zero_face_zero]
  apply commonMapThenCompose_twoSimplex

/-- The last face of the last compositor-prism tetrahedron is exactly the
canonical compose-then-map source 2-simplex. -/
@[simp]
theorem commonCompositionPrism_lastFace
    {X Y Z : B}
    {f₀ f₁ f₂ : X ⟶ Y} {g₀ g₁ g₂ : Y ⟶ Z}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) :
    ((CategoryTheory.nerve
      (CommonTargetHom (Q := Q) X Z)).δ (Fin.last 3)).hom'
        (commonCompositionPrismSimplex Q α₀ α₁ β₀ β₁ (Fin.last 2)) =
      ComposableArrows.mk₂
        ((AsSmall.up :
          (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
          (Q.map₂ (horizontalTwoCell α₀ β₀)))
        ((AsSmall.up :
          (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
          (Q.map₂ (horizontalTwoCell α₁ β₁))) := by
  unfold commonCompositionPrismSimplex commonCompositionPrismSimplexAt
  rw [SSet.Homotopy.prismSimplex_last_face_last]
  apply commonComposeThenMap_twoSimplex

/-- Full degree-two compositor prism package. The three actual target
3-simplices have all twelve faces identified by the generic prism equations,
and their two outer faces are normalized to the exact source and target
horizontal pair 2-simplices. -/
def CommonCompositionPrismGlue
    {X Y Z : B}
    {f₀ f₁ f₂ : X ⟶ Y} {g₀ g₁ g₂ : Y ⟶ Z}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) : Prop :=
  SSet.Homotopy.DegreeTwoPrismFaces
    (commonCompositionComparisonHomotopy Q X Y Z)
    (commonHorizontalPairTwoSimplex Q α₀ α₁ β₀ β₁) ∧
  ((CategoryTheory.nerve
      (CommonTargetHom (Q := Q) X Z)).δ 0).hom'
        (commonCompositionPrismSimplex Q α₀ α₁ β₀ β₁ 0) =
      ComposableArrows.mk₂
        ((AsSmall.up :
          (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
          (horizontalTwoCell (Q.map₂ α₀) (Q.map₂ β₀)))
        ((AsSmall.up :
          (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
          (horizontalTwoCell (Q.map₂ α₁) (Q.map₂ β₁))) ∧
  ((CategoryTheory.nerve
      (CommonTargetHom (Q := Q) X Z)).δ (Fin.last 3)).hom'
        (commonCompositionPrismSimplex Q α₀ α₁ β₀ β₁ (Fin.last 2)) =
      ComposableArrows.mk₂
        ((AsSmall.up :
          (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
          (Q.map₂ (horizontalTwoCell α₀ β₀)))
        ((AsSmall.up :
          (Q.obj X ⟶ Q.obj Z) ⥤ CommonTargetHom (Q := Q) X Z).map
          (Q.map₂ (horizontalTwoCell α₁ β₁)))

/-- Every vertically composable horizontal pair has an explicit three-
tetrahedron compositor prism with all faces identified. -/
theorem commonCompositionPrismGlue
    {X Y Z : B}
    {f₀ f₁ f₂ : X ⟶ Y} {g₀ g₁ g₂ : Y ⟶ Z}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) :
    CommonCompositionPrismGlue Q α₀ α₁ β₀ β₁ :=
  ⟨SSet.Homotopy.degreeTwoPrismFaces _ _,
    commonCompositionPrism_zeroFace Q α₀ α₁ β₀ β₁,
    commonCompositionPrism_lastFace Q α₀ α₁ β₀ β₁⟩

/-- Common-universe edge proposition expressing exact pseudofunctor
associator coherence. -/
def CommonAssociatorCompatibility
    {A B₁ C₁ D : B} (f : A ⟶ B₁) (g : B₁ ⟶ C₁)
    (h : C₁ ⟶ D) : Prop :=
  ComposableArrows.mk₁ ((AsSmall.up :
      (Q.obj A ⟶ Q.obj D) ⥤ CommonTargetHom Q A D).map
        (Q.map₂ (α_ f g h).hom)) =
    ComposableArrows.mk₁ ((AsSmall.up :
      (Q.obj A ⟶ Q.obj D) ⥤ CommonTargetHom Q A D).map
        ((Q.mapComp (f ≫ g) h).hom ≫
          (Q.mapComp f g).hom ▷ Q.map h ≫
            (α_ (Q.map f) (Q.map g) (Q.map h)).hom ≫
              Q.map f ◁ (Q.mapComp g h).inv ≫
                (Q.mapComp f (g ≫ h)).inv))

/-- The lifted associator edge is exactly the lifted compositor/target-
associator pasting. -/
theorem commonAssociatorCompatibility
    {A B₁ C₁ D : B} (f : A ⟶ B₁) (g : B₁ ⟶ C₁)
    (h : C₁ ⟶ D) :
    CommonAssociatorCompatibility Q f g h := by
  unfold CommonAssociatorCompatibility
  rw [Q.map₂_associator]

/-- Common-universe edge proposition expressing exact pseudofunctor
left-unitor coherence. -/
def CommonLeftUnitorCompatibility
    {A B₁ : B} (f : A ⟶ B₁) : Prop :=
  ComposableArrows.mk₁ ((AsSmall.up :
      (Q.obj A ⟶ Q.obj B₁) ⥤ CommonTargetHom Q A B₁).map
        (Q.map₂ (λ_ f).hom)) =
    ComposableArrows.mk₁ ((AsSmall.up :
      (Q.obj A ⟶ Q.obj B₁) ⥤ CommonTargetHom Q A B₁).map
        ((Q.mapComp (𝟙 A) f).hom ≫
          (Q.mapId A).hom ▷ Q.map f ≫ (λ_ (Q.map f)).hom))

/-- The lifted left-unitor edge is exactly the lifted unit/compositor/target-
unitor pasting. -/
theorem commonLeftUnitorCompatibility
    {A B₁ : B} (f : A ⟶ B₁) :
    CommonLeftUnitorCompatibility Q f := by
  unfold CommonLeftUnitorCompatibility
  rw [Q.map₂_left_unitor]

/-- Common-universe edge proposition expressing exact pseudofunctor
right-unitor coherence. -/
def CommonRightUnitorCompatibility
    {A B₁ : B} (f : A ⟶ B₁) : Prop :=
  ComposableArrows.mk₁ ((AsSmall.up :
      (Q.obj A ⟶ Q.obj B₁) ⥤ CommonTargetHom Q A B₁).map
        (Q.map₂ (ρ_ f).hom)) =
    ComposableArrows.mk₁ ((AsSmall.up :
      (Q.obj A ⟶ Q.obj B₁) ⥤ CommonTargetHom Q A B₁).map
        ((Q.mapComp f (𝟙 B₁)).hom ≫
          Q.map f ◁ (Q.mapId B₁).hom ≫ (ρ_ (Q.map f)).hom))

/-- The lifted right-unitor edge is exactly the lifted
compositor/unit/target-unitor pasting. -/
theorem commonRightUnitorCompatibility
    {A B₁ : B} (f : A ⟶ B₁) :
    CommonRightUnitorCompatibility Q f := by
  unfold CommonRightUnitorCompatibility
  rw [Q.map₂_right_unitor]

universe u₅ v₅ w₅

variable (W : Bicategory.MorphismProperty B)

/-- Universe-explicit localization predicate for the common-universe nerve
comparison. Source, localization target, and quantified semantic target may
all live in independent universes. -/
abbrev IsHigherLocalization : Prop :=
  Bicategory.MorphismProperty.IsBicategoricalLocalization.{
    u₃, v₃, w₃, u₄, v₄, w₄, u₅, v₅, w₅} W Q

/-- Chosen target equivalence for a marked source arrow. -/
noncomputable def markedEquivalence
    (hQ : IsHigherLocalization Q W) {X Y : B}
    (f : X ⟶ Y) (hf : W f) : Q.obj X ≌ Q.obj Y :=
  (Classical.choice (hQ.inverts f hf)).1

@[simp]
theorem markedEquivalence_hom
    (hQ : IsHigherLocalization Q W) {X Y : B}
    (f : X ⟶ Y) (hf : W f) :
    (markedEquivalence Q W hQ f hf).hom = Q.map f :=
  (Classical.choice (hQ.inverts f hf)).2

/-- Machine-facing coherent common-universe local-nerve action of a
pseudofunctor. -/
structure PseudofunctorNerveCore where
  /-- Map on every full local mapping nerve after common-universe replacement. -/
  localMap : ∀ X Y : B,
    CommonLocalMappingNerve Q X Y ⟶ CommonTargetMappingNerve Q X Y
  /-- The packaged maps are the canonical lifted nerve maps. -/
  localMap_eq : localMap = UniverseLiftedNerve.commonLocalMap Q
  /-- Exact action on lifted 1-cell vertices. -/
  mapsVertex : ∀ {X Y : B} (f : X ⟶ Y),
    (localMap X Y).app (op ⦋0⦌)
        (ComposableArrows.mk₀ ((AsSmall.up :
          (X ⟶ Y) ⥤ CommonSourceHom Q X Y).obj f)) =
      ComposableArrows.mk₀ ((AsSmall.up :
        (Q.obj X ⟶ Q.obj Y) ⥤ CommonTargetHom Q X Y).obj (Q.map f))
  /-- Exact action on lifted arbitrary 2-cell edges. -/
  mapsTwoCell : ∀ {X Y : B} {f g : X ⟶ Y} (α : f ⟶ g),
    (localMap X Y).app (op ⦋1⦌)
        (ComposableArrows.mk₁ ((AsSmall.up :
          (X ⟶ Y) ⥤ CommonSourceHom Q X Y).map α)) =
      ComposableArrows.mk₁ ((AsSmall.up :
        (Q.obj X ⟶ Q.obj Y) ⥤ CommonTargetHom Q X Y).map (Q.map₂ α))
  /-- Exact lifted action on canonical 2-simplices of vertically composable
  2-cells. -/
  mapsTwoSimplex : ∀ {X Y : B} {f g h : X ⟶ Y}
    (α : f ⟶ g) (β : g ⟶ h),
    (localMap X Y).app (op ⦋2⦌)
        (ComposableArrows.mk₂
          ((AsSmall.up : (X ⟶ Y) ⥤ CommonSourceHom Q X Y).map α)
          ((AsSmall.up : (X ⟶ Y) ⥤ CommonSourceHom Q X Y).map β)) =
      ComposableArrows.mk₂
        ((AsSmall.up :
          (Q.obj X ⟶ Q.obj Y) ⥤ CommonTargetHom Q X Y).map (Q.map₂ α))
        ((AsSmall.up :
          (Q.obj X ⟶ Q.obj Y) ⥤ CommonTargetHom Q X Y).map (Q.map₂ β))
  /-- Exact degree-one action of both horizontal-composition maps together
  with the compositor naturality square. -/
  horizontalCompositionGlue : ∀
    {X Y Z : B} {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z}
    (α : f₀ ⟶ f₁) (β : g₀ ⟶ g₁),
    CommonHorizontalCompositionGlue Q α β
  /-- Exact degree-two action and vertical-pasting coherence for two
  composable horizontal 2-cell pairs. -/
  horizontalCompositionPastingGlue : ∀
    {X Y Z : B}
    {f₀ f₁ f₂ : X ⟶ Y} {g₀ g₁ g₂ : Y ⟶ Z}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂),
    CommonHorizontalCompositionPastingGlue Q α₀ α₁ β₀ β₁
  /-- Complete arbitrary-degree face and degeneracy coherence of the
  compositor prism for every object triple. -/
  compositionPrismCore : ∀ X Y Z : B,
    CommonCompositionPrismCore Q X Y Z
  /-- Three genuine compositor-prism 3-simplices with all faces identified
  over every common-universe horizontal pair 2-simplex. -/
  compositionPrismGlue : ∀
    {X Y Z : B}
    {f₀ f₁ f₂ : X ⟶ Y} {g₀ g₁ g₂ : Y ⟶ Z}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂),
    CommonCompositionPrismGlue Q α₀ α₁ β₀ β₁
  /-- Common-universe compositor natural isomorphism. -/
  compositionIso : ∀ X Y Z : B,
    commonAsSmallFunctor (composeThenMapFunctor Q X Y Z) ≅
      commonAsSmallFunctor (mapThenComposeFunctor Q X Y Z)
  /-- Common-universe unit natural isomorphism. -/
  identityIso : ∀ X : B,
    commonAsSmallFunctor
        (mappedIdentityFunctor Q X) ≅
      commonAsSmallFunctor
        (targetIdentityFunctor Q X)
  /-- Genuine common-universe simplicial unit homotopy. -/
  identityHomotopy : ∀ X : B,
    SSet.Homotopy
      (commonNerveMap
        (mappedIdentityFunctor Q X))
      (commonNerveMap
        (targetIdentityFunctor Q X))
  /-- Genuine common-universe simplicial compositor homotopy. -/
  compositionHomotopy : ∀ X Y Z : B,
    SSet.Homotopy
      (commonNerveMap (composeThenMapFunctor Q X Y Z))
      (commonNerveMap (mapThenComposeFunctor Q X Y Z))
  /-- Exact lifted associator-edge coherence. -/
  associatorCoherence : ∀ {A B₁ C₁ D : B}
    (f : A ⟶ B₁) (g : B₁ ⟶ C₁) (h : C₁ ⟶ D),
    CommonAssociatorCompatibility Q f g h
  /-- Exact lifted left-unitor-edge coherence. -/
  leftUnitorCoherence : ∀ {A B₁ : B} (f : A ⟶ B₁),
    CommonLeftUnitorCompatibility Q f
  /-- Exact lifted right-unitor-edge coherence. -/
  rightUnitorCoherence : ∀ {A B₁ : B} (f : A ⟶ B₁),
    CommonRightUnitorCompatibility Q f

/-- Canonical common-universe nerve action package. -/
noncomputable def pseudofunctorNerveCore : PseudofunctorNerveCore Q where
  localMap := commonLocalMap Q
  localMap_eq := rfl
  mapsVertex := commonLocalMap_vertex Q
  mapsTwoCell := commonLocalMap_twoCell Q
  mapsTwoSimplex := commonLocalMap_twoSimplex Q
  horizontalCompositionGlue := commonHorizontalCompositionGlue Q
  horizontalCompositionPastingGlue :=
    commonHorizontalCompositionPastingGlue Q
  compositionPrismCore := commonCompositionPrismCore Q
  compositionPrismGlue := commonCompositionPrismGlue Q
  compositionIso := commonCompositionComparisonNatIso Q
  identityIso := commonIdentityComparisonNatIso Q
  identityHomotopy := commonIdentityComparisonHomotopy Q
  compositionHomotopy := commonCompositionComparisonHomotopy Q
  associatorCoherence := commonAssociatorCompatibility Q
  leftUnitorCoherence := commonLeftUnitorCompatibility Q
  rightUnitorCoherence := commonRightUnitorCompatibility Q

/-- Common-universe higher-localization comparison package. -/
structure HigherLocalizationNerveCore
    (hQ : IsHigherLocalization Q W) extends PseudofunctorNerveCore Q where
  /-- Full bicategorical localization theorem. -/
  localization : IsHigherLocalization Q W := hQ
  /-- Every marked source vertex lands at the chosen target equivalence. -/
  markedVertex : ∀ {X Y : B} (f : X ⟶ Y) (hf : W f),
    (toPseudofunctorNerveCore.localMap X Y).app (op ⦋0⦌)
        (ComposableArrows.mk₀ ((AsSmall.up :
          (X ⟶ Y) ⥤ CommonSourceHom Q X Y).obj f)) =
      ComposableArrows.mk₀ ((AsSmall.up :
        (Q.obj X ⟶ Q.obj Y) ⥤ CommonTargetHom Q X Y).obj
          (markedEquivalence Q W hQ f hf).hom)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every bicategorical localization supplies its common-universe full local
nerve comparison. -/
noncomputable def higherLocalizationNerveCore
    (hQ : IsHigherLocalization Q W) : HigherLocalizationNerveCore Q W hQ where
  toPseudofunctorNerveCore := pseudofunctorNerveCore Q
  localization := hQ
  markedVertex := by
    intro X Y f hf
    change (commonLocalMap Q X Y).app (op ⦋0⦌)
        (ComposableArrows.mk₀ ((AsSmall.up :
          (X ⟶ Y) ⥤ CommonSourceHom Q X Y).obj f)) = _
    rw [commonLocalMap_vertex, markedEquivalence_hom]

/-- Rezk outer-diagram map after replacing both categories by the same
common-universe small models. -/
noncomputable def commonRezkDiagramMap (F : C ⥤ D) :=
  RezkCore.diagramMap (AsSmall.{max u₂ v₂} C)
    (commonAsSmallFunctor F)

/-- Exact action of the common-universe outer Rezk map on an arrow vertex. -/
theorem commonRezkDiagramMap_arrowVertex (F : C ⥤ D)
    {X Y : C} (f : X ⟶ Y) :
    ((commonRezkDiagramMap F).app
      (Opposite.op (SimplexCategory.mk 1))).app
        (Opposite.op (SimplexCategory.mk 0))
        (RezkCore.arrowVertex (AsSmall.{max u₂ v₂} C)
          ((AsSmall.up : C ⥤ AsSmall.{max u₂ v₂} C).map f)) =
      RezkCore.arrowVertex (AsSmall.{max u₁ v₁} D)
        ((AsSmall.up : D ⥤ AsSmall.{max u₁ v₁} D).map (F.map f)) := by
  apply RezkCore.diagramMap_arrowVertex

end Ript.Higher.UniverseLiftedNerve
