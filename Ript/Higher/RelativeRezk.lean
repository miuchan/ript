import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy
import Mathlib.CategoryTheory.Widesubcategory
import Ript.Higher.TotalModelCompleteSegal

/-!
# Relative Rezk diagrams

For a category `C` with a multiplicative marking `W`, the relative Rezk
diagram has all finite strings in `C` as outer simplices. Its vertical
morphisms are natural transformations whose components lie pointwise in `W`.

If a functor `L : C ⟶ D` inverts `W`, postcomposition sends every such
vertical transformation to a natural isomorphism. This gives a natural map
from the relative Rezk diagram to the ordinary Rezk core diagram of `D` in
every outer and inner simplicial degree.
-/

set_option autoImplicit false

namespace Ript.Higher.RelativeRezk

open CategoryTheory
open Opposite
open Simplicial

universe u

variable {C D : Type u} [Category.{u} C] [Category.{u} D]

variable (W : MorphismProperty C) [W.IsMultiplicative]

/-- Pointwise multiplicativity on functor categories. -/
instance functorCategoryIsMultiplicative
    (J : Type*) [Category* J] :
    (W.functorCategory J).IsMultiplicative where
  id_mem F j := by
    change W (𝟙 (F.obj j))
    exact W.id_mem _
  comp_mem f g hf hg j := by
    change W (f.app j ≫ g.app j)
    exact W.comp_mem _ _ (hf j) (hg j)

/-- The relative category of `n`-strings. Objects are arbitrary strings;
morphisms are pointwise marked natural transformations. -/
abbrev StringCategory (n : ℕ) :=
  WideSubcategory (W.functorCategory (Fin (n + 1)))

/-- Restriction of relative strings along an indexing functor. -/
def restrictionFunctor {m n : ℕ} (F : Fin (m + 1) ⥤ Fin (n + 1)) :
    StringCategory (W := W) n ⥤ StringCategory (W := W) m where
  obj X := ⟨F ⋙ X.obj⟩
  map η := ⟨Functor.whiskerLeft F η.hom,
    fun i => η.property (F.obj i)⟩
  map_id X := by
    apply WideSubcategory.hom_ext
    apply NatTrans.ext
    funext i
    rfl
  map_comp f g := by
    apply WideSubcategory.hom_ext
    apply NatTrans.ext
    funext i
    rfl

/-- The category-valued relative Rezk diagram. -/
def diagramCat : SimplicialObject Cat where
  obj Δ := Cat.of (StringCategory (W := W) Δ.unop.len)
  map f := (restrictionFunctor (W := W)
    (SimplexCategory.toCat.map f.unop).toFunctor).toCatHom
  map_id Δ := by
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.hext
    · intro X
      rfl
    · intro X Y f
      apply heq_of_eq
      apply WideSubcategory.hom_ext
      rfl
  map_comp f g := by
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.hext
    · intro X
      rfl
    · intro X Y η
      apply heq_of_eq
      apply WideSubcategory.hom_ext
      rfl

/-- The bisimplicial relative Rezk diagram. -/
def diagram : SimplicialObject SSet :=
  diagramCat (W := W) ⋙ CategoryTheory.nerveFunctor

variable (L : C ⥤ D)

/-- A pointwise marked natural transformation maps to a natural isomorphism. -/
noncomputable def mappedNatIso
    (hL : MorphismProperty.IsInvertedBy W L) {n : ℕ}
    {X Y : StringCategory (W := W) n}
    (η : X ⟶ Y) :
    (L.mapComposableArrows n).obj X.obj ≅
      (L.mapComposableArrows n).obj Y.obj :=
  NatIso.ofComponents
    (fun i => @asIso D _ _ _ (L.map (η.hom.app i))
      (hL (η.hom.app i) (η.property i)))
    (fun {i j} f => by
      change L.map (X.obj.map f) ≫ L.map (η.hom.app j) =
        L.map (η.hom.app i) ≫ L.map (Y.obj.map f)
      rw [← L.map_comp, η.hom.naturality f, L.map_comp])

/-- In every outer degree, postcomposition with an inverting functor maps the
relative string category to the maximal core of target strings. -/
noncomputable def levelFunctor
    (hL : MorphismProperty.IsInvertedBy W L) (n : ℕ) :
    StringCategory (W := W) n ⥤ Core (ComposableArrows D n) where
  obj X := ⟨(L.mapComposableArrows n).obj X.obj⟩
  map η := ⟨mappedNatIso (W := W) (L := L) (hL := hL) η⟩
  map_id X := by
    apply Core.hom_ext
    apply NatTrans.ext
    funext i
    simp [mappedNatIso]
    rfl
  map_comp f g := by
    apply Core.hom_ext
    apply NatTrans.ext
    funext i
    simp [mappedNatIso]
    rfl

/-- The inverting functor induces a natural map into the category-valued Rezk
core diagram of the target. -/
noncomputable def comparisonCat
    (hL : MorphismProperty.IsInvertedBy W L) :
    diagramCat (W := W) ⟶ RezkCore.diagramCat D where
  app Δ := (levelFunctor (W := W) (L := L) (hL := hL)
    Δ.unop.len).toCatHom
  naturality := by
    intro Δ Γ f
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.hext
    · intro X
      rfl
    · intro X Y η
      apply heq_of_eq
      apply Core.hom_ext
      apply NatTrans.ext
      funext i
      rfl

/-- The all-dimensional bisimplicial comparison from the relative Rezk
diagram to the target Rezk core diagram. -/
noncomputable def comparison
    (hL : MorphismProperty.IsInvertedBy W L) :
    diagram (W := W) ⟶ RezkCore.diagram D :=
  Functor.whiskerRight
    (comparisonCat (W := W) (L := L) (hL := hL))
    CategoryTheory.nerveFunctor

/-- A source arrow as a vertical vertex in relative outer degree one. -/
def arrowVertex {X Y : C} (f : X ⟶ Y) :
    ((diagram (W := W)).obj (op (SimplexCategory.mk 1))).obj
      (op (SimplexCategory.mk 0)) :=
  ComposableArrows.mk₀
    (⟨ComposableArrows.mk₁ f⟩ : StringCategory (W := W) 1)

private theorem coreObj_ext {E : Type u} {X Y : Core E}
    (h : X.of = Y.of) : X = Y := by
  cases X
  cases Y
  cases h
  rfl

/-- The relative comparison sends an arrow vertex to the target Rezk vertex
represented by its functor image. -/
theorem comparison_arrowVertex
    (hL : MorphismProperty.IsInvertedBy W L)
    {X Y : C} (f : X ⟶ Y) :
    ((comparison (W := W) (L := L) (hL := hL)).app
      (op (SimplexCategory.mk 1))).app
        (op (SimplexCategory.mk 0)) (arrowVertex (W := W) f) =
      RezkCore.arrowVertex D (L.map f) := by
  change (CategoryTheory.nerveMap
      (levelFunctor (W := W) (L := L) (hL := hL) 1)).app
      (op (SimplexCategory.mk 0))
        (ComposableArrows.mk₀
          (⟨ComposableArrows.mk₁ f⟩ : StringCategory (W := W) 1)) = _
  rw [CategoryTheory.nerveMap_app_mk₀]
  apply ComposableArrows.ext₀
  apply coreObj_ext
  exact CategoryTheory.nerveMap_app_mk₁ L f

end Ript.Higher.RelativeRezk
