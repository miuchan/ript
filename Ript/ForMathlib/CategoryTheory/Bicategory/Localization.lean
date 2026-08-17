import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Ript.ForMathlib.CategoryTheory.Bicategory.MorphismProperty

/-!
# Marked localization interfaces for bicategories

Mathlib provides pseudofunctors, strong transformations, modifications, and
the bicategory of pseudofunctors, but it does not currently package a
bicategorical localization.  This file supplies the minimal API needed to
state that universal property without truncating noninvertible 2-morphisms.

The key distinction from ordinary Gabriel--Zisman localization is that a
marked 1-morphism is required to become an adjoint equivalence, while the
source and target remain bicategories and pseudofunctors retain every
2-morphism.  The actual existence of such a localization is deliberately not
asserted here.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]
variable {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable {D : Type u₃} [Bicategory.{w₃, v₃} D]

namespace Bicategory

/-- A 1-morphism in a bicategory is an equivalence when it is the forward
1-morphism of a chosen adjoint equivalence.  The equality in the subtype keeps
the predicate attached to the original 1-morphism rather than merely to
isomorphic data. -/
def IsEquivalence {X Y : B} (f : X ⟶ Y) : Prop :=
  Nonempty {e : X ≌ Y // e.hom = f}

/-- Every adjoint equivalence supplies an equivalence 1-morphism. -/
theorem isEquivalence_hom {X Y : B} (e : X ≌ Y) : IsEquivalence e.hom :=
  ⟨⟨e, rfl⟩⟩

end Bicategory

namespace Pseudofunctor

/-- Pseudofunctors preserve adjoint equivalences. -/
noncomputable def mapEquivalence (F : B ⥤ᵖ C)
    {X Y : B} (e : X ≌ Y) : F.obj X ≌ F.obj Y :=
  Bicategory.Equivalence.mkOfAdjointifyCounit
    ((F.mapId X).symm ≪≫ F.map₂Iso e.unit ≪≫ F.mapComp e.hom e.inv)
    ((F.mapComp e.inv e.hom).symm ≪≫ F.map₂Iso e.counit ≪≫ F.mapId Y)

@[simp]
theorem mapEquivalence_hom (F : B ⥤ᵖ C)
    {X Y : B} (e : X ≌ Y) : (F.mapEquivalence e).hom = F.map e.hom :=
  rfl

end Pseudofunctor

namespace Bicategory

/-- A pseudofunctor sends a property of source 1-morphisms to equivalences. -/
def MorphismProperty.IsInvertedBy (W : MorphismProperty B) (F : B ⥤ᵖ C) : Prop :=
  ∀ ⦃X Y : B⦄ (f : X ⟶ Y), W f → Bicategory.IsEquivalence (F.map f)

/-- The identity pseudofunctor inverts exactly those marked arrows that are
already bicategorical equivalences. -/
theorem MorphismProperty.isInvertedBy_id_iff (W : MorphismProperty B) :
    W.IsInvertedBy (Pseudofunctor.id B) ↔
      ∀ ⦃X Y : B⦄ (f : X ⟶ Y), W f → IsEquivalence f := by
  rfl

/-- Inverting a marking is preserved by postcomposition with a
pseudofunctor. -/
theorem MorphismProperty.IsInvertedBy.comp (W : MorphismProperty B)
    {F : B ⥤ᵖ C} (hF : W.IsInvertedBy F) (G : C ⥤ᵖ D) :
    W.IsInvertedBy (F.comp G) := by
  intro X Y f hf
  obtain ⟨⟨e, he⟩⟩ := hF f hf
  refine ⟨⟨G.mapEquivalence e, ?_⟩⟩
  change G.map e.hom = G.map (F.map f)
  rw [he]

end Bicategory

namespace Pseudofunctor.StrongTrans

variable {F G : C ⥤ᵖ D}

/-- Prewhisker a strong transformation by a pseudofunctor. -/
@[simps app]
def prewhisker (Q : B ⥤ᵖ C) (η : F ⟶ G) : Q.comp F ⟶ Q.comp G where
  app X := η.app (Q.obj X)
  naturality f := η.naturality (Q.map f)
  naturality_naturality θ := by
    change F.map₂ (Q.map₂ θ) ▷ η.app (Q.obj _) ≫
        (η.naturality (Q.map _)).hom =
      (η.naturality (Q.map _)).hom ≫
        η.app (Q.obj _) ◁ G.map₂ (Q.map₂ θ)
    exact η.naturality_naturality (Q.map₂ θ)
  naturality_id X := by
    change (η.naturality (Q.map (𝟙 X))).hom ≫
        η.app (Q.obj X) ◁
          (G.map₂Iso (Q.mapId X) ≪≫ G.mapId (Q.obj X)).hom =
      (F.map₂Iso (Q.mapId X) ≪≫ F.mapId (Q.obj X)).hom ▷
          η.app (Q.obj X) ≫
        (λ_ (η.app (Q.obj X))).hom ≫
          (ρ_ (η.app (Q.obj X))).inv
    simp only [Iso.trans_hom, PrelaxFunctor.map₂Iso_hom,
      whiskerLeft_comp, comp_whiskerRight, Category.assoc]
    rw [← η.naturality_naturality_assoc (Q.mapId X).hom]
    rw [η.naturality_id]
  naturality_comp f g := by
    change (η.naturality (Q.map (f ≫ g))).hom ≫
        η.app (Q.obj _) ◁
          (G.map₂Iso (Q.mapComp f g) ≪≫
            G.mapComp (Q.map f) (Q.map g)).hom =
      (F.map₂Iso (Q.mapComp f g) ≪≫
          F.mapComp (Q.map f) (Q.map g)).hom ▷ η.app (Q.obj _) ≫
        (α_ _ _ _).hom ≫
          F.map (Q.map f) ◁ (η.naturality (Q.map g)).hom ≫
            (α_ _ _ _).inv ≫
              (η.naturality (Q.map f)).hom ▷ G.map (Q.map g) ≫
                (α_ _ _ _).hom
    simp only [Iso.trans_hom, PrelaxFunctor.map₂Iso_hom,
      whiskerLeft_comp, comp_whiskerRight, Category.assoc]
    rw [← η.naturality_naturality_assoc (Q.mapComp f g).hom]
    rw [η.naturality_comp]

namespace Modification

variable {η θ : F ⟶ G}

/-- Prewhisker a modification by a pseudofunctor. -/
@[simps app]
def prewhisker (Q : B ⥤ᵖ C) (Γ : Modification η θ) :
    Modification (StrongTrans.prewhisker Q η) (StrongTrans.prewhisker Q θ) where
  app X := Γ.app (Q.obj X)
  naturality f := by
    change F.map (Q.map f) ◁ Γ.app (Q.obj _) ≫
        (θ.naturality (Q.map f)).hom =
      (η.naturality (Q.map f)).hom ≫
        Γ.app (Q.obj _) ▷ G.map (Q.map f)
    exact Γ.naturality (Q.map f)

end Modification

end Pseudofunctor.StrongTrans

/-- Precomposition by a pseudofunctor, retaining strong transformations and
modifications rather than collapsing them to equalities. -/
@[simps! obj map_app map₂_as_app]
def Pseudofunctor.precomposition (Q : B ⥤ᵖ C) :
    (C ⥤ᵖ D) ⥤ᵖ (B ⥤ᵖ D) where
  obj F := Q.comp F
  map η := Pseudofunctor.StrongTrans.prewhisker Q η
  map₂ Γ :=
    ⟨Pseudofunctor.StrongTrans.Modification.prewhisker Q Γ.as⟩
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _
  map₂_id _ := by ext X; rfl
  map₂_comp _ _ := by ext X; rfl
  map₂_whisker_left := by
    intro A B C f g h η
    ext X
    change f.app (Q.obj X) ◁ η.as.app (Q.obj X) =
      𝟙 _ ≫ (f.app (Q.obj X) ◁ η.as.app (Q.obj X)) ≫ 𝟙 _
    simp
  map₂_whisker_right := by
    intro A B C f g η h
    ext X
    change η.as.app (Q.obj X) ▷ h.app (Q.obj X) =
      𝟙 _ ≫ (η.as.app (Q.obj X) ▷ h.app (Q.obj X)) ≫ 𝟙 _
    simp
  map₂_associator := by
    intro A B C E f g h
    ext X
    change (α_ (f.app (Q.obj X)) (g.app (Q.obj X))
        (h.app (Q.obj X))).hom =
      𝟙 _ ≫ (𝟙 _ ▷ h.app (Q.obj X)) ≫
        (α_ (f.app (Q.obj X)) (g.app (Q.obj X))
          (h.app (Q.obj X))).hom ≫
          (f.app (Q.obj X) ◁ 𝟙 _) ≫ 𝟙 _
    simp
  map₂_left_unitor := by
    intro A B f
    ext X
    change (λ_ (f.app (Q.obj X))).hom =
      𝟙 _ ≫ (𝟙 _ ▷ f.app (Q.obj X)) ≫ (λ_ (f.app (Q.obj X))).hom
    simp
  map₂_right_unitor := by
    intro A B f
    ext X
    change (ρ_ (f.app (Q.obj X))).hom =
      𝟙 _ ≫ (f.app (Q.obj X) ◁ 𝟙 _) ≫ (ρ_ (f.app (Q.obj X))).hom
    simp

/-- The functor induced by precomposition on one local hom-category.  Its
objects are strong transformations and its morphisms are modifications, so
local equivalence of this functor is the fully faithful part of a genuine
bicategorical universal property. -/
@[simps! obj_app map_as_app]
def Pseudofunctor.localPrecomposition (Q : B ⥤ᵖ C) (F G : C ⥤ᵖ D) :
    (F ⟶ G) ⥤ (Q.comp F ⟶ Q.comp G) where
  obj η := Pseudofunctor.StrongTrans.prewhisker Q η
  map Γ :=
    ⟨Pseudofunctor.StrongTrans.Modification.prewhisker Q Γ.as⟩
  map_id _ := by ext X; rfl
  map_comp _ _ := by ext X; rfl

namespace Bicategory.MorphismProperty

/-- A pseudofunctor is a bicategorical localization at `W` when it sends the
marked 1-morphisms to adjoint equivalences and precomposition has the expected
2-dimensional universal property.

The `lift` field is biessential surjectivity onto pseudofunctors that invert
`W`.  The `local_equivalence` field says that strong transformations and their
modifications are recovered, up to equivalence, after precomposition.  This
is the standard local-equivalence-plus-biessential-surjectivity formulation
of a biequivalence onto the full sub-bicategory of `W`-inverting
pseudofunctors.  Unlike an ordinary localization of a homotopy category, the
definition quantifies over and therefore retains noninvertible 2-morphisms. -/
structure IsBicategoricalLocalization (W : MorphismProperty B) (Q : B ⥤ᵖ C) : Prop where
  /-- Every marked source 1-morphism becomes an adjoint equivalence. -/
  inverts : W.IsInvertedBy Q
  /-- Every pseudofunctor that inverts the marking factors through the
  localization up to an adjoint equivalence of pseudofunctors. -/
  lift : ∀ (E : Type u₃) [Bicategory.{w₃, v₃} E] (F : B ⥤ᵖ E),
    W.IsInvertedBy F →
      ∃ G : C ⥤ᵖ E, Nonempty (Q.comp G ≌ F)
  /-- Precomposition is an equivalence on every category of strong
  transformations and modifications. -/
  local_equivalence : ∀ (E : Type u₃) [Bicategory.{w₃, v₃} E]
    (F G : C ⥤ᵖ E), (Q.localPrecomposition F G).IsEquivalence

end Bicategory.MorphismProperty

end CategoryTheory
