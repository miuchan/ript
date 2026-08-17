import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy
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

namespace Equivalence

/-- The adjunction underlying a chosen adjoint equivalence. -/
def toAdjunction {X Y : B} (e : X ≌ Y) : e.hom ⊣ e.inv where
  unit := e.unit.hom
  counit := e.counit.hom
  left_triangle := e.left_triangle_hom
  right_triangle := e.right_triangle_hom

/-- Adjoint equivalences compose.  Mathlib already composes bicategorical
adjunctions; this packages the invertible unit and counit at the level of its
`Equivalence` structure. -/
noncomputable def trans {X Y Z : B} (e : X ≌ Y) (e' : Y ≌ Z) : X ≌ Z := by
  let η : 𝟙 X ≅ (e.hom ≫ e'.hom) ≫ (e'.inv ≫ e.inv) :=
    e.unit ≪⊗≫
      whiskerLeftIso e.hom (whiskerRightIso e'.unit e.inv) ≪⊗≫
        Iso.refl _
  let ε : (e'.inv ≫ e.inv) ≫ (e.hom ≫ e'.hom) ≅ 𝟙 Z :=
    Iso.refl _ ≪⊗≫
      whiskerLeftIso e'.inv (whiskerRightIso e.counit e'.hom) ≪⊗≫
        e'.counit
  exact mkOfAdjointifyCounit η ε

/-- Reverse a chosen adjoint equivalence. -/
noncomputable def symm {X Y : B} (e : X ≌ Y) : Y ≌ X :=
  mkOfAdjointifyCounit e.counit.symm e.unit.symm

/-- Replace the forward 1-morphism of an adjoint equivalence by an
isomorphic 1-morphism. -/
noncomputable def replaceHom {X Y : B} (e : X ≌ Y)
    {f : X ⟶ Y} (h : e.hom ≅ f) : X ≌ Y :=
  mkOfAdjointifyCounit
    (e.unit ≪≫ whiskerRightIso h e.inv)
    ((whiskerLeftIso e.inv h).symm ≪≫ e.counit)

@[simp]
theorem trans_hom {X Y Z : B} (e : X ≌ Y) (e' : Y ≌ Z) :
    (e.trans e').hom = e.hom ≫ e'.hom :=
  rfl

@[simp]
theorem trans_inv {X Y Z : B} (e : X ≌ Y) (e' : Y ≌ Z) :
    (e.trans e').inv = e'.inv ≫ e.inv :=
  rfl

@[simp]
theorem symm_hom {X Y : B} (e : X ≌ Y) : e.symm.hom = e.inv :=
  rfl

@[simp]
theorem symm_inv {X Y : B} (e : X ≌ Y) : e.symm.inv = e.hom :=
  rfl

@[simp]
theorem replaceHom_hom {X Y : B} (e : X ≌ Y)
    {f : X ⟶ Y} (h : e.hom ≅ f) :
    (e.replaceHom h).hom = f :=
  rfl

end Equivalence

/-- Taking mates commutes with precomposition by a 2-morphism on the left
vertical edge of a square. -/
theorem mateEquiv_precomp
    {a b c d : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a}
    {l₂ : c ⟶ d} {r₂ : d ⟶ c}
    (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂)
    {g g' : a ⟶ c} {h : b ⟶ d} (γ : g ⟶ g')
    (α : g' ≫ l₂ ⟶ l₁ ≫ h) :
    mateEquiv adj₁ adj₂ (γ ▷ l₂ ≫ α) =
      r₁ ◁ γ ≫ mateEquiv adj₁ adj₂ α := by
  simp only [mateEquiv_apply']
  calc
    _ = 𝟙 _ ⊗≫
          r₁ ◁ (g ◁ adj₂.unit ≫ γ ▷ (l₂ ≫ r₂)) ⊗≫
            r₁ ◁ α ▷ r₂ ⊗≫ adj₁.counit ▷ h ▷ r₂ ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫
          r₁ ◁ (γ ▷ 𝟙 c ≫ g' ◁ adj₂.unit) ⊗≫
            r₁ ◁ α ▷ r₂ ⊗≫ adj₁.counit ▷ h ▷ r₂ ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]
    _ = _ := by bicategory

/-- Taking mates commutes with postcomposition by a 2-morphism on the right
vertical edge of a square. -/
theorem mateEquiv_postcomp
    {a b c d : B} {l₁ : a ⟶ b} {r₁ : b ⟶ a}
    {l₂ : c ⟶ d} {r₂ : d ⟶ c}
    (adj₁ : l₁ ⊣ r₁) (adj₂ : l₂ ⊣ r₂)
    {g : a ⟶ c} {h h' : b ⟶ d} (α : g ≫ l₂ ⟶ l₁ ≫ h)
    (δ : h ⟶ h') :
    mateEquiv adj₁ adj₂ (α ≫ l₁ ◁ δ) =
      mateEquiv adj₁ adj₂ α ≫ δ ▷ r₂ := by
  simp only [mateEquiv_apply']
  calc
    _ = 𝟙 _ ⊗≫ r₁ ◁ g ◁ adj₂.unit ⊗≫ r₁ ◁ α ▷ r₂ ⊗≫
          ((r₁ ≫ l₁) ◁ δ ≫ adj₁.counit ▷ h') ▷ r₂ ⊗≫ 𝟙 _ := by
      bicategory
    _ = 𝟙 _ ⊗≫ r₁ ◁ g ◁ adj₂.unit ⊗≫ r₁ ◁ α ▷ r₂ ⊗≫
          (adj₁.counit ▷ h ≫ 𝟙 b ◁ δ) ▷ r₂ ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]
    _ = _ := by bicategory

namespace IsEquivalence

/-- Being an adjoint equivalence is invariant under a 2-isomorphism of
1-morphisms. -/
theorem of_iso {X Y : B} {f g : X ⟶ Y}
    (hf : IsEquivalence f) (h : f ≅ g) : IsEquivalence g := by
  obtain ⟨⟨e, he⟩⟩ := hf
  exact ⟨⟨e.replaceHom (eqToIso he ≪≫ h), rfl⟩⟩

/-- A composite of adjoint equivalences is an adjoint equivalence. -/
theorem comp {X Y Z : B} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsEquivalence f) (hg : IsEquivalence g) :
    IsEquivalence (f ≫ g) := by
  obtain ⟨⟨e, he⟩⟩ := hf
  obtain ⟨⟨e', he'⟩⟩ := hg
  exact ⟨⟨e.trans e', by simp [he, he']⟩⟩

/-- Cancel an adjoint equivalence from the right of a composite. -/
theorem of_comp_right {X Y Z : B} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hfg : IsEquivalence (f ≫ g)) (hg : IsEquivalence g) :
    IsEquivalence f := by
  obtain ⟨⟨efg, hefg⟩⟩ := hfg
  obtain ⟨⟨eg, heg⟩⟩ := hg
  let h : (efg.trans eg.symm).hom ≅ f :=
    whiskerRightIso (eqToIso hefg) eg.inv ≪≫
      α_ f g eg.inv ≪≫
        whiskerLeftIso f
          (whiskerRightIso (eqToIso heg).symm eg.inv ≪≫ eg.unit.symm) ≪≫
            ρ_ f
  exact ⟨⟨(efg.trans eg.symm).replaceHom h, rfl⟩⟩

end IsEquivalence

end Bicategory

namespace Pseudofunctor

/-- A source pseudofunctor factors through `Q` when it is adjoint equivalent
to the precomposition of some pseudofunctor out of the target of `Q`.  This is
the exact object-level witness used by bicategorical localization. -/
def FactorsThrough (Q : B ⥤ᵖ C) (F : B ⥤ᵖ D) : Prop :=
  ∃ G : C ⥤ᵖ D, Nonempty (Q.comp G ≌ F)

namespace FactorsThrough

/-- Factorization through `Q` is replete: replacing the source
pseudofunctor by an adjoint-equivalent one preserves the factorization. -/
theorem trans {Q : B ⥤ᵖ C} {F F' : B ⥤ᵖ D}
    (h : Q.FactorsThrough F) (e : F ≌ F') : Q.FactorsThrough F' := by
  obtain ⟨G, ⟨e'⟩⟩ := h
  exact ⟨G, ⟨e'.trans e⟩⟩

end FactorsThrough

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

namespace LocallyDiscrete

/-- An isomorphism in a category determines an adjoint equivalence in its
locally discrete bicategory. -/
noncomputable def equivalenceOfIsIso {E : Type u₁} [Category.{v₁} E]
    {X Y : E} (f : X ⟶ Y) [IsIso f] :
    LocallyDiscrete.mk X ≌ LocallyDiscrete.mk Y := by
  let η : 𝟙 (LocallyDiscrete.mk X) ≅ f.toLoc ≫ (inv f).toLoc :=
    eqToIso (by
      apply Discrete.ext
      simp)
  let ε : (inv f).toLoc ≫ f.toLoc ≅ 𝟙 (LocallyDiscrete.mk Y) :=
    eqToIso (by
      apply Discrete.ext
      simp)
  exact Bicategory.Equivalence.mkOfAdjointifyCounit η ε

@[simp]
theorem equivalenceOfIsIso_hom {E : Type u₁} [Category.{v₁} E]
    {X Y : E} (f : X ⟶ Y) [IsIso f] :
    (equivalenceOfIsIso f).hom = f.toLoc :=
  rfl

/-- Every arrow of the locally discrete bicategory associated to a groupoid
is an adjoint equivalence. -/
theorem isEquivalence_of_groupoid {E : Type u₁} [Groupoid.{v₁} E]
    {X Y : LocallyDiscrete E} (f : X ⟶ Y) :
    Bicategory.IsEquivalence f := by
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨f⟩ := f
  exact Bicategory.isEquivalence_hom (equivalenceOfIsIso f)

end LocallyDiscrete

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

namespace MorphismProperty

/-- Lift a property of arrows in a category to the corresponding locally
discrete bicategory. -/
def locallyDiscrete {E : Type u₁} [Category.{v₁} E]
    (W : CategoryTheory.MorphismProperty E) :
    Bicategory.MorphismProperty (LocallyDiscrete E) :=
  fun {_ _} f => W f.as

/-- Ordinary inversion by a functor implies bicategorical inversion by the
induced pseudofunctor between locally discrete bicategories. -/
theorem locallyDiscrete_isInvertedBy
    {E : Type u₁} [Category.{v₁} E]
    {E' : Type u₂} [Category.{v₂} E']
    (W : CategoryTheory.MorphismProperty E) (F : E ⥤ E')
    (hF : CategoryTheory.MorphismProperty.IsInvertedBy W F) :
    (locallyDiscrete W).IsInvertedBy F.toPseudofunctor := by
  intro X Y f hf
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨f⟩ := f
  let _ : IsIso (F.map f) := hF f hf
  exact Bicategory.isEquivalence_hom
    (LocallyDiscrete.equivalenceOfIsIso (F.map f))

end MorphismProperty

end Bicategory

namespace Pseudofunctor.StrongTrans

variable {F G : C ⥤ᵖ D}

/-- Evaluate an isomorphism of strong transformations at one source
object. -/
def isoAppAt {η θ : F ⟶ G} (e : η ≅ θ) (X : C) : η.app X ≅ θ.app X where
  hom := e.hom.as.app X
  inv := e.inv.as.app X
  hom_inv_id := congrArg (fun k => k.as.app X) e.hom_inv_id
  inv_hom_id := congrArg (fun k => k.as.app X) e.inv_hom_id

/-- The modification naturality equation for a proposed family of object
components, restricted to a single 1-morphism.  Packaging the equation lets
free constructions establish it by generators, inverses, and composition. -/
def NaturalityAt (η θ : F ⟶ G)
    (app : ∀ X, η.app X ⟶ θ.app X)
    {a b : C} (f : a ⟶ b) : Prop :=
  F.map f ◁ app b ≫ (θ.naturality f).hom =
    (η.naturality f).hom ≫ app a ▷ G.map f

/-- Transport a candidate strong-naturality isomorphism across a
2-isomorphism between parallel source 1-morphisms.  This is the constructor
form of `naturality_naturality_iso`. -/
def naturalityIsoOfIso (F G : C ⥤ᵖ D) {a b : C} {f g : a ⟶ b}
    (appA : F.obj a ⟶ G.obj a) (appB : F.obj b ⟶ G.obj b)
    (α : F.map f ≫ appB ≅ appA ≫ G.map f) (e : f ≅ g) :
    F.map g ≫ appB ≅ appA ≫ G.map g :=
  whiskerRightIso (F.map₂Iso e.symm) appB ≪≫ α ≪≫
    whiskerLeftIso appA (G.map₂Iso e)

/-- Compose candidate strong-naturality isomorphisms.  The pseudofunctor
comparison maps and bicategorical associators make the result a constraint at
the composite source 1-morphism.  This is the constructor form of
`naturality_comp_iso`. -/
def naturalityCompIsoOfIsos (F G : C ⥤ᵖ D)
    {a b c : C} (f : a ⟶ b) (g : b ⟶ c)
    (appA : F.obj a ⟶ G.obj a) (appB : F.obj b ⟶ G.obj b)
    (appC : F.obj c ⟶ G.obj c)
    (α : F.map f ≫ appB ≅ appA ≫ G.map f)
    (β : F.map g ≫ appC ≅ appB ≫ G.map g) :
    F.map (f ≫ g) ≫ appC ≅ appA ≫ G.map (f ≫ g) :=
  whiskerRightIso (F.mapComp f g) appC ≪≫ (α_ _ _ _) ≪≫
    whiskerLeftIso (F.map f) β ≪≫ (α_ _ _ _).symm ≪≫
    whiskerRightIso α (G.map g) ≪≫ α_ _ _ _ ≪≫
    whiskerLeftIso appA (G.mapComp f g).symm

/-- Derive the strong-naturality isomorphism at the chosen inverse of an
adjoint equivalence from a constraint at its forward 1-morphism.

For a general adjunction the mate of an invertible 2-cell need not be
invertible.  Here both adjunctions are images of an *adjoint equivalence*, so
their unit and counit are invertible.  The explicit bicategorical composite
therefore packages the mate as an isomorphism without invoking choice. -/
def inverseNaturalityIso (F G : C ⥤ᵖ D) {a b : C} (e : a ≌ b)
    (appA : F.obj a ⟶ G.obj a) (appB : F.obj b ⟶ G.obj b)
    (α : F.map e.hom ≫ appB ≅ appA ≫ G.map e.hom) :
    F.map e.inv ≫ appA ≅ appB ≫ G.map e.inv :=
  Iso.refl _ ≪⊗≫
    whiskerLeftIso (F.map e.inv)
      (whiskerLeftIso appA
        ((G.mapId a).symm ≪≫ G.map₂Iso e.unit ≪≫
          G.mapComp e.hom e.inv)) ≪⊗≫
    whiskerLeftIso (F.map e.inv)
      (whiskerRightIso α.symm (G.map e.inv)) ≪⊗≫
    whiskerRightIso
      (whiskerRightIso
        ((F.mapComp e.inv e.hom).symm ≪≫ F.map₂Iso e.counit ≪≫
          F.mapId b) appB)
      (G.map e.inv) ≪⊗≫
    Iso.refl _

/-- The hom of `inverseNaturalityIso` is the ordinary bicategorical mate of
the inverse forward constraint. -/
theorem inverseNaturalityIso_hom (F G : C ⥤ᵖ D)
    {a b : C} (e : a ≌ b)
    (appA : F.obj a ⟶ G.obj a) (appB : F.obj b ⟶ G.obj b)
    (α : F.map e.hom ≫ appB ≅ appA ≫ G.map e.hom) :
    (inverseNaturalityIso F G e appA appB α).hom =
      mateEquiv (F.mapAdjunction e.toAdjunction)
        (G.mapAdjunction e.toAdjunction) α.inv := by
  rw [mateEquiv_apply']
  rfl

/-- Transporting an existing strong-transformation constraint with
`naturalityIsoOfIso` recovers its constraint at the isomorphic 1-morphism. -/
theorem naturalityIsoOfIso_eq (η : F ⟶ G)
    {a b : C} {f g : a ⟶ b} (e : f ≅ g) :
    naturalityIsoOfIso F G (η.app a) (η.app b)
        (η.naturality f) e = η.naturality g :=
  (naturality_naturality_iso η e).symm

/-- Composing two existing strong-transformation constraints with
`naturalityCompIsoOfIsos` recovers the constraint at their composite. -/
theorem naturalityCompIsoOfIsos_eq (η : F ⟶ G)
    {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    naturalityCompIsoOfIsos F G f g (η.app a) (η.app b) (η.app c)
        (η.naturality f) (η.naturality g) =
      η.naturality (f ≫ g) :=
  (naturality_comp_iso η f g).symm

/-- Every proposed family of modification components is natural at identity
1-morphisms. -/
theorem naturalityAt_id (η θ : F ⟶ G)
    (app : ∀ X, η.app X ⟶ θ.app X) (a : C) :
    NaturalityAt η θ app (𝟙 a) := by
  rw [NaturalityAt, naturality_id_hom, naturality_id_hom]
  simp only [← Category.assoc]
  rw [whisker_exchange (F.mapId a).hom (app a)]
  simp only [Category.assoc]
  rw [whisker_exchange (app a) (G.mapId a).inv]
  bicategory

/-- Naturality of proposed modification components is closed under
composition of 1-morphisms. -/
theorem naturalityAt_comp (η θ : F ⟶ G)
    (app : ∀ X, η.app X ⟶ θ.app X)
    {a b c : C} {f : a ⟶ b} {g : b ⟶ c}
    (hf : NaturalityAt η θ app f) (hg : NaturalityAt η θ app g) :
    NaturalityAt η θ app (f ≫ g) := by
  simp only [NaturalityAt] at hf hg ⊢
  rw [naturality_comp_hom, naturality_comp_hom]
  simp only [← Category.assoc]
  rw [whisker_exchange (F.mapComp f g).hom (app c)]
  simp only [Category.assoc]
  rw [whisker_exchange (app a) (G.mapComp f g).inv]
  rw [← cancel_epi ((F.mapComp f g).inv ▷ η.app c)]
  rw [← cancel_mono (θ.app a ◁ (G.mapComp f g).hom)]
  simp
  simp only [← Category.assoc]
  rw [← whiskerLeft_comp, hg]
  simp only [Category.assoc]
  simp only [whiskerLeft_comp]
  rw [← cancel_epi (F.map f ◁ (η.naturality g).inv)]
  simp
  calc
    _ = (α_ (F.map f) (η.app b) (G.map g)).inv ≫
        ((F.map f ◁ app b ≫ (θ.naturality f).hom) ▷ G.map g) ≫
          (α_ (θ.app a) (G.map f) (G.map g)).hom := by
      bicategory
    _ = (α_ (F.map f) (η.app b) (G.map g)).inv ≫
        (((η.naturality f).hom ≫ app a ▷ G.map f) ▷ G.map g) ≫
          (α_ (θ.app a) (G.map f) (G.map g)).hom := by
      rw [hf]
    _ = _ := by bicategory

/-- Naturality of proposed modification components is invariant under a
2-isomorphism between parallel 1-morphisms. -/
theorem naturalityAt_of_iso (η θ : F ⟶ G)
    (app : ∀ X, η.app X ⟶ θ.app X)
    {a b : C} {f g : a ⟶ b} (e : f ≅ g)
    (h : NaturalityAt η θ app f) :
    NaturalityAt η θ app g := by
  simp only [NaturalityAt] at h ⊢
  rw [naturality_naturality_hom θ e,
    naturality_naturality_hom η e]
  simp only [← Category.assoc]
  rw [whisker_exchange (F.map₂ e.inv) (app b)]
  simp only [Category.assoc]
  have h' := congrArg (fun k => k ≫ θ.app a ◁ G.map₂ e.hom) h
  simp only [Category.assoc] at h'
  rw [h']
  rw [← whisker_exchange (app a) (G.map₂ e.hom)]

/-- The naturality isomorphism of a strong transformation at the chosen
inverse of an adjoint equivalence is the mate of its forward naturality
isomorphism. -/
theorem mate_naturality (η : F ⟶ G) {a b : C} (e : a ≌ b) :
    mateEquiv (F.mapAdjunction e.toAdjunction)
      (G.mapAdjunction e.toAdjunction)
      (η.naturality e.hom).inv = (η.naturality e.inv).hom := by
  rw [mateEquiv_eq_iff]
  rw [Adjunction.homEquiv₁_symm_apply, Adjunction.homEquiv₂_apply]
  rw [← cancel_mono ((α_ (F.map e.hom) (η.app b) (G.map e.inv)).inv ≫
    (η.naturality e.hom).hom ▷ G.map e.inv)]
  simp
  rw [← cancel_mono ((α_ (η.app a) (G.map e.hom) (G.map e.inv)).hom ≫
    η.app a ◁ (G.mapComp e.hom e.inv).inv)]
  simp
  rw [← naturality_comp_hom η e.hom e.inv]
  rw [η.naturality_naturality e.toAdjunction.unit]
  rw [naturality_id_hom]
  simp

/-- For an existing strong transformation, the explicitly invertible mate
constructor recovers its naturality isomorphism at the chosen inverse. -/
theorem inverseNaturalityIso_eq (η : F ⟶ G) {a b : C} (e : a ≌ b) :
    inverseNaturalityIso F G e (η.app a) (η.app b)
        (η.naturality e.hom) = η.naturality e.inv := by
  apply Iso.ext
  rw [inverseNaturalityIso_hom, mate_naturality]

/-- If proposed modification components are natural at the forward arrow of
an adjoint equivalence, they are automatically natural at its chosen
inverse.  This is the key extension step for modifications on a free
groupoid. -/
theorem naturalityAt_inv (η θ : F ⟶ G)
    (app : ∀ X, η.app X ⟶ θ.app X)
    {a b : C} (e : a ≌ b)
    (h : NaturalityAt η θ app e.hom) :
    NaturalityAt η θ app e.inv := by
  simp only [NaturalityAt] at h ⊢
  have h' :
      app a ▷ G.map e.hom ≫ (θ.naturality e.hom).inv =
        (η.naturality e.hom).inv ≫ F.map e.hom ◁ app b := by
    rw [← cancel_epi (η.naturality e.hom).hom]
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← h]
    simp
  have hmateLeft :
      mateEquiv (F.mapAdjunction e.toAdjunction)
          (G.mapAdjunction e.toAdjunction)
          (app a ▷ G.map e.hom ≫ (θ.naturality e.hom).inv) =
        F.map e.inv ◁ app a ≫ (θ.naturality e.inv).hom := by
    rw [Bicategory.mateEquiv_precomp]
    rw [mate_naturality θ e]
  have hmateRight :
      mateEquiv (F.mapAdjunction e.toAdjunction)
          (G.mapAdjunction e.toAdjunction)
          ((η.naturality e.hom).inv ≫ F.map e.hom ◁ app b) =
        (η.naturality e.inv).hom ≫ app b ▷ G.map e.inv := by
    rw [Bicategory.mateEquiv_postcomp]
    rw [mate_naturality η e]
  rw [← hmateLeft, ← hmateRight, h']

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

/-- Evaluate an adjoint equivalence of pseudofunctors at one source object.
The resulting 1-morphism is again an adjoint equivalence. -/
noncomputable def equivalenceApp {F G : C ⥤ᵖ D} (e : F ≌ G) (X : C) :
    F.obj X ≌ G.obj X :=
  Bicategory.Equivalence.mkOfAdjointifyCounit
    (isoAppAt e.unit X) (isoAppAt e.counit X)

@[simp]
theorem equivalenceApp_hom {F G : C ⥤ᵖ D} (e : F ≌ G) (X : C) :
    (equivalenceApp e X).hom = e.hom.app X :=
  rfl

end Pseudofunctor.StrongTrans

namespace Bicategory.MorphismProperty

/-- Inversion of a marking is invariant under an adjoint equivalence of
pseudofunctors. -/
theorem IsInvertedBy.of_equivalence (W : MorphismProperty B)
    {F G : B ⥤ᵖ C} (hG : W.IsInvertedBy G) (e : F ≌ G) :
    W.IsInvertedBy F := by
  intro X Y f hf
  let eX := Pseudofunctor.StrongTrans.equivalenceApp e X
  let eY := Pseudofunctor.StrongTrans.equivalenceApp e Y
  have hRight : IsEquivalence (e.hom.app X ≫ G.map f) :=
    (isEquivalence_hom eX).comp (hG f hf)
  have hLeft : IsEquivalence (F.map f ≫ e.hom.app Y) :=
    hRight.of_iso (e.hom.naturality f).symm
  exact hLeft.of_comp_right (isEquivalence_hom eY)

end Bicategory.MorphismProperty

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

/-- If a pseudofunctor is surjective on objects, precomposition with it is
faithful on every local category of strong transformations and
modifications.  Modification equality is recovered objectwise from a chosen
source preimage. -/
theorem Pseudofunctor.localPrecomposition_faithful_of_obj_surjective
    (Q : B ⥤ᵖ C) (hQ : Function.Surjective Q.obj)
    (F G : C ⥤ᵖ D) : (Q.localPrecomposition F G).Faithful :=
  { map_injective := by
      intro η θ Γ Δ h
      apply Pseudofunctor.StrongTrans.homCategory.ext
      intro X
      obtain ⟨Y, rfl⟩ := hQ X
      exact congrArg (fun k => k.as.app Y) h }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical strong transformation from precomposition by the identity
pseudofunctor back to the original pseudofunctor.  Its object components are
identities; the explicit transformation is necessary because pseudofunctor
composition is not definitionally unital in its coherence fields. -/
noncomputable def Pseudofunctor.idCompStrongTrans (F : B ⥤ᵖ C) :
    (Pseudofunctor.id B).comp F ⟶ F where
  app X := 𝟙 (F.obj X)
  naturality f := (ρ_ (F.map f)) ≪≫ (λ_ (F.map f)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The inverse-direction strong transformation for identity
precomposition. -/
noncomputable def Pseudofunctor.idCompStrongTransInv (F : B ⥤ᵖ C) :
    F ⟶ (Pseudofunctor.id B).comp F where
  app X := 𝟙 (F.obj X)
  naturality f := (ρ_ (F.map f)) ≪≫ (λ_ (F.map f)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Precomposition by the identity pseudofunctor is adjoint equivalent to
the original pseudofunctor. -/
noncomputable def Pseudofunctor.idCompEquivalence (F : B ⥤ᵖ C) :
    (Pseudofunctor.id B).comp F ≌ F :=
  Bicategory.Equivalence.mkOfAdjointifyCounit
    (Pseudofunctor.StrongTrans.isoMk
      (η := 𝟙 ((Pseudofunctor.id B).comp F))
      (θ := F.idCompStrongTrans ≫ F.idCompStrongTransInv)
      (fun X => (ρ_ (𝟙 (F.obj X))).symm)
      (by
        intro a b f
        dsimp [Pseudofunctor.idCompStrongTrans,
          Pseudofunctor.idCompStrongTransInv]
        bicategory))
    (Pseudofunctor.StrongTrans.isoMk
      (η := F.idCompStrongTransInv ≫ F.idCompStrongTrans)
      (θ := 𝟙 F)
      (fun X => ρ_ (𝟙 (F.obj X)))
      (by
        intro a b f
        dsimp [Pseudofunctor.idCompStrongTrans,
          Pseudofunctor.idCompStrongTransInv]
        bicategory))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Identity precomposition is an equivalence on every local category of
strong transformations and modifications.  Essential surjectivity is proved
by conjugating a strong transformation with the explicit identity-composition
adjoint equivalences; fullness and faithfulness retain modification
components exactly. -/
theorem Pseudofunctor.localPrecomposition_id_isEquivalence
    (F G : B ⥤ᵖ C) :
    ((Pseudofunctor.id B).localPrecomposition F G).IsEquivalence where
  faithful :=
    { map_injective := by
        intro η θ Γ Δ h
        apply Pseudofunctor.StrongTrans.homCategory.ext
        intro X
        exact congrArg (fun k => k.as.app X) h }
  full :=
    { map_surjective := by
        intro η θ Γ
        let Δ : η ⟶ θ :=
          ⟨{ app := fun X => Γ.as.app X
             naturality := fun f => Γ.as.naturality f }⟩
        refine ⟨Δ, ?_⟩
        ext X
        rfl }
  essSurj :=
    { mem_essImage := by
        intro η
        let eF := F.idCompEquivalence
        let eG := G.idCompEquivalence
        let θ : F ⟶ G := eF.inv ≫ η ≫ eG.hom
        refine ⟨θ, ⟨Pseudofunctor.StrongTrans.isoMk
          (η := (Pseudofunctor.id B).localPrecomposition F G |>.obj θ)
          (θ := η)
          (fun X => λ_ (η.app X ≫ 𝟙 (G.obj X)) ≪≫ ρ_ (η.app X)) ?_⟩⟩
        intro a b f
        dsimp [θ, eF, eG, Pseudofunctor.idCompEquivalence,
          Pseudofunctor.idCompStrongTrans,
          Pseudofunctor.idCompStrongTransInv,
          Pseudofunctor.localPrecomposition,
          Pseudofunctor.StrongTrans.prewhisker,
          Bicategory.Equivalence.mkOfAdjointifyCounit]
        bicategory }

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

/-- The marking consisting precisely of bicategorical equivalence
1-morphisms. -/
def equivalences : MorphismProperty B :=
  fun {_ _} f => Bicategory.IsEquivalence f

/-- If every marked arrow is already a bicategorical equivalence, the
identity pseudofunctor is a genuine bicategorical localization.  This fills
all three parts of the universal property: inversion, factorization, and
local equivalence on strong transformations and modifications. -/
theorem isBicategoricalLocalization_id (W : MorphismProperty B)
    (hW : ∀ ⦃X Y : B⦄ (f : X ⟶ Y), W f → Bicategory.IsEquivalence f) :
    W.IsBicategoricalLocalization (Pseudofunctor.id B) where
  inverts := (W.isInvertedBy_id_iff).2 hW
  lift _ _ F _ := ⟨F, ⟨F.idCompEquivalence⟩⟩
  local_equivalence _ _ F G :=
    Pseudofunctor.localPrecomposition_id_isEquivalence F G

/-- The identity pseudofunctor is a bicategorical localization at `W` if and
only if every marked arrow was already an equivalence. -/
theorem isBicategoricalLocalization_id_iff (W : MorphismProperty B) :
    W.IsBicategoricalLocalization (Pseudofunctor.id B) ↔
      ∀ ⦃X Y : B⦄ (f : X ⟶ Y), W f → Bicategory.IsEquivalence f :=
  ⟨fun h => (W.isInvertedBy_id_iff).1 h.inverts,
    W.isBicategoricalLocalization_id⟩

/-- The identity pseudofunctor is the bicategorical localization at the class
of arrows that are already adjoint equivalences. -/
theorem equivalences_isBicategoricalLocalization_id :
    (equivalences : MorphismProperty B).IsBicategoricalLocalization
      (Pseudofunctor.id B) :=
  equivalences.isBicategoricalLocalization_id (by intros; assumption)

end Bicategory.MorphismProperty

end CategoryTheory
