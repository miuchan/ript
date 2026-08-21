import Ript.ForMathlib.CategoryTheory.Bicategory.MarkedZigzag

/-!
# Local universal property of marked-zigzag localization

This module extends strong transformations and modifications from the source
generators to the full presented marked-zigzag bicategory. Forward constraints
are retained, marked reverse constraints are their adjoint mates, and identity
and binary-composite constraints are canonical. Naturality is proved for every
raw 2-cell generator and then descended to the quotient.

Consequently, precomposition by the canonical inclusion is faithful, full,
and essentially surjective on every local category. Combined with marking
inversion and the explicit pseudofunctor factorization, this proves the full
bicategorical localization universal property.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace CategoryTheory.Bicategory.MarkedZigzag.LocalExtension

open CategoryTheory
open CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans

universe u₁ v₁ w₁ u₂ v₂ w₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]
variable (W : Bicategory.MorphismProperty B)
variable {D : Type u₂} [Bicategory.{w₂, v₂} D]
variable (F G : Presented.Localization W ⥤ᵖ D)
variable (η : (Presented.inclusion W).comp F ⟶
  (Presented.inclusion W).comp G)

/-- Reuse the component of a source strong transformation at the unchanged
underlying object of the presented localization. -/
def app : ∀ X : Presented.Localization W, F.obj X ⟶ G.obj X
  | ⟨X⟩ => η.app X

/-- Recursively extend strong naturality from forward source arrows to marked
formal inverses, identity words, and binary composites. -/
noncomputable def naturalityWord :
    ∀ {X Y : B} (word : Word W X Y),
      F.map word ≫ app W F G η ⟨Y⟩ ≅
        app W F G η ⟨X⟩ ≫ G.map word
  | _, _, .atom (.forward f) => η.naturality f
  | _, _, .atom (.backward f hf) =>
      Pseudofunctor.StrongTrans.inverseNaturalityIso F G
        (Presented.markedEquivalence W f hf)
        (app W F G η _) (app W F G η _) (η.naturality f)
  | X, _, .nil _ =>
      Pseudofunctor.StrongTrans.identityNaturalityIso F G ⟨X⟩
        (app W F G η ⟨X⟩)
  | _, _, .comp first second =>
      Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G first second
        (app W F G η _) (app W F G η _) (app W F G η _)
        (naturalityWord first) (naturalityWord second)

/-- The recursively extended naturality isomorphism for a 1-cell of the
presented localization. -/
noncomputable def naturality {X Y : Presented.Localization W} (word : X ⟶ Y) :
    F.map word ≫ app W F G η Y ≅ app W F G η X ≫ G.map word := by
  rcases X with ⟨X⟩
  rcases Y with ⟨Y⟩
  exact naturalityWord W F G η word

@[simp]
theorem naturality_mk {X Y : B} (word : Word W X Y) :
    naturality W F G η (X := ⟨X⟩) (Y := ⟨Y⟩) word =
      naturalityWord W F G η word :=
  rfl

@[simp]
theorem mk_id {X Y : B} (word : Word W X Y) :
    Presented.mk W (Cell.id word) = 𝟙 word :=
  rfl

@[simp]
theorem mk_vcomp {X Y : B} {first middle last : Word W X Y}
    (firstCell : Cell W first middle) (secondCell : Cell W middle last) :
    Presented.mk W (Cell.vcomp firstCell secondCell) =
      @CategoryStruct.comp (Word W X Y)
        (Presented.wordCategory W X Y).toCategoryStruct
        first middle last (Presented.mk W firstCell) (Presented.mk W secondCell) :=
  rfl

@[simp]
theorem mk_original {X Y : B} {f g : X ⟶ Y} (α : f ⟶ g) :
    Presented.mk W (Cell.original (W := W) α) =
      (Presented.inclusion W).map₂ α :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem naturalityIsoOfIso_hom
    {a b : Presented.Localization W} {f g : a ⟶ b}
    (appA : F.obj a ⟶ G.obj a) (appB : F.obj b ⟶ G.obj b)
    (α : F.map f ≫ appB ≅ appA ≫ G.map f) (e : f ≅ g) :
    F.map₂ e.hom ▷ appB ≫
        (Pseudofunctor.StrongTrans.naturalityIsoOfIso F G appA appB α e).hom =
      α.hom ≫ appA ◁ G.map₂ e.hom := by
  dsimp [Pseudofunctor.StrongTrans.naturalityIsoOfIso]
  rw [← Category.assoc]
  rw [← comp_whiskerRight, ← F.map₂_comp, Iso.hom_inv_id, F.map₂_id]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem naturalityIsoOfIso_inv_hom
    {a b : Presented.Localization W} {f g : a ⟶ b}
    (appA : F.obj a ⟶ G.obj a) (appB : F.obj b ⟶ G.obj b)
    (α : F.map f ≫ appB ≅ appA ≫ G.map f) (e : f ≅ g) :
    F.map₂ e.inv ▷ appB ≫ α.hom =
      (Pseudofunctor.StrongTrans.naturalityIsoOfIso F G appA appB α e).hom ≫
        appA ◁ G.map₂ e.inv := by
  rw [← cancel_epi (F.map₂ e.hom ▷ appB)]
  rw [← Category.assoc]
  rw [← comp_whiskerRight, ← F.map₂_comp, Iso.hom_inv_id, F.map₂_id]
  simp only [id_whiskerRight, Category.id_comp]
  rw [← Category.assoc]
  rw [naturalityIsoOfIso_hom W F G appA appB α e]
  rw [Category.assoc]
  rw [← whiskerLeft_comp, ← G.map₂_comp, Iso.hom_inv_id, G.map₂_id]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem sourceIdNaturality (X : B) :
    Pseudofunctor.StrongTrans.naturalityIsoOfIso F G
        (η.app X) (η.app X) (η.naturality (𝟙 X))
        (Presented.sourceIdIso W X) =
      Pseudofunctor.StrongTrans.identityNaturalityIso F G ⟨X⟩ (η.app X) := by
  apply Iso.ext
  dsimp only [Pseudofunctor.StrongTrans.naturalityIsoOfIso,
    Pseudofunctor.StrongTrans.identityNaturalityIso]
  simp only [Iso.trans_hom, whiskerRightIso_hom, whiskerLeftIso_hom,
    Iso.symm_hom, PrelaxFunctor.map₂Iso_hom]
  rw [Pseudofunctor.StrongTrans.naturality_id_hom]
  change F.map₂ (Presented.sourceIdIso W X).inv ▷ η.app X ≫
      (((F.map₂ (Presented.sourceIdIso W X).hom ≫
          (F.mapId ⟨X⟩).hom) ▷ η.app X ≫
        (λ_ (η.app X)).hom ≫ (ρ_ (η.app X)).inv ≫
        η.app X ◁ ((G.mapId ⟨X⟩).inv ≫
          G.map₂ (Presented.sourceIdIso W X).inv)) ≫
        η.app X ◁ G.map₂ (Presented.sourceIdIso W X).hom) =
      (F.mapId ⟨X⟩).hom ▷ η.app X ≫
        (λ_ (η.app X)).hom ≫ (ρ_ (η.app X)).inv ≫
          η.app X ◁ (G.mapId ⟨X⟩).inv
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [← comp_whiskerRight_assoc, ← F.map₂_comp,
    Iso.inv_hom_id, F.map₂_id]
  simp only [id_whiskerRight, Category.id_comp]
  rw [← whiskerLeft_comp, ← G.map₂_comp, Iso.inv_hom_id, G.map₂_id]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem sourceCompNaturality {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Pseudofunctor.StrongTrans.naturalityIsoOfIso F G
        (η.app X) (η.app Z) (η.naturality (f ≫ g))
        (Presented.sourceCompIso W f g) =
      Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        (Word.forward W f) (Word.forward W g)
        (η.app X) (η.app Y) (η.app Z)
        (η.naturality f) (η.naturality g) := by
  apply Iso.ext
  dsimp only [Pseudofunctor.StrongTrans.naturalityIsoOfIso,
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos]
  simp only [Iso.trans_hom, whiskerRightIso_hom, whiskerLeftIso_hom,
    Iso.symm_hom, PrelaxFunctor.map₂Iso_hom]
  rw [Pseudofunctor.StrongTrans.naturality_comp_hom]
  have hF :
      (((Presented.inclusion W).comp F).mapComp f g).hom =
        F.map₂ (Presented.sourceCompIso W f g).hom ≫
          (F.mapComp (Word.forward W f) (Word.forward W g)).hom :=
    rfl
  have hG :
      (((Presented.inclusion W).comp G).mapComp f g).inv =
        (G.mapComp (Word.forward W f) (Word.forward W g)).inv ≫
          G.map₂ (Presented.sourceCompIso W f g).inv :=
    rfl
  rw [hF, hG]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [← comp_whiskerRight_assoc, ← F.map₂_comp,
    Iso.inv_hom_id, F.map₂_id]
  simp only [id_whiskerRight, Category.id_comp]
  rw [← whiskerLeft_comp, ← G.map₂_comp,
    Iso.inv_hom_id, G.map₂_id]
  simp
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem naturalityCompIsoOfIsos_left_id
    {a b : Presented.Localization W} (f : a ⟶ b)
    (appA : F.obj a ⟶ G.obj a) (appB : F.obj b ⟶ G.obj b)
    (α : F.map f ≫ appB ≅ appA ≫ G.map f) :
    Pseudofunctor.StrongTrans.naturalityIsoOfIso F G appA appB
        (Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
          (𝟙 a) f appA appA appB
          (Pseudofunctor.StrongTrans.identityNaturalityIso F G a appA) α)
        (λ_ f) = α := by
  apply Iso.ext
  dsimp [Pseudofunctor.StrongTrans.naturalityIsoOfIso,
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos,
    Pseudofunctor.StrongTrans.identityNaturalityIso]
  rw [← cancel_epi (F.map₂ (λ_ f).hom ▷ appB)]
  simp only [← Category.assoc]
  rw [← comp_whiskerRight, ← F.map₂_comp]
  simp only [Iso.hom_inv_id, F.map₂_id, id_whiskerRight,
    Category.id_comp]
  rw [← cancel_mono (appA ◁ G.map₂ (λ_ f).inv)]
  simp only [Category.assoc]
  rw [← whiskerLeft_comp, ← G.map₂_comp]
  simp only [Iso.hom_inv_id, G.map₂_id, whiskerLeft_id,
    Category.comp_id]
  rw [F.mapComp_id_left_hom, G.mapComp_id_left_inv]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  apply (cancel_epi (F.map₂ (λ_ f).hom ▷ appB)).mpr
  simp only [← Category.assoc]
  apply (cancel_mono (appA ◁ G.map₂ (λ_ f).inv)).mpr
  simp only [Category.assoc]
  slice_lhs 2 3 =>
    rw [associator_naturality_left]
  slice_lhs 1 2 => simp
  slice_lhs 2 3 =>
    rw [← whisker_exchange]
  slice_lhs 4 5 =>
    rw [← associator_inv_naturality_left]
  slice_lhs 3 4 =>
    rw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem naturalityCell {X Y : B} {first second : Word W X Y}
    (cell : Cell W first second) :
    F.map₂ (Presented.mk W cell) ▷ app W F G η ⟨Y⟩ ≫
        (naturalityWord W F G η second).hom =
      (naturalityWord W F G η first).hom ≫
        app W F G η ⟨X⟩ ◁ G.map₂ (Presented.mk W cell) := by
  induction cell
  case id word =>
    rw [mk_id, F.map₂_id, G.map₂_id]
    simp [app]
  case vcomp α β hα hβ =>
    simp only [mk_vcomp, F.map₂_comp, G.map₂_comp,
      comp_whiskerRight, whiskerLeft_comp, Category.assoc]
    rw [hβ]
    simp only [← Category.assoc]
    rw [hα]
  case original α =>
    exact η.naturality_naturality α
  case sourceId X =>
    change F.map₂ (Presented.sourceIdIso W X).hom ▷ η.app X ≫
        (Pseudofunctor.StrongTrans.identityNaturalityIso F G ⟨X⟩
          (η.app X)).hom =
      (η.naturality (𝟙 X)).hom ≫
        η.app X ◁ G.map₂ (Presented.sourceIdIso W X).hom
    rw [← sourceIdNaturality W F G η X]
    exact naturalityIsoOfIso_hom W F G _ _ _ _
  case sourceIdInv X =>
    change F.map₂ (Presented.sourceIdIso W X).inv ▷ η.app X ≫
        (η.naturality (𝟙 X)).hom =
      (Pseudofunctor.StrongTrans.identityNaturalityIso F G ⟨X⟩
          (η.app X)).hom ≫
        η.app X ◁ G.map₂ (Presented.sourceIdIso W X).inv
    rw [← sourceIdNaturality W F G η X]
    exact naturalityIsoOfIso_inv_hom W F G _ _ _ _
  case sourceComp X Y Z f g =>
    change F.map₂ (Presented.sourceCompIso W f g).hom ▷ η.app Z ≫
        (Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
          (Word.forward W f) (Word.forward W g)
          (η.app X) (η.app Y) (η.app Z)
          (η.naturality f) (η.naturality g)).hom =
      (η.naturality (f ≫ g)).hom ≫
        η.app X ◁ G.map₂ (Presented.sourceCompIso W f g).hom
    rw [← sourceCompNaturality W F G η f g]
    exact naturalityIsoOfIso_hom W F G _ _ _ _
  case sourceCompInv X Y Z f g =>
    change F.map₂ (Presented.sourceCompIso W f g).inv ▷ η.app Z ≫
        (η.naturality (f ≫ g)).hom =
      (Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
          (Word.forward W f) (Word.forward W g)
          (η.app X) (η.app Y) (η.app Z)
          (η.naturality f) (η.naturality g)).hom ≫
        η.app X ◁ G.map₂ (Presented.sourceCompIso W f g).inv
    rw [← sourceCompNaturality W F G η f g]
    exact naturalityIsoOfIso_inv_hom W F G _ _ _ _
  case markedUnit X Y f hf =>
    let e := Presented.markedEquivalence W f hf
    let α := Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
      e.hom e.inv (η.app X) (η.app Y) (η.app X)
      (η.naturality f)
      (Pseudofunctor.StrongTrans.inverseNaturalityIso F G e
        (η.app X) (η.app Y) (η.naturality f))
    have h := Pseudofunctor.StrongTrans.hom_comp_inverseNaturalityIso_unit
      F G e (η.app X) (η.app Y) (η.naturality f)
    change F.map₂ e.unit.hom ▷ η.app X ≫ α.hom =
      (Pseudofunctor.StrongTrans.identityNaturalityIso F G ⟨X⟩
        (η.app X)).hom ≫ η.app X ◁ G.map₂ e.unit.hom
    rw [← h]
    exact naturalityIsoOfIso_inv_hom W F G _ _ α e.unit.symm
  case markedUnitInv X Y f hf =>
    let e := Presented.markedEquivalence W f hf
    let α := Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
      e.hom e.inv (η.app X) (η.app Y) (η.app X)
      (η.naturality f)
      (Pseudofunctor.StrongTrans.inverseNaturalityIso F G e
        (η.app X) (η.app Y) (η.naturality f))
    have h := Pseudofunctor.StrongTrans.hom_comp_inverseNaturalityIso_unit
      F G e (η.app X) (η.app Y) (η.naturality f)
    change F.map₂ e.unit.inv ▷ η.app X ≫
        (Pseudofunctor.StrongTrans.identityNaturalityIso F G ⟨X⟩
          (η.app X)).hom =
      α.hom ≫ η.app X ◁ G.map₂ e.unit.inv
    rw [← h]
    exact naturalityIsoOfIso_hom W F G _ _ α e.unit.symm
  case markedCounit X Y f hf =>
    let e := Presented.markedEquivalence W f hf
    let α := Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
      e.inv e.hom (η.app Y) (η.app X) (η.app Y)
      (Pseudofunctor.StrongTrans.inverseNaturalityIso F G e
        (η.app X) (η.app Y) (η.naturality f))
      (η.naturality f)
    have h := Pseudofunctor.StrongTrans.inverseNaturalityIso_comp_hom_counit
      F G e (η.app X) (η.app Y) (η.naturality f)
    change F.map₂ e.counit.hom ▷ η.app Y ≫
        (Pseudofunctor.StrongTrans.identityNaturalityIso F G ⟨Y⟩
          (η.app Y)).hom =
      α.hom ≫ η.app Y ◁ G.map₂ e.counit.hom
    rw [← h]
    exact naturalityIsoOfIso_hom W F G _ _ α e.counit
  case markedCounitInv X Y f hf =>
    let e := Presented.markedEquivalence W f hf
    let α := Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
      e.inv e.hom (η.app Y) (η.app X) (η.app Y)
      (Pseudofunctor.StrongTrans.inverseNaturalityIso F G e
        (η.app X) (η.app Y) (η.naturality f))
      (η.naturality f)
    have h := Pseudofunctor.StrongTrans.inverseNaturalityIso_comp_hom_counit
      F G e (η.app X) (η.app Y) (η.naturality f)
    change F.map₂ e.counit.inv ▷ η.app Y ≫ α.hom =
      (Pseudofunctor.StrongTrans.identityNaturalityIso F G ⟨Y⟩
        (η.app Y)).hom ≫ η.app Y ◁ G.map₂ e.counit.inv
    rw [← h]
    exact naturalityIsoOfIso_inv_hom W F G _ _ α e.counit
  case leftUnitor X Y word =>
    let e : Word.append W (Word.nil X) word ≅ word :=
      Presented.wordLeftUnitorIso W word
    let α := Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
      (Word.nil X) word (η.app X) (η.app X) (η.app Y)
      (Pseudofunctor.StrongTrans.identityNaturalityIso F G ⟨X⟩ (η.app X))
      (naturalityWord W F G η word)
    have h := naturalityCompIsoOfIsos_left_id W F G word
      (η.app X) (η.app Y) (naturalityWord W F G η word)
    change F.map₂ e.hom ▷ η.app Y ≫
        (naturalityWord W F G η word).hom =
      α.hom ≫ η.app X ◁ G.map₂ e.hom
    rw [← h]
    exact naturalityIsoOfIso_hom W F G _ _ α e
  case leftUnitorInv X Y word =>
    let e : Word.append W (Word.nil X) word ≅ word :=
      Presented.wordLeftUnitorIso W word
    let α := Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
      (Word.nil X) word (η.app X) (η.app X) (η.app Y)
      (Pseudofunctor.StrongTrans.identityNaturalityIso F G ⟨X⟩ (η.app X))
      (naturalityWord W F G η word)
    have h := naturalityCompIsoOfIsos_left_id W F G word
      (η.app X) (η.app Y) (naturalityWord W F G η word)
    change F.map₂ e.inv ▷ η.app Y ≫ α.hom =
      (naturalityWord W F G η word).hom ≫
        η.app X ◁ G.map₂ e.inv
    rw [← h]
    exact naturalityIsoOfIso_inv_hom W F G _ _ α e
  case whiskerLeft X Y Z preword first second cell hcell =>
    convert
      Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos_naturality_right
        F G preword (Presented.mk W cell)
        (η.app X) (η.app Y) (η.app Z)
        (naturalityWord W F G η preword)
        (naturalityWord W F G η first)
        (naturalityWord W F G η second) hcell using 1 <;> rfl
  case whiskerRight X Y Z first second cell postword hcell =>
    convert
      Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos_naturality_left
        F G (Presented.mk W cell) postword
        (η.app X) (η.app Y) (η.app Z)
        (naturalityWord W F G η first)
        (naturalityWord W F G η second)
        (naturalityWord W F G η postword) hcell using 1 <;> rfl
  case associator X Y Z T first second third =>
    let e : Word.append W (Word.append W first second) third ≅
        Word.append W first (Word.append W second third) :=
      Presented.wordAssociatorIso W first second third
    let α := Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
      (first ≫ second) third (η.app X) (η.app Z) (η.app T)
      (Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        first second (η.app X) (η.app Y) (η.app Z)
        (naturalityWord W F G η first)
        (naturalityWord W F G η second))
      (naturalityWord W F G η third)
    have h := Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos_assoc
      F G first second third (η.app X) (η.app Y) (η.app Z)
      (η.app T) (naturalityWord W F G η first)
      (naturalityWord W F G η second) (naturalityWord W F G η third)
    change Pseudofunctor.StrongTrans.naturalityIsoOfIso F G
        (η.app X) (η.app T) α e =
      Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        first (Word.append W second third) (η.app X) (η.app Y) (η.app T)
        (naturalityWord W F G η first)
        (Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
          second third (η.app Y) (η.app Z) (η.app T)
          (naturalityWord W F G η second)
          (naturalityWord W F G η third)) at h
    have base := naturalityIsoOfIso_hom W F G (η.app X) (η.app T) α e
    rw [h] at base
    convert base using 1 <;> rfl
  case associatorInv X Y Z T first second third =>
    let e : Word.append W (Word.append W first second) third ≅
        Word.append W first (Word.append W second third) :=
      Presented.wordAssociatorIso W first second third
    let α := Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
      (first ≫ second) third (η.app X) (η.app Z) (η.app T)
      (Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        first second (η.app X) (η.app Y) (η.app Z)
        (naturalityWord W F G η first)
        (naturalityWord W F G η second))
      (naturalityWord W F G η third)
    have h := Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos_assoc
      F G first second third (η.app X) (η.app Y) (η.app Z)
      (η.app T) (naturalityWord W F G η first)
      (naturalityWord W F G η second) (naturalityWord W F G η third)
    change Pseudofunctor.StrongTrans.naturalityIsoOfIso F G
        (η.app X) (η.app T) α e =
      Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        first (Word.append W second third) (η.app X) (η.app Y) (η.app T)
        (naturalityWord W F G η first)
        (Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
          second third (η.app Y) (η.app Z) (η.app T)
          (naturalityWord W F G η second)
          (naturalityWord W F G η third)) at h
    have base := naturalityIsoOfIso_inv_hom W F G
      (η.app X) (η.app T) α e
    rw [h] at base
    convert base using 1 <;> rfl
  case rightUnitor X Y word =>
    let e : Word.append W word (Word.nil Y) ≅ word :=
      Presented.wordRightUnitorIso W word
    let α := Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
      word (Word.nil Y) (η.app X) (η.app Y) (η.app Y)
      (naturalityWord W F G η word)
      (Pseudofunctor.StrongTrans.identityNaturalityIso F G ⟨Y⟩ (η.app Y))
    have h := Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos_right_id
      F G word (η.app X) (η.app Y) (naturalityWord W F G η word)
    change F.map₂ e.hom ▷ η.app Y ≫
        (naturalityWord W F G η word).hom =
      α.hom ≫ η.app X ◁ G.map₂ e.hom
    rw [← h]
    exact naturalityIsoOfIso_hom W F G _ _ α e
  case rightUnitorInv X Y word =>
    let e : Word.append W word (Word.nil Y) ≅ word :=
      Presented.wordRightUnitorIso W word
    let α := Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
      word (Word.nil Y) (η.app X) (η.app Y) (η.app Y)
      (naturalityWord W F G η word)
      (Pseudofunctor.StrongTrans.identityNaturalityIso F G ⟨Y⟩ (η.app Y))
    have h := Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos_right_id
      F G word (η.app X) (η.app Y) (naturalityWord W F G η word)
    change F.map₂ e.inv ▷ η.app Y ≫ α.hom =
      (naturalityWord W F G η word).hom ≫
        η.app X ◁ G.map₂ e.inv
    rw [← h]
    exact naturalityIsoOfIso_inv_hom W F G _ _ α e
  case transport source_eq target_eq cell hcell =>
    cases source_eq
    cases target_eq
    rw [show Presented.mk W (Cell.transport rfl rfl cell) =
      Presented.mk W cell from Quot.sound (Presented.Rel.transport_refl cell)]
    exact hcell

/-- Naturality of the recursively extended constraint for every quotient
2-cell in the presented localization. -/
theorem naturalityHom {X Y : B} {first second : Word W X Y}
    (θ : Presented.Hom W first second) :
    F.map₂ θ ▷ app W F G η ⟨Y⟩ ≫
        (naturalityWord W F G η second).hom =
      (naturalityWord W F G η first).hom ≫
        app W F G η ⟨X⟩ ◁ G.map₂ θ :=
  Quot.inductionOn θ (naturalityCell W F G η)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Extend a strong transformation from the source generators to every
presented marked zigzag. -/
noncomputable def extension : F ⟶ G where
  app := app W F G η
  naturality := naturality W F G η
  naturality_naturality := by
    intro A B first second θ
    rcases A with ⟨X⟩
    rcases B with ⟨Y⟩
    exact naturalityHom W F G η θ
  naturality_id := by
    rintro ⟨X⟩
    change (Pseudofunctor.StrongTrans.identityNaturalityIso F G ⟨X⟩
        (app W F G η ⟨X⟩)).hom ≫
          app W F G η ⟨X⟩ ◁ (G.mapId ⟨X⟩).hom =
      (F.mapId ⟨X⟩).hom ▷ app W F G η ⟨X⟩ ≫
        (λ_ (app W F G η ⟨X⟩)).hom ≫
          (ρ_ (app W F G η ⟨X⟩)).inv
    dsimp [Pseudofunctor.StrongTrans.identityNaturalityIso]
    simp
  naturality_comp := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ first second
    change (Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        first second (app W F G η ⟨X⟩) (app W F G η ⟨Y⟩)
        (app W F G η ⟨Z⟩) (naturalityWord W F G η first)
        (naturalityWord W F G η second)).hom ≫
          app W F G η ⟨X⟩ ◁ (G.mapComp first second).hom = _
    dsimp [Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos]
    simp

@[simp]
theorem extension_app_mk (X : B) :
    (extension W F G η).app ⟨X⟩ = η.app X :=
  rfl

@[simp]
theorem extension_naturality_forward {X Y : B} (f : X ⟶ Y) :
    (extension W F G η).naturality (Word.forward W f) = η.naturality f :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Restricting the extended strong transformation recovers the original
one up to an identity-component invertible modification. -/
noncomputable def restrictionExtensionIso :
    ((Presented.inclusion W).localPrecomposition F G).obj
        (extension W F G η) ≅ η :=
  Pseudofunctor.StrongTrans.isoMk
    (fun X => Iso.refl (η.app X))
    (by
      intro X Y f
      change F.map (Word.forward W f) ◁ 𝟙 (η.app Y) ≫
          (η.naturality f).hom =
        (η.naturality f).hom ≫ 𝟙 (η.app X) ▷
          G.map (Word.forward W f)
      simp only [whiskerLeft_id, id_whiskerRight, Category.id_comp]
      exact (Category.comp_id _).symm)

variable {firstTrans secondTrans : F ⟶ G}

/-- Object components of a modification extended from the source
generators. -/
def modificationApp
    (Γ : ((Presented.inclusion W).localPrecomposition F G).obj firstTrans ⟶
      ((Presented.inclusion W).localPrecomposition F G).obj secondTrans) :
    ∀ X : Presented.Localization W,
      firstTrans.app X ⟶ secondTrans.app X
  | ⟨X⟩ => Γ.as.app X

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Modification naturality extends from forward generators to identities,
formal inverses of marked arrows, and binary composites. -/
theorem modificationNaturalityWord
    (Γ : ((Presented.inclusion W).localPrecomposition F G).obj firstTrans ⟶
      ((Presented.inclusion W).localPrecomposition F G).obj secondTrans) :
    ∀ {X Y : B} (word : Word W X Y),
      Pseudofunctor.StrongTrans.NaturalityAt firstTrans secondTrans
        (modificationApp W F G Γ) word
  | _, _, .atom (.forward f) => Γ.as.naturality f
  | _, _, .atom (.backward f hf) =>
      Pseudofunctor.StrongTrans.naturalityAt_inv firstTrans secondTrans
        (modificationApp W F G Γ) (Presented.markedEquivalence W f hf)
        (Γ.as.naturality f)
  | X, _, .nil _ =>
      Pseudofunctor.StrongTrans.naturalityAt_id firstTrans secondTrans
        (modificationApp W F G Γ) ⟨X⟩
  | _, _, .comp first second =>
      Pseudofunctor.StrongTrans.naturalityAt_comp firstTrans secondTrans
        (modificationApp W F G Γ)
        (modificationNaturalityWord Γ first)
        (modificationNaturalityWord Γ second)

/-- Extend a modification from the restricted strong transformations to all
presented zigzags. -/
def modificationExtension
    (Γ : ((Presented.inclusion W).localPrecomposition F G).obj firstTrans ⟶
      ((Presented.inclusion W).localPrecomposition F G).obj secondTrans) :
    firstTrans ⟶ secondTrans :=
  ⟨{ app := modificationApp W F G Γ
     naturality := by
       rintro ⟨X⟩ ⟨Y⟩ word
       exact modificationNaturalityWord W F G Γ word }⟩

@[simp]
theorem modificationExtension_app_mk
    (Γ : ((Presented.inclusion W).localPrecomposition F G).obj firstTrans ⟶
      ((Presented.inclusion W).localPrecomposition F G).obj secondTrans)
    (X : B) :
    (modificationExtension W F G Γ).as.app ⟨X⟩ = Γ.as.app X :=
  rfl

/-- Restricting an extended modification recovers it exactly. -/
theorem restrictionModificationExtension
    (Γ : ((Presented.inclusion W).localPrecomposition F G).obj firstTrans ⟶
      ((Presented.inclusion W).localPrecomposition F G).obj secondTrans) :
    ((Presented.inclusion W).localPrecomposition F G).map
        (modificationExtension W F G Γ) = Γ := by
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro X
  rfl

/-- The canonical inclusion is surjective on the unchanged object set. -/
theorem inclusion_obj_surjective :
    Function.Surjective (Presented.inclusion W).obj := by
  rintro ⟨X⟩
  exact ⟨X, rfl⟩

/-- Precomposition by the presented inclusion is faithful on modifications. -/
theorem localPrecomposition_faithful :
    ((Presented.inclusion W).localPrecomposition F G).Faithful :=
  Pseudofunctor.localPrecomposition_faithful_of_obj_surjective
    (Presented.inclusion W) (inclusion_obj_surjective W) F G

/-- Every modification between restricted strong transformations extends to
the presented localization. -/
theorem localPrecomposition_full :
    ((Presented.inclusion W).localPrecomposition F G).Full where
  map_surjective := by
    intro firstTrans secondTrans Γ
    exact ⟨modificationExtension W F G Γ,
      restrictionModificationExtension W F G Γ⟩

/-- Every strong transformation between restricted target pseudofunctors is
isomorphic to the restriction of its recursive marked-zigzag extension. -/
theorem localPrecomposition_essSurj :
    ((Presented.inclusion W).localPrecomposition F G).EssSurj where
  mem_essImage := by
    intro η
    exact ⟨extension W F G η, ⟨restrictionExtensionIso W F G η⟩⟩

/-- **Local universal property of the marked-zigzag presentation.**
Precomposition by the canonical inclusion is an equivalence on the category
of strong transformations and modifications. -/
theorem localPrecomposition_isEquivalence :
    ((Presented.inclusion W).localPrecomposition F G).IsEquivalence where
  faithful := localPrecomposition_faithful W F G
  full := localPrecomposition_full W F G
  essSurj := localPrecomposition_essSurj W F G

/-- The presented marked-zigzag inclusion satisfies the complete
bicategorical localization universal property. -/
theorem inclusion_isBicategoricalLocalization :
    W.IsBicategoricalLocalization (Presented.inclusion W) where
  inverts := Presented.inclusion_inverts W
  lift _ _ Q hQ := InversionData.factorsThrough W Q hQ
  local_equivalence _ _ F G := localPrecomposition_isEquivalence W F G
end CategoryTheory.Bicategory.MarkedZigzag.LocalExtension
