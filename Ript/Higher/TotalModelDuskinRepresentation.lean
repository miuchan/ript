import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
import Ript.Higher.TotalModelDuskinNerve

/-!
# Coordinate representation of the total-model Duskin nerve

The inverse representation is built through a constructor-friendly copy of a
finite ordinal.  Its morphisms distinguish identity and strict arrows by data,
so normalization can eliminate into computational structure without dependent
`Eq.rec` noise.  This category is then compared with Mathlib's usual thin
category on `Fin (n + 1)`.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Higher

open CategoryTheory
open CategoryTheory.Bicategory

universe u v w uB vB wB

namespace TotalModelDuskinRepresentation

namespace DegenerateCoherence

variable {X : Type uB} [Bicategory.{wB, vB} X] {A B C D : X}

/-- Coherence for a tetrahedron whose four vertices are equal. -/
theorem allIdentity (A : X) :
    (Bicategory.leftUnitor (𝟙 A)).hom ▷ 𝟙 A ≫
        (Bicategory.leftUnitor (𝟙 A)).hom =
      (Bicategory.associator (𝟙 A) (𝟙 A) (𝟙 A)).hom ≫
        𝟙 A ◁ (Bicategory.leftUnitor (𝟙 A)).hom ≫
        (Bicategory.leftUnitor (𝟙 A)).hom := by
  bicategory

/-- Coherence for two repeated initial edges followed by one strict edge. -/
theorem leftLeft (f : A ⟶ D) :
    (Bicategory.leftUnitor (𝟙 A)).hom ▷ f ≫
        (Bicategory.leftUnitor f).hom =
      (Bicategory.associator (𝟙 A) (𝟙 A) f).hom ≫
        𝟙 A ◁ (Bicategory.leftUnitor f).hom ≫
        (Bicategory.leftUnitor f).hom := by
  bicategory

/-- Coherence for a repeated initial vertex and repeated final vertex. -/
theorem leftRight (f : A ⟶ C) :
    (Bicategory.leftUnitor f).hom ▷ 𝟙 C ≫
        (Bicategory.rightUnitor f).hom =
      (Bicategory.associator (𝟙 A) f (𝟙 C)).hom ≫
        𝟙 A ◁ (Bicategory.rightUnitor f).hom ≫
        (Bicategory.leftUnitor f).hom := by
  bicategory

/-- Naturality coherence for a repeated initial vertex. -/
theorem leftNaturality
    (f : A ⟶ C) (g : C ⟶ D) (h : A ⟶ D) (theta : f ≫ g ⟶ h) :
    (Bicategory.leftUnitor f).hom ▷ g ≫ theta =
      (Bicategory.associator (𝟙 A) f g).hom ≫
        𝟙 A ◁ theta ≫ (Bicategory.leftUnitor h).hom := by
  bicategory

/-- Coherence for one strict edge followed by two repeated edges. -/
theorem rightRight (f : A ⟶ B) :
    (Bicategory.rightUnitor f).hom ▷ 𝟙 B ≫
        (Bicategory.rightUnitor f).hom =
      (Bicategory.associator f (𝟙 B) (𝟙 B)).hom ≫
        f ◁ (Bicategory.leftUnitor (𝟙 B)).hom ≫
        (Bicategory.rightUnitor f).hom := by
  bicategory

/-- Triangle coherence for a repeated middle vertex. -/
theorem middleIdentity
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D) (theta : f ≫ g ⟶ h) :
    (Bicategory.rightUnitor f).hom ▷ g ≫ theta =
      (Bicategory.associator f (𝟙 B) g).hom ≫
        f ◁ (Bicategory.leftUnitor g).hom ≫ theta := by
  bicategory

/-- Naturality coherence for a repeated final vertex. -/
theorem rightNaturality
    (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C) (theta : f ≫ g ⟶ h) :
    theta ▷ 𝟙 C ≫ (Bicategory.rightUnitor h).hom =
      (Bicategory.associator f g (𝟙 C)).hom ≫
        f ◁ (Bicategory.rightUnitor g).hom ≫ theta := by
  bicategory

end DegenerateCoherence

namespace TotalModelBridge

variable {A B C : ResourceModel.{u, v, w}}

/-- Bicategory identity notation is the concrete total-model identity. -/
@[simp]
theorem id_eq (A : ResourceModel.{u, v, w}) :
    (𝟙 A : ResourceModelHom A A) = ResourceModelHom.id A :=
  rfl

/-- Bicategory composition notation is concrete total-model composition. -/
@[simp]
theorem comp_eq (f : ResourceModelHom A B) (g : ResourceModelHom B C) :
    (@CategoryStruct.comp ResourceModel.{u, v, w}
      resourceModelBicategory.toCategoryStruct A B C f g) = f.comp g :=
  rfl

/-- Bicategorical left whiskering is the concrete total-model operation. -/
@[simp]
theorem whiskerLeft_eq (f : ResourceModelHom A B)
    {g h : ResourceModelHom B C} (eta : ResourceModelTransformation g h) :
    (@Bicategory.whiskerLeft ResourceModel.{u, v, w}
      resourceModelBicategory A B C f g h eta) =
      ResourceModelTransformation.whiskerLeft f eta :=
  rfl

/-- Bicategorical right whiskering is the concrete total-model operation. -/
@[simp]
theorem whiskerRight_eq {f g : ResourceModelHom A B}
    (eta : ResourceModelTransformation f g) (h : ResourceModelHom B C) :
    (@Bicategory.whiskerRight ResourceModel.{u, v, w}
      resourceModelBicategory A B C f g eta h) =
      ResourceModelTransformation.whiskerRight eta h :=
  rfl

/-- The exposed associator transformation is the bicategory associator. -/
@[simp]
theorem associator_eq
    {D : ResourceModel.{u, v, w}}
    (f : ResourceModelHom A B) (g : ResourceModelHom B C)
    (h : ResourceModelHom C D) :
    TotalModelSimplicial.associatorTransformation f g h =
      (@Bicategory.associator ResourceModel.{u, v, w}
        resourceModelBicategory A B C D f g h).hom :=
  rfl

end TotalModelBridge

/-- The generic all-identity coherence equation transported to the concrete
total-model operations. -/
theorem totalModelAllIdentityCoherence (A : ResourceModel.{u, v, w}) :
    ResourceModelTransformation.whiskerRight
          (Bicategory.leftUnitor
            (B := ResourceModel.{u, v, w}) (ResourceModelHom.id A)).hom
          (ResourceModelHom.id A) ≫
        (Bicategory.leftUnitor
          (B := ResourceModel.{u, v, w}) (ResourceModelHom.id A)).hom =
      TotalModelSimplicial.associatorTransformation
          (ResourceModelHom.id A) (ResourceModelHom.id A)
          (ResourceModelHom.id A) ≫
        ResourceModelTransformation.whiskerLeft
          (ResourceModelHom.id A)
          (Bicategory.leftUnitor
            (B := ResourceModel.{u, v, w}) (ResourceModelHom.id A)).hom ≫
        (Bicategory.leftUnitor
          (B := ResourceModel.{u, v, w}) (ResourceModelHom.id A)).hom := by
  simpa only [TotalModelBridge.id_eq, TotalModelBridge.comp_eq,
    TotalModelBridge.whiskerLeft_eq, TotalModelBridge.whiskerRight_eq,
    TotalModelBridge.associator_eq] using
    (DegenerateCoherence.allIdentity
      (X := ResourceModel.{u, v, w}) A)

namespace TotalModelDegenerateCoherence

variable {A B C D : ResourceModel.{u, v, w}}

theorem leftLeft (f : ResourceModelHom A D) :
    ResourceModelTransformation.whiskerRight
          (Bicategory.leftUnitor
            (B := ResourceModel.{u, v, w}) (ResourceModelHom.id A)).hom f ≫
        (Bicategory.leftUnitor (B := ResourceModel.{u, v, w}) f).hom =
      TotalModelSimplicial.associatorTransformation
          (ResourceModelHom.id A) (ResourceModelHom.id A) f ≫
        ResourceModelTransformation.whiskerLeft (ResourceModelHom.id A)
          (Bicategory.leftUnitor (B := ResourceModel.{u, v, w}) f).hom ≫
        (Bicategory.leftUnitor (B := ResourceModel.{u, v, w}) f).hom := by
  simpa only [TotalModelBridge.id_eq, TotalModelBridge.comp_eq,
    TotalModelBridge.whiskerLeft_eq, TotalModelBridge.whiskerRight_eq,
    TotalModelBridge.associator_eq] using
    (DegenerateCoherence.leftLeft (X := ResourceModel.{u, v, w}) f)

theorem leftRight (f : ResourceModelHom A C) :
    ResourceModelTransformation.whiskerRight
          (Bicategory.leftUnitor (B := ResourceModel.{u, v, w}) f).hom
          (ResourceModelHom.id C) ≫
        (Bicategory.rightUnitor (B := ResourceModel.{u, v, w}) f).hom =
      TotalModelSimplicial.associatorTransformation
          (ResourceModelHom.id A) f (ResourceModelHom.id C) ≫
        ResourceModelTransformation.whiskerLeft (ResourceModelHom.id A)
          (Bicategory.rightUnitor (B := ResourceModel.{u, v, w}) f).hom ≫
        (Bicategory.leftUnitor (B := ResourceModel.{u, v, w}) f).hom := by
  simpa only [TotalModelBridge.id_eq, TotalModelBridge.comp_eq,
    TotalModelBridge.whiskerLeft_eq, TotalModelBridge.whiskerRight_eq,
    TotalModelBridge.associator_eq] using
    (DegenerateCoherence.leftRight (X := ResourceModel.{u, v, w}) f)

theorem leftNaturality
    (f : ResourceModelHom A C) (g : ResourceModelHom C D)
    (h : ResourceModelHom A D) (theta : ResourceModelTransformation (f.comp g) h) :
    ResourceModelTransformation.whiskerRight
          (Bicategory.leftUnitor (B := ResourceModel.{u, v, w}) f).hom g ≫ theta =
      TotalModelSimplicial.associatorTransformation
          (ResourceModelHom.id A) f g ≫
        ResourceModelTransformation.whiskerLeft (ResourceModelHom.id A) theta ≫
        (Bicategory.leftUnitor (B := ResourceModel.{u, v, w}) h).hom := by
  simpa only [TotalModelBridge.id_eq, TotalModelBridge.comp_eq,
    TotalModelBridge.whiskerLeft_eq, TotalModelBridge.whiskerRight_eq,
    TotalModelBridge.associator_eq] using
    (DegenerateCoherence.leftNaturality
      (X := ResourceModel.{u, v, w}) f g h theta)

theorem rightRight (f : ResourceModelHom A B) :
    ResourceModelTransformation.whiskerRight
          (Bicategory.rightUnitor (B := ResourceModel.{u, v, w}) f).hom
          (ResourceModelHom.id B) ≫
        (Bicategory.rightUnitor (B := ResourceModel.{u, v, w}) f).hom =
      TotalModelSimplicial.associatorTransformation
          f (ResourceModelHom.id B) (ResourceModelHom.id B) ≫
        ResourceModelTransformation.whiskerLeft f
          (Bicategory.leftUnitor
            (B := ResourceModel.{u, v, w}) (ResourceModelHom.id B)).hom ≫
        (Bicategory.rightUnitor (B := ResourceModel.{u, v, w}) f).hom := by
  simpa only [TotalModelBridge.id_eq, TotalModelBridge.comp_eq,
    TotalModelBridge.whiskerLeft_eq, TotalModelBridge.whiskerRight_eq,
    TotalModelBridge.associator_eq] using
    (DegenerateCoherence.rightRight (X := ResourceModel.{u, v, w}) f)

theorem middleIdentity
    (f : ResourceModelHom A B) (g : ResourceModelHom B D)
    (h : ResourceModelHom A D) (theta : ResourceModelTransformation (f.comp g) h) :
    ResourceModelTransformation.whiskerRight
          (Bicategory.rightUnitor (B := ResourceModel.{u, v, w}) f).hom g ≫ theta =
      TotalModelSimplicial.associatorTransformation
          f (ResourceModelHom.id B) g ≫
        ResourceModelTransformation.whiskerLeft f
          (Bicategory.leftUnitor (B := ResourceModel.{u, v, w}) g).hom ≫ theta := by
  simpa only [TotalModelBridge.id_eq, TotalModelBridge.comp_eq,
    TotalModelBridge.whiskerLeft_eq, TotalModelBridge.whiskerRight_eq,
    TotalModelBridge.associator_eq] using
    (DegenerateCoherence.middleIdentity
      (X := ResourceModel.{u, v, w}) f g h theta)

theorem rightNaturality
    (f : ResourceModelHom A B) (g : ResourceModelHom B C)
    (h : ResourceModelHom A C) (theta : ResourceModelTransformation (f.comp g) h) :
    ResourceModelTransformation.whiskerRight theta (ResourceModelHom.id C) ≫
        (Bicategory.rightUnitor (B := ResourceModel.{u, v, w}) h).hom =
      TotalModelSimplicial.associatorTransformation
          f g (ResourceModelHom.id C) ≫
        ResourceModelTransformation.whiskerLeft f
          (Bicategory.rightUnitor (B := ResourceModel.{u, v, w}) g).hom ≫ theta := by
  simpa only [TotalModelBridge.id_eq, TotalModelBridge.comp_eq,
    TotalModelBridge.whiskerLeft_eq, TotalModelBridge.whiskerRight_eq,
    TotalModelBridge.associator_eq] using
    (DegenerateCoherence.rightNaturality
      (X := ResourceModel.{u, v, w}) f g h theta)

end TotalModelDegenerateCoherence

/-- A constructor-friendly copy of the finite ordinal `[n]`. -/
@[ext]
structure Ordinal (n : Nat) where
  /-- The underlying finite index. -/
  index : Fin (n + 1)

namespace Ordinal

/-- Morphisms are either definitional identities or strict inequalities. -/
inductive Hom {n : Nat} : Ordinal n → Ordinal n → Type
  | refl (i : Ordinal n) : Hom i i
  | strict {i j : Ordinal n} (hij : i.index < j.index) : Hom i j

namespace Hom

/-- Composition of constructor-normal ordinal morphisms. -/
def comp {n : Nat} {i j k : Ordinal n} : Hom i j → Hom j k → Hom i k
  | .refl _, second => second
  | first, .refl _ => first
  | .strict hij, .strict hjk => .strict (hij.trans hjk)

@[simp]
theorem refl_comp {n : Nat} {i j : Ordinal n} (f : Hom i j) :
    comp (.refl i) f = f := by
  cases f <;> rfl

@[simp]
theorem comp_refl {n : Nat} {i j : Ordinal n} (f : Hom i j) :
    comp f (.refl j) = f := by
  cases f <;> rfl

@[simp]
theorem comp_assoc {n : Nat} {i j k l : Ordinal n}
    (f : Hom i j) (g : Hom j k) (h : Hom k l) :
    comp (comp f g) h = comp f (comp g h) := by
  cases f <;> cases g <;> cases h <;> rfl

end Hom

/-- The constructor-normal finite ordinal as a small category. -/
instance smallCategory (n : Nat) : SmallCategory (Ordinal n) where
  Hom := Hom
  id := Hom.refl
  comp := Hom.comp
  id_comp := Hom.refl_comp
  comp_id := Hom.comp_refl
  assoc := Hom.comp_assoc

@[simp]
theorem category_id {n : Nat} (i : Ordinal n) :
    (𝟙 i : i ⟶ i) = Hom.refl i :=
  rfl

@[simp]
theorem category_refl_comp {n : Nat} {i j : Ordinal n} (f : i ⟶ j) :
    (Hom.refl i : i ⟶ i) ≫ f = f := by
  cases f <;> rfl

@[simp]
theorem category_comp_refl {n : Nat} {i j : Ordinal n} (f : i ⟶ j) :
    f ≫ (Hom.refl j : j ⟶ j) = f := by
  cases f <;> rfl

/-- Category notation reduces to the computable constructor-level
composition.  This bridge is especially useful under dependent transports. -/
theorem category_comp {n : Nat} {i j k : Ordinal n}
    (f : i ⟶ j) (g : j ⟶ k) :
    (@CategoryStruct.comp (Ordinal n) (smallCategory n).toCategoryStruct
      i j k f g) = Hom.comp f g :=
  rfl

/-- Every constructor-normal ordinal hom-type is a subsingleton. -/
instance homSubsingleton {n : Nat} (i j : Ordinal n) :
    Subsingleton (i ⟶ j) where
  allEq first second := by
    cases first with
    | refl =>
        cases second with
        | refl => rfl
        | strict h => exact h.false.elim
    | strict h =>
        cases second with
        | refl => exact h.false.elim
        | strict _ => rfl

/-- Every ordinal morphism witnesses weak increase of its endpoints. -/
theorem Hom.le {n : Nat} {i j : Ordinal n} (f : i ⟶ j) : i.index ≤ j.index :=
  match f with
  | .refl _ => le_rfl
  | .strict hij => hij.le

/-- Construct the unique constructor-normal arrow from a weak inequality. -/
def Hom.ofLE {n : Nat} {i j : Ordinal n} (hij : i.index ≤ j.index) : i ⟶ j := by
  if equality : i.index = j.index then
    have objectEquality : i = j := Ordinal.ext equality
    subst j
    exact Hom.refl i
  else
    exact Hom.strict (lt_of_le_of_ne hij equality)

@[simp]
theorem Hom.ofLE_refl {n : Nat} (i : Ordinal n) :
    Hom.ofLE (show i.index ≤ i.index from le_rfl) = Hom.refl i := by
  simp [Hom.ofLE]

@[simp]
theorem Hom.ofLE_of_lt {n : Nat} {i j : Ordinal n}
    (hij : i.index < j.index) :
    Hom.ofLE hij.le = Hom.strict hij := by
  simp [Hom.ofLE, hij.ne]

/-- Forget constructor normal form to Mathlib's thin category on `Fin`. -/
def toFin (n : Nat) : Functor (Ordinal n) (Fin (n + 1)) where
  obj i := i.index
  map f := homOfLE (Hom.le f)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Rebuild constructor normal form from Mathlib's thin finite ordinal. -/
def fromFin (n : Nat) : Functor (Fin (n + 1)) (Ordinal n) where
  obj i := ⟨i⟩
  map f := Hom.ofLE (leOfHom f)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp]
theorem fromFin_obj_index {n : Nat} (i : Fin (n + 1)) :
    ((fromFin n).obj i).index = i :=
  rfl

@[simp]
theorem fromFin_map_homOfLE {n : Nat} {i j : Fin (n + 1)}
    (hij : i ≤ j) :
    (fromFin n).map (homOfLE hij) =
      Hom.ofLE (i := (fromFin n).obj i) (j := (fromFin n).obj j) hij :=
  rfl

theorem fromFin_map_strict {n : Nat} {i j : Fin (n + 1)}
    (hij : i < j) :
    (fromFin n).map (homOfLE hij.le) = Hom.strict hij := by
  exact Hom.ofLE_of_lt hij

instance toFin_faithful (n : Nat) : (toFin n).Faithful where
  map_injective _ := Subsingleton.elim _ _

instance toFin_full (n : Nat) : (toFin n).Full where
  map_surjective {X Y} f := by
    change X.index ⟶ Y.index at f
    exact ⟨Hom.ofLE (leOfHom f), Subsingleton.elim _ _⟩

instance toFin_essSurj (n : Nat) : (toFin n).EssSurj :=
  Functor.essSurj_of_surj fun i ↦ ⟨⟨i⟩, by
    change i = i
    rfl⟩

noncomputable instance toFin_isEquivalence (n : Nat) :
    (toFin n).IsEquivalence where

/-- The constructor-normal ordinal is explicitly and computably equivalent to
Mathlib's standard thin finite ordinal. -/
def equivalence (n : Nat) : Ordinal n ≌ Fin (n + 1) where
  functor := toFin n
  inverse := fromFin n
  unitIso := NatIso.ofComponents (fun i => eqToIso (by
    apply Ordinal.ext
    rfl)) (fun _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun i => Iso.refl i)
    (fun _ => Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

end Ordinal

/-- Coordinate simplices from the semi-simplicial presentation. -/
abbrev CoordinateSimplex := TotalModelSemiSimplicial.Simplex

/-- The locally discrete bicategory on the constructor-normal ordinal. -/
abbrev NormalOrdinal (n : Nat) := LocallyDiscrete (Ordinal n)

/-- The explicit forgetful functor, lifted to a strictly unitary lax functor
toward Mathlib's finite ordinal bicategory. -/
def normalToFiniteOrdinal (n : Nat) :
    StrictlyUnitaryLaxFunctor (NormalOrdinal n)
      (TotalModelDuskinNerve.FiniteOrdinal n) :=
  (TotalModelDuskinNerve.locallyDiscretePseudofunctor
    (Ordinal.toFin n)).toStrictlyUnitaryLaxFunctor

/-- Constructor-level core of the explicit finite-to-normal ordinal map. All
2-cell laws are unique because the target is locally discrete. -/
def finiteToNormalOrdinalCore (n : Nat) :
    StrictlyUnitaryLaxFunctorCore
      (TotalModelDuskinNerve.FiniteOrdinal n) (NormalOrdinal n) where
  obj i := LocallyDiscrete.mk ⟨i.as⟩
  map f := Quiver.Hom.toLoc
    (Ordinal.Hom.ofLE (leOfHom f.as))
  map_id _ := by
    apply Discrete.ext
    apply Subsingleton.elim
  map₂ := by
    intro a b f g eta
    have equality : f = g := LocallyDiscrete.eq_of_hom eta
    subst g
    exact 𝟙 _
  map₂_id _ := Subsingleton.elim _ _
  map₂_comp _ _ := Subsingleton.elim _ _
  mapComp _ _ := eqToHom (by
    apply Discrete.ext
    apply Subsingleton.elim)
  mapComp_naturality_left := by
    intros
    apply Subsingleton.elim
  mapComp_naturality_right := by
    intros
    apply Subsingleton.elim
  map₂_leftUnitor := by
    intros
    apply Subsingleton.elim
  map₂_rightUnitor := by
    intros
    apply Subsingleton.elim
  map₂_associator := by
    intros
    apply Subsingleton.elim

/-- The explicit constructor-normal rebuilding functor. Precomposition with
this map transports constructor-normal simplex data into the native Duskin
nerve without selecting a quasi-inverse. -/
def finiteToNormalOrdinal (n : Nat) :
    StrictlyUnitaryLaxFunctor (TotalModelDuskinNerve.FiniteOrdinal n)
      (NormalOrdinal n) :=
  StrictlyUnitaryLaxFunctor.mk' (finiteToNormalOrdinalCore n)

@[simp]
theorem finiteToNormalOrdinal_obj {n : Nat}
    (i : TotalModelDuskinNerve.FiniteOrdinal n) :
    (finiteToNormalOrdinal n).obj i = LocallyDiscrete.mk ⟨i.as⟩ :=
  rfl

@[simp]
theorem finiteToNormalOrdinal_map_ordinalHom {n : Nat}
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    (finiteToNormalOrdinal n).map
        (TotalModelDuskinNerve.ordinalHom hij) =
      Quiver.Hom.toLoc (C := Ordinal n) (Ordinal.Hom.ofLE hij) :=
  rfl

theorem finiteToNormalOrdinal_map_strict {n : Nat}
    {i j : Fin (n + 1)} (hij : i < j) :
    (finiteToNormalOrdinal n).map
        (TotalModelDuskinNerve.ordinalHom hij.le) =
      Quiver.Hom.toLoc (C := Ordinal n) (Ordinal.Hom.strict hij) := by
  rw [finiteToNormalOrdinal_map_ordinalHom, Ordinal.Hom.ofLE_of_lt]

theorem finiteToNormalOrdinal_mapComp_ordinalHom {n : Nat}
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    (finiteToNormalOrdinal n).mapComp
        (TotalModelDuskinNerve.ordinalHom hij)
        (TotalModelDuskinNerve.ordinalHom hjk) =
      eqToHom (by
        apply Discrete.ext
        apply Subsingleton.elim) := by
  apply Subsingleton.elim

@[simp]
theorem finiteToNormalOrdinal_map_comp_ordinalHom {n : Nat}
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    (finiteToNormalOrdinal n).map
        (TotalModelDuskinNerve.ordinalHom hij ≫
          TotalModelDuskinNerve.ordinalHom hjk) =
      Quiver.Hom.toLoc (C := Ordinal n)
        (Ordinal.Hom.ofLE (hij.trans hjk)) := by
  apply Discrete.ext
  apply Subsingleton.elim

namespace CoordinateSimplex

/-- The left unitor with its concrete total-model transformation type. -/
def leftUnitorTransformation
    {A B : ResourceModel.{u, v, w}} (F : ResourceModelHom A B) :
    ResourceModelTransformation (ResourceModelHom.id A |>.comp F) F := by
  exact (Bicategory.leftUnitor
    (B := ResourceModel.{u, v, w}) F).hom

/-- The right unitor with its concrete total-model transformation type. -/
def rightUnitorTransformation
    {A B : ResourceModel.{u, v, w}} (F : ResourceModelHom A B) :
    ResourceModelTransformation (F.comp (ResourceModelHom.id B)) F := by
  exact (Bicategory.rightUnitor
    (B := ResourceModel.{u, v, w}) F).hom

/-- Left-unit normalization cancels the target left unitor. -/
theorem leftUnitEquation
    {A B : ResourceModel.{u, v, w}} (F : ResourceModelHom A B) :
    (𝟙 F : ResourceModelTransformation F F) =
      (Bicategory.leftUnitor (B := ResourceModel.{u, v, w}) F).inv ≫
        leftUnitorTransformation F := by
  rw [show leftUnitorTransformation F =
    (Bicategory.leftUnitor (B := ResourceModel.{u, v, w}) F).hom by rfl]
  exact (Iso.inv_hom_id _).symm

/-- Right-unit normalization cancels the target right unitor. -/
theorem rightUnitEquation
    {A B : ResourceModel.{u, v, w}} (F : ResourceModelHom A B) :
    (𝟙 F : ResourceModelTransformation F F) =
      (Bicategory.rightUnitor (B := ResourceModel.{u, v, w}) F).inv ≫
        rightUnitorTransformation F := by
  rw [show rightUnitorTransformation F =
    (Bicategory.rightUnitor (B := ResourceModel.{u, v, w}) F).hom by rfl]
  exact (Iso.inv_hom_id _).symm

/-- Left and right unitors agree on the concrete identity 1-cell. -/
theorem identityUnitorsEqual (A : ResourceModel.{u, v, w}) :
    (Bicategory.leftUnitor
      (B := ResourceModel.{u, v, w}) (ResourceModelHom.id A)).hom =
      (Bicategory.rightUnitor
        (B := ResourceModel.{u, v, w}) (ResourceModelHom.id A)).hom := by
  simpa only [TotalModelBridge.id_eq] using
    (Bicategory.unitors_equal
      (B := ResourceModel.{u, v, w}) (a := A))

/-- Right-unit normalization for the chosen left-unitor comparison on an
identity edge. -/
theorem identityRightUnitEquation (A : ResourceModel.{u, v, w}) :
    (𝟙 (ResourceModelHom.id A) :
      ResourceModelTransformation (ResourceModelHom.id A) (ResourceModelHom.id A)) =
      (Bicategory.rightUnitor
        (B := ResourceModel.{u, v, w}) (ResourceModelHom.id A)).inv ≫
        leftUnitorTransformation (ResourceModelHom.id A) := by
  rw [show leftUnitorTransformation (ResourceModelHom.id A) =
    (Bicategory.leftUnitor
      (B := ResourceModel.{u, v, w}) (ResourceModelHom.id A)).hom by rfl]
  rw [identityUnitorsEqual]
  exact (Iso.inv_hom_id _).symm

/-- Interpret one constructor-normal ordinal morphism as a coordinate edge. -/
def mapHom {n : Nat} (simplex : CoordinateSimplex.{u, v, w} n)
    {i j : Ordinal n} (f : i ⟶ j) :
    ResourceModelHom (simplex.vertex i.index) (simplex.vertex j.index) := by
  cases f with
  | refl => exact ResourceModelHom.id _
  | strict hij => exact simplex.edge _ _ hij

@[simp]
theorem mapHom_refl {n : Nat} (simplex : CoordinateSimplex.{u, v, w} n)
    (i : Ordinal n) :
    simplex.mapHom (Ordinal.Hom.refl i) =
      ResourceModelHom.id (simplex.vertex i.index) :=
  rfl

@[simp]
theorem mapHom_strict {n : Nat} (simplex : CoordinateSimplex.{u, v, w} n)
    {i j : Ordinal n} (hij : i.index < j.index) :
    simplex.mapHom (Ordinal.Hom.strict hij) =
      simplex.edge i.index j.index hij :=
  rfl

/-- Interpret the unique source 2-cell by the induced equality of normalized
target edges. -/
def mapTwoCell {n : Nat} (simplex : CoordinateSimplex.{u, v, w} n)
    {i j : NormalOrdinal n} {f g : i ⟶ j} (eta : f ⟶ g) :
    simplex.mapHom f.as ⟶ simplex.mapHom g.as := by
  have equality : f = g := LocallyDiscrete.eq_of_hom eta
  subst g
  exact 𝟙 _

@[simp]
theorem mapTwoCell_id {n : Nat} (simplex : CoordinateSimplex.{u, v, w} n)
    {i j : NormalOrdinal n} (f : i ⟶ j) :
    simplex.mapTwoCell (𝟙 f) = 𝟙 (simplex.mapHom f.as) := by
  apply ResourceModelTransformation.ext
  rfl

/-- Interpret a composable pair by a unitor or a stored strict triangle. -/
def mapComp {n : Nat} (simplex : CoordinateSimplex.{u, v, w} n)
    {i j k : Ordinal n} (f : i ⟶ j) (g : j ⟶ k) :
    ResourceModelTransformation
      ((simplex.mapHom f).comp (simplex.mapHom g))
      (simplex.mapHom (Ordinal.Hom.comp f g)) := by
  cases f with
  | refl =>
      cases g with
      | refl => exact leftUnitorTransformation _
      | strict _ => exact leftUnitorTransformation _
  | strict hij =>
      cases g with
      | refl => exact rightUnitorTransformation _
      | strict hjk => exact simplex.triangle _ _ _ hij hjk

@[simp]
theorem mapComp_refl_left {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n)
    {i j : Ordinal n} (g : i ⟶ j) :
    simplex.mapComp (Ordinal.Hom.refl i) g =
      leftUnitorTransformation (simplex.mapHom g) := by
  cases g <;> rfl

@[simp]
theorem mapComp_strict_refl {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n)
    {i j : Ordinal n} (hij : i.index < j.index) :
    simplex.mapComp (Ordinal.Hom.strict hij) (Ordinal.Hom.refl j) =
      rightUnitorTransformation (simplex.edge i.index j.index hij) :=
  rfl

@[simp]
theorem mapComp_strict_strict {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n)
    {i j k : Ordinal n} (hij : i.index < j.index) (hjk : j.index < k.index) :
    simplex.mapComp (Ordinal.Hom.strict hij) (Ordinal.Hom.strict hjk) =
      simplex.triangle i.index j.index k.index hij hjk :=
  rfl

/-- On three strict arrows, the constructor-normal comparison cells satisfy
exactly the stored coordinate tetrahedral equation. -/
theorem strictTetrahedralCoherence {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n)
    {i j k l : Ordinal n}
    (hij : i.index < j.index) (hjk : j.index < k.index)
    (hkl : k.index < l.index) :
    ResourceModelTransformation.whiskerRight
          (simplex.mapComp (Ordinal.Hom.strict hij) (Ordinal.Hom.strict hjk))
          (simplex.mapHom (Ordinal.Hom.strict hkl)) ≫
        simplex.mapComp (Ordinal.Hom.strict (hij.trans hjk))
          (Ordinal.Hom.strict hkl) =
      TotalModelSimplicial.associatorTransformation
          (simplex.mapHom (Ordinal.Hom.strict hij))
          (simplex.mapHom (Ordinal.Hom.strict hjk))
          (simplex.mapHom (Ordinal.Hom.strict hkl)) ≫
        ResourceModelTransformation.whiskerLeft
          (simplex.mapHom (Ordinal.Hom.strict hij))
          (simplex.mapComp (Ordinal.Hom.strict hjk)
            (Ordinal.Hom.strict hkl)) ≫
        simplex.mapComp (Ordinal.Hom.strict hij)
          (Ordinal.Hom.strict (hjk.trans hkl)) := by
  exact simplex.tetrahedron i.index j.index k.index l.index hij hjk hkl

/-- All eight constructor patterns satisfy tetrahedral coherence, with `HEq`
recording the source-category associativity transport. -/
theorem constructorTetrahedralCoherence {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n)
    {i j k l : Ordinal n} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l) :
    HEq (ResourceModelTransformation.whiskerRight
          (simplex.mapComp f g) (simplex.mapHom h) ≫
        simplex.mapComp (Ordinal.Hom.comp f g) h)
      (TotalModelSimplicial.associatorTransformation
          (simplex.mapHom f) (simplex.mapHom g) (simplex.mapHom h) ≫
        ResourceModelTransformation.whiskerLeft
          (simplex.mapHom f) (simplex.mapComp g h) ≫
        simplex.mapComp f (Ordinal.Hom.comp g h)) := by
  cases f with
  | refl =>
      cases g with
      | refl =>
          cases h with
          | refl =>
              exact heq_of_eq
                (totalModelAllIdentityCoherence (simplex.vertex i.index))
          | strict hkl =>
              exact heq_of_eq
                (TotalModelDegenerateCoherence.leftLeft
                  (simplex.edge i.index l.index hkl))
      | strict hjk =>
          cases h with
          | refl =>
              exact heq_of_eq
                (TotalModelDegenerateCoherence.leftRight
                  (simplex.edge i.index k.index hjk))
          | strict hkl =>
              exact heq_of_eq
                (TotalModelDegenerateCoherence.leftNaturality
                  (simplex.edge i.index k.index hjk)
                  (simplex.edge k.index l.index hkl)
                  (simplex.edge i.index l.index (hjk.trans hkl))
                  (simplex.triangle i.index k.index l.index hjk hkl))
  | strict hij =>
      cases g with
      | refl =>
          cases h with
          | refl =>
              exact heq_of_eq
                (TotalModelDegenerateCoherence.rightRight
                  (simplex.edge i.index j.index hij))
          | strict hkl =>
              exact heq_of_eq
                (TotalModelDegenerateCoherence.middleIdentity
                  (simplex.edge i.index j.index hij)
                  (simplex.edge j.index l.index hkl)
                  (simplex.edge i.index l.index (hij.trans hkl))
                  (simplex.triangle i.index j.index l.index hij hkl))
      | strict hjk =>
          cases h with
          | refl =>
              exact heq_of_eq
                (TotalModelDegenerateCoherence.rightNaturality
                  (simplex.edge i.index j.index hij)
                  (simplex.edge j.index k.index hjk)
                  (simplex.edge i.index k.index (hij.trans hjk))
                  (simplex.triangle i.index j.index k.index hij hjk))
          | strict hkl =>
              exact heq_of_eq (simplex.strictTetrahedralCoherence hij hjk hkl)

/-- The comparison cell with its target indexed by composition in the wrapped
locally discrete source.  This exposes exactly the type required by the lax
functor core. -/
def normalMapComp {n : Nat} (simplex : CoordinateSimplex.{u, v, w} n)
    {a b c : NormalOrdinal n} (f : a ⟶ b) (g : b ⟶ c) :
    ResourceModelTransformation
      ((simplex.mapHom f.as).comp (simplex.mapHom g.as))
      (simplex.mapHom (f ≫ g).as) :=
  simplex.mapComp f.as g.as

/-- Transport the strict identity equation before left composition. -/
def leftIdentityTransport {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n)
    {a b : NormalOrdinal n} (f : a ⟶ b) :
    ResourceModelTransformation
      ((ResourceModelHom.id (simplex.vertex a.as.index)).comp
        (simplex.mapHom f.as))
      ((simplex.mapHom (𝟙 a : Discrete (a.as ⟶ a.as)).as).comp
        (simplex.mapHom f.as)) :=
  eqToHom (congrArg (fun g => g.comp (simplex.mapHom f.as))
    (show simplex.mapHom (𝟙 a : Discrete (a.as ⟶ a.as)).as =
      ResourceModelHom.id (simplex.vertex a.as.index) by rfl).symm)

/-- Transport the strict identity equation after right composition. -/
def rightIdentityTransport {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n)
    {a b : NormalOrdinal n} (f : a ⟶ b) :
    ResourceModelTransformation
      ((simplex.mapHom f.as).comp
        (ResourceModelHom.id (simplex.vertex b.as.index)))
      ((simplex.mapHom f.as).comp
        (simplex.mapHom (𝟙 b : Discrete (b.as ⟶ b.as)).as)) :=
  eqToHom (congrArg (simplex.mapHom f.as).comp
    (show simplex.mapHom (𝟙 b : Discrete (b.as ⟶ b.as)).as =
      ResourceModelHom.id (simplex.vertex b.as.index) by rfl).symm)

@[simp]
theorem leftIdentityTransport_eq_id {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n)
    {a b : NormalOrdinal n} (f : a ⟶ b) :
    simplex.leftIdentityTransport f =
      𝟙 ((ResourceModelHom.id (simplex.vertex a.as.index)).comp
        (simplex.mapHom f.as)) := by
  apply ResourceModelTransformation.ext
  rfl

@[simp]
theorem rightIdentityTransport_eq_id {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n)
    {a b : NormalOrdinal n} (f : a ⟶ b) :
    simplex.rightIdentityTransport f =
      𝟙 ((simplex.mapHom f.as).comp
        (ResourceModelHom.id (simplex.vertex b.as.index))) := by
  apply ResourceModelTransformation.ext
  rfl

/-- The left-unit law after adapting the source unitor and strict identity
transport to the wrapped normal ordinal. -/
theorem sourceLeftUnitEquation {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n)
    {i j : Ordinal n} (f : i ⟶ j) :
    simplex.mapTwoCell
        (Bicategory.leftUnitor
          (B := NormalOrdinal n) (Quiver.Hom.toLoc f)).inv =
      (Bicategory.leftUnitor
          (B := ResourceModel.{u, v, w}) (simplex.mapHom f)).inv ≫
        simplex.leftIdentityTransport (Quiver.Hom.toLoc f) ≫
        simplex.normalMapComp
          (𝟙 (LocallyDiscrete.mk i)) (Quiver.Hom.toLoc f) := by
  cases f with
  | refl =>
      simp [mapTwoCell, normalMapComp, mapComp, Quiver.Hom.toLoc,
        Ordinal.category_comp, Ordinal.Hom.comp, leftUnitorTransformation]
  | strict hij =>
      simp [mapTwoCell, normalMapComp, mapComp, Quiver.Hom.toLoc,
        Ordinal.category_comp, Ordinal.Hom.comp, leftUnitorTransformation]

/-- The right-unit law after adapting the source unitor and strict identity
transport to the wrapped normal ordinal. -/
theorem sourceRightUnitEquation {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n)
    {i j : Ordinal n} (f : i ⟶ j) :
    simplex.mapTwoCell
        (Bicategory.rightUnitor
          (B := NormalOrdinal n) (Quiver.Hom.toLoc f)).inv =
      (Bicategory.rightUnitor
          (B := ResourceModel.{u, v, w}) (simplex.mapHom f)).inv ≫
        simplex.rightIdentityTransport (Quiver.Hom.toLoc f) ≫
        simplex.normalMapComp
          (Quiver.Hom.toLoc f) (𝟙 (LocallyDiscrete.mk j)) := by
  cases f with
  | refl =>
      simpa [mapTwoCell, normalMapComp, mapComp, Quiver.Hom.toLoc,
        Ordinal.category_comp, Ordinal.Hom.comp, leftUnitorTransformation] using
        (identityRightUnitEquation (simplex.vertex i.index))
  | strict hij =>
      simp [mapTwoCell, normalMapComp, mapComp, Quiver.Hom.toLoc,
        Ordinal.category_comp, Ordinal.Hom.comp, rightUnitorTransformation]

/-- The constructor tetrahedral theorem with the source associator map
inserted, in exactly the equality type required by a lax functor. -/
theorem sourceTetrahedralCoherence {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n)
    {i j k l : Ordinal n} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l) :
    ResourceModelTransformation.whiskerRight
          (simplex.normalMapComp
            (Quiver.Hom.toLoc f) (Quiver.Hom.toLoc g))
          (simplex.mapHom h) ≫
        simplex.normalMapComp
            ((Quiver.Hom.toLoc f) ≫ (Quiver.Hom.toLoc g))
            (Quiver.Hom.toLoc h) ≫
          simplex.mapTwoCell
            (Bicategory.associator (Quiver.Hom.toLoc f)
              (Quiver.Hom.toLoc g) (Quiver.Hom.toLoc h)).hom =
      TotalModelSimplicial.associatorTransformation
          (simplex.mapHom f) (simplex.mapHom g) (simplex.mapHom h) ≫
        ResourceModelTransformation.whiskerLeft (simplex.mapHom f)
            (simplex.normalMapComp
              (Quiver.Hom.toLoc g) (Quiver.Hom.toLoc h)) ≫
          simplex.normalMapComp (Quiver.Hom.toLoc f)
            ((Quiver.Hom.toLoc g) ≫ (Quiver.Hom.toLoc h)) := by
  cases f with
  | refl =>
      cases g with
      | refl =>
          cases h with
          | refl =>
              simpa [mapTwoCell, normalMapComp, Quiver.Hom.toLoc,
                Ordinal.category_comp, Ordinal.Hom.comp, leftUnitorTransformation,
                rightUnitorTransformation, Category.comp_id] using
                (totalModelAllIdentityCoherence (simplex.vertex i.index))
          | strict hkl =>
              simpa [mapTwoCell, normalMapComp, Quiver.Hom.toLoc,
                Ordinal.category_comp, Ordinal.Hom.comp, leftUnitorTransformation,
                rightUnitorTransformation, Category.comp_id] using
                (TotalModelDegenerateCoherence.leftLeft
                  (simplex.edge i.index l.index hkl))
      | strict hjk =>
          cases h with
          | refl =>
              simpa [mapTwoCell, normalMapComp, Quiver.Hom.toLoc,
                Ordinal.category_comp, Ordinal.Hom.comp, leftUnitorTransformation,
                rightUnitorTransformation, Category.comp_id] using
                (TotalModelDegenerateCoherence.leftRight
                  (simplex.edge i.index k.index hjk))
          | strict hkl =>
              simpa [mapTwoCell, normalMapComp, Quiver.Hom.toLoc,
                Ordinal.category_comp, Ordinal.Hom.comp, leftUnitorTransformation,
                rightUnitorTransformation, Category.comp_id] using
                (TotalModelDegenerateCoherence.leftNaturality
                  (simplex.edge i.index k.index hjk)
                  (simplex.edge k.index l.index hkl)
                  (simplex.edge i.index l.index (hjk.trans hkl))
                  (simplex.triangle i.index k.index l.index hjk hkl))
  | strict hij =>
      cases g with
      | refl =>
          cases h with
          | refl =>
              simpa [mapTwoCell, normalMapComp, Quiver.Hom.toLoc,
                Ordinal.category_comp, Ordinal.Hom.comp, leftUnitorTransformation,
                rightUnitorTransformation, Category.comp_id] using
                (TotalModelDegenerateCoherence.rightRight
                  (simplex.edge i.index j.index hij))
          | strict hkl =>
              simpa [mapTwoCell, normalMapComp, Quiver.Hom.toLoc,
                Ordinal.category_comp, Ordinal.Hom.comp, leftUnitorTransformation,
                rightUnitorTransformation, Category.comp_id] using
                (TotalModelDegenerateCoherence.middleIdentity
                  (simplex.edge i.index j.index hij)
                  (simplex.edge j.index l.index hkl)
                  (simplex.edge i.index l.index (hij.trans hkl))
                  (simplex.triangle i.index j.index l.index hij hkl))
      | strict hjk =>
          cases h with
          | refl =>
              simpa [mapTwoCell, normalMapComp, Quiver.Hom.toLoc,
                Ordinal.category_comp, Ordinal.Hom.comp, leftUnitorTransformation,
                rightUnitorTransformation, Category.comp_id] using
                (TotalModelDegenerateCoherence.rightNaturality
                  (simplex.edge i.index j.index hij)
                  (simplex.edge j.index k.index hjk)
                  (simplex.edge i.index k.index (hij.trans hjk))
                  (simplex.triangle i.index j.index k.index hij hjk))
          | strict hkl =>
              simpa [mapTwoCell, normalMapComp, Quiver.Hom.toLoc,
                Ordinal.category_comp, Ordinal.Hom.comp, leftUnitorTransformation,
                rightUnitorTransformation, Category.comp_id] using
                (simplex.strictTetrahedralCoherence hij hjk hkl)

/-- Assemble coordinate simplex data into the exact core of a strictly
unitary lax functor on the constructor-normal ordinal. -/
def toCore {n : Nat} (simplex : CoordinateSimplex.{u, v, w} n) :
    StrictlyUnitaryLaxFunctorCore (NormalOrdinal n) ResourceModel where
  obj i := simplex.vertex i.as.index
  map f := simplex.mapHom f.as
  map_id _ := rfl
  map₂ eta := simplex.mapTwoCell eta
  map₂_id f := simplex.mapTwoCell_id f
  map₂_comp := by
    intro a b f g h eta theta
    obtain rfl := LocallyDiscrete.eq_of_hom eta
    obtain rfl := LocallyDiscrete.eq_of_hom theta
    have eta_eq : eta = 𝟙 f := Subsingleton.elim _ _
    have theta_eq : theta = 𝟙 f := Subsingleton.elim _ _
    subst eta
    subst theta
    simp
  mapComp f g := simplex.normalMapComp f g
  mapComp_naturality_left := by
    intro a b c f f' eta g
    obtain rfl := LocallyDiscrete.eq_of_hom eta
    have eta_eq : eta = 𝟙 f := Subsingleton.elim _ _
    subst eta
    have source : (𝟙 f) ▷ g = 𝟙 (f ≫ g) := Subsingleton.elim _ _
    rw [source, mapTwoCell_id, mapTwoCell_id]
    rw [Category.comp_id,
      @Bicategory.id_whiskerRight ResourceModel resourceModelBicategory _ _ _
        (simplex.mapHom f.as) (simplex.mapHom g.as),
      Category.id_comp]
  mapComp_naturality_right := by
    intro a b c f g g' eta
    obtain rfl := LocallyDiscrete.eq_of_hom eta
    have eta_eq : eta = 𝟙 g := Subsingleton.elim _ _
    subst eta
    have source : f ◁ (𝟙 g) = 𝟙 (f ≫ g) := Subsingleton.elim _ _
    rw [source, mapTwoCell_id, mapTwoCell_id]
    rw [Category.comp_id,
      @Bicategory.whiskerLeft_id ResourceModel resourceModelBicategory _ _ _
        (simplex.mapHom f.as) (simplex.mapHom g.as),
      Category.id_comp]
  map₂_leftUnitor := by
    intro a b f
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    rcases f with ⟨f⟩
    exact simplex.sourceLeftUnitEquation f
  map₂_rightUnitor := by
    intro a b f
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    rcases f with ⟨f⟩
    exact simplex.sourceRightUnitEquation f
  map₂_associator := by
    intro a b c d f g h
    exact simplex.sourceTetrahedralCoherence f.as g.as h.as

/-- The coordinate simplex as a genuine strictly unitary lax functor on the
constructor-normal ordinal. -/
def toNormalOrdinalSimplex {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n) :
    StrictlyUnitaryLaxFunctor (NormalOrdinal n) ResourceModel :=
  StrictlyUnitaryLaxFunctor.mk' simplex.toCore

@[simp]
theorem toNormalOrdinalSimplex_map_strict {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n)
    {i j : Ordinal n} (hij : i.index < j.index) :
    simplex.toNormalOrdinalSimplex.map
        (Quiver.Hom.toLoc (C := Ordinal n) (Ordinal.Hom.strict hij)) =
      simplex.edge i.index j.index hij :=
  rfl

@[simp]
theorem toNormalOrdinalSimplex_mapComp_strict {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n)
    {i j k : Ordinal n} (hij : i.index < j.index)
    (hjk : j.index < k.index) :
    simplex.toNormalOrdinalSimplex.toLaxFunctor.mapComp'
        (Quiver.Hom.toLoc (C := Ordinal n) (Ordinal.Hom.strict hij))
        (Quiver.Hom.toLoc (C := Ordinal n) (Ordinal.Hom.strict hjk))
        (Quiver.Hom.toLoc (C := Ordinal n)
          (Ordinal.Hom.strict (hij.trans hjk))) rfl =
      simplex.triangle i.index j.index k.index hij hjk := by
  simp [toNormalOrdinalSimplex, StrictlyUnitaryLaxFunctor.mk',
    LaxFunctor.mapComp', toCore, normalMapComp, mapTwoCell,
    Quiver.Hom.toLoc, Ordinal.category_comp, Ordinal.Hom.comp]
  exact Category.comp_id _

/-- Decode a normal-lax simplex on the constructor-normal ordinal back to
strictly increasing coordinate data. -/
def fromNormalOrdinalSimplex {n : Nat}
    (simplex : StrictlyUnitaryLaxFunctor
      (NormalOrdinal n) ResourceModel.{u, v, w}) :
    CoordinateSimplex.{u, v, w} n where
  vertex i := simplex.obj (LocallyDiscrete.mk ⟨i⟩)
  edge i j hij := simplex.map
    (Quiver.Hom.toLoc (C := Ordinal n) (Ordinal.Hom.strict hij))
  triangle i j k hij hjk := by
    let f₀₁ := Quiver.Hom.toLoc (C := Ordinal n) (Ordinal.Hom.strict hij)
    let f₁₂ := Quiver.Hom.toLoc (C := Ordinal n) (Ordinal.Hom.strict hjk)
    let f₀₂ := Quiver.Hom.toLoc (C := Ordinal n)
      (Ordinal.Hom.strict (hij.trans hjk))
    exact simplex.toLaxFunctor.mapComp' f₀₁ f₁₂ f₀₂ (by
      apply Discrete.ext
      apply Subsingleton.elim)
  tetrahedron i j k l hij hjk hkl := by
    let f₀₁ := Quiver.Hom.toLoc (C := Ordinal n) (Ordinal.Hom.strict hij)
    let f₁₂ := Quiver.Hom.toLoc (C := Ordinal n) (Ordinal.Hom.strict hjk)
    let f₂₃ := Quiver.Hom.toLoc (C := Ordinal n) (Ordinal.Hom.strict hkl)
    let f₀₂ := Quiver.Hom.toLoc (C := Ordinal n)
      (Ordinal.Hom.strict (hij.trans hjk))
    let f₁₃ := Quiver.Hom.toLoc (C := Ordinal n)
      (Ordinal.Hom.strict (hjk.trans hkl))
    let f₀₃ := Quiver.Hom.toLoc (C := Ordinal n)
      (Ordinal.Hom.strict (hij.trans (hjk.trans hkl)))
    have h₀₂ : f₀₁ ≫ f₁₂ = f₀₂ := by
      apply Discrete.ext
      apply Subsingleton.elim
    have h₁₃ : f₁₂ ≫ f₂₃ = f₁₃ := by
      apply Discrete.ext
      apply Subsingleton.elim
    have h₀₃ : f₀₂ ≫ f₂₃ = f₀₃ := by
      apply Discrete.ext
      apply Subsingleton.elim
    have h₀₁₃ : f₀₁ ≫ f₁₃ = f₀₃ := by
      apply Discrete.ext
      apply Subsingleton.elim
    change
      simplex.toLaxFunctor.mapComp' f₀₁ f₁₂ f₀₂ h₀₂ ▷
            simplex.map f₂₃ ≫
          simplex.toLaxFunctor.mapComp' f₀₂ f₂₃ f₀₃ h₀₃ =
        (α_ (simplex.map f₀₁) (simplex.map f₁₂)
          (simplex.map f₂₃)).hom ≫
          simplex.map f₀₁ ◁
              simplex.toLaxFunctor.mapComp' f₁₂ f₂₃ f₁₃ h₁₃ ≫
            simplex.toLaxFunctor.mapComp' f₀₁ f₁₃ f₀₃ h₀₁₃
    exact simplex.toLaxFunctor.mapComp'_whiskerRight_comp_mapComp'
      f₀₁ f₁₂ f₂₃ f₀₂ f₁₃ f₀₃ h₀₂ h₁₃ h₀₃

/-- Decoding the constructor-normal lax simplex reconstructed from coordinates
returns the original coordinate simplex exactly. -/
theorem fromNormalOrdinalSimplex_toNormalOrdinalSimplex {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n) :
    fromNormalOrdinalSimplex simplex.toNormalOrdinalSimplex = simplex := by
  apply TotalModelSemiSimplicial.Simplex.extensionality
  · rfl
  · rfl
  · apply heq_of_eq
    funext i j k hij hjk
    apply ResourceModelTransformation.ext
    simp [fromNormalOrdinalSimplex, toNormalOrdinalSimplex,
      StrictlyUnitaryLaxFunctor.mk', LaxFunctor.mapComp', toCore,
      normalMapComp, mapTwoCell, Quiver.Hom.toLoc, Ordinal.category_comp,
      Ordinal.Hom.comp]
    rfl

/-- Precompose by the explicit constructor-normal rebuilding functor to obtain
a native simplex of the full Duskin nerve. -/
def toNativeSimplex {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n) :
    TotalModelDuskinNerve.Simplex.{u, v, w} n :=
  (finiteToNormalOrdinal n).comp simplex.toNormalOrdinalSimplex

/-- Composing with the image of a locally discrete source 2-cell changes only
the dependent target type. -/
theorem comp_mapTwoCell_heq {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n)
    {a b : NormalOrdinal n} {f g : a ⟶ b}
    {q : ResourceModelHom
      (simplex.vertex a.as.index) (simplex.vertex b.as.index)}
    (theta : ResourceModelTransformation q (simplex.mapHom f.as))
    (eta : f ⟶ g) :
    HEq (theta ≫ simplex.mapTwoCell eta) theta := by
  have equality : f = g := LocallyDiscrete.eq_of_hom eta
  subst g
  have etaEquality : eta = 𝟙 f := Subsingleton.elim _ _
  subst eta
  rw [mapTwoCell_id, Category.comp_id]

/-- Any two constructor-normal arrows with strictly increasing endpoints are
the strict constructors, so their comparison is the stored triangle up to
dependent endpoint transport. -/
theorem mapComp_strict_heq_triangle {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n)
    {i j k : Ordinal n} (f : i ⟶ j) (g : j ⟶ k)
    (hij : i.index < j.index) (hjk : j.index < k.index) :
    HEq (simplex.mapComp f g)
      (simplex.triangle i.index j.index k.index hij hjk) := by
  have fEquality : f = Ordinal.Hom.strict hij := Subsingleton.elim _ _
  have gEquality : g = Ordinal.Hom.strict hjk := Subsingleton.elim _ _
  subst f
  subst g
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Strict native comparisons decode to the stored coordinate triangles. -/
theorem toNativeSimplex_comparison {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n)
    {i j k : Fin (n + 1)} (hij : i < j) (hjk : j < k) :
    HEq (simplex.toNativeSimplex.comparison hij.le hjk.le)
      (simplex.triangle i j k hij hjk) := by
  let f := TotalModelDuskinNerve.ordinalHom hij.le
  let g := TotalModelDuskinNerve.ordinalHom hjk.le
  let fg := TotalModelDuskinNerve.ordinalHom (hij.trans hjk).le
  have sourceComposition : f ≫ g = fg := by
    apply Discrete.ext
    apply Subsingleton.elim
  change HEq
    (((finiteToNormalOrdinal n).comp
      simplex.toNormalOrdinalSimplex).toLaxFunctor.mapComp'
        f g fg sourceComposition)
      (simplex.triangle i j k hij hjk)
  unfold LaxFunctor.mapComp'
  simp only [StrictlyUnitaryLaxFunctor.comp_mapComp,
    StrictlyUnitaryLaxFunctor.comp_map₂,
    StrictlyUnitaryLaxFunctor.comp_map]
  simp only [toNormalOrdinalSimplex, StrictlyUnitaryLaxFunctor.mk', toCore]
  let first := simplex.normalMapComp
    ((finiteToNormalOrdinal n).map f) ((finiteToNormalOrdinal n).map g)
  let second := first ≫
    simplex.mapTwoCell ((finiteToNormalOrdinal n).mapComp f g)
  have eraseSecond : HEq
      (second ≫ simplex.mapTwoCell
        ((finiteToNormalOrdinal n).map₂ (eqToHom sourceComposition)))
      second :=
    simplex.comp_mapTwoCell_heq second _
  have eraseFirst : HEq second first :=
    simplex.comp_mapTwoCell_heq first _
  have strictComparison : HEq first
      (simplex.triangle i j k hij hjk) :=
    simplex.mapComp_strict_heq_triangle
      ((finiteToNormalOrdinal n).map f).as
      ((finiteToNormalOrdinal n).map g).as hij hjk
  exact eraseSecond.trans (eraseFirst.trans strictComparison)

/-- Reconstructing a native simplex and applying the existing coordinate
decoder strictly recovers the original coordinate simplex. -/
theorem toNativeSimplex_toSemiSimplex {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n) :
    simplex.toNativeSimplex.toSemiSimplex = simplex := by
  apply TotalModelSemiSimplicial.Simplex.extensionality
  · rfl
  · refine Function.hfunext rfl fun i i' hi => ?_
    cases eq_of_heq hi
    refine Function.hfunext rfl fun j j' hj => ?_
    cases eq_of_heq hj
    refine Function.hfunext rfl fun hij hij' _ => ?_
    have proofEquality : hij = hij' := Subsingleton.elim _ _
    subst hij'
    change HEq
      ((finiteToNormalOrdinal n).comp
          simplex.toNormalOrdinalSimplex |>.map
        (TotalModelDuskinNerve.ordinalHom hij.le))
      (simplex.edge i j hij)
    rw [StrictlyUnitaryLaxFunctor.comp_map]
    have rebuilding := congrArg
      (fun arrow => simplex.toNormalOrdinalSimplex.map arrow)
      (finiteToNormalOrdinal_map_strict hij)
    exact HEq.trans (heq_of_eq rebuilding)
      (heq_of_eq (simplex.toNormalOrdinalSimplex_map_strict hij))
  · refine Function.hfunext rfl fun i i' hi => ?_
    cases eq_of_heq hi
    refine Function.hfunext rfl fun j j' hj => ?_
    cases eq_of_heq hj
    refine Function.hfunext rfl fun k k' hk => ?_
    cases eq_of_heq hk
    refine Function.hfunext rfl fun hij hij' _ => ?_
    have hijEquality : hij = hij' := Subsingleton.elim _ _
    subst hij'
    refine Function.hfunext rfl fun hjk hjk' _ => ?_
    have hjkEquality : hjk = hjk' := Subsingleton.elim _ _
    subst hjk'
    exact simplex.toNativeSimplex_comparison hij hjk

/-- A strict native edge of a reconstructed coordinate simplex is the stored
coordinate edge, up to its dependent endpoint transport. -/
theorem toNativeSimplex_map_strict {n : Nat}
    (simplex : CoordinateSimplex.{u, v, w} n)
    {i j : Fin (n + 1)} (hij : i < j) :
    HEq (simplex.toNativeSimplex.map
        (TotalModelDuskinNerve.ordinalHom hij.le))
      (simplex.edge i j hij) := by
  change HEq
    ((finiteToNormalOrdinal n).comp simplex.toNormalOrdinalSimplex |>.map
      (TotalModelDuskinNerve.ordinalHom hij.le))
    (simplex.edge i j hij)
  rw [StrictlyUnitaryLaxFunctor.comp_map]
  have rebuilding := congrArg
    (fun arrow => simplex.toNormalOrdinalSimplex.map arrow)
    (finiteToNormalOrdinal_map_strict hij)
  exact HEq.trans (heq_of_eq rebuilding)
    (heq_of_eq (simplex.toNormalOrdinalSimplex_map_strict hij))

/-- Reconstructing after coordinate decoding preserves every native 1-cell. -/
theorem toSemiSimplex_toNative_map {n : Nat}
    (simplex : TotalModelDuskinNerve.Simplex.{u, v, w} n)
    {X Y : TotalModelDuskinNerve.FiniteOrdinal n} (arrow : X ⟶ Y) :
    HEq ((CoordinateSimplex.toNativeSimplex
      simplex.toSemiSimplex).map arrow) (simplex.map arrow) := by
  rcases X with ⟨i⟩
  rcases Y with ⟨j⟩
  by_cases equality : i = j
  · subst j
    have arrowEquality : arrow = 𝟙 (LocallyDiscrete.mk i) := by
      apply Discrete.ext
      apply Subsingleton.elim
    subst arrow
    have reconstructedId := (CoordinateSimplex.toNativeSimplex
      simplex.toSemiSimplex).map_id (LocallyDiscrete.mk i)
    have identityObjects : HEq
        (𝟙 ((CoordinateSimplex.toNativeSimplex
          simplex.toSemiSimplex).obj (LocallyDiscrete.mk i)))
        (𝟙 (simplex.obj (LocallyDiscrete.mk i))) := by
      rfl
    exact (heq_of_eq reconstructedId).trans
      (identityObjects.trans (heq_of_eq (simplex.map_id _).symm))
  · have increase : i ≤ j := leOfHom arrow.as
    have strict : i < j := lt_of_le_of_ne increase equality
    have arrowEquality : arrow =
        TotalModelDuskinNerve.ordinalHom strict.le := by
      apply Discrete.ext
      apply Subsingleton.elim
    subst arrow
    exact (toNativeSimplex_map_strict simplex.toSemiSimplex strict).trans
      (by rfl)

/-- Identity 2-cells respect heterogeneous equality of their 1-cells. -/
theorem idTwoCell_heq_of_heq
    {X : Type u} [Bicategory.{w, v} X]
    {a b : X} {f : a ⟶ b} {g : a ⟶ b} (equality : HEq f g) :
    HEq (𝟙 f) (𝟙 g) := by
  cases equality
  rfl

/-- An equality transport is heterogeneously the corresponding identity. -/
theorem eqToHom_heq_id
    {C : Type u} [Category.{v} C] {X Y : C} (equality : X = Y) :
    HEq (eqToHom equality) (𝟙 X) := by
  subst Y
  rfl

/-- The unit cell of a normal lax functor is heterogeneously an identity. -/
theorem mapId_heq_id
    {B C : Type*} [Bicategory B] [Bicategory C]
    (F : StrictlyUnitaryLaxFunctor B C) (a : B) :
    HEq (F.mapId a) (𝟙 (𝟙 (F.obj a))) := by
  exact (heq_of_eq (F.mapId_eq_eqToHom a)).trans
    (eqToHom_heq_id _)

/-- Reconstructing after coordinate decoding preserves every native 2-cell. -/
theorem toSemiSimplex_toNative_map₂ {n : Nat}
    (simplex : TotalModelDuskinNerve.Simplex.{u, v, w} n)
    {a b : TotalModelDuskinNerve.FiniteOrdinal n}
    {f g : a ⟶ b} (eta : f ⟶ g) :
    HEq ((CoordinateSimplex.toNativeSimplex
      simplex.toSemiSimplex).map₂ eta) (simplex.map₂ eta) := by
  have fgEquality : f = g := LocallyDiscrete.eq_of_hom eta
  subst g
  have etaEquality : eta = 𝟙 f := Subsingleton.elim _ _
  subst eta
  have identityCells : HEq
      (𝟙 ((CoordinateSimplex.toNativeSimplex
        simplex.toSemiSimplex).map f))
      (𝟙 (simplex.map f)) :=
    idTwoCell_heq_of_heq (toSemiSimplex_toNative_map simplex f)
  exact (heq_of_eq ((CoordinateSimplex.toNativeSimplex
    simplex.toSemiSimplex).map₂_id f)).trans
    (identityCells.trans (heq_of_eq (simplex.map₂_id f).symm))

/-- In a normal lax functor the left-identity compositor is determined by the
mapped source unitor, the strict identity equation, and the target unitor. -/
theorem mapComp_leftIdentity
    {B C : Type*} [Bicategory B] [Bicategory C]
    (F : StrictlyUnitaryLaxFunctor B C)
    {a b : B} (f : a ⟶ b) :
    F.mapComp (𝟙 a) f =
      eqToHom (by rw [F.map_id a]) ≫
        (Bicategory.leftUnitor (F.map f)).hom ≫
          F.map₂ (Bicategory.leftUnitor f).inv := by
  rw [F.map₂_leftUnitor f]
  simp [F.mapId_eq_eqToHom]

/-- Right-identity compositors of normal lax functors have the analogous
canonical formula. -/
theorem mapComp_rightIdentity
    {B C : Type*} [Bicategory B] [Bicategory C]
    (F : StrictlyUnitaryLaxFunctor B C)
    {a b : B} (f : a ⟶ b) :
    F.mapComp f (𝟙 b) =
      eqToHom (by rw [F.map_id b]) ≫
        (Bicategory.rightUnitor (F.map f)).hom ≫
          F.map₂ (Bicategory.rightUnitor f).inv := by
  rw [F.map₂_rightUnitor f]
  simp [F.mapId_eq_eqToHom]

/-- `mapComp'` differs from `mapComp` only by the dependent source-composition
transport. -/
theorem mapCompPrime_heq_mapComp
    {B C : Type*} [Bicategory B] [Bicategory C]
    (F : StrictlyUnitaryLaxFunctor B C)
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c)
    (composition : f ≫ g = fg) :
    HEq (F.toLaxFunctor.mapComp' f g fg composition) (F.mapComp f g) := by
  cases composition.symm
  simp [LaxFunctor.mapComp']

/-- The reconstructed and original native simplices have exactly the same
underlying object/1-cell prefunctor. -/
theorem toSemiSimplex_toNative_prefunctor {n : Nat}
    (simplex : TotalModelDuskinNerve.Simplex.{u, v, w} n) :
    (CoordinateSimplex.toNativeSimplex
      simplex.toSemiSimplex).toPrefunctor = simplex.toPrefunctor := by
  apply Prefunctor.ext
  · intro X Y arrow
    exact eq_of_heq (toSemiSimplex_toNative_map simplex arrow)
  · intro X
    rfl

set_option maxHeartbeats 800000 in
/-- Reconstructing after coordinate decoding preserves every compositor. The
proof separates left identity, right identity, and two-strict-arrow cases. -/
theorem toSemiSimplex_toNative_mapComp {n : Nat}
    (simplex : TotalModelDuskinNerve.Simplex.{u, v, w} n)
    {a b c : TotalModelDuskinNerve.FiniteOrdinal n}
    (f : a ⟶ b) (g : b ⟶ c) :
    HEq ((CoordinateSimplex.toNativeSimplex
      simplex.toSemiSimplex).mapComp f g) (simplex.mapComp f g) := by
  rcases a with ⟨i⟩
  rcases b with ⟨j⟩
  rcases c with ⟨k⟩
  by_cases firstIdentity : i = j
  · subst j
    have fEquality : f = 𝟙 (LocallyDiscrete.mk i) := by
      apply Discrete.ext
      apply Subsingleton.elim
    subst f
    rw [mapComp_leftIdentity, mapComp_leftIdentity]
    have hMapId := toSemiSimplex_toNative_map simplex
      (𝟙 (LocallyDiscrete.mk i))
    have hMapG := toSemiSimplex_toNative_map simplex g
    have hMapComp := toSemiSimplex_toNative_map simplex
      (𝟙 (LocallyDiscrete.mk i) ≫ g)
    have hMap₂ := toSemiSimplex_toNative_map₂ simplex
      (Bicategory.leftUnitor g).inv
    have hPrefunctor := toSemiSimplex_toNative_prefunctor simplex
    have hSource : HEq
        ((CoordinateSimplex.toNativeSimplex simplex.toSemiSimplex).map
            (𝟙 (LocallyDiscrete.mk i)) ≫
          (CoordinateSimplex.toNativeSimplex simplex.toSemiSimplex).map g)
        (simplex.map (𝟙 (LocallyDiscrete.mk i)) ≫ simplex.map g) := by
      congr! 1
    congr! 1
    case e'_4 =>
      rw [eq_of_heq hMapG]
      rfl
    case e'_6 =>
      exact (eqToHom_heq_id _).trans
        ((idTwoCell_heq_of_heq hSource).trans
          (eqToHom_heq_id _).symm)
    case e'_7 =>
      congr! 4
  · have firstIncrease : i ≤ j := leOfHom f.as
    have firstStrict : i < j := lt_of_le_of_ne firstIncrease firstIdentity
    have fEquality : f = TotalModelDuskinNerve.ordinalHom firstStrict.le := by
      apply Discrete.ext
      apply Subsingleton.elim
    subst f
    by_cases secondIdentity : j = k
    · subst k
      have gEquality : g = 𝟙 (LocallyDiscrete.mk j) := by
        apply Discrete.ext
        apply Subsingleton.elim
      subst g
      rw [mapComp_rightIdentity, mapComp_rightIdentity]
      have hMapF := toSemiSimplex_toNative_map simplex
        (TotalModelDuskinNerve.ordinalHom firstStrict.le)
      have hMapId := toSemiSimplex_toNative_map simplex
        (𝟙 (LocallyDiscrete.mk j))
      have hMapComp := toSemiSimplex_toNative_map simplex
        (TotalModelDuskinNerve.ordinalHom firstStrict.le ≫
          𝟙 (LocallyDiscrete.mk j))
      have hMap₂ := toSemiSimplex_toNative_map₂ simplex
        (Bicategory.rightUnitor
          (TotalModelDuskinNerve.ordinalHom firstStrict.le)).inv
      have hPrefunctor := toSemiSimplex_toNative_prefunctor simplex
      have hSource : HEq
          ((CoordinateSimplex.toNativeSimplex simplex.toSemiSimplex).map
              (TotalModelDuskinNerve.ordinalHom firstStrict.le) ≫
            (CoordinateSimplex.toNativeSimplex simplex.toSemiSimplex).map
              (𝟙 (LocallyDiscrete.mk j)))
          (simplex.map
              (TotalModelDuskinNerve.ordinalHom firstStrict.le) ≫
            simplex.map (𝟙 (LocallyDiscrete.mk j))) := by
        congr! 1
      congr! 1
      case e'_4 =>
        rw [eq_of_heq hMapF]
        rfl
      case e'_6 =>
        exact (eqToHom_heq_id _).trans
          ((idTwoCell_heq_of_heq hSource).trans
            (eqToHom_heq_id _).symm)
      case e'_7 =>
        congr! 4
    · have secondIncrease : j ≤ k := leOfHom g.as
      have secondStrict : j < k :=
        lt_of_le_of_ne secondIncrease secondIdentity
      have gEquality : g =
          TotalModelDuskinNerve.ordinalHom secondStrict.le := by
        apply Discrete.ext
        apply Subsingleton.elim
      subst g
      let fg := TotalModelDuskinNerve.ordinalHom
        (firstStrict.trans secondStrict).le
      have composition :
          TotalModelDuskinNerve.ordinalHom firstStrict.le ≫
            TotalModelDuskinNerve.ordinalHom secondStrict.le = fg := by
        apply Discrete.ext
        apply Subsingleton.elim
      have reconstructedComparison := mapCompPrime_heq_mapComp
        (CoordinateSimplex.toNativeSimplex simplex.toSemiSimplex)
        (TotalModelDuskinNerve.ordinalHom firstStrict.le)
        (TotalModelDuskinNerve.ordinalHom secondStrict.le) fg composition
      have decodedComparison :=
        CoordinateSimplex.toNativeSimplex_comparison
          simplex.toSemiSimplex firstStrict secondStrict
      have originalComparison := mapCompPrime_heq_mapComp simplex
        (TotalModelDuskinNerve.ordinalHom firstStrict.le)
        (TotalModelDuskinNerve.ordinalHom secondStrict.le) fg composition
      have coordinateIsOriginal : HEq
          (simplex.toSemiSimplex.triangle i j k firstStrict secondStrict)
          (simplex.toLaxFunctor.mapComp'
            (TotalModelDuskinNerve.ordinalHom firstStrict.le)
            (TotalModelDuskinNerve.ordinalHom secondStrict.le)
            fg composition) := by
        rfl
      exact reconstructedComparison.symm.trans
        (decodedComparison.trans
          (coordinateIsOriginal.trans originalComparison))

/-- Native decoding followed by reconstruction is the identity on every
normal-lax finite-ordinal simplex. -/
theorem toSemiSimplex_toNativeSimplex {n : Nat}
    (simplex : TotalModelDuskinNerve.Simplex.{u, v, w} n) :
    CoordinateSimplex.toNativeSimplex simplex.toSemiSimplex = simplex := by
  apply StrictlyUnitaryLaxFunctor.ext
  · rfl
  · refine Function.hfunext rfl fun X X' hX => ?_
    cases eq_of_heq hX
    refine Function.hfunext rfl fun Y Y' hY => ?_
    cases eq_of_heq hY
    refine Function.hfunext rfl fun arrow arrow' hArrow => ?_
    cases eq_of_heq hArrow
    exact toSemiSimplex_toNative_map simplex arrow
  · refine Function.hfunext rfl fun a a' ha => ?_
    cases eq_of_heq ha
    refine Function.hfunext rfl fun b b' hb => ?_
    cases eq_of_heq hb
    refine Function.hfunext rfl fun f f' hf => ?_
    cases eq_of_heq hf
    refine Function.hfunext rfl fun g g' hg => ?_
    cases eq_of_heq hg
    refine Function.hfunext rfl fun eta eta' heta => ?_
    cases eq_of_heq heta
    exact toSemiSimplex_toNative_map₂ simplex eta
  · refine Function.hfunext rfl fun a a' ha => ?_
    cases eq_of_heq ha
    have identityObjects : HEq
        (𝟙 (𝟙 ((CoordinateSimplex.toNativeSimplex
          simplex.toSemiSimplex).obj a)))
        (𝟙 (𝟙 (simplex.obj a))) := by
      rfl
    exact (mapId_heq_id
      (CoordinateSimplex.toNativeSimplex simplex.toSemiSimplex) a).trans
      (identityObjects.trans (mapId_heq_id simplex a).symm)
  · refine Function.hfunext rfl fun a a' ha => ?_
    cases eq_of_heq ha
    refine Function.hfunext rfl fun b b' hb => ?_
    cases eq_of_heq hb
    refine Function.hfunext rfl fun c c' hc => ?_
    cases eq_of_heq hc
    refine Function.hfunext rfl fun f f' hf => ?_
    cases eq_of_heq hf
    refine Function.hfunext rfl fun g g' hg => ?_
    cases eq_of_heq hg
    exact toSemiSimplex_toNative_mapComp simplex f g

/-- **Degreewise Duskin representation equivalence.** Coordinate simplices and
native normal-lax finite-ordinal simplices contain exactly the same data. -/
def nativeCoordinateEquiv (n : Nat) :
    CoordinateSimplex.{u, v, w} n ≃
      TotalModelDuskinNerve.Simplex.{u, v, w} n where
  toFun := toNativeSimplex
  invFun := TotalModelDuskinNerve.Simplex.toSemiSimplex
  left_inv := toNativeSimplex_toSemiSimplex
  right_inv := toSemiSimplex_toNativeSimplex

/-- The coordinate presentation transported along the degreewise equivalence.
Unlike the original semi-simplicial presentation, this functor has all
degeneracy maps. -/
def coordinateNerve : TotalModelDuskinNerve.SSet.{u, v, w} where
  obj dimension := CoordinateSimplex.{u, v, w} dimension.unop.len
  map map := ↾fun simplex =>
    (TotalModelDuskinNerve.nerve.{u, v, w}.map map
      (toNativeSimplex simplex)).toSemiSimplex
  map_id dimension := by
    ext simplex
    have nativeIdentity :
        TotalModelDuskinNerve.nerve.{u, v, w}.map (𝟙 dimension)
            (toNativeSimplex simplex) = toNativeSimplex simplex := by
      exact congrArg
        (fun morphism => (ConcreteCategory.hom morphism)
          (toNativeSimplex simplex))
        (TotalModelDuskinNerve.nerve.{u, v, w}.map_id dimension)
    exact (congrArg TotalModelDuskinNerve.Simplex.toSemiSimplex
      nativeIdentity).trans simplex.toNativeSimplex_toSemiSimplex
  map_comp first second := by
    ext simplex
    let native := toNativeSimplex simplex
    let firstImage :=
      TotalModelDuskinNerve.nerve.{u, v, w}.map first native
    have nativeComposition :
        TotalModelDuskinNerve.nerve.{u, v, w}.map (first ≫ second) native =
          TotalModelDuskinNerve.nerve.{u, v, w}.map second firstImage := by
      exact congrArg
        (fun morphism => (ConcreteCategory.hom morphism) native)
        (TotalModelDuskinNerve.nerve.{u, v, w}.map_comp first second)
    have innerRoundTrip : toNativeSimplex firstImage.toSemiSimplex = firstImage :=
      toSemiSimplex_toNativeSimplex firstImage
    exact (congrArg TotalModelDuskinNerve.Simplex.toSemiSimplex
      nativeComposition).trans (congrArg
        (fun next => (TotalModelDuskinNerve.nerve.{u, v, w}.map second
          next).toSemiSimplex) innerRoundTrip.symm)

/-- The full coordinate nerve is naturally isomorphic to the native Duskin
nerve in every dimension and along every face or degeneracy map. -/
def coordinateNerveIsoNative :
    coordinateNerve.{u, v, w} ≅ TotalModelDuskinNerve.nerve.{u, v, w} :=
  NatIso.ofComponents
    (fun dimension => Equiv.toIso
      (nativeCoordinateEquiv.{u, v, w} dimension.unop.len))
    (fun map => by
      ext simplex
      change toNativeSimplex
          ((TotalModelDuskinNerve.nerve.{u, v, w}.map map
            (toNativeSimplex simplex)).toSemiSimplex) =
        TotalModelDuskinNerve.nerve.{u, v, w}.map map
          (toNativeSimplex simplex)
      exact toSemiSimplex_toNativeSimplex _)

end CoordinateSimplex

end TotalModelDuskinRepresentation

end Ript.Higher
