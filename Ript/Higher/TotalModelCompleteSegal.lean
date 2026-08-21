import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Ript.ForMathlib.AlgebraicTopology.GroupoidalCompleteSegal
import Ript.ForMathlib.AlgebraicTopology.NerveHomotopy
import Ript.ForMathlib.CategoryTheory.GroupoidInterval
import Ript.ForMathlib.CategoryTheory.Isofibration
import Ript.ForMathlib.CategoryTheory.TriangleBoundary
import Ript.Higher.TotalModelDuskinRepresentation

/-!
# Rezk completeness core for total resource models

For a category `C`, the Rezk core diagram places in outer degree `n` the
nerve of the maximal subgroupoid of `Fin (n + 1) ⥤ C`.  Thus every vertical
level is genuinely Kan, even when `C` contains noninvertible arrows.

This file builds that diagram generically and specializes it to the homotopy
category of the total resource-model bicategory.  It also constructs an
explicit selected equivalence-arrow space and presents the object-to-identity
arrow map as the nerve of a categorical equivalence.  Its inclusion into
actual outer degree one is proved naturally isomorphic to the genuine outer
zero-degeneracy and packaged as a categorical completeness factorization.  A
generic natural-transformation-to-nerve-homotopy bridge upgrades this to an
actual simplicial homotopy.  The degree-one Reedy matching restriction is now
the literal pair of outer faces, transported to the selected simplicial-set
product, and proved a Kan fibration.  Degree two has an explicit triangular
boundary category, strict-image representation theorem, and Kan-fibration
restriction; its boundary nerve is now explicitly isomorphic to the selected
abstract Reedy matching limit.  Every matching map in dimensions at least
three is also an isomorphism, by categorical-nerve boundary filling, so the
positive-degree Reedy package is complete.  The remaining comparison problem
is the higher-localization comparison.  The full local mapping nerves retain
noninvertible 2-cells in the attached higher package.  Outer Segal
reconstruction is established by identifying each horizontal row with the
nerve of a category of equivalence strings, while the selected equivalence
space is explicitly compared with the actual invertible-arrow subspace.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Higher

open CategoryTheory
open CategoryTheory.Limits
open HomotopicalAlgebra
open Opposite
open Simplicial
open SSet
open scoped SSet.modelCategoryQuillen

universe u

namespace RezkCore

variable (C : Type u) [Category.{u} C]

/-- Constant zero-simplex diagrams. -/
abbrev zeroConstantFunctor : C ⥤ ComposableArrows C 0 :=
  Functor.const (Fin 1)

/-- Evaluation of a zero-simplex diagram at its unique vertex. -/
abbrev zeroEvaluationFunctor : ComposableArrows C 0 ⥤ C :=
  (evaluation (Fin 1) C).obj 0

/-- Every diagram on `Fin 1` is naturally its constant diagram. -/
def zeroConstantNatIso :
    zeroEvaluationFunctor C ⋙ zeroConstantFunctor C ≅
      𝟭 (ComposableArrows C 0) :=
  NatIso.ofComponents
    (fun F => ComposableArrows.isoMk₀ (Iso.refl (F.obj' 0)))
    (fun _ => by
      apply NatTrans.ext
      funext i
      fin_cases i
      simp [zeroEvaluationFunctor, zeroConstantFunctor])

/-- A category is explicitly equivalent to its category of zero-simplex
diagrams. -/
def zeroDiagramEquivalence : C ≌ ComposableArrows C 0 where
  functor := zeroConstantFunctor C
  inverse := zeroEvaluationFunctor C
  unitIso := (Functor.constCompEvaluationObj C (0 : Fin 1)).symm
  counitIso := zeroConstantNatIso C
  functor_unitIso_comp _ := by
    apply ComposableArrows.hom_ext₀
    simp [zeroConstantNatIso, zeroConstantFunctor]

/-- The category-valued Rezk core diagram. Outer `n` consists of finite
`n`-strings and invertible natural transformations between them. -/
def diagramCat : SimplicialObject Cat where
  obj Δ := Cat.of (Core (ComposableArrows C Δ.unop.len))
  map f := ((ComposableArrows.whiskerLeftFunctor
    (SimplexCategory.toCat.map f.unop).toFunctor).core).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The bisimplicial Rezk core diagram. -/
def diagram : SimplicialObject SSet :=
  diagramCat C ⋙ CategoryTheory.nerveFunctor

/-- Every vertical level is Kan because it is the nerve of a maximal
subgroupoid. -/
instance levelKan (Δ : SimplexCategoryᵒᵖ) :
    KanComplex ((diagram C).obj Δ) :=
  CategoryTheory.Nerve.kanComplex (Core (ComposableArrows C Δ.unop.len))

/-- Property of a finite string whose every structure map is invertible. -/
def equivalenceStringProperty (k : ℕ) :
    ObjectProperty (ComposableArrows C k) :=
  fun F ↦ ∀ {i j : Fin (k + 1)} (f : i ⟶ j), IsIso (F.map f)

/-- The full category of length-`k` equivalence strings in `C`, with arbitrary
natural transformations as morphisms.  These are the objects seen by a fixed
vertical degree of the Rezk core diagram. -/
abbrev EquivalenceString (k : ℕ) :=
  (equivalenceStringProperty C k).FullSubcategory

private lemma coreObj_ext {A : Type*} {X Y : Core A}
    (h : X.of = Y.of) : X = Y := by
  cases X
  cases Y
  cases h
  rfl

/-- Any functor induces a natural map between the corresponding Rezk core
diagrams by postcomposition in every outer string degree. -/
def diagramCatMap {D : Type u} [Category.{u} D] (F : C ⥤ D) :
    diagramCat C ⟶ diagramCat D where
  app Δ := ((F.mapComposableArrows Δ.unop.len).core).toCatHom
  naturality := by
    intro Δ Γ f
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.hext
    · intro X
      apply coreObj_ext
      rfl
    · intro X Y η
      apply heq_of_eq
      apply Core.hom_ext
      apply NatTrans.ext
      funext i
      rfl

/-- The induced natural transformation of bisimplicial Rezk diagrams. -/
def diagramMap {D : Type u} [Category.{u} D] (F : C ⥤ D) :
    diagram C ⟶ diagram D :=
  Functor.whiskerRight (diagramCatMap C F) CategoryTheory.nerveFunctor

/-- The vertical zero-simplex in outer degree one represented by an arrow of
the underlying category. -/
def arrowVertex {X Y : C} (f : X ⟶ Y) :
    ((diagram C).obj (op (SimplexCategory.mk 1))).obj
      (op (SimplexCategory.mk 0)) :=
  ComposableArrows.mk₀
    (⟨ComposableArrows.mk₁ f⟩ : Core (ComposableArrows C 1))

/-- Functorial Rezk comparison sends an arrow vertex to the vertex represented
by the mapped arrow. -/
theorem diagramMap_arrowVertex {D : Type u} [Category.{u} D]
    (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    ((diagramMap C F).app (op (SimplexCategory.mk 1))).app
        (op (SimplexCategory.mk 0)) (arrowVertex C f) =
      arrowVertex D (F.map f) := by
  change (CategoryTheory.nerveMap ((F.mapComposableArrows 1).core)).app
      (op (SimplexCategory.mk 0))
        (ComposableArrows.mk₀
          (⟨ComposableArrows.mk₁ f⟩ : Core (ComposableArrows C 1))) =
    ComposableArrows.mk₀
      (⟨ComposableArrows.mk₁ (F.map f)⟩ : Core (ComposableArrows D 1))
  rw [CategoryTheory.nerveMap_app_mk₀]
  apply ComposableArrows.ext₀
  apply coreObj_ext
  exact CategoryTheory.nerveMap_app_mk₁ F f

private lemma eqToHom_prod_core_fst_app
    {A B : Core (ComposableArrows C 0) × Core (ComposableArrows C 0)}
    (h : A = B) :
    (eqToHom h).1.iso.hom.app 0 =
      eqToHom (congrArg (fun Z => Z.1.of.obj 0) h) := by
  subst h
  rfl

private lemma eqToHom_prod_core_snd_app
    {A B : Core (ComposableArrows C 0) × Core (ComposableArrows C 0)}
    (h : A = B) :
    (eqToHom h).2.iso.hom.app 0 =
      eqToHom (congrArg (fun Z => Z.2.of.obj 0) h) := by
  subst h
  rfl

/-- The literal degree-one boundary restriction of the category-valued Rezk
core diagram.  Its two components are the actual outer face maps, ordered as
source (`d₁`) and target (`d₀`), and its codomain retains the genuine
zero-simplex diagram coordinates rather than replacing them by `Core C`. -/
def degreeOneMatchingFunctor :
    Core (ComposableArrows C 1) ⥤
      Core (ComposableArrows C 0) × Core (ComposableArrows C 0) :=
  ((diagramCat C).δ (1 : Fin 2)).toFunctor.prod'
    ((diagramCat C).δ (0 : Fin 2)).toFunctor

@[simp]
theorem degreeOneMatchingFunctor_obj_fst_obj
    (X : Core (ComposableArrows C 1)) :
    ((degreeOneMatchingFunctor C).obj X).1.of.obj 0 = X.of.obj 0 :=
  rfl

@[simp]
theorem degreeOneMatchingFunctor_obj_snd_obj
    (X : Core (ComposableArrows C 1)) :
    ((degreeOneMatchingFunctor C).obj X).2.of.obj 0 = X.of.obj 1 :=
  rfl

@[simp]
theorem degreeOneMatchingFunctor_map_fst_app
    {X Y : Core (ComposableArrows C 1)} (η : X ⟶ Y) :
    (((degreeOneMatchingFunctor C).map η).1.iso.hom.app 0) =
      η.iso.hom.app 0 :=
  rfl

@[simp]
theorem degreeOneMatchingFunctor_map_snd_app
    {X Y : Core (ComposableArrows C 1)} (η : X ⟶ Y) :
    (((degreeOneMatchingFunctor C).map η).2.iso.hom.app 0) =
      η.iso.hom.app 1 :=
  rfl

private lemma degreeOneMatching_eqToHom_fst_app
    (Y : Core (ComposableArrows C 0) × Core (ComposableArrows C 0))
    (g : Y.1.of.obj 0 ⟶ Y.2.of.obj 0)
    (h : (degreeOneMatchingFunctor C).obj
      (⟨ComposableArrows.mk₁ g⟩ : Core (ComposableArrows C 1)) = Y) :
    (eqToHom h.symm).1.iso.hom.app 0 = 𝟙 _ := by
  rw [eqToHom_prod_core_fst_app]
  rw [show congrArg
      (fun Z : Core (ComposableArrows C 0) ×
        Core (ComposableArrows C 0) => Z.1.of.obj 0)
      h.symm = rfl from Subsingleton.elim _ _]
  rfl

private lemma degreeOneMatching_eqToHom_snd_app
    (Y : Core (ComposableArrows C 0) × Core (ComposableArrows C 0))
    (g : Y.1.of.obj 0 ⟶ Y.2.of.obj 0)
    (h : (degreeOneMatchingFunctor C).obj
      (⟨ComposableArrows.mk₁ g⟩ : Core (ComposableArrows C 1)) = Y) :
    (eqToHom h.symm).2.iso.hom.app 0 = 𝟙 _ := by
  rw [eqToHom_prod_core_snd_app]
  rw [show congrArg
      (fun Z : Core (ComposableArrows C 0) ×
        Core (ComposableArrows C 0) => Z.2.of.obj 0)
      h.symm = rfl from Subsingleton.elim _ _]
  rfl

/-- The genuine degree-one boundary restriction is a strict categorical
isofibration.  A pair of endpoint isomorphisms lifts by conjugating the
original arrow; equality of zero-diagrams follows from their unique vertex. -/
instance degreeOneMatchingFunctorIsIsofibration :
    (degreeOneMatchingFunctor C).IsIsofibration where
  exists_isoLift {X Y} e := by
    let α₀ : X.of.obj 0 ≅ Y.1.of.obj 0 :=
      (e.hom.1.iso.app 0)
    let α₁ : X.of.obj 1 ≅ Y.2.of.obj 0 :=
      (e.hom.2.iso.app 0)
    let g : Y.1.of.obj 0 ⟶ Y.2.of.obj 0 :=
      α₀.inv ≫ X.of.hom ≫ α₁.hom
    let X' : Core (ComposableArrows C 1) :=
      ⟨ComposableArrows.mk₁ g⟩
    let η : X ≅ X' := Core.isoMk
      (ComposableArrows.isoMk₁ α₀ α₁ (by
        change X.of.hom ≫ α₁.hom = α₀.hom ≫ g
        simp only [g, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]))
    have h₀ : ((degreeOneMatchingFunctor C).obj X').1 = Y.1 := by
      apply coreObj_ext
      apply ComposableArrows.ext₀
      rfl
    have h₁ : ((degreeOneMatchingFunctor C).obj X').2 = Y.2 := by
      apply coreObj_ext
      apply ComposableArrows.ext₀
      rfl
    let h : (degreeOneMatchingFunctor C).obj X' = Y :=
      Prod.ext h₀ h₁
    exact ⟨{
      obj := X'
      obj_eq := h
      iso := η
      map_iso_hom := by
        apply Prod.hom_ext
        · apply Core.hom_ext
          apply ComposableArrows.hom_ext₀
          change (((degreeOneMatchingFunctor C).map η.hom).1.iso.hom.app 0) =
            ((e.hom ≫ eqToHom h.symm).1.iso.hom.app 0)
          rw [degreeOneMatchingFunctor_map_fst_app]
          change e.hom.1.iso.hom.app 0 =
            e.hom.1.iso.hom.app 0 ≫
              (eqToHom h.symm).1.iso.hom.app 0
          rw [degreeOneMatching_eqToHom_fst_app C Y g h]
          exact (Category.comp_id (e.hom.1.iso.hom.app 0)).symm
        · apply Core.hom_ext
          apply ComposableArrows.hom_ext₀
          change (((degreeOneMatchingFunctor C).map η.hom).2.iso.hom.app 0) =
            ((e.hom ≫ eqToHom h.symm).2.iso.hom.app 0)
          rw [degreeOneMatchingFunctor_map_snd_app]
          change e.hom.2.iso.hom.app 0 =
            e.hom.2.iso.hom.app 0 ≫
              (eqToHom h.symm).2.iso.hom.app 0
          rw [degreeOneMatching_eqToHom_snd_app C Y g h]
          exact (Category.comp_id (e.hom.2.iso.hom.app 0)).symm }⟩

/-- Before converting the categorical product to the simplicial-set product,
the nerve of the literal degree-one restriction is already a Kan fibration. -/
theorem degreeOneMatchingNerveMap_fibration :
    Fibration (CategoryTheory.nerveMap (degreeOneMatchingFunctor C)) :=
  CategoryTheory.Functor.nerveMap_fibration
    (degreeOneMatchingFunctor C)

/-- After taking nerves, the first component is still the genuine outer
source face of the Rezk core diagram. -/
theorem degreeOneMatchingNerveMap_comp_fst :
    CategoryTheory.nerveMap (degreeOneMatchingFunctor C) ≫
        CategoryTheory.nerveMap (CategoryTheory.Prod.fst
          (Core (ComposableArrows C 0)) (Core (ComposableArrows C 0))) =
      (diagram C).δ (1 : Fin 2) :=
  rfl

/-- After taking nerves, the second component is the genuine outer target
face of the Rezk core diagram. -/
theorem degreeOneMatchingNerveMap_comp_snd :
    CategoryTheory.nerveMap (degreeOneMatchingFunctor C) ≫
        CategoryTheory.nerveMap (CategoryTheory.Prod.snd
          (Core (ComposableArrows C 0)) (Core (ComposableArrows C 0))) =
      (diagram C).δ (0 : Fin 2) :=
  rfl

/-- Kernel-checked degree-one Reedy data in the literal categorical product
coordinates.  The two projection equations prevent an unrelated fibration
with the same source and target from being substituted for the actual pair
of outer faces. -/
structure DegreeOneMatchingCore where
  /-- Nerve of the pair of genuine outer face functors. -/
  matchingMap :
    CategoryTheory.nerve (Core (ComposableArrows C 1)) ⟶
      CategoryTheory.nerve
        (Core (ComposableArrows C 0) × Core (ComposableArrows C 0))
  /-- Kan fibration evidence for the displayed restriction. -/
  matchingFibration : Fibration matchingMap
  /-- Its first projection is the actual source face. -/
  sourceFace :
    matchingMap ≫ CategoryTheory.nerveMap (CategoryTheory.Prod.fst
      (Core (ComposableArrows C 0)) (Core (ComposableArrows C 0))) =
        (diagram C).δ (1 : Fin 2)
  /-- Its second projection is the actual target face. -/
  targetFace :
    matchingMap ≫ CategoryTheory.nerveMap (CategoryTheory.Prod.snd
      (Core (ComposableArrows C 0)) (Core (ComposableArrows C 0))) =
        (diagram C).δ (0 : Fin 2)

/-- Package the genuine degree-one matching restriction, its fibration, and
both literal face equations. -/
noncomputable def degreeOneMatchingCore : DegreeOneMatchingCore C where
  matchingMap := CategoryTheory.nerveMap (degreeOneMatchingFunctor C)
  matchingFibration := degreeOneMatchingNerveMap_fibration C
  sourceFace := degreeOneMatchingNerveMap_comp_fst C
  targetFace := degreeOneMatchingNerveMap_comp_snd C

/-- The ordinary product category of two outer zero-categories, equipped with
its two projection functors as a cone in `Cat`. -/
private def degreeZeroTypeProductCone :
    BinaryFan
      (Cat.of (Core (ComposableArrows C 0)))
      (Cat.of (Core (ComposableArrows C 0))) :=
  BinaryFan.mk
    (CategoryTheory.Prod.fst
      (Core (ComposableArrows C 0))
      (Core (ComposableArrows C 0))).toCatHom
    (CategoryTheory.Prod.snd
      (Core (ComposableArrows C 0))
      (Core (ComposableArrows C 0))).toCatHom

/-- The explicit product category is a genuine strict binary-product limit in
`Cat`, not only a bicategorical product. -/
private def degreeZeroTypeProductConeIsLimit :
    IsLimit (degreeZeroTypeProductCone C) :=
  BinaryFan.IsLimit.mk _
    (fun f g => (f.toFunctor.prod' g.toFunctor).toCatHom)
    (fun _ _ => by
      apply Cat.Hom.ext
      rfl)
    (fun _ _ => by
      apply Cat.Hom.ext
      rfl)
    (by cat_disch)

/-- The explicit product category is isomorphic to the product object selected
by Mathlib's small-category limit instance. -/
noncomputable def degreeZeroTypeProductIso :
    Cat.of (Core (ComposableArrows C 0) ×
      Core (ComposableArrows C 0)) ≅
      Cat.of (Core (ComposableArrows C 0)) ⨯
        Cat.of (Core (ComposableArrows C 0)) :=
  (degreeZeroTypeProductConeIsLimit C).conePointUniqueUpToIso
    (limit.isLimit _)

/-- Taking nerves and then using preservation of binary products transports
the categorical product model to Mathlib's selected simplicial-set product. -/
noncomputable def degreeZeroNerveProductIso :
    CategoryTheory.nerve
        (Core (ComposableArrows C 0) × Core (ComposableArrows C 0)) ≅
      CategoryTheory.nerve (Core (ComposableArrows C 0)) ⨯
        CategoryTheory.nerve (Core (ComposableArrows C 0)) :=
  CategoryTheory.nerveFunctor.mapIso (degreeZeroTypeProductIso C) ≪≫
    PreservesLimitPair.iso CategoryTheory.nerveFunctor
      (Cat.of (Core (ComposableArrows C 0)))
      (Cat.of (Core (ComposableArrows C 0)))

/-- The first projection of the nerve-product transport is the nerve of the
ordinary first projection functor. -/
theorem degreeZeroNerveProductIso_hom_fst :
    (degreeZeroNerveProductIso C).hom ≫ prod.fst =
      CategoryTheory.nerveMap (CategoryTheory.Prod.fst
        (Core (ComposableArrows C 0))
        (Core (ComposableArrows C 0))) := by
  change
    ((CategoryTheory.nerveFunctor.mapIso
        (degreeZeroTypeProductIso C)).hom ≫
      (PreservesLimitPair.iso CategoryTheory.nerveFunctor
        (Cat.of (Core (ComposableArrows C 0)))
        (Cat.of (Core (ComposableArrows C 0)))).hom) ≫ prod.fst =
      CategoryTheory.nerveFunctor.map
        (CategoryTheory.Prod.fst
          (Core (ComposableArrows C 0))
          (Core (ComposableArrows C 0))).toCatHom
  rw [Category.assoc, PreservesLimitPair.iso_hom, prodComparison_fst,
    CategoryTheory.Functor.mapIso_hom,
    ← CategoryTheory.nerveFunctor.map_comp]
  apply congrArg CategoryTheory.nerveFunctor.map
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    (degreeZeroTypeProductConeIsLimit C)
    (limit.isLimit (pair
      (Cat.of (Core (ComposableArrows C 0)))
      (Cat.of (Core (ComposableArrows C 0)))))
    ⟨WalkingPair.left⟩

/-- The second projection of the nerve-product transport is the nerve of the
ordinary second projection functor. -/
theorem degreeZeroNerveProductIso_hom_snd :
    (degreeZeroNerveProductIso C).hom ≫ prod.snd =
      CategoryTheory.nerveMap (CategoryTheory.Prod.snd
        (Core (ComposableArrows C 0))
        (Core (ComposableArrows C 0))) := by
  change
    ((CategoryTheory.nerveFunctor.mapIso
        (degreeZeroTypeProductIso C)).hom ≫
      (PreservesLimitPair.iso CategoryTheory.nerveFunctor
        (Cat.of (Core (ComposableArrows C 0)))
        (Cat.of (Core (ComposableArrows C 0)))).hom) ≫ prod.snd =
      CategoryTheory.nerveFunctor.map
        (CategoryTheory.Prod.snd
          (Core (ComposableArrows C 0))
          (Core (ComposableArrows C 0))).toCatHom
  rw [Category.assoc, PreservesLimitPair.iso_hom, prodComparison_snd,
    CategoryTheory.Functor.mapIso_hom,
    ← CategoryTheory.nerveFunctor.map_comp]
  apply congrArg CategoryTheory.nerveFunctor.map
  exact IsLimit.conePointUniqueUpToIso_hom_comp
    (degreeZeroTypeProductConeIsLimit C)
    (limit.isLimit (pair
      (Cat.of (Core (ComposableArrows C 0)))
      (Cat.of (Core (ComposableArrows C 0)))))
    ⟨WalkingPair.right⟩

/-- The standard degree-one Reedy matching map, now landing in Mathlib's
selected binary product of the two outer zero-spaces. -/
noncomputable def degreeOneMatchingMap :
    (diagram C).obj (op (SimplexCategory.mk 1)) ⟶
      (diagram C).obj (op (SimplexCategory.mk 0)) ⨯
        (diagram C).obj (op (SimplexCategory.mk 0)) :=
  CategoryTheory.nerveMap (degreeOneMatchingFunctor C) ≫
    (degreeZeroNerveProductIso C).hom

/-- The standard degree-one Reedy matching map is a Kan fibration. -/
theorem degreeOneMatchingMap_fibration :
    Fibration (degreeOneMatchingMap C) := by
  change Fibration
    (CategoryTheory.nerveMap (degreeOneMatchingFunctor C) ≫
      (degreeZeroNerveProductIso C).hom)
  rw [SSet.modelCategoryQuillen.fibration_iff]
  apply (fibrations SSet).comp_mem
  · rw [SSet.modelCategoryQuillen.fibrations_eq]
    exact (SSet.modelCategoryQuillen.fibration_iff _).mp
      (degreeOneMatchingNerveMap_fibration C)
  · rw [SSet.modelCategoryQuillen.fibrations_eq]
    exact (SSet.modelCategoryQuillen.fibration_iff _).mp (by infer_instance)

/-- The transported map is exactly the canonical map to the binary product
whose components are the two genuine outer faces. -/
theorem degreeOneMatchingMap_eq_faces :
    degreeOneMatchingMap C =
      prod.lift ((diagram C).δ (1 : Fin 2))
        ((diagram C).δ (0 : Fin 2)) := by
  apply prod.hom_ext
  · rw [prod.lift_fst]
    change (CategoryTheory.nerveMap (degreeOneMatchingFunctor C) ≫
      (degreeZeroNerveProductIso C).hom) ≫ prod.fst = _
    rw [Category.assoc, degreeZeroNerveProductIso_hom_fst,
      degreeOneMatchingNerveMap_comp_fst]
  · rw [prod.lift_snd]
    change (CategoryTheory.nerveMap (degreeOneMatchingFunctor C) ≫
      (degreeZeroNerveProductIso C).hom) ≫ prod.snd = _
    rw [Category.assoc, degreeZeroNerveProductIso_hom_snd,
      degreeOneMatchingNerveMap_comp_snd]

/-- Full degree-one Reedy witness: the categorical matching presentation,
its transport to the selected simplicial-set product, exact identification
with the canonical face pair, and Kan fibration evidence. -/
structure DegreeOneReedyCore extends DegreeOneMatchingCore C where
  /-- Matching map into Mathlib's selected simplicial-set binary product. -/
  standardMatchingMap :
    (diagram C).obj (op (SimplexCategory.mk 1)) ⟶
      (diagram C).obj (op (SimplexCategory.mk 0)) ⨯
        (diagram C).obj (op (SimplexCategory.mk 0))
  /-- The standard matching map is a Kan fibration. -/
  standardMatchingFibration : Fibration standardMatchingMap
  /-- The standard map is exactly the product lift of `d₁` and `d₀`. -/
  standardMatchingMap_eq_faces :
    standardMatchingMap =
      prod.lift ((diagram C).δ (1 : Fin 2))
        ((diagram C).δ (0 : Fin 2))

/-- Package all genuine degree-one Reedy data. -/
noncomputable def degreeOneReedyCore : DegreeOneReedyCore C where
  toDegreeOneMatchingCore := degreeOneMatchingCore C
  standardMatchingMap := degreeOneMatchingMap C
  standardMatchingFibration := degreeOneMatchingMap_fibration C
  standardMatchingMap_eq_faces := degreeOneMatchingMap_eq_faces C

/-- Vertical space of independently specified triangular boundaries. -/
abbrev degreeTwoBoundarySpace : SSet.{u} :=
  CategoryTheory.nerve (Core (CategoryTheory.TriangleBoundary C))

/-- Restrict an outer two-simplex to its three independently specified
boundary edges. -/
def degreeTwoBoundaryMap :
    (diagram C).obj (op (SimplexCategory.mk 2)) ⟶
      degreeTwoBoundarySpace C :=
  CategoryTheory.nerveMap
    (CategoryTheory.TriangleBoundary.coreRestrictionFunctor (C := C))

/-- The degree-two boundary restriction is a Kan fibration. -/
theorem degreeTwoBoundaryMap_fibration :
    Fibration (degreeTwoBoundaryMap C) :=
  CategoryTheory.TriangleBoundary.nerveMap_coreRestrictionFunctor_fibration C

/-- The selected abstract Reedy matching object in an arbitrary outer
degree. -/
noncomputable abbrev abstractMatchingObject (n : ℕ) : SSet.{u} :=
  SSet.SimplicialSpaceBoundaryMatchingObject (diagram C) n

/-- The universal abstract Reedy matching map in an arbitrary outer degree. -/
noncomputable def abstractMatchingMap (n : ℕ) :
    (diagram C).obj (op (SimplexCategory.mk n)) ⟶
      abstractMatchingObject C n :=
  SSet.simplicialSpaceBoundaryMatchingMap (diagram C) n

/-- The arbitrary-degree matching map is the selected limit lift of the
boundary-restriction cone. -/
theorem abstractMatchingMap_eq_limitLift (n : ℕ) :
    (SSet.simplicialSpaceBoundaryMatchingConeIsLimit (diagram C) n).lift
        (SSet.simplicialSpaceBoundaryRestrictionCone (diagram C) n) =
      abstractMatchingMap C n :=
  SSet.simplicialSpaceBoundaryMatchingMap_eq_limitLift (diagram C) n

/-- Every projection of the arbitrary-degree matching map is the
corresponding outer boundary restriction. -/
theorem abstractMatchingMap_fac (n : ℕ)
    (j : SSet.BoundaryMatchingIndex.{u} n) :
    abstractMatchingMap C n ≫
        (SSet.simplicialSpaceBoundaryMatchingCone (diagram C) n).π.app j =
      (SSet.simplicialSpaceBoundaryRestrictionCone (diagram C) n).π.app j := by
  rw [← abstractMatchingMap_eq_limitLift]
  exact (SSet.simplicialSpaceBoundaryMatchingConeIsLimit
    (diagram C) n).fac
      (SSet.simplicialSpaceBoundaryRestrictionCone (diagram C) n) j

/-- The selected abstract degree-two Reedy matching object. -/
noncomputable abbrev degreeTwoAbstractMatchingObject : SSet.{u} :=
  SSet.SimplicialSpaceBoundaryMatchingObject (diagram C) 2

/-- The actual abstract degree-two Reedy matching map, defined by the
universal lift of the full boundary restriction cone. -/
noncomputable def degreeTwoAbstractMatchingMap :
    (diagram C).obj (op (SimplexCategory.mk 2)) ⟶
      degreeTwoAbstractMatchingObject C :=
  SSet.simplicialSpaceBoundaryMatchingMap (diagram C) 2

/-- The abstract degree-two map is exactly the selected limit lift. -/
theorem degreeTwoAbstractMatchingMap_eq_limitLift :
    (SSet.simplicialSpaceBoundaryMatchingConeIsLimit (diagram C) 2).lift
        (SSet.simplicialSpaceBoundaryRestrictionCone (diagram C) 2) =
      degreeTwoAbstractMatchingMap C :=
  SSet.simplicialSpaceBoundaryMatchingMap_eq_limitLift (diagram C) 2

/-- Cone from the explicit triangular-boundary nerve to every outer face in
the abstract degree-two matching diagram. -/
def degreeTwoBoundaryComparisonCone :
    Limits.Cone
      (SSet.simplicialSpaceBoundaryMatchingDiagram (diagram C) 2) where
  pt := degreeTwoBoundarySpace C
  π := {
    app j := CategoryTheory.nerveMap
      ((CategoryTheory.TriangleBoundary.restrictAlongFunctor
        (C := C) (SSet.boundaryMatchingSimplex 2 j)
          (SSet.boundaryMatchingSimplex_not_surjective 2 j)).core)
    naturality := by
      intro j k f
      let σ := SSet.boundaryMatchingSimplex 2 j
      let τ := f.unop.unop.val.unop
      have hσ := SSet.boundaryMatchingSimplex_not_surjective 2 j
      have hfun := CategoryTheory.TriangleBoundary.restrictAlongFunctor_comp
        (C := C) σ hσ τ
      have hcore := congrArg CategoryTheory.Functor.core hfun
      have hs := SSet.boundaryMatchingSimplex_naturality 2 f
      change 𝟙 _ ≫ CategoryTheory.nerveMap
          ((CategoryTheory.TriangleBoundary.restrictAlongFunctor
            (C := C) (SSet.boundaryMatchingSimplex 2 k)
              (SSet.boundaryMatchingSimplex_not_surjective 2 k)).core) =
        CategoryTheory.nerveMap
            ((CategoryTheory.TriangleBoundary.restrictAlongFunctor
              (C := C) (SSet.boundaryMatchingSimplex 2 j)
                (SSet.boundaryMatchingSimplex_not_surjective 2 j)).core) ≫
          CategoryTheory.nerveMap
            ((ComposableArrows.whiskerLeftFunctor
              (SimplexCategory.toCat.map τ).toFunctor).core)
      rw [Category.id_comp]
      change CategoryTheory.nerveMap
          ((CategoryTheory.TriangleBoundary.restrictAlongFunctor
            (C := C) (SSet.boundaryMatchingSimplex 2 k)
              (SSet.boundaryMatchingSimplex_not_surjective 2 k)).core) =
        CategoryTheory.nerveMap
          ((CategoryTheory.TriangleBoundary.restrictAlongFunctor
              (C := C) (SSet.boundaryMatchingSimplex 2 j)
                (SSet.boundaryMatchingSimplex_not_surjective 2 j)).core ⋙
            (ComposableArrows.whiskerLeftFunctor
              (SimplexCategory.toCat.map τ).toFunctor).core)
      apply congrArg CategoryTheory.nerveMap
      calc
        _ = (CategoryTheory.TriangleBoundary.restrictAlongFunctor
              (C := C) σ hσ ⋙
            ComposableArrows.whiskerLeftFunctor
              (SimplexCategory.toCat.map τ).toFunctor).core := by
          simpa [σ, τ, hs] using hcore.symm
        _ = (CategoryTheory.TriangleBoundary.restrictAlongFunctor
              (C := C) σ hσ).core ⋙
            (ComposableArrows.whiskerLeftFunctor
              (SimplexCategory.toCat.map τ).toFunctor).core := by
          apply CategoryTheory.Functor.hext
          · intro X
            rfl
          · intro X Y η
            rfl }

/-- Canonical comparison from the explicit triangular-boundary nerve to the
selected abstract degree-two matching limit. -/
noncomputable def degreeTwoBoundaryToAbstractMatching :
    degreeTwoBoundarySpace C ⟶ degreeTwoAbstractMatchingObject C :=
  (SSet.simplicialSpaceBoundaryMatchingConeIsLimit (diagram C) 2).lift
    (degreeTwoBoundaryComparisonCone C)

/-- Every leg of the comparison is the corresponding explicit boundary
restriction. -/
theorem degreeTwoBoundaryToAbstractMatching_fac
    (j : SSet.BoundaryMatchingIndex.{u} 2) :
    degreeTwoBoundaryToAbstractMatching C ≫
        (SSet.simplicialSpaceBoundaryMatchingCone (diagram C) 2).π.app j =
      (degreeTwoBoundaryComparisonCone C).π.app j :=
  (SSet.simplicialSpaceBoundaryMatchingConeIsLimit
    (diagram C) 2).fac (degreeTwoBoundaryComparisonCone C) j

/-- The explicit triangular-boundary matching map factors exactly through the
canonical comparison to the selected abstract Reedy matching limit. -/
theorem degreeTwoMatchingMap_factorization :
    degreeTwoBoundaryMap C ≫ degreeTwoBoundaryToAbstractMatching C =
      degreeTwoAbstractMatchingMap C := by
  apply (SSet.simplicialSpaceBoundaryMatchingConeIsLimit
    (diagram C) 2).hom_ext
  intro j
  erw [Category.assoc]
  erw [degreeTwoBoundaryToAbstractMatching_fac]
  erw [← degreeTwoAbstractMatchingMap_eq_limitLift]
  erw [(SSet.simplicialSpaceBoundaryMatchingConeIsLimit
    (diagram C) 2).fac (SSet.simplicialSpaceBoundaryRestrictionCone
      (diagram C) 2) j]
  let σ := SSet.boundaryMatchingSimplex 2 j
  let hσ := SSet.boundaryMatchingSimplex_not_surjective 2 j
  have hfun :=
    CategoryTheory.TriangleBoundary.restrictionFunctor_comp_restrictAlongFunctor
      (C := C) σ hσ
  have hcore := congrArg CategoryTheory.Functor.core hfun
  change CategoryTheory.nerveMap
      ((CategoryTheory.TriangleBoundary.restrictionFunctor (C := C)).core ⋙
        (CategoryTheory.TriangleBoundary.restrictAlongFunctor
          (C := C) σ hσ).core) =
    CategoryTheory.nerveMap
      ((ComposableArrows.whiskerLeftFunctor
        (SimplexCategory.toCat.map σ).toFunctor).core)
  exact congrArg CategoryTheory.nerveMap hcore

/-- Projection of the abstract degree-two matching object to one of its three
canonical nondegenerate edges. -/
noncomputable def degreeTwoAbstractFaceProjection (i : Fin 3) :
    degreeTwoAbstractMatchingObject C ⟶
      (diagram C).obj (op (SimplexCategory.mk 1)) :=
  (SSet.simplicialSpaceBoundaryMatchingCone (diagram C) 2).π.app
    (SSet.degreeTwoBoundaryFaceElement.{u} i)

/-- The canonical comparison followed by an abstract face projection is the
corresponding explicit restriction of triangular boundaries. -/
theorem degreeTwoBoundaryToAbstractMatching_comp_faceProjection (i : Fin 3) :
    degreeTwoBoundaryToAbstractMatching C ≫
        degreeTwoAbstractFaceProjection C i =
      CategoryTheory.nerveMap
        ((CategoryTheory.TriangleBoundary.restrictAlongFunctor
          (C := C) (SimplexCategory.δ i)
            (SSet.boundaryMatchingSimplex_not_surjective 2
              (SSet.degreeTwoBoundaryFaceElement.{u} i))).core) := by
  exact degreeTwoBoundaryToAbstractMatching_fac C
    (SSet.degreeTwoBoundaryFaceElement.{u} i)

/-- Projection of the abstract degree-two matching object to one of its three
canonical vertices. -/
noncomputable def degreeTwoAbstractVertexProjection (r : Fin 3) :
    degreeTwoAbstractMatchingObject C ⟶
      (diagram C).obj (op (SimplexCategory.mk 0)) :=
  (SSet.simplicialSpaceBoundaryMatchingCone (diagram C) 2).π.app
    (SSet.degreeTwoBoundaryVertexElement.{u} r)

/-- The canonical comparison followed by an abstract vertex projection is
the corresponding pointwise restriction of triangular boundaries. -/
theorem degreeTwoBoundaryToAbstractMatching_comp_vertexProjection (r : Fin 3) :
    degreeTwoBoundaryToAbstractMatching C ≫
        degreeTwoAbstractVertexProjection C r =
      CategoryTheory.nerveMap
        ((CategoryTheory.TriangleBoundary.restrictAlongFunctor
          (C := C)
            (SimplexCategory.const (SimplexCategory.mk 0)
              (SimplexCategory.mk 2) r)
            (SSet.boundaryMatchingSimplex_not_surjective 2
              (SSet.degreeTwoBoundaryVertexElement.{u} r))).core) := by
  exact degreeTwoBoundaryToAbstractMatching_fac C
    (SSet.degreeTwoBoundaryVertexElement.{u} r)

/-- The endpoint of a canonical abstract edge projection is the corresponding
canonical vertex projection.  This is the strict compatibility supplied by
the matching-limit cone. -/
theorem degreeTwoAbstractFaceProjection_comp_incidence
    (i : Fin 3) (t : Fin 2) :
    degreeTwoAbstractFaceProjection C i ≫
        (SSet.simplicialSpaceBoundaryMatchingDiagram (diagram C) 2).map
          (SSet.degreeTwoBoundaryFaceToVertex.{u} i t) =
      degreeTwoAbstractVertexProjection C ((SimplexCategory.δ i) t) := by
  have h := (SSet.simplicialSpaceBoundaryMatchingCone
    (diagram C) 2).π.naturality
      (SSet.degreeTwoBoundaryFaceToVertex.{u} i t)
  change 𝟙 _ ≫ degreeTwoAbstractVertexProjection C
      ((SimplexCategory.δ i) t) =
    degreeTwoAbstractFaceProjection C i ≫
      (SSet.simplicialSpaceBoundaryMatchingDiagram (diagram C) 2).map
        (SSet.degreeTwoBoundaryFaceToVertex.{u} i t) at h
  rw [Category.id_comp] at h
  exact h.symm

/-- Machine-facing degree-two boundary representation and fibration data.
Unlike the degree-one package, the remaining comparison with the abstract
Reedy matching limit is not claimed here. -/
structure DegreeTwoMatchingCore where
  /-- The displayed boundary-restriction map. -/
  matchingMap :
    (diagram C).obj (op (SimplexCategory.mk 2)) ⟶
      degreeTwoBoundarySpace C
  /-- Kan fibration evidence. -/
  matchingFibration : Fibration matchingMap
  /-- The selected abstract Reedy matching map. -/
  abstractMatchingMap :
    (diagram C).obj (op (SimplexCategory.mk 2)) ⟶
      degreeTwoAbstractMatchingObject C
  /-- Its definition as the universal lift of the boundary restriction cone. -/
  abstractMatchingMap_eq_limitLift :
    (SSet.simplicialSpaceBoundaryMatchingConeIsLimit (diagram C) 2).lift
        (SSet.simplicialSpaceBoundaryRestrictionCone (diagram C) 2) =
      abstractMatchingMap
  /-- Canonical comparison from the explicit triangular-boundary nerve to the
  selected abstract matching limit. -/
  boundaryToAbstractMatching :
    degreeTwoBoundarySpace C ⟶ degreeTwoAbstractMatchingObject C
  /-- Exact compatibility of the explicit and abstract matching maps. -/
  matchingMap_factorization :
    matchingMap ≫ boundaryToAbstractMatching = abstractMatchingMap
  /-- Strict image representation: exactly the fillable boundaries extend. -/
  strictImage : ∀ Y : CategoryTheory.TriangleBoundary C,
    CategoryTheory.TriangleBoundary.Fillable Y ↔
      ∃ F : ComposableArrows C 2,
        (CategoryTheory.TriangleBoundary.restrictionFunctor
          (C := C)).obj F = Y
  /-- Hom-wise representability of triangular boundary families. -/
  homWiseUniversal : ∀ (T : Type u) [Category.{u} T],
    (T ⥤ CategoryTheory.TriangleBoundary C) ≃
      CategoryTheory.TriangleBoundary (T ⥤ C)
  /-- Complete simplicial encoding of a triangle boundary in the nerve. -/
  boundaryNerveEncoding :
    CategoryTheory.TriangleBoundary C →
      ((∂Δ[2] : SSet.{u}) ⟶ CategoryTheory.nerve C)
  /-- Decoding of a boundary-to-nerve map into vertices and independent edges. -/
  boundaryNerveDecoding :
    ((∂Δ[2] : SSet.{u}) ⟶ CategoryTheory.nerve C) →
      CategoryTheory.TriangleBoundary C
  /-- Full representation equivalence between explicit boundaries and maps
  out of the standard simplicial boundary. -/
  boundaryNerveUniversal :
    CategoryTheory.TriangleBoundary C ≃
      ((∂Δ[2] : SSet.{u}) ⟶ CategoryTheory.nerve C)

/-- Package the degree-two boundary representation theorem and Kan
fibration. -/
noncomputable def degreeTwoMatchingCore : DegreeTwoMatchingCore C where
  matchingMap := degreeTwoBoundaryMap C
  matchingFibration := degreeTwoBoundaryMap_fibration C
  abstractMatchingMap := degreeTwoAbstractMatchingMap C
  abstractMatchingMap_eq_limitLift :=
    degreeTwoAbstractMatchingMap_eq_limitLift C
  boundaryToAbstractMatching := degreeTwoBoundaryToAbstractMatching C
  matchingMap_factorization := degreeTwoMatchingMap_factorization C
  strictImage := CategoryTheory.TriangleBoundary.fillable_iff_exists_extension
  homWiseUniversal := fun _ _ =>
    CategoryTheory.TriangleBoundary.functorBoundaryEquiv
  boundaryNerveEncoding :=
    CategoryTheory.TriangleBoundary.toBoundaryNerveMap
  boundaryNerveDecoding :=
    CategoryTheory.TriangleBoundary.ofBoundaryNerveMap
  boundaryNerveUniversal :=
    CategoryTheory.TriangleBoundary.boundaryNerveEquiv

private lemma fullObj_ext {A : Type*} [Category* A]
    {P : ObjectProperty A} {X Y : P.FullSubcategory}
    (h : X.obj = Y.obj) : X = Y := by
  cases X
  cases Y
  cases h
  rfl

private noncomputable def functorToCoreOfMapIso
    {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B)
    (hF : ∀ {X Y : A} (f : X ⟶ Y), IsIso (F.map f)) :
    A ⥤ Core B where
  obj X := ⟨F.obj X⟩
  map f := ⟨asIso (F.map f)⟩
  map_id X := by
    apply Core.hom_ext
    simp
  map_comp f g := by
    apply Core.hom_ext
    simp

/-- Forget an internal triangle boundary of equivalence strings to a triangle
boundary of the underlying vertical functors. -/
def forgetEquivalenceStringBoundary (k : ℕ)
    (Y : CategoryTheory.TriangleBoundary (EquivalenceString C k)) :
    CategoryTheory.TriangleBoundary (ComposableArrows C k) where
  vertex0 := Y.vertex0.obj
  vertex1 := Y.vertex1.obj
  vertex2 := Y.vertex2.obj
  edge01 := Y.edge01.hom
  edge12 := Y.edge12.hom
  edge02 := Y.edge02.hom

/-- Evaluate a triangle boundary of vertical equivalence strings pointwise;
all resulting vertical boundary maps remain invertible. -/
def triangleBoundaryToEquivalenceString (k : ℕ)
    (Y : CategoryTheory.TriangleBoundary (EquivalenceString C k)) :
    EquivalenceString (CategoryTheory.TriangleBoundary C) k := by
  let F := CategoryTheory.TriangleBoundary.uncurryFunctor
    (forgetEquivalenceStringBoundary C k Y)
  exact ⟨F, fun {i j} f => by
    have h0 : IsIso (F.map f).app0 := by
      change IsIso (Y.vertex0.obj.map f)
      exact Y.vertex0.property f
    have h1 : IsIso (F.map f).app1 := by
      change IsIso (Y.vertex1.obj.map f)
      exact Y.vertex1.property f
    have h2 : IsIso (F.map f).app2 := by
      change IsIso (Y.vertex2.obj.map f)
      exact Y.vertex2.property f
    exact @CategoryTheory.TriangleBoundary.homIsIso_of_components
      C _ _ _ (F.map f) h0 h1 h2⟩

/-- Curry a vertical equivalence string of triangle boundaries into one
triangle boundary internal to the category of equivalence strings. -/
def equivalenceStringToTriangleBoundary (k : ℕ)
    (F : EquivalenceString (CategoryTheory.TriangleBoundary C) k) :
    CategoryTheory.TriangleBoundary (EquivalenceString C k) := by
  let Y := CategoryTheory.TriangleBoundary.curryFunctor F.obj
  exact {
    vertex0 := ⟨Y.vertex0, fun {i j} f => by
      have hf : IsIso (F.obj.map f) := F.property f
      change IsIso (F.obj.map f).app0
      exact @CategoryTheory.TriangleBoundary.app0IsIso
        C _ _ _ (F.obj.map f) hf⟩
    vertex1 := ⟨Y.vertex1, fun {i j} f => by
      have hf : IsIso (F.obj.map f) := F.property f
      change IsIso (F.obj.map f).app1
      exact @CategoryTheory.TriangleBoundary.app1IsIso
        C _ _ _ (F.obj.map f) hf⟩
    vertex2 := ⟨Y.vertex2, fun {i j} f => by
      have hf : IsIso (F.obj.map f) := F.property f
      change IsIso (F.obj.map f).app2
      exact @CategoryTheory.TriangleBoundary.app2IsIso
        C _ _ _ (F.obj.map f) hf⟩
    edge01 := ObjectProperty.homMk Y.edge01
    edge12 := ObjectProperty.homMk Y.edge12
    edge02 := ObjectProperty.homMk Y.edge02 }

/-- Triangle boundaries commute exactly with passage to vertical equivalence
strings.  This is the pointwise categorical representation needed for the
inverse of the degree-two Reedy comparison. -/
def triangleBoundaryEquivalenceStringEquiv (k : ℕ) :
    CategoryTheory.TriangleBoundary (EquivalenceString C k) ≃
      EquivalenceString (CategoryTheory.TriangleBoundary C) k where
  toFun := triangleBoundaryToEquivalenceString C k
  invFun := equivalenceStringToTriangleBoundary C k
  left_inv Y := by
    apply CategoryTheory.TriangleBoundary.obj_ext
    · apply ObjectProperty.FullSubcategory.ext
      rfl
    · apply ObjectProperty.FullSubcategory.ext
      rfl
    · apply ObjectProperty.FullSubcategory.ext
      rfl
    · apply heq_of_eq
      rfl
    · apply heq_of_eq
      rfl
    · apply heq_of_eq
      rfl
  right_inv F := by
    apply ObjectProperty.FullSubcategory.ext
    exact (CategoryTheory.TriangleBoundary.functorBoundaryEquiv.symm_apply_apply
      F.obj)

/-- Flip a vertical string of invertible transformations between outer
`n`-strings into an outer `n`-string of vertical equivalence strings. -/
def toEquivalenceStringDiagram (k n : ℕ)
    (F : ComposableArrows (Core (ComposableArrows C n)) k) :
    ComposableArrows (EquivalenceString C k) n :=
  (equivalenceStringProperty C k).lift
    ((F ⋙ Core.inclusion (ComposableArrows C n)).flip)
    (fun i ↦ by
      intro a b f
      change IsIso ((F.map f).iso.hom.app i)
      infer_instance)

/-- Reverse the bidegree flip by turning every pointwise-invertible vertical
transformation into a morphism of the maximal core. -/
noncomputable def fromEquivalenceStringDiagram (k n : ℕ)
    (F : ComposableArrows (EquivalenceString C k) n) :
    ComposableArrows (Core (ComposableArrows C n)) k := by
  exact functorToCoreOfMapIso
    (F := ((F ⋙ (equivalenceStringProperty C k).ι).flip))
    (fun {a b} f ↦ by
      refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
      intro i
      change IsIso ((F.obj i).obj.map f)
      exact (F.obj i).property f)

/-- Flipping to equivalence strings and back is the identity. -/
theorem fromEquivalenceStringDiagram_toEquivalenceStringDiagram
    (k n : ℕ)
    (F : ComposableArrows (Core (ComposableArrows C n)) k) :
    fromEquivalenceStringDiagram C k n
      (toEquivalenceStringDiagram C k n F) = F := by
  let L := fromEquivalenceStringDiagram C k n
    (toEquivalenceStringDiagram C k n F)
  have hObj (i : Fin (k + 1)) : L.obj i = F.obj i := by
    apply coreObj_ext
    dsimp [L, fromEquivalenceStringDiagram,
      toEquivalenceStringDiagram, functorToCoreOfMapIso]
    exact CategoryTheory.Functor.hext
      (fun a ↦ rfl) (fun a b f ↦ by rfl)
  exact CategoryTheory.Functor.hext hObj (fun i j f ↦ by
    cases hObj i
    cases hObj j
    dsimp [L, fromEquivalenceStringDiagram,
      toEquivalenceStringDiagram, functorToCoreOfMapIso]
    apply heq_of_eq
    apply Core.hom_ext
    apply NatTrans.ext
    funext a
    rfl)

/-- Flipping from equivalence strings and back is the identity. -/
theorem toEquivalenceStringDiagram_fromEquivalenceStringDiagram
    (k n : ℕ) (F : ComposableArrows (EquivalenceString C k) n) :
    toEquivalenceStringDiagram C k n
      (fromEquivalenceStringDiagram C k n F) = F := by
  let L := toEquivalenceStringDiagram C k n
    (fromEquivalenceStringDiagram C k n F)
  have hObj (i : Fin (n + 1)) : L.obj i = F.obj i := by
    apply fullObj_ext
    dsimp [L, fromEquivalenceStringDiagram,
      toEquivalenceStringDiagram, functorToCoreOfMapIso]
    exact CategoryTheory.Functor.hext
      (fun a ↦ rfl) (fun a b f ↦ by rfl)
  exact CategoryTheory.Functor.hext hObj (fun i j f ↦ by
    dsimp [L, fromEquivalenceStringDiagram,
      toEquivalenceStringDiagram, functorToCoreOfMapIso]
    rfl)

/-- Bidegree flipping identifies vertical `k`-simplices in outer degree `n`
with `n`-simplices in the nerve of the equivalence-string category. -/
noncomputable def horizontalSimplexEquiv (k n : ℕ) :
    ComposableArrows (Core (ComposableArrows C n)) k ≃
      ComposableArrows (EquivalenceString C k) n where
  toFun := toEquivalenceStringDiagram C k n
  invFun := fromEquivalenceStringDiagram C k n
  left_inv := fromEquivalenceStringDiagram_toEquivalenceStringDiagram C k n
  right_inv := toEquivalenceStringDiagram_fromEquivalenceStringDiagram C k n

/-- Horizontal row obtained by fixing vertical simplicial degree `k`. -/
abbrev horizontalRow (k : ℕ) : SSet.{u} :=
  SSet.horizontalRow (diagram C) k

/-- Every horizontal row of the Rezk core diagram is naturally the ordinary
nerve of the category of vertical equivalence strings. -/
noncomputable def horizontalRowIso (k : ℕ) :
    horizontalRow C k ≅
      CategoryTheory.nerve (EquivalenceString C k) :=
  NatIso.ofComponents
    (fun Δ ↦ Equiv.toIso (horizontalSimplexEquiv C k Δ.unop.len))
    (fun {n m} f ↦ by
      ext F
      rfl)

/-- A simplex of an arbitrary selected abstract matching limit determines a
complete boundary map in the nerve of the corresponding category of vertical
equivalence strings. -/
noncomputable def abstractMatchingBoundaryMap (n k : ℕ)
    (x : (abstractMatchingObject C n).obj
      (op (SimplexCategory.mk k))) :
    (∂Δ[n] : SSet.{u}) ⟶ CategoryTheory.nerve (EquivalenceString C k) where
  app Δ := ↾fun s =>
    let j : SSet.BoundaryMatchingIndex.{u} n :=
      (Opposite.op (Opposite.op
        (⟨Δ, s⟩ : (SSet.boundary.{u} n : SSet.{u}).Elements)) :
          SSet.BoundaryMatchingIndex.{u} n)
    (horizontalRowIso C k).hom.app Δ
      ((SSet.simplicialSpaceBoundaryMatchingCone (diagram C) n).π.app j
        |>.app (op (SimplexCategory.mk k)) x)
  naturality := by
    intro Δ Γ f
    ext s
    let j : SSet.BoundaryMatchingIndex.{u} n :=
      (Opposite.op (Opposite.op
        (⟨Δ, s⟩ : (SSet.boundary.{u} n : SSet.{u}).Elements)) :
          SSet.BoundaryMatchingIndex.{u} n)
    let j' : SSet.BoundaryMatchingIndex.{u} n :=
      (Opposite.op (Opposite.op
        (⟨Γ, (SSet.boundary.{u} n : SSet.{u}).map f s⟩ :
          (SSet.boundary.{u} n : SSet.{u}).Elements)) :
            SSet.BoundaryMatchingIndex.{u} n)
    let q : j ⟶ j' := SSet.boundaryMatchingIndexMap n f s
    have hc := (SSet.simplicialSpaceBoundaryMatchingCone
      (diagram C) n).π.naturality q
    have hc' := ConcreteCategory.congr_hom
      (NatTrans.congr_app hc (op (SimplexCategory.mk k))) x
    have hn := (horizontalRowIso C k).hom.naturality f
    let y := (SSet.simplicialSpaceBoundaryMatchingCone
      (diagram C) n).π.app j |>.app (op (SimplexCategory.mk k)) x
    have hn' := ConcreteCategory.congr_hom hn y
    change ((SSet.simplicialSpaceBoundaryMatchingCone
        (diagram C) n).π.app j' |>.app
          (op (SimplexCategory.mk k)) x) =
      (horizontalRow C k).map f y at hc'
    change (horizontalRowIso C k).hom.app Γ
        ((horizontalRow C k).map f y) =
      (CategoryTheory.nerve (EquivalenceString C k)).map f
        ((horizontalRowIso C k).hom.app Δ y) at hn'
    change (horizontalRowIso C k).hom.app Γ
        ((SSet.simplicialSpaceBoundaryMatchingCone
          (diagram C) n).π.app j' |>.app
            (op (SimplexCategory.mk k)) x) =
      (CategoryTheory.nerve (EquivalenceString C k)).map f
        ((horizontalRowIso C k).hom.app Δ
          ((SSet.simplicialSpaceBoundaryMatchingCone
            (diagram C) n).π.app j |>.app
              (op (SimplexCategory.mk k)) x))
    rw [hc']
    exact hn'

/-- Elements of an arbitrary selected matching limit are equal when every
boundary-index projection agrees in the same vertical degree. -/
theorem abstractMatchingElement_ext (n k : ℕ)
    {x y : (abstractMatchingObject C n).obj
      (op (SimplexCategory.mk k))}
    (h : ∀ j : SSet.BoundaryMatchingIndex.{u} n,
      ((SSet.simplicialSpaceBoundaryMatchingCone (diagram C) n).π.app j).app
          (op (SimplexCategory.mk k)) x =
        ((SSet.simplicialSpaceBoundaryMatchingCone (diagram C) n).π.app j).app
          (op (SimplexCategory.mk k)) y) : x = y := by
  apply SSet.yonedaEquiv.symm.injective
  apply (SSet.simplicialSpaceBoundaryMatchingConeIsLimit
    (diagram C) n).hom_ext
  intro j
  apply SSet.yonedaEquiv.injective
  erw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp]
  calc
    _ = ((SSet.simplicialSpaceBoundaryMatchingCone
          (diagram C) n).π.app j).app (op (SimplexCategory.mk k)) x :=
      congrArg _ (SSet.yonedaEquiv.apply_symm_apply x)
    _ = ((SSet.simplicialSpaceBoundaryMatchingCone
          (diagram C) n).π.app j).app (op (SimplexCategory.mk k)) y := h j
    _ = _ := congrArg _ (SSet.yonedaEquiv.apply_symm_apply y).symm

/-- The arbitrary-degree boundary assembly retains every matching projection
and is injective. -/
theorem abstractMatchingBoundaryMap_injective (n k : ℕ) :
    Function.Injective (abstractMatchingBoundaryMap C n k) := by
  intro x y hxy
  apply abstractMatchingElement_ext C n k
  intro j
  let Δ := j.unop.unop.fst
  let s := j.unop.unop.snd
  have h := congrArg (fun φ => φ.app Δ s) hxy
  change (horizontalRowIso C k).hom.app Δ
      (((SSet.simplicialSpaceBoundaryMatchingCone
        (diagram C) n).π.app j).app (op (SimplexCategory.mk k)) x) =
    (horizontalRowIso C k).hom.app Δ
      (((SSet.simplicialSpaceBoundaryMatchingCone
        (diagram C) n).π.app j).app (op (SimplexCategory.mk k)) y) at h
  exact (horizontalSimplexEquiv C k Δ.unop.len).injective h

/-- Assembling the boundary of a simplex after applying the arbitrary-degree
matching map is exactly restriction of its horizontal categorical-nerve
simplex to the standard boundary. -/
theorem abstractMatchingBoundaryMap_matchingMap (n k : ℕ)
    (F : ((diagram C).obj (op (SimplexCategory.mk n))).obj
      (op (SimplexCategory.mk k))) :
    abstractMatchingBoundaryMap C n k
        ((abstractMatchingMap C n).app (op (SimplexCategory.mk k)) F) =
      (SSet.boundary n).ι ≫
        SSet.yonedaEquiv.symm
          ((horizontalRowIso C k).hom.app
            (op (SimplexCategory.mk n)) F) := by
  ext Δ s
  let j : SSet.BoundaryMatchingIndex.{u} n :=
    (Opposite.op (Opposite.op
      (⟨Δ, s⟩ : (SSet.boundary.{u} n : SSet.{u}).Elements)) :
        SSet.BoundaryMatchingIndex.{u} n)
  have hf := abstractMatchingMap_fac C n j
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app hf (op (SimplexCategory.mk k))) F
  change ((SSet.simplicialSpaceBoundaryMatchingCone
      (diagram C) n).π.app j |>.app (op (SimplexCategory.mk k))
        ((abstractMatchingMap C n).app
          (op (SimplexCategory.mk k)) F)) =
    ((SSet.simplicialSpaceBoundaryRestrictionCone
      (diagram C) n).π.app j).app (op (SimplexCategory.mk k)) F at h
  let σ := SSet.stdSimplex.objEquiv ((SSet.boundary n).ι.app Δ s)
  let y := ((diagram C).map σ.op).app
    (op (SimplexCategory.mk k)) F
  have hn := (horizontalRowIso C k).hom.naturality σ.op
  have hn' := ConcreteCategory.congr_hom hn F
  change (horizontalRowIso C k).hom.app Δ
      ((SSet.simplicialSpaceBoundaryMatchingCone
        (diagram C) n).π.app j |>.app (op (SimplexCategory.mk k))
          ((abstractMatchingMap C n).app
            (op (SimplexCategory.mk k)) F)) =
    ((SSet.boundary n).ι ≫
      SSet.yonedaEquiv.symm
        ((horizontalRowIso C k).hom.app
          (op (SimplexCategory.mk n)) F)).app Δ s
  rw [h]
  change (horizontalRowIso C k).hom.app Δ y = _
  change (horizontalRowIso C k).hom.app Δ y =
    (CategoryTheory.nerve (EquivalenceString C k)).map σ.op
      ((horizontalRowIso C k).hom.app
        (op (SimplexCategory.mk n)) F)
  exact hn'

/-- In every outer degree at least two, the abstract Reedy matching map is
degreewise injective.  This is the uniqueness half of categorical-nerve
boundary filling, transported through the horizontal-row isomorphism. -/
theorem abstractMatchingMap_app_injective (m k : ℕ) :
    Function.Injective
      ((abstractMatchingMap C (m + 2)).app
        (op (SimplexCategory.mk k))) := by
  intro F G h
  apply (horizontalSimplexEquiv C k (m + 2)).injective
  apply CategoryTheory.Nerve.boundaryRestriction_injective
    (C := EquivalenceString C k) m
  dsimp [CategoryTheory.Nerve.boundaryRestriction]
  erw [← abstractMatchingBoundaryMap_matchingMap C (m + 2) k F]
  erw [← abstractMatchingBoundaryMap_matchingMap C (m + 2) k G]
  exact congrArg (abstractMatchingBoundaryMap C (m + 2) k) h

/-- In every outer degree at least three, the abstract matching map is
degreewise surjective.  Fill the assembled categorical-nerve boundary and
transport the filler back through the horizontal simplex equivalence. -/
theorem abstractMatchingMap_app_surjective_high (m k : ℕ) :
    Function.Surjective
      ((abstractMatchingMap C (m + 3)).app
        (op (SimplexCategory.mk k))) := by
  intro x
  obtain ⟨y, hy⟩ := CategoryTheory.Nerve.boundaryRestriction_surjective
    (C := EquivalenceString C k) m
      (abstractMatchingBoundaryMap C (m + 3) k x)
  let F := (horizontalSimplexEquiv C k (m + 3)).symm y
  refine ⟨F, ?_⟩
  apply abstractMatchingBoundaryMap_injective C (m + 3) k
  erw [abstractMatchingBoundaryMap_matchingMap]
  change CategoryTheory.Nerve.boundaryRestriction (m + 3)
      ((horizontalSimplexEquiv C k (m + 3)) F) =
    abstractMatchingBoundaryMap C (m + 3) k x
  rw [(horizontalSimplexEquiv C k (m + 3)).apply_symm_apply]
  exact hy

/-- Every component of every matching map in outer degree at least three is
bijective. -/
theorem abstractMatchingMap_app_bijective_high (m k : ℕ) :
    Function.Bijective
      ((abstractMatchingMap C (m + 3)).app
        (op (SimplexCategory.mk k))) :=
  ⟨abstractMatchingMap_app_injective C (m + 1) k,
    abstractMatchingMap_app_surjective_high C m k⟩

/-- Every abstract matching map in outer degree at least three is an
isomorphism of simplicial sets. -/
instance abstractMatchingMapHighIsIso (m : ℕ) :
    IsIso (abstractMatchingMap C (m + 3)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  rintro ⟨⟨k⟩⟩
  rw [CategoryTheory.isIso_iff_bijective]
  exact abstractMatchingMap_app_bijective_high C m k

/-- Explicit high-dimensional Reedy matching isomorphism. -/
noncomputable def abstractMatchingMapHighIso (m : ℕ) :
    (diagram C).obj (op (SimplexCategory.mk (m + 3))) ≅
      abstractMatchingObject C (m + 3) :=
  asIso (abstractMatchingMap C (m + 3))

/-- Package every Reedy matching dimension at least three. -/
structure HigherMatchingCore where
  /-- The matching map is an isomorphism in each high degree. -/
  matchingIso : ∀ m : ℕ,
    (diagram C).obj (op (SimplexCategory.mk (m + 3))) ≅
      abstractMatchingObject C (m + 3)
  /-- Its forward map is the universal abstract matching map. -/
  matchingIso_hom : ∀ m : ℕ,
    (matchingIso m).hom = abstractMatchingMap C (m + 3)
  /-- Consequently every high matching map is a Kan fibration. -/
  matchingFibration : ∀ m : ℕ,
    Fibration (abstractMatchingMap C (m + 3))

/-- Full package of all matching dimensions at least three. -/
noncomputable def higherMatchingCore : HigherMatchingCore C where
  matchingIso := abstractMatchingMapHighIso C
  matchingIso_hom := fun _ => rfl
  matchingFibration := fun _ => by infer_instance

/-- A simplex of the selected abstract degree-two matching limit determines
a complete boundary map into the nerve of the corresponding category of
vertical equivalence strings. -/
noncomputable def degreeTwoAbstractMatchingBoundaryMap (k : ℕ)
    (x : (degreeTwoAbstractMatchingObject C).obj
      (op (SimplexCategory.mk k))) :
    (∂Δ[2] : SSet.{u}) ⟶ CategoryTheory.nerve (EquivalenceString C k) where
  app Δ := ↾fun s =>
    let j : SSet.BoundaryMatchingIndex.{u} 2 :=
      (Opposite.op (Opposite.op
        (⟨Δ, s⟩ : (SSet.boundary.{u} 2 : SSet.{u}).Elements)) :
          SSet.BoundaryMatchingIndex.{u} 2)
    (horizontalRowIso C k).hom.app Δ
      ((SSet.simplicialSpaceBoundaryMatchingCone (diagram C) 2).π.app j
        |>.app (op (SimplexCategory.mk k)) x)
  naturality := by
    intro Δ Γ f
    ext s
    let j : SSet.BoundaryMatchingIndex.{u} 2 :=
      (Opposite.op (Opposite.op
        (⟨Δ, s⟩ : (SSet.boundary.{u} 2 : SSet.{u}).Elements)) :
          SSet.BoundaryMatchingIndex.{u} 2)
    let j' : SSet.BoundaryMatchingIndex.{u} 2 :=
      (Opposite.op (Opposite.op
        (⟨Γ, (SSet.boundary.{u} 2 : SSet.{u}).map f s⟩ :
          (SSet.boundary.{u} 2 : SSet.{u}).Elements)) :
            SSet.BoundaryMatchingIndex.{u} 2)
    let q : j ⟶ j' := SSet.boundaryMatchingIndexMap 2 f s
    have hc := (SSet.simplicialSpaceBoundaryMatchingCone
      (diagram C) 2).π.naturality q
    have hc' := ConcreteCategory.congr_hom
      (NatTrans.congr_app hc (op (SimplexCategory.mk k))) x
    have hn := (horizontalRowIso C k).hom.naturality f
    let y := (SSet.simplicialSpaceBoundaryMatchingCone
      (diagram C) 2).π.app j |>.app (op (SimplexCategory.mk k)) x
    have hn' := ConcreteCategory.congr_hom hn y
    change ((SSet.simplicialSpaceBoundaryMatchingCone
        (diagram C) 2).π.app j' |>.app
          (op (SimplexCategory.mk k)) x) =
      (horizontalRow C k).map f y at hc'
    change (horizontalRowIso C k).hom.app Γ
        ((horizontalRow C k).map f y) =
      (CategoryTheory.nerve (EquivalenceString C k)).map f
        ((horizontalRowIso C k).hom.app Δ y) at hn'
    change (horizontalRowIso C k).hom.app Γ
        ((SSet.simplicialSpaceBoundaryMatchingCone
          (diagram C) 2).π.app j' |>.app
            (op (SimplexCategory.mk k)) x) =
      (CategoryTheory.nerve (EquivalenceString C k)).map f
        ((horizontalRowIso C k).hom.app Δ
          ((SSet.simplicialSpaceBoundaryMatchingCone
            (diagram C) 2).π.app j |>.app
              (op (SimplexCategory.mk k)) x))
    rw [hc']
    exact hn'

/-- Elements of the selected abstract matching limit are equal when all
boundary-index projections agree in the same vertical degree. -/
theorem degreeTwoMatchingElement_ext (k : ℕ)
    {x y : (degreeTwoAbstractMatchingObject C).obj
      (op (SimplexCategory.mk k))}
    (h : ∀ j : SSet.BoundaryMatchingIndex.{u} 2,
      ((SSet.simplicialSpaceBoundaryMatchingCone (diagram C) 2).π.app j).app
          (op (SimplexCategory.mk k)) x =
        ((SSet.simplicialSpaceBoundaryMatchingCone (diagram C) 2).π.app j).app
          (op (SimplexCategory.mk k)) y) : x = y := by
  apply SSet.yonedaEquiv.symm.injective
  apply (SSet.simplicialSpaceBoundaryMatchingConeIsLimit
    (diagram C) 2).hom_ext
  intro j
  apply SSet.yonedaEquiv.injective
  erw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp]
  calc
    _ = ((SSet.simplicialSpaceBoundaryMatchingCone
          (diagram C) 2).π.app j).app (op (SimplexCategory.mk k)) x :=
      congrArg _ (SSet.yonedaEquiv.apply_symm_apply x)
    _ = ((SSet.simplicialSpaceBoundaryMatchingCone
          (diagram C) 2).π.app j).app (op (SimplexCategory.mk k)) y := h j
    _ = _ := congrArg _ (SSet.yonedaEquiv.apply_symm_apply y).symm

/-- The assembled equivalence-string boundary map retains every projection of
the selected abstract matching element and is therefore injective. -/
theorem degreeTwoAbstractMatchingBoundaryMap_injective (k : ℕ) :
    Function.Injective (degreeTwoAbstractMatchingBoundaryMap C k) := by
  intro x y hxy
  apply degreeTwoMatchingElement_ext C k
  intro j
  let Δ := j.unop.unop.fst
  let s := j.unop.unop.snd
  have h := congrArg (fun φ => φ.app Δ s) hxy
  change (horizontalRowIso C k).hom.app Δ
      (((SSet.simplicialSpaceBoundaryMatchingCone
        (diagram C) 2).π.app j).app (op (SimplexCategory.mk k)) x) =
    (horizontalRowIso C k).hom.app Δ
      (((SSet.simplicialSpaceBoundaryMatchingCone
        (diagram C) 2).π.app j).app (op (SimplexCategory.mk k)) y) at h
  exact (horizontalSimplexEquiv C k Δ.unop.len).injective h

/-- Every horizontal row has a canonical strict Segal structure. -/
noncomputable def horizontalStrictSegal (k : ℕ) :
    SSet.StrictSegal (horizontalRow C k) :=
  SSet.StrictSegal.ofIso
    (horizontalRowIso C k)
    (CategoryTheory.Nerve.strictSegal (EquivalenceString C k))

/-- Proposition-level strict-Segal instance for every horizontal row. -/
instance horizontalRowIsStrictSegal (k : ℕ) :
    (horizontalRow C k).IsStrictSegal :=
  (horizontalStrictSegal C k).isStrictSegal

/-- The actual outer spine comparison is an equivalence in every bidegree. -/
noncomputable def outerSegalEquiv (k n : ℕ) :
    (horizontalRow C k).obj (op (SimplexCategory.mk n)) ≃
      (horizontalRow C k).Path n :=
  (horizontalStrictSegal C k).spineEquiv n

/-- The forward map of the outer Segal equivalence is the actual spine map. -/
theorem outerSegalEquiv_apply (k n : ℕ)
    (x : ((diagram C).obj (op (SimplexCategory.mk n))).obj
      (op (SimplexCategory.mk k))) :
    (outerSegalEquiv C k n :
      ((diagram C).obj (op (SimplexCategory.mk n))).obj
          (op (SimplexCategory.mk k)) ≃
        (horizontalRow C k).Path n) x =
      (horizontalRow C k).spine n x :=
  rfl

/-- Lift a string whose structure maps are invertible to a string valued in
the maximal core. -/
noncomputable def equivalenceStringToCoreString {k : ℕ}
    (F : EquivalenceString C k) : ComposableArrows (Core C) k :=
  functorToCoreOfMapIso F.obj (fun f ↦ F.property f)

/-- Forget a core-valued string to an equivalence string in the underlying
category. -/
def coreStringToEquivalenceString (k : ℕ)
    (F : ComposableArrows (Core C) k) : EquivalenceString C k :=
  ⟨F ⋙ Core.inclusion C, fun {i j} f => by
    change IsIso ((F.map f).iso.hom)
    infer_instance⟩

/-- Lifting a forgotten core string recovers the original core-valued
string. -/
theorem equivalenceStringToCoreString_coreStringToEquivalenceString
    (k : ℕ) (F : ComposableArrows (Core C) k) :
    equivalenceStringToCoreString C (coreStringToEquivalenceString C k F) =
      F := by
  let L := equivalenceStringToCoreString C
    (coreStringToEquivalenceString C k F)
  have hObj (i : Fin (k + 1)) : L.obj i = F.obj i := by
    apply coreObj_ext
    rfl
  exact CategoryTheory.Functor.hext hObj (fun i j f => by
    cases hObj i
    cases hObj j
    dsimp [L, equivalenceStringToCoreString,
      coreStringToEquivalenceString, functorToCoreOfMapIso]
    apply heq_of_eq
    apply Core.hom_ext
    rfl)

/-- Forgetting a lifted equivalence string recovers the original
equivalence string. -/
theorem coreStringToEquivalenceString_equivalenceStringToCoreString
    (k : ℕ) (F : EquivalenceString C k) :
    coreStringToEquivalenceString C k (equivalenceStringToCoreString C F) =
      F := by
  apply ObjectProperty.FullSubcategory.ext
  exact CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => by
    dsimp [equivalenceStringToCoreString,
      coreStringToEquivalenceString, functorToCoreOfMapIso]
    rfl)

/-- The vertical equivalence string obtained by reading one vertex from every
boundary in a core-valued boundary string. -/
noncomputable def coreBoundaryStringVertex (k : ℕ)
    (F : ComposableArrows
      (Core (CategoryTheory.TriangleBoundary C)) k)
    (r : Fin 3) : EquivalenceString C k := by
  let V : ComposableArrows C k := {
    obj := fun a => CategoryTheory.TriangleBoundary.vertexAt (F.obj a).of r
    map := fun {a b} f => CategoryTheory.TriangleBoundary.appAt
      (F.map f).iso.hom r
    map_id := fun a => by
      rw [F.map_id]
      exact CategoryTheory.TriangleBoundary.appAt_id (F.obj a).of r
    map_comp := fun f g => by
      rw [F.map_comp]
      exact CategoryTheory.TriangleBoundary.appAt_comp
        (F.map f).iso.hom (F.map g).iso.hom r }
  exact ⟨V, fun {_ _} f => by
    dsimp [V]
    infer_instance⟩

/-- Reading a vertex from a core boundary string agrees with first forgetting
to an equivalence string of boundaries and then currying the boundary. -/
theorem coreBoundaryStringVertex_eq (k : ℕ)
    (F : ComposableArrows
      (Core (CategoryTheory.TriangleBoundary C)) k)
    (r : Fin 3) :
    coreBoundaryStringVertex C k F r =
      CategoryTheory.TriangleBoundary.vertexAt
        (equivalenceStringToTriangleBoundary C k
          (coreStringToEquivalenceString
            (CategoryTheory.TriangleBoundary C) k F)) r := by
  fin_cases r <;> apply ObjectProperty.FullSubcategory.ext <;> rfl

/-- The vertical natural transformation obtained by reading one boundary edge
from every object in a core-valued boundary string. -/
noncomputable def coreBoundaryStringEdge (k : ℕ)
    (F : ComposableArrows
      (Core (CategoryTheory.TriangleBoundary C)) k)
    (r s : Fin 3) (h : r ≤ s) :
    coreBoundaryStringVertex C k F r ⟶
      coreBoundaryStringVertex C k F s :=
  ObjectProperty.homMk {
    app := fun a => CategoryTheory.TriangleBoundary.edgeAt (F.obj a).of r s h
    naturality := fun _ _ f =>
      (CategoryTheory.TriangleBoundary.edgeAt_naturality
        (F.map f).iso.hom r s h).symm }

/-- Reading an edge from a core boundary string agrees, up to the endpoint
equalities above, with reading the corresponding edge after currying. -/
theorem coreBoundaryStringEdge_heq (k : ℕ)
    (F : ComposableArrows
      (Core (CategoryTheory.TriangleBoundary C)) k)
    (r s : Fin 3) (h : r ≤ s) :
    HEq (coreBoundaryStringEdge C k F r s h)
      (CategoryTheory.TriangleBoundary.edgeAt
        (equivalenceStringToTriangleBoundary C k
          (coreStringToEquivalenceString
            (CategoryTheory.TriangleBoundary C) k F)) r s h) := by
  have hr := coreBoundaryStringVertex_eq C k F r
  have hs := coreBoundaryStringVertex_eq C k F s
  apply (conj_eqToHom_iff_heq
    (coreBoundaryStringEdge C k F r s h)
    (CategoryTheory.TriangleBoundary.edgeAt
      (equivalenceStringToTriangleBoundary C k
        (coreStringToEquivalenceString
          (CategoryTheory.TriangleBoundary C) k F)) r s h)
    hr hs).1
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext a
  simp only [ObjectProperty.FullSubcategory.comp_hom,
    CategoryTheory.NatTrans.comp_app]
  rw [ObjectProperty.eqToHom_hom, ObjectProperty.eqToHom_hom]
  rw [CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_app]
  apply (conj_eqToHom_iff_heq _ _ _ _).2
  rcases r with ⟨r, hr'⟩
  rcases s with ⟨s, hs'⟩
  simp only [Fin.mk_le_mk] at h
  have hrCases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  have hsCases : s = 0 ∨ s = 1 ∨ s = 2 := by omega
  rcases hrCases with rfl | rfl | rfl <;>
    rcases hsCases with rfl | rfl | rfl
  all_goals simp_all [coreBoundaryStringEdge,
    CategoryTheory.TriangleBoundary.edgeAt,
    CategoryTheory.TriangleBoundary.curryFunctor,
    equivalenceStringToTriangleBoundary,
    coreStringToEquivalenceString,
    coreBoundaryStringVertex, Core.inclusion]

/-- Degreewise candidate inverse to the canonical comparison: decode the
abstract matching family as a boundary of equivalence strings, commute
triangle boundaries with equivalence strings, then lift back to the maximal
core. -/
noncomputable def degreeTwoBoundaryComparisonInverseApp (k : ℕ) :
    (degreeTwoAbstractMatchingObject C).obj
        (op (SimplexCategory.mk k)) →
      (degreeTwoBoundarySpace C).obj (op (SimplexCategory.mk k)) :=
  fun x =>
    equivalenceStringToCoreString (CategoryTheory.TriangleBoundary C)
      ((triangleBoundaryEquivalenceStringEquiv C k)
        (CategoryTheory.TriangleBoundary.ofBoundaryNerveMap
          (degreeTwoAbstractMatchingBoundaryMap C k x)))

/-- Assembling the abstract boundary of a simplex already coming from the
explicit triangular-boundary nerve recovers the canonical encoded boundary of
the associated equivalence string. -/
theorem degreeTwoAbstractMatchingBoundaryMap_comparison (k : ℕ)
    (F : ComposableArrows
      (Core (CategoryTheory.TriangleBoundary C)) k) :
    degreeTwoAbstractMatchingBoundaryMap C k
        ((degreeTwoBoundaryToAbstractMatching C).app
          (op (SimplexCategory.mk k)) F) =
      CategoryTheory.TriangleBoundary.toBoundaryNerveMap
        (equivalenceStringToTriangleBoundary C k
          (coreStringToEquivalenceString
            (CategoryTheory.TriangleBoundary C) k F)) := by
  ext Δ x
  let j : SSet.BoundaryMatchingIndex.{u} 2 :=
    (Opposite.op (Opposite.op
      (⟨Δ, x⟩ : (SSet.boundary.{u} 2 : SSet.{u}).Elements)) :
        SSet.BoundaryMatchingIndex.{u} 2)
  have hf := degreeTwoBoundaryToAbstractMatching_fac C j
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app hf (op (SimplexCategory.mk k))) F
  change ((SSet.simplicialSpaceBoundaryMatchingCone
      (diagram C) 2).π.app j |>.app (op (SimplexCategory.mk k))
        ((degreeTwoBoundaryToAbstractMatching C).app
          (op (SimplexCategory.mk k)) F)) =
    ((degreeTwoBoundaryComparisonCone C).π.app j).app
      (op (SimplexCategory.mk k)) F at h
  change (horizontalRowIso C k).hom.app Δ
      ((SSet.simplicialSpaceBoundaryMatchingCone
        (diagram C) 2).π.app j |>.app (op (SimplexCategory.mk k))
          ((degreeTwoBoundaryToAbstractMatching C).app
            (op (SimplexCategory.mk k)) F)) =
    CategoryTheory.TriangleBoundary.restrictAlong
      (equivalenceStringToTriangleBoundary C k
        (coreStringToEquivalenceString
          (CategoryTheory.TriangleBoundary C) k F))
      (SSet.stdSimplex.objEquiv ((SSet.boundary 2).ι.app Δ x)) x.property
  rw [h]
  have hσ : SSet.boundaryMatchingSimplex 2 j =
      SSet.stdSimplex.objEquiv ((SSet.boundary 2).ι.app Δ x) := by
    rfl
  change toEquivalenceStringDiagram C k Δ.unop.len
      (((CategoryTheory.TriangleBoundary.restrictAlongFunctor
        (C := C) (SSet.boundaryMatchingSimplex 2 j)
          (SSet.boundaryMatchingSimplex_not_surjective 2 j)).core
            |>.mapComposableArrows k).obj F) =
    CategoryTheory.TriangleBoundary.restrictAlong
      (equivalenceStringToTriangleBoundary C k
        (coreStringToEquivalenceString
          (CategoryTheory.TriangleBoundary C) k F))
      (SSet.stdSimplex.objEquiv ((SSet.boundary 2).ι.app Δ x)) x.property
  cases hσ
  change toEquivalenceStringDiagram C k Δ.unop.len
      (((CategoryTheory.TriangleBoundary.restrictAlongFunctor
        (C := C)
          (SSet.stdSimplex.objEquiv ((SSet.boundary 2).ι.app Δ x))
          x.property).core |>.mapComposableArrows k).obj F) =
    CategoryTheory.TriangleBoundary.restrictAlong
      (equivalenceStringToTriangleBoundary C k
        (coreStringToEquivalenceString
          (CategoryTheory.TriangleBoundary C) k F))
      (SSet.stdSimplex.objEquiv ((SSet.boundary 2).ι.app Δ x)) x.property
  let σ := SSet.stdSimplex.objEquiv ((SSet.boundary 2).ι.app Δ x)
  let L := toEquivalenceStringDiagram C k Δ.unop.len
      (((CategoryTheory.TriangleBoundary.restrictAlongFunctor
        (C := C) σ x.property).core |>.mapComposableArrows k).obj F)
  let R := CategoryTheory.TriangleBoundary.restrictAlong
      (equivalenceStringToTriangleBoundary C k
        (coreStringToEquivalenceString
          (CategoryTheory.TriangleBoundary C) k F)) σ x.property
  have hObj (i : Fin (Δ.unop.len + 1)) : L.obj i = R.obj i := by
    change coreBoundaryStringVertex C k F (σ i) =
      CategoryTheory.TriangleBoundary.vertexAt
        (equivalenceStringToTriangleBoundary C k
          (coreStringToEquivalenceString
            (CategoryTheory.TriangleBoundary C) k F)) (σ i)
    exact coreBoundaryStringVertex_eq C k F (σ i)
  exact CategoryTheory.Functor.hext hObj (fun i i' g => by
    change HEq (coreBoundaryStringEdge C k F (σ i) (σ i') _)
      (CategoryTheory.TriangleBoundary.edgeAt
        (equivalenceStringToTriangleBoundary C k
          (coreStringToEquivalenceString
            (CategoryTheory.TriangleBoundary C) k F)) (σ i) (σ i') _)
    exact coreBoundaryStringEdge_heq C k F _ _ _)

/-- The degreewise inverse candidate is a left inverse of the canonical
comparison on every simplex of the explicit triangular-boundary nerve. -/
theorem degreeTwoBoundaryComparisonInverseApp_comparison (k : ℕ)
    (F : ComposableArrows
      (Core (CategoryTheory.TriangleBoundary C)) k) :
    degreeTwoBoundaryComparisonInverseApp C k
        ((degreeTwoBoundaryToAbstractMatching C).app
          (op (SimplexCategory.mk k)) F) = F := by
  change equivalenceStringToCoreString
      (CategoryTheory.TriangleBoundary C)
      ((triangleBoundaryEquivalenceStringEquiv C k)
        (CategoryTheory.TriangleBoundary.ofBoundaryNerveMap
          (degreeTwoAbstractMatchingBoundaryMap C k
            ((degreeTwoBoundaryToAbstractMatching C).app
              (op (SimplexCategory.mk k)) F)))) = F
  rw [degreeTwoAbstractMatchingBoundaryMap_comparison]
  rw [CategoryTheory.TriangleBoundary.ofBoundaryNerveMap_toBoundaryNerveMap]
  let E := coreStringToEquivalenceString
    (CategoryTheory.TriangleBoundary C) k F
  have ht : (triangleBoundaryEquivalenceStringEquiv C k)
      (equivalenceStringToTriangleBoundary C k E) = E := by
    exact (triangleBoundaryEquivalenceStringEquiv C k).apply_symm_apply E
  rw [ht]
  exact equivalenceStringToCoreString_coreStringToEquivalenceString
    (CategoryTheory.TriangleBoundary C) k F

/-- The canonical comparison is also a left inverse of the degreewise inverse
candidate on every simplex of the selected abstract matching limit. -/
theorem degreeTwoBoundaryToAbstractMatching_inverseApp (k : ℕ)
    (x : (degreeTwoAbstractMatchingObject C).obj
      (op (SimplexCategory.mk k))) :
    (degreeTwoBoundaryToAbstractMatching C).app
        (op (SimplexCategory.mk k))
        (degreeTwoBoundaryComparisonInverseApp C k x) = x := by
  apply degreeTwoAbstractMatchingBoundaryMap_injective C k
  erw [degreeTwoAbstractMatchingBoundaryMap_comparison]
  let φ := degreeTwoAbstractMatchingBoundaryMap C k x
  let B := CategoryTheory.TriangleBoundary.ofBoundaryNerveMap φ
  let E := (triangleBoundaryEquivalenceStringEquiv C k) B
  change CategoryTheory.TriangleBoundary.toBoundaryNerveMap
      (equivalenceStringToTriangleBoundary C k
        (coreStringToEquivalenceString
          (CategoryTheory.TriangleBoundary C) k
          (equivalenceStringToCoreString
            (CategoryTheory.TriangleBoundary C) E))) = φ
  rw [coreStringToEquivalenceString_equivalenceStringToCoreString]
  have ht : equivalenceStringToTriangleBoundary C k E = B := by
    exact (triangleBoundaryEquivalenceStringEquiv C k).symm_apply_apply B
  rw [ht]
  exact CategoryTheory.TriangleBoundary.toBoundaryNerveMap_ofBoundaryNerveMap φ

/-- Every simplicial degree of the canonical comparison is bijective, with
the explicit inverse constructed above. -/
theorem degreeTwoBoundaryToAbstractMatching_app_bijective (k : ℕ) :
    Function.Bijective
      ((degreeTwoBoundaryToAbstractMatching C).app
        (op (SimplexCategory.mk k))) := by
  constructor
  · intro F G h
    have h' := congrArg (degreeTwoBoundaryComparisonInverseApp C k) h
    calc
      F = degreeTwoBoundaryComparisonInverseApp C k
          ((degreeTwoBoundaryToAbstractMatching C).app
            (op (SimplexCategory.mk k)) F) :=
        (degreeTwoBoundaryComparisonInverseApp_comparison C k F).symm
      _ = degreeTwoBoundaryComparisonInverseApp C k
          ((degreeTwoBoundaryToAbstractMatching C).app
            (op (SimplexCategory.mk k)) G) := h'
      _ = G := degreeTwoBoundaryComparisonInverseApp_comparison C k G
  · intro x
    exact ⟨degreeTwoBoundaryComparisonInverseApp C k x,
      degreeTwoBoundaryToAbstractMatching_inverseApp C k x⟩

/-- The canonical comparison from explicit triangular boundaries to the
selected abstract degree-two Reedy matching limit is an isomorphism. -/
instance degreeTwoBoundaryToAbstractMatchingIsIso :
    IsIso (degreeTwoBoundaryToAbstractMatching C) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  rintro ⟨⟨k⟩⟩
  rw [CategoryTheory.isIso_iff_bijective]
  exact degreeTwoBoundaryToAbstractMatching_app_bijective C k

/-- Explicit isomorphism identifying the triangular-boundary nerve with the
selected abstract degree-two matching object. -/
noncomputable def degreeTwoBoundaryAbstractMatchingIso :
    degreeTwoBoundarySpace C ≅ degreeTwoAbstractMatchingObject C :=
  asIso (degreeTwoBoundaryToAbstractMatching C)

/-- Full degree-two Reedy package, including the isomorphism from the explicit
triangular-boundary nerve to the selected abstract matching limit. -/
structure DegreeTwoReedyCore extends DegreeTwoMatchingCore C where
  /-- The canonical comparison, now promoted to an isomorphism. -/
  boundaryComparisonIso :
    degreeTwoBoundarySpace C ≅ degreeTwoAbstractMatchingObject C
  /-- Its forward map is the previously constructed universal comparison. -/
  boundaryComparisonIso_hom :
    boundaryComparisonIso.hom = boundaryToAbstractMatching

/-- Package the complete degree-two matching presentation. -/
noncomputable def degreeTwoReedyCore : DegreeTwoReedyCore C where
  toDegreeTwoMatchingCore := degreeTwoMatchingCore C
  boundaryComparisonIso := degreeTwoBoundaryAbstractMatchingIso C
  boundaryComparisonIso_hom := rfl

/-- Forget a core-valued equivalence string to a genuinely invertible string
in `C`, retaining only invertible transformations in the surrounding core. -/
noncomputable def equivalenceStringCoreForward (k : ℕ) :
    Core (ComposableArrows (Core C) k) ⥤
      Core (EquivalenceString C k) where
  obj X := ⟨⟨X.of ⋙ Core.inclusion C, fun {i j} f ↦ by
    change IsIso ((X.of.map f).iso.hom)
    infer_instance⟩⟩
  map {X Y} eta := ⟨(equivalenceStringProperty C k).isoMk
    (NatIso.ofComponents
      (fun i ↦ (eta.iso.hom.app i).iso)
      (fun {i j} f ↦ by
        have h := eta.iso.hom.naturality f
        exact congrArg (fun g ↦ g.iso.hom) h))⟩
  map_id X := by
    apply Core.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext i
    rfl
  map_comp eta theta := by
    apply Core.hom_ext
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext i
    rfl

/-- Lift a genuinely invertible string and its invertible transformations to
the corresponding string in `Core C`. -/
noncomputable def equivalenceStringCoreBackward (k : ℕ) :
  Core (EquivalenceString C k) ⥤
      Core (ComposableArrows (Core C) k) where
  obj X := ⟨equivalenceStringToCoreString C X.of⟩
  map {X Y} eta := ⟨NatIso.ofComponents
    (fun i ↦ Core.isoMk
      ((((equivalenceStringProperty C k).ι).mapIso eta.iso).app i))
    (fun {i j} f ↦ by
      apply Core.hom_ext
      exact ((((equivalenceStringProperty C k).ι).mapIso
        eta.iso).hom.naturality f))⟩
  map_id X := by
    apply Core.hom_ext
    apply NatTrans.ext
    funext i
    apply Core.hom_ext
    change 𝟙 _ = 𝟙 _
    rfl
  map_comp eta theta := by
    apply Core.hom_ext
    apply NatTrans.ext
    funext i
    apply Core.hom_ext
    rfl

private noncomputable def equivalenceStringCoreUnitComponent (k : ℕ)
    (X : Core (ComposableArrows (Core C) k)) :
    X ≅ (equivalenceStringCoreForward C k ⋙
      equivalenceStringCoreBackward C k).obj X :=
  Core.isoMk (NatIso.ofComponents
    (fun i ↦ Core.isoMk (Iso.refl (X.of.obj i).of))
    (fun {i j} f ↦ by
      apply Core.hom_ext
      change (X.of.map f).iso.hom ≫ 𝟙 _ =
        𝟙 _ ≫ (X.of.map f).iso.hom
      simp))

private noncomputable def equivalenceStringCoreUnitIso (k : ℕ) :
    Functor.id (Core (ComposableArrows (Core C) k)) ≅
      equivalenceStringCoreForward C k ⋙
        equivalenceStringCoreBackward C k :=
  NatIso.ofComponents
    (equivalenceStringCoreUnitComponent C k)
    (fun {X Y} eta ↦ by
      apply Core.hom_ext
      apply NatTrans.ext
      funext i
      apply Core.hom_ext
      change (eta.iso.hom.app i).iso.hom ≫ 𝟙 _ =
        𝟙 _ ≫ (eta.iso.hom.app i).iso.hom
      simp)

private noncomputable def equivalenceStringCoreCounitComponent (k : ℕ)
    (X : Core (EquivalenceString C k)) :
    (equivalenceStringCoreBackward C k ⋙
      equivalenceStringCoreForward C k).obj X ≅ X :=
  Core.isoMk ((equivalenceStringProperty C k).isoMk
    (NatIso.ofComponents
      (fun i ↦ Iso.refl (X.of.obj.obj i))
      (fun {i j} f ↦ by
        change X.of.obj.map f ≫ 𝟙 _ = 𝟙 _ ≫ X.of.obj.map f
        simp)))

private noncomputable def equivalenceStringCoreCounitIso (k : ℕ) :
    equivalenceStringCoreBackward C k ⋙
        equivalenceStringCoreForward C k ≅
      Functor.id (Core (EquivalenceString C k)) :=
  NatIso.ofComponents
    (equivalenceStringCoreCounitComponent C k)
    (fun {X Y} eta ↦ by
      apply Core.hom_ext
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext i
      change eta.iso.hom.hom.app i ≫ 𝟙 _ =
        𝟙 _ ≫ eta.iso.hom.hom.app i
      simp)

/-- Core-valued equivalence strings and genuinely invertible strings with
invertible transformations are explicitly equivalent categories. -/
noncomputable def equivalenceStringCoreEquivalence (k : ℕ) :
    Core (ComposableArrows (Core C) k) ≌
      Core (EquivalenceString C k) :=
  CategoryTheory.Equivalence.mk
    (equivalenceStringCoreForward C k)
    (equivalenceStringCoreBackward C k)
    (equivalenceStringCoreUnitIso C k)
    (equivalenceStringCoreCounitIso C k)

/-- Outer degree zero of the Rezk core diagram. -/
abbrev objectSpace : SSet := (diagram C).obj (op ⦋0⦌)

/-- The selected space of equivalence arrows: one-step diagrams in the core
of `C`. -/
abbrev equivalenceSpace : SSet :=
  CategoryTheory.nerve (Core (ComposableArrows (Core C) 1))

instance equivalenceSpaceKan : KanComplex (equivalenceSpace C) :=
  CategoryTheory.Nerve.kanComplex (Core (ComposableArrows (Core C) 1))

/-- Evaluation identifies the outer object space with the nerve of `Core C`. -/
noncomputable def objectSpaceEquivalence :
    Core (ComposableArrows C 0) ≌ Core C :=
  (zeroDiagramEquivalence C).symm.core

/-- The displayed map from the outer object space to the ordinary object-core
nerve. -/
noncomputable def objectSpaceMap :
    objectSpace C ⟶ CategoryTheory.nerve (Core C) :=
  CategoryTheory.nerveMap (objectSpaceEquivalence C).functor

/-- Categorical equivalence evidence for the object-space comparison. -/
noncomputable def objectSpaceWitness :
    NerveEquivalenceWitness (objectSpaceMap C) :=
  NerveEquivalenceWitness.ofEquivalence (objectSpaceEquivalence C)

/-- A groupoid is equivalent to the core of its underlying category. -/
def groupoidCoreEquivalence (G : Type u) [Groupoid.{u} G] : Core G ≌ G where
  functor := Core.inclusion G
  inverse := Core.functorToCore (𝟭 G)
  unitIso := NatIso.ofComponents (fun X => Iso.refl X) (fun f => by
    apply Core.hom_ext
    change f.iso.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.iso.hom
    simp)
  counitIso := NatIso.ofComponents (fun X => Iso.refl X) (fun f => by
    change f ≫ 𝟙 _ = 𝟙 _ ≫ f
    simp)
  functor_unitIso_comp _ := by
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp

/-- Sending an object to its identity equivalence arrow is a categorical
equivalence after the zero-diagram identification. -/
noncomputable def completenessEquivalence :
    Core (ComposableArrows C 0) ≌
      Core (ComposableArrows (Core C) 1) :=
  (zeroDiagramEquivalence C).symm.core.trans
    ((groupoidCoreEquivalence (Core C)).symm.trans
      (CategoryTheory.Groupoid.identityArrowEquivalence (Core C)).core)

/-- The selected Rezk completeness map. -/
noncomputable def completenessMap : objectSpace C ⟶ equivalenceSpace C :=
  CategoryTheory.nerveMap (completenessEquivalence C).functor

/-- Strong categorical evidence that the selected completeness map is a weak
equivalence once a simplicial weak-equivalence API is available. -/
noncomputable def completenessWitness :
    NerveEquivalenceWitness (completenessMap C) :=
  NerveEquivalenceWitness.ofEquivalence (completenessEquivalence C)

/-- Transparent object-to-identity-arrow functor. This is the canonical
forward map hidden inside the compositional construction of
`completenessEquivalence`. -/
def selectedIdentityFunctor :
    Core (ComposableArrows C 0) ⥤
      Core (ComposableArrows (Core C) 1) where
  obj X := ⟨(Functor.const (Fin 2)).obj ⟨X.of.obj 0⟩⟩
  map eta := ⟨NatIso.ofComponents
    (fun _ => Core.isoMk (eta.iso.app 0))
    (fun {i j} f => by
      apply Core.hom_ext
      change 𝟙 _ ≫ (eta.iso.app 0).hom = (eta.iso.app 0).hom ≫ 𝟙 _
      simp)⟩
  map_id X := by
    apply Core.hom_ext
    apply NatTrans.ext
    funext i
    apply Core.hom_ext
    simp
  map_comp eta theta := by
    apply Core.hom_ext
    apply NatTrans.ext
    funext i
    apply Core.hom_ext
    rfl

@[simp]
theorem completenessEquivalence_obj_of
    (X : Core (ComposableArrows C 0)) :
    ((completenessEquivalence C).functor.obj X).of =
      (Functor.const (Fin 2)).obj ⟨X.of.obj 0⟩ :=
  rfl

@[simp]
theorem completenessEquivalence_map_app
    {X Y : Core (ComposableArrows C 0)} (eta : X ⟶ Y) (i : Fin 2) :
    ((((completenessEquivalence C).functor.map eta).iso.hom.app i).iso.hom) =
      eta.iso.hom.app 0 :=
  rfl

@[simp]
theorem selectedIdentityFunctor_obj_of
    (X : Core (ComposableArrows C 0)) :
    ((selectedIdentityFunctor C).obj X).of =
      (Functor.const (Fin 2)).obj ⟨X.of.obj 0⟩ :=
  rfl

/-- Componentwise identity isomorphism between the compositional and
transparent completeness functors. -/
noncomputable def selectedComponentIso
    (X : Core (ComposableArrows C 0)) (i : Fin 2) :
    ((completenessEquivalence C).functor.obj X).of.obj i ≅
      ((selectedIdentityFunctor C).obj X).of.obj i :=
  Core.isoMk (Iso.refl (X.of.obj 0))

/-- The existing categorical equivalence has the transparent identity-arrow
functor as its forward map, up to displayed natural isomorphism. -/
noncomputable def completenessFunctorIsoSelected :
    (completenessEquivalence C).functor ≅ selectedIdentityFunctor C :=
  NatIso.ofComponents
    (fun X => Core.isoMk (NatIso.ofComponents
      (fun i => selectedComponentIso C X i)
      (fun {i j} f => by
        apply Core.hom_ext
        simp [selectedComponentIso, selectedIdentityFunctor])))
    (fun {X Y} eta => by
      apply Core.hom_ext
      apply NatTrans.ext
      funext i
      apply Core.hom_ext
      simp only [CategoryTheory.coreCategory_comp_iso, Iso.trans_hom,
        NatTrans.comp_app]
      rw [completenessEquivalence_map_app]
      change eta.iso.hom.app 0 ≫ 𝟙 (Y.of.obj 0) =
        𝟙 (X.of.obj 0) ≫ eta.iso.hom.app 0
      simp)

/-- Canonical completeness equivalence whose forward map is definitionally
the transparent identity-arrow functor. -/
noncomputable def selectedCompletenessEquivalence :
    Core (ComposableArrows C 0) ≌
      Core (ComposableArrows (Core C) 1) :=
  (completenessEquivalence C).changeFunctor
    (completenessFunctorIsoSelected C)

@[simp]
theorem selectedCompletenessEquivalence_functor :
    (selectedCompletenessEquivalence C).functor = selectedIdentityFunctor C :=
  rfl

/-- Completeness map using the canonical transparent forward functor. -/
noncomputable def selectedCompletenessMap :
    objectSpace C ⟶ equivalenceSpace C :=
  CategoryTheory.nerveMap (selectedCompletenessEquivalence C).functor

/-- Categorical equivalence witness for the canonical completeness map. -/
noncomputable def selectedCompletenessWitness :
    NerveEquivalenceWitness (selectedCompletenessMap C) :=
  NerveEquivalenceWitness.ofEquivalence (selectedCompletenessEquivalence C)

/-- Inclusion of the selected equivalence-arrow core into actual outer degree
one. The remaining factorization theorem compares its composite with the
actual outer degeneracy. -/
def equivalenceInclusionFunctor :
    Core (ComposableArrows (Core C) 1) ⥤
      Core (ComposableArrows C 1) :=
  ((CategoryTheory.Functor.whiskeringRight
    (Fin 2) (Core C) C).obj (Core.inclusion C)).core

/-- Nerve of the selected equivalence-arrow inclusion. -/
def equivalenceSpaceInclusion :
    equivalenceSpace C ⟶ (diagram C).obj (op ⦋1⦌) :=
  CategoryTheory.nerveMap (equivalenceInclusionFunctor C)

/-- Actual equivalence-arrow category inside outer degree one: its objects are
arrows of `C` that are isomorphisms, and its morphisms are invertible natural
transformations. -/
abbrev ActualEquivalenceCategory := Core (EquivalenceString C 1)

/-- The actual vertical simplicial subspace of equivalence arrows. -/
abbrev actualEquivalenceSpace : SSet.{u} :=
  CategoryTheory.nerve (ActualEquivalenceCategory C)

instance actualEquivalenceSpaceKan :
    KanComplex (actualEquivalenceSpace C) :=
  CategoryTheory.Nerve.kanComplex (ActualEquivalenceCategory C)

/-- Inclusion of the actual equivalence-arrow category into all outer
degree-one arrows. -/
def actualEquivalenceInclusionFunctor :
    ActualEquivalenceCategory C ⥤ Core (ComposableArrows C 1) :=
  ((equivalenceStringProperty C 1).ι).core

/-- Inclusion of the actual equivalence-arrow subspace into outer degree one. -/
def actualEquivalenceSpaceInclusion :
    actualEquivalenceSpace C ⟶ (diagram C).obj (op ⦋1⦌) :=
  CategoryTheory.nerveMap (actualEquivalenceInclusionFunctor C)

/-- An isomorphism of `C` regarded as an object of the actual equivalence-arrow
category. -/
noncomputable def actualEquivalenceObjectOfIso
    {X Y : C} (f : X ⟶ Y) [IsIso f] : ActualEquivalenceCategory C :=
  ⟨⟨ComposableArrows.mk₁ f, fun {i j} g => by
    have hij := leOfHom g
    fin_cases i <;> fin_cases j
    · change IsIso (𝟙 X)
      infer_instance
    · change IsIso f
      infer_instance
    · simp at hij
    · change IsIso (𝟙 Y)
      infer_instance⟩⟩

/-- The corresponding vertical vertex of the actual equivalence subspace. -/
noncomputable def actualEquivalenceVertexOfIso
    {X Y : C} (f : X ⟶ Y) [IsIso f] :
    (actualEquivalenceSpace C).obj (op (SimplexCategory.mk 0)) :=
  ComposableArrows.mk₀ (actualEquivalenceObjectOfIso C f)

/-- Inclusion of the actual equivalence vertex is exactly the outer arrow
vertex represented by the same isomorphism. -/
theorem actualEquivalenceSpaceInclusion_vertexOfIso
    {X Y : C} (f : X ⟶ Y) [IsIso f] :
    (actualEquivalenceSpaceInclusion C).app
        (op (SimplexCategory.mk 0))
        (actualEquivalenceVertexOfIso C f) = arrowVertex C f := by
  change (CategoryTheory.nerveMap
      (actualEquivalenceInclusionFunctor C)).app
        (op (SimplexCategory.mk 0))
        (ComposableArrows.mk₀ (actualEquivalenceObjectOfIso C f)) =
    ComposableArrows.mk₀
      (⟨ComposableArrows.mk₁ f⟩ : Core (ComposableArrows C 1))
  rw [CategoryTheory.nerveMap_app_mk₀]
  apply ComposableArrows.ext₀
  apply coreObj_ext
  rfl

/-- The selected equivalence-arrow category and the actual equivalence-arrow
subcategory are explicitly equivalent. -/
noncomputable def selectedActualEquivalence :
    Core (ComposableArrows (Core C) 1) ≌ ActualEquivalenceCategory C :=
  equivalenceStringCoreEquivalence C 1

/-- The selected-to-actual functor followed by actual inclusion is exactly the
previous selected inclusion. -/
theorem selectedActualInclusionFunctor :
    (selectedActualEquivalence C).functor ⋙
        actualEquivalenceInclusionFunctor C =
      equivalenceInclusionFunctor C := by
  apply CategoryTheory.Functor.hext
  · intro X
    rfl
  · intro X Y eta
    apply heq_of_eq
    apply Core.hom_ext
    apply NatTrans.ext
    funext i
    rfl

/-- Nerve map from the selected equivalence space to the actual equivalence
subspace. -/
noncomputable def selectedToActualEquivalenceMap :
    equivalenceSpace C ⟶ actualEquivalenceSpace C :=
  CategoryTheory.nerveMap (selectedActualEquivalence C).functor

/-- The selected-to-actual comparison is presented as the nerve of a category
equivalence. -/
noncomputable def selectedToActualEquivalenceWitness :
    NerveEquivalenceWitness (selectedToActualEquivalenceMap C) :=
  NerveEquivalenceWitness.ofEquivalence (selectedActualEquivalence C)

/-- Selected-to-actual comparison followed by actual inclusion recovers the
selected inclusion as a simplicial map. -/
theorem selectedToActualEquivalenceMap_comp_inclusion :
    selectedToActualEquivalenceMap C ≫
        actualEquivalenceSpaceInclusion C =
      equivalenceSpaceInclusion C := by
  change CategoryTheory.nerveMap
      (selectedActualEquivalence C).functor ≫
        CategoryTheory.nerveMap (actualEquivalenceInclusionFunctor C) =
    CategoryTheory.nerveMap (equivalenceInclusionFunctor C)
  rw [← selectedActualInclusionFunctor C]
  rfl

/-- Object-to-equivalence comparison landing directly in the actual
equivalence-arrow category. -/
noncomputable def actualCompletenessEquivalence :
    Core (ComposableArrows C 0) ≌ ActualEquivalenceCategory C :=
  (selectedCompletenessEquivalence C).trans (selectedActualEquivalence C)

/-- Completeness map with codomain the actual equivalence subspace. -/
noncomputable def actualCompletenessMap :
    objectSpace C ⟶ actualEquivalenceSpace C :=
  CategoryTheory.nerveMap (actualCompletenessEquivalence C).functor

/-- The actual-subspace completeness map is the nerve of a category
equivalence. -/
noncomputable def actualCompletenessWitness :
    NerveEquivalenceWitness (actualCompletenessMap C) :=
  NerveEquivalenceWitness.ofEquivalence (actualCompletenessEquivalence C)

/-- The actual completeness map factors through the selected completeness map. -/
theorem actualCompletenessMap_eq_selected :
    actualCompletenessMap C =
      selectedCompletenessMap C ≫ selectedToActualEquivalenceMap C :=
  rfl

/-- Including actual equivalences after the actual completeness map recovers
the former selected factorization into outer degree one. -/
theorem actualCompletenessMap_comp_inclusion :
    actualCompletenessMap C ≫ actualEquivalenceSpaceInclusion C =
      selectedCompletenessMap C ≫ equivalenceSpaceInclusion C := by
  rw [actualCompletenessMap_eq_selected, Category.assoc,
    selectedToActualEquivalenceMap_comp_inclusion]

/-- The object of `Fin 1` selected from an outer-degeneracy vertex. -/
abbrev outerDegeneracyIndex (i : Fin 2) : Fin 1 :=
  (SimplexCategory.toCat.map
    (SimplexCategory.σ (0 : Fin 1))).toFunctor.obj i

/-- The ordinal functor underlying outer zero-degeneracy. -/
abbrev outerDegeneracyFunctor : Fin 2 ⥤ Fin 1 :=
  (SimplexCategory.toCat.map
    (SimplexCategory.σ (0 : Fin 1))).toFunctor

/-- A zero-simplex diagram is naturally isomorphic to its pullback along the
outer zero-degeneracy. The component is the image of the unique source arrow
in `Fin 1`. -/
noncomputable def constantToDegeneracyIso
    (X : ComposableArrows C 0) :
    (Functor.const (Fin 2)).obj (X.obj 0) ≅
      outerDegeneracyFunctor ⋙ X :=
  NatIso.ofComponents
    (fun i => asIso (X.map
      (eqToHom (Fin.eq_zero (outerDegeneracyIndex i)).symm)))
    (fun {i j} f => by
      change 𝟙 _ ≫ X.map _ = X.map _ ≫ X.map _
      rw [Category.id_comp, ← X.map_comp]
      congr)

/-- The selected inclusion is definitionally the constant `Fin 2` diagram. -/
theorem selectedIncludedUnderlying_eq
    (X : Core (ComposableArrows C 0)) :
    ((selectedIdentityFunctor C ⋙
      equivalenceInclusionFunctor C).obj X).of =
        (Functor.const (Fin 2)).obj (X.of.obj 0) :=
  rfl

/-- Actual outer zero-degeneracy is precomposition by its ordinal functor. -/
theorem actualDegeneracyUnderlying_eq
    (X : Core (ComposableArrows C 0)) :
    (((diagramCat C).σ (0 : Fin 1)).toFunctor.obj X).of =
      outerDegeneracyFunctor ⋙ X.of :=
  rfl

/-- Objectwise comparison between selected identity arrows and actual outer
zero-degeneracy. -/
noncomputable def selectedCompletenessComponentIso
    (X : Core (ComposableArrows C 0)) :
    (selectedIdentityFunctor C ⋙ equivalenceInclusionFunctor C).obj X ≅
      ((diagramCat C).σ (0 : Fin 1)).toFunctor.obj X :=
  Core.isoMk (constantToDegeneracyIso C X.of)

/-- **Actual categorical completeness factorization.** The selected
identity-arrow functor followed by inclusion is naturally isomorphic to the
real outer zero-degeneracy functor. -/
noncomputable def selectedCompletenessFunctorIsoDegeneracy :
    selectedIdentityFunctor C ⋙ equivalenceInclusionFunctor C ≅
      ((diagramCat C).σ (0 : Fin 1)).toFunctor :=
  NatIso.ofComponents
    (selectedCompletenessComponentIso C)
    (fun {X Y} eta => by
      apply Core.hom_ext
      apply NatTrans.ext
      funext i
      change eta.iso.hom.app 0 ≫
          Y.of.map (eqToHom (Fin.eq_zero (outerDegeneracyIndex i)).symm) =
        X.of.map (eqToHom (Fin.eq_zero (outerDegeneracyIndex i)).symm) ≫
          eta.iso.hom.app (outerDegeneracyIndex i)
      exact (eta.iso.hom.naturality _).symm)

/-- The canonical selected completeness equivalence factors through actual
outer zero-degeneracy up to the displayed natural isomorphism. -/
noncomputable def completenessFunctorIsoDegeneracy :
    (selectedCompletenessEquivalence C).functor ⋙
        equivalenceInclusionFunctor C ≅
      ((diagramCat C).σ (0 : Fin 1)).toFunctor := by
  rw [selectedCompletenessEquivalence_functor]
  exact selectedCompletenessFunctorIsoDegeneracy C

/-- Machine-facing categorical factorization data for Rezk completeness.

The selected equivalence-arrow category mediates between outer degree zero
and the actual outer degree-one category.  The comparison field records that
the mediated functor is the genuine zero-degeneracy up to natural
isomorphism. -/
structure CompletenessFactorization where
  /-- The categorical completeness equivalence. -/
  selected :
    Core (ComposableArrows C 0) ≌
      Core (ComposableArrows (Core C) 1)
  /-- Inclusion of selected equivalence arrows into all outer one-simplices. -/
  inclusion :
    Core (ComposableArrows (Core C) 1) ⥤
      Core (ComposableArrows C 1)
  /-- The actual outer zero-degeneracy functor. -/
  degeneracy :
    Core (ComposableArrows C 0) ⥤
      Core (ComposableArrows C 1)
  /-- The selected factorization agrees with actual zero-degeneracy. -/
  comparison : selected.functor ⋙ inclusion ≅ degeneracy

/-- Pack the selected equivalence, its inclusion, the actual zero-degeneracy,
and their displayed comparison into one kernel-checked factorization. -/
noncomputable def completenessFactorization : CompletenessFactorization C where
  selected := selectedCompletenessEquivalence C
  inclusion := equivalenceInclusionFunctor C
  degeneracy := ((diagramCat C).σ (0 : Fin 1)).toFunctor
  comparison := completenessFunctorIsoDegeneracy C

/-- Nerve-level completeness factorization data.  The categorical
factorization is retained together with an actual simplicial homotopy between
the nerve of its mediated functor and the nerve of outer zero-degeneracy. -/
structure NerveCompletenessFactorization where
  /-- The underlying categorical factorization. -/
  categorical : CompletenessFactorization C
  /-- The displayed natural isomorphism induces a genuine nerve homotopy. -/
  comparisonHomotopy :
    SSet.Homotopy
      (CategoryTheory.nerveMap
        (categorical.selected.functor ⋙ categorical.inclusion))
      (CategoryTheory.nerveMap categorical.degeneracy)

/-- The composite through the selected equivalence-arrow nerve is the nerve
of the corresponding composite functor. -/
theorem selectedCompletenessMap_comp_inclusion :
    selectedCompletenessMap C ≫ equivalenceSpaceInclusion C =
      CategoryTheory.nerveMap
        ((selectedCompletenessEquivalence C).functor ⋙
          equivalenceInclusionFunctor C) :=
  rfl

/-- The nerve of the categorical degeneracy is the actual outer
zero-degeneracy of the Rezk core diagram. -/
theorem nerveMap_degeneracy_eq_actual :
    CategoryTheory.nerveMap
      ((diagramCat C).σ (0 : Fin 1)).toFunctor =
        (diagram C).σ (0 : Fin 1) :=
  rfl

/-- **Nerve-level completeness square.**  The selected completeness map
followed by inclusion is simplicially homotopic to actual outer
zero-degeneracy. -/
noncomputable def completenessNerveHomotopy :
    SSet.Homotopy
      (selectedCompletenessMap C ≫ equivalenceSpaceInclusion C)
      ((diagram C).σ (0 : Fin 1)) := by
  rw [selectedCompletenessMap_comp_inclusion,
    ← nerveMap_degeneracy_eq_actual]
  exact CategoryTheory.NerveHomotopy.ofNatTrans
    (completenessFunctorIsoDegeneracy C).hom

/-- Completeness through the actual equivalence subspace is simplicially
homotopic, after inclusion, to real outer zero-degeneracy. -/
noncomputable def actualCompletenessNerveHomotopy :
    SSet.Homotopy
      (actualCompletenessMap C ≫ actualEquivalenceSpaceInclusion C)
      ((diagram C).σ (0 : Fin 1)) := by
  rw [actualCompletenessMap_comp_inclusion]
  exact completenessNerveHomotopy C

/-- Package categorical and nerve-level completeness factorization data. -/
noncomputable def nerveCompletenessFactorization :
    NerveCompletenessFactorization C where
  categorical := completenessFactorization C
  comparisonHomotopy := CategoryTheory.NerveHomotopy.ofNatTrans
    (completenessFunctorIsoDegeneracy C).hom

/-- Minimal vertical-Kan and selected-completeness data retained as a reusable
layer beneath the actual-subspace and outer-Segal packages. -/
structure CompletenessCore where
  /-- The Rezk core diagram. -/
  W : SimplicialObject SSet.{u}
  /-- Every vertical level is Kan. -/
  levelKan : ∀ Δ, KanComplex (W.obj Δ)
  /-- A selected equivalence-arrow space. -/
  equivalences : SSet.{u}
  /-- The equivalence-arrow space is Kan. -/
  equivalencesKan : KanComplex equivalences
  /-- Object-to-identity-arrow comparison. -/
  completenessMap : W.obj (op ⦋0⦌) ⟶ equivalences
  /-- Categorical presentation of that comparison as an equivalence. -/
  completeness : NerveEquivalenceWitness completenessMap

/-- Package the vertical Kan and selected completeness data of the Rezk core
diagram. -/
noncomputable def completenessCore : CompletenessCore.{u} where
  W := diagram C
  levelKan := levelKan C
  equivalences := equivalenceSpace C
  equivalencesKan := equivalenceSpaceKan C
  completenessMap := selectedCompletenessMap C
  completeness := selectedCompletenessWitness C

/-- Vertical Kan data, selected completeness equivalence, and the actual
zero-degeneracy homotopy packaged without claiming the still-missing outer
Segal and Reedy fields. -/
structure CompletenessHomotopyCore extends CompletenessCore.{u} where
  /-- Categorical factorization and its nerve-level comparison. -/
  factorization : NerveCompletenessFactorization C

/-- Package all currently proved complete-Segal completeness data, including
the explicit homotopy to actual outer zero-degeneracy. -/
noncomputable def completenessHomotopyCore :
    CompletenessHomotopyCore C where
  toCompletenessCore := completenessCore C
  factorization := nerveCompletenessFactorization C

/-- Selected and actual equivalence spaces, their equivalence witness, and
the actual completeness map together with its zero-degeneracy homotopy. -/
structure ActualCompletenessCore extends CompletenessHomotopyCore C where
  /-- Actual subspace of invertible outer arrows. -/
  actualEquivalences : SSet.{u}
  /-- The actual equivalence subspace is Kan. -/
  actualEquivalencesKan : KanComplex actualEquivalences
  /-- Comparison from the selected presentation to the actual subspace. -/
  selectedToActual : equivalences ⟶ actualEquivalences
  /-- The selected-to-actual comparison is a categorical nerve equivalence. -/
  selectedToActualEquivalence : NerveEquivalenceWitness selectedToActual
  /-- Inclusion of actual equivalences into outer degree one. -/
  actualInclusion : actualEquivalences ⟶ W.obj (op ⦋1⦌)
  /-- Object-to-identity map landing directly in actual equivalences. -/
  actualCompletenessMap : W.obj (op ⦋0⦌) ⟶ actualEquivalences
  /-- The actual-subspace completeness map is a categorical nerve equivalence. -/
  actualCompleteness : NerveEquivalenceWitness actualCompletenessMap
  /-- Actual completeness followed by inclusion is homotopic to zero-degeneracy. -/
  actualDegeneracyHomotopy :
    SSet.Homotopy (actualCompletenessMap ≫ actualInclusion)
      (W.σ (0 : Fin 1))

/-- Package selected and actual completeness data of the Rezk core diagram. -/
noncomputable def actualCompletenessCore : ActualCompletenessCore C where
  toCompletenessHomotopyCore := completenessHomotopyCore C
  actualEquivalences := actualEquivalenceSpace C
  actualEquivalencesKan := actualEquivalenceSpaceKan C
  selectedToActual := selectedToActualEquivalenceMap C
  selectedToActualEquivalence := selectedToActualEquivalenceWitness C
  actualInclusion := actualEquivalenceSpaceInclusion C
  actualCompletenessMap := actualCompletenessMap C
  actualCompleteness := actualCompletenessWitness C
  actualDegeneracyHomotopy := actualCompletenessNerveHomotopy C

/-- Vertical Kan data, actual outer Segal reconstruction, the actual
equivalence-subspace comparison through real zero-degeneracy, and the complete
positive-degree Reedy matching presentation. Attachment of noninvertible local
mapping nerves remains separate. -/
structure SegalCompletenessCore extends ActualCompletenessCore C where
  /-- Every horizontal row satisfies strict Segal reconstruction. -/
  horizontalStrictSegal : ∀ k, SSet.StrictSegal (horizontalRow C k)
  /-- The genuine standard degree-one Reedy matching restriction. -/
  degreeOneMatching : DegreeOneReedyCore C
  /-- Degree-two triangular-boundary representation, comparison isomorphism,
  and fibration. -/
  degreeTwoMatching : DegreeTwoReedyCore C
  /-- Every matching map in degree at least three is an isomorphism and hence
  a fibration. -/
  higherMatching : HigherMatchingCore C

/-- Package every currently proved outer Segal, completeness, degree-one
standard Reedy, and degree-two categorical boundary field without claiming
full higher Reedy fibrancy. -/
noncomputable def segalCompletenessCore : SegalCompletenessCore C where
  toActualCompletenessCore := actualCompletenessCore C
  horizontalStrictSegal := horizontalStrictSegal C
  degreeOneMatching := degreeOneReedyCore C
  degreeTwoMatching := degreeTwoReedyCore C
  higherMatching := higherMatchingCore C

end RezkCore

namespace TotalModelCompleteSegal

universe uR vR wR

open CategoryTheory.Bicategory

/-- The homotopy category of the total resource-model bicategory. -/
abbrev HomotopyCategory := TotalModelSimplicial.HomotopyCategory

/-- A universe-balanced copy used by the category-valued Rezk construction. -/
abbrev SmallHomotopyCategory :=
  AsSmall.{0} HomotopyCategory.{uR, vR, wR}

/-- Rezk core diagram of total resource models at homotopy-1 level. -/
abbrev Diagram :=
  RezkCore.diagram SmallHomotopyCategory.{uR, vR, wR}

/-- Every vertical level of the total-model Rezk core diagram is Kan. -/
instance diagramLevelKan (Δ : SimplexCategoryᵒᵖ) :
    KanComplex (Diagram.{uR, vR, wR}.obj Δ) :=
  RezkCore.levelKan SmallHomotopyCategory.{uR, vR, wR} Δ

/-- Horizontal row of the total-model Rezk core diagram. -/
abbrev HorizontalRow (k : ℕ) :=
  RezkCore.horizontalRow SmallHomotopyCategory.{uR, vR, wR} k

/-- Every total-model horizontal row is naturally the nerve of its category
of vertical equivalence strings. -/
noncomputable def horizontalRowIso (k : ℕ) :
    HorizontalRow.{uR, vR, wR} k ≅
      CategoryTheory.nerve
        (RezkCore.EquivalenceString
          SmallHomotopyCategory.{uR, vR, wR} k) :=
  RezkCore.horizontalRowIso
    SmallHomotopyCategory.{uR, vR, wR} k

/-- Every total-model horizontal row satisfies strict Segal reconstruction. -/
noncomputable def horizontalStrictSegal (k : ℕ) :
    SSet.StrictSegal (HorizontalRow.{uR, vR, wR} k) :=
  RezkCore.horizontalStrictSegal
    SmallHomotopyCategory.{uR, vR, wR} k

instance horizontalRowIsStrictSegal (k : ℕ) :
    (HorizontalRow.{uR, vR, wR} k).IsStrictSegal :=
  (horizontalStrictSegal.{uR, vR, wR} k).isStrictSegal

/-- The actual total-model outer spine comparison is an equivalence in every
bidegree. -/
noncomputable def outerSegalEquiv (k n : ℕ) :
    (HorizontalRow.{uR, vR, wR} k).obj
        (op (SimplexCategory.mk n)) ≃
      (HorizontalRow.{uR, vR, wR} k).Path n :=
  RezkCore.outerSegalEquiv
    SmallHomotopyCategory.{uR, vR, wR} k n

theorem outerSegalEquiv_apply (k n : ℕ)
    (x : (Diagram.{uR, vR, wR}.obj
      (op (SimplexCategory.mk n))).obj (op (SimplexCategory.mk k))) :
    (outerSegalEquiv.{uR, vR, wR} k n :
      (Diagram.{uR, vR, wR}.obj
          (op (SimplexCategory.mk n))).obj
            (op (SimplexCategory.mk k)) ≃
        (HorizontalRow.{uR, vR, wR} k).Path n) x =
      (HorizontalRow.{uR, vR, wR} k).spine n x :=
  rfl

/-- The small outer object core is categorically equivalent to the original
total-model object core, including the universe-balancing equivalence. -/
noncomputable def objectCoreEquivalence :
    Core (ComposableArrows SmallHomotopyCategory.{uR, vR, wR} 0) ≌
      TotalModelSimplicial.ObjectCore.{uR, vR, wR} :=
  (RezkCore.objectSpaceEquivalence
      SmallHomotopyCategory.{uR, vR, wR}).trans
    (((AsSmall.equiv
      (C := HomotopyCategory.{uR, vR, wR})).symm).core)

/-- Selected equivalence-arrow space for total resource models. -/
abbrev EquivalenceSpace :=
  RezkCore.equivalenceSpace SmallHomotopyCategory.{uR, vR, wR}

instance equivalenceSpaceKan :
    KanComplex EquivalenceSpace.{uR, vR, wR} :=
  RezkCore.equivalenceSpaceKan SmallHomotopyCategory.{uR, vR, wR}

/-- Selected completeness comparison for total resource models. -/
noncomputable def completenessMap :
    Diagram.{uR, vR, wR}.obj (op ⦋0⦌) ⟶
      EquivalenceSpace.{uR, vR, wR} :=
  RezkCore.selectedCompletenessMap SmallHomotopyCategory.{uR, vR, wR}

/-- The selected completeness comparison is presented as the nerve of a
category equivalence. -/
noncomputable def completenessWitness :
    NerveEquivalenceWitness (completenessMap.{uR, vR, wR}) :=
  RezkCore.selectedCompletenessWitness SmallHomotopyCategory.{uR, vR, wR}

/-- Inclusion of the selected equivalence-arrow space into actual outer
degree one. -/
def equivalenceSpaceInclusion :
    EquivalenceSpace.{uR, vR, wR} ⟶
      Diagram.{uR, vR, wR}.obj (op ⦋1⦌) :=
  RezkCore.equivalenceSpaceInclusion SmallHomotopyCategory.{uR, vR, wR}

/-- Actual subspace of invertible outer arrows for total resource models. -/
abbrev ActualEquivalenceSpace :=
  RezkCore.actualEquivalenceSpace SmallHomotopyCategory.{uR, vR, wR}

instance actualEquivalenceSpaceKan :
    KanComplex ActualEquivalenceSpace.{uR, vR, wR} :=
  RezkCore.actualEquivalenceSpaceKan
    SmallHomotopyCategory.{uR, vR, wR}

/-- Categorical-equivalence comparison from the selected presentation to the
actual equivalence-arrow subspace. -/
noncomputable def selectedToActualEquivalenceMap :
    EquivalenceSpace.{uR, vR, wR} ⟶
      ActualEquivalenceSpace.{uR, vR, wR} :=
  RezkCore.selectedToActualEquivalenceMap
    SmallHomotopyCategory.{uR, vR, wR}

/-- The selected-to-actual comparison is the nerve of a category equivalence. -/
noncomputable def selectedToActualEquivalenceWitness :
    NerveEquivalenceWitness
      (selectedToActualEquivalenceMap.{uR, vR, wR}) :=
  RezkCore.selectedToActualEquivalenceWitness
    SmallHomotopyCategory.{uR, vR, wR}

/-- Inclusion of actual total-model equivalence arrows into outer degree one. -/
def actualEquivalenceSpaceInclusion :
    ActualEquivalenceSpace.{uR, vR, wR} ⟶
      Diagram.{uR, vR, wR}.obj (op ⦋1⦌) :=
  RezkCore.actualEquivalenceSpaceInclusion
    SmallHomotopyCategory.{uR, vR, wR}

/-- Completeness comparison landing directly in actual equivalence arrows. -/
noncomputable def actualCompletenessMap :
    Diagram.{uR, vR, wR}.obj (op ⦋0⦌) ⟶
      ActualEquivalenceSpace.{uR, vR, wR} :=
  RezkCore.actualCompletenessMap
    SmallHomotopyCategory.{uR, vR, wR}

/-- Actual-subspace completeness is presented as the nerve of a category
equivalence. -/
noncomputable def actualCompletenessWitness :
    NerveEquivalenceWitness (actualCompletenessMap.{uR, vR, wR}) :=
  RezkCore.actualCompletenessWitness
    SmallHomotopyCategory.{uR, vR, wR}

/-- The selected completeness equivalence followed by inclusion is naturally
isomorphic to actual outer zero-degeneracy. -/
noncomputable def completenessFunctorIsoDegeneracy :
    (RezkCore.selectedCompletenessEquivalence
        SmallHomotopyCategory.{uR, vR, wR}).functor ⋙
        RezkCore.equivalenceInclusionFunctor
          SmallHomotopyCategory.{uR, vR, wR} ≅
      ((RezkCore.diagramCat
        SmallHomotopyCategory.{uR, vR, wR}).σ (0 : Fin 1)).toFunctor :=
  RezkCore.completenessFunctorIsoDegeneracy
    SmallHomotopyCategory.{uR, vR, wR}

/-- Packaged categorical factorization of total-model completeness through
the selected equivalence-arrow category and into actual outer degree one. -/
noncomputable def completenessFactorization :
    RezkCore.CompletenessFactorization
      SmallHomotopyCategory.{uR, vR, wR} :=
  RezkCore.completenessFactorization
    SmallHomotopyCategory.{uR, vR, wR}

/-- The total-model selected completeness map followed by inclusion is
simplicially homotopic to actual outer zero-degeneracy. -/
noncomputable def completenessNerveHomotopy :
    SSet.Homotopy
      (completenessMap.{uR, vR, wR} ≫
        equivalenceSpaceInclusion.{uR, vR, wR})
      (Diagram.{uR, vR, wR}.σ (0 : Fin 1)) :=
  RezkCore.completenessNerveHomotopy
    SmallHomotopyCategory.{uR, vR, wR}

/-- Actual-subspace completeness followed by inclusion is simplicially
homotopic to real total-model zero-degeneracy. -/
noncomputable def actualCompletenessNerveHomotopy :
    SSet.Homotopy
      (actualCompletenessMap.{uR, vR, wR} ≫
        actualEquivalenceSpaceInclusion.{uR, vR, wR})
      (Diagram.{uR, vR, wR}.σ (0 : Fin 1)) :=
  RezkCore.actualCompletenessNerveHomotopy
    SmallHomotopyCategory.{uR, vR, wR}

/-- Packaged categorical and nerve-homotopical completeness factorization
for total resource models. -/
noncomputable def nerveCompletenessFactorization :
    RezkCore.NerveCompletenessFactorization
      SmallHomotopyCategory.{uR, vR, wR} :=
  RezkCore.nerveCompletenessFactorization
    SmallHomotopyCategory.{uR, vR, wR}

/-- Packaged vertical-Kan and categorical-completeness core for total resource
models. -/
noncomputable def completenessCore : RezkCore.CompletenessCore :=
  RezkCore.completenessCore SmallHomotopyCategory.{uR, vR, wR}

/-- Packaged vertical-Kan, categorical-completeness, and nerve-homotopy data
for total resource models. -/
noncomputable def completenessHomotopyCore :
    RezkCore.CompletenessHomotopyCore
      SmallHomotopyCategory.{uR, vR, wR} :=
  RezkCore.completenessHomotopyCore
    SmallHomotopyCategory.{uR, vR, wR}

/-- Packaged selected/actual equivalence-space comparison and actual
completeness data for total resource models. -/
noncomputable def actualCompletenessCore :
    RezkCore.ActualCompletenessCore
      SmallHomotopyCategory.{uR, vR, wR} :=
  RezkCore.actualCompletenessCore
    SmallHomotopyCategory.{uR, vR, wR}

/-- The literal degree-one total-model matching restriction, its Kan
fibration proof, and its two actual outer-face projection equations. -/
noncomputable def degreeOneMatchingCore :
    RezkCore.DegreeOneMatchingCore
      SmallHomotopyCategory.{uR, vR, wR} :=
  RezkCore.degreeOneMatchingCore
    SmallHomotopyCategory.{uR, vR, wR}

/-- The standard total-model degree-one Reedy map into the selected
simplicial-set product, its exact face-pair equation, and its fibration. -/
noncomputable def degreeOneReedyCore :
    RezkCore.DegreeOneReedyCore
      SmallHomotopyCategory.{uR, vR, wR} :=
  RezkCore.degreeOneReedyCore
    SmallHomotopyCategory.{uR, vR, wR}

/-- The total-model degree-two triangular-boundary representation and Kan
fibration package. -/
noncomputable def degreeTwoMatchingCore :
    RezkCore.DegreeTwoMatchingCore
      SmallHomotopyCategory.{uR, vR, wR} :=
  RezkCore.degreeTwoMatchingCore
    SmallHomotopyCategory.{uR, vR, wR}

/-- The total-model degree-two package with the canonical comparison promoted
to an isomorphism onto the selected abstract Reedy matching object. -/
noncomputable def degreeTwoReedyCore :
    RezkCore.DegreeTwoReedyCore
      SmallHomotopyCategory.{uR, vR, wR} :=
  RezkCore.degreeTwoReedyCore
    SmallHomotopyCategory.{uR, vR, wR}

/-- All total-model Reedy matching maps in degree at least three, packaged as
isomorphisms and Kan fibrations. -/
noncomputable def higherMatchingCore :
    RezkCore.HigherMatchingCore
      SmallHomotopyCategory.{uR, vR, wR} :=
  RezkCore.higherMatchingCore
    SmallHomotopyCategory.{uR, vR, wR}

/-- A total resource model as a vertical vertex in outer degree zero of the
Rezk core diagram. -/
noncomputable def rezkObjectVertex (M : ResourceModel.{uR, vR, wR}) :
    (Diagram.{uR, vR, wR}.obj (op (SimplexCategory.mk 0))).obj
      (op (SimplexCategory.mk 0)) :=
  CategoryTheory.nerveEquiv.symm
    ((objectCoreEquivalence.{uR, vR, wR}).inverse.obj
      (TotalModelSimplicial.objectCoreVertex M))

/-- Rezk–Segal–completeness data with the full non-groupoidal local mapping
nerves attached over the same total-model objects.  The local nerves retain
all 2-cells, while the Rezk object direction keeps only equivalences.
Horizontal composition is accompanied by natural associator and unitor
isomorphisms, their induced simplicial homotopies, and the pointwise pentagon
and triangle equations. -/
structure HigherCompleteSegalCore where
  /-- Groupoidal Rezk/Segal/completeness and low-degree Reedy data. -/
  rezk : RezkCore.SegalCompletenessCore
    SmallHomotopyCategory.{uR, vR, wR}
  /-- Embedding of each total model into the Rezk object space. -/
  objectVertex : ∀ _M : ResourceModel.{uR, vR, wR},
    (Diagram.{uR, vR, wR}.obj (op (SimplexCategory.mk 0))).obj
      (op (SimplexCategory.mk 0))
  /-- Vertices of each full local nerve are exactly total-model 1-cells. -/
  mappingVertexEquiv : ∀ M N : ResourceModel.{uR, vR, wR},
    TotalModelSimplicial.MappingNerve M N _⦋0⦌ ≃ ResourceModelHom M N
  /-- Edges of each full local nerve are exactly arbitrary total-model
  2-cells, with no invertibility hypothesis. -/
  mappingEdgeEquiv : ∀ {M N : ResourceModel.{uR, vR, wR}}
    (F G : ResourceModelHom M N),
    (TotalModelSimplicial.MappingNerve M N).Edge
        (TotalModelSimplicial.mappingNerveVertex F)
        (TotalModelSimplicial.mappingNerveVertex G) ≃
      ResourceModelTransformation F G
  /-- Encoding and then decoding any local 2-cell is exact. -/
  transformationEncodeDecode :
    ∀ {M N : ResourceModel.{uR, vR, wR}}
      {F G : ResourceModelHom M N}
      (α : F ⟶ G),
      TotalModelSimplicial.mappingNerveEdgeEquiv F G
          (TotalModelSimplicial.mappingNerveTransformationEdge α) = α
  /-- Noninvertible 2-cells remain noninvertible after edge encoding and exact
  decoding. -/
  transformationNoninvertible :
    ∀ {M N : ResourceModel.{uR, vR, wR}}
      {F G : ResourceModelHom M N}
      (α : F ⟶ G),
      ¬ IsIso α →
        ¬ IsIso
          (show F ⟶ G from
            TotalModelSimplicial.mappingNerveEdgeEquiv F G
              (TotalModelSimplicial.mappingNerveTransformationEdge α))
  /-- Every local mapping nerve is strict Segal. -/
  mappingStrictSegal : ∀ M N : ResourceModel.{uR, vR, wR},
    SSet.StrictSegal (TotalModelSimplicial.MappingNerve M N)
  /-- Every local mapping nerve is a quasicategory. -/
  mappingQuasicategory : ∀ M N : ResourceModel.{uR, vR, wR},
    Quasicategory (TotalModelSimplicial.MappingNerve M N)
  /-- Every local mapping nerve is 2-coskeletal. -/
  mappingTwoCoskeletal : ∀ M N : ResourceModel.{uR, vR, wR},
    SimplicialObject.IsCoskeletal
      (TotalModelSimplicial.MappingNerve M N) 2
  /-- Exact simplicial horizontal composition of 1- and 2-cells. -/
  horizontalComposition : ∀ A B C : ResourceModel.{uR, vR, wR},
    CategoryTheory.nerve
        (ResourceModelHom A B × ResourceModelHom B C) ⟶
      TotalModelSimplicial.MappingNerve A C
  /-- Natural associativity of the two triple horizontal-composition
  functors on full local categories. -/
  horizontalAssociator : ∀ A B C D : ResourceModel.{uR, vR, wR},
    TotalModelSimplicial.leftAssociatedCompositionFunctor A B C D ≅
      TotalModelSimplicial.rightAssociatedCompositionFunctor A B C D
  /-- The associator natural isomorphism induces a genuine simplicial
  homotopy between the corresponding local-nerve maps. -/
  horizontalAssociatorHomotopy :
    ∀ A B C D : ResourceModel.{uR, vR, wR},
      SSet.Homotopy
        (CategoryTheory.nerveMap
          (TotalModelSimplicial.leftAssociatedCompositionFunctor A B C D))
        (CategoryTheory.nerveMap
          (TotalModelSimplicial.rightAssociatedCompositionFunctor A B C D))
  /-- Natural left-unit coherence on every full local category. -/
  horizontalLeftUnitor : ∀ A B : ResourceModel.{uR, vR, wR},
    TotalModelSimplicial.leftUnitCompositionFunctor A B ≅
      𝟭 (ResourceModelHom A B)
  /-- Simplicial left-unit homotopy on every full local nerve. -/
  horizontalLeftUnitorHomotopy :
    ∀ A B : ResourceModel.{uR, vR, wR},
      SSet.Homotopy
        (CategoryTheory.nerveMap
          (TotalModelSimplicial.leftUnitCompositionFunctor A B))
        (𝟙 (TotalModelSimplicial.MappingNerve A B))
  /-- Natural right-unit coherence on every full local category. -/
  horizontalRightUnitor : ∀ A B : ResourceModel.{uR, vR, wR},
    TotalModelSimplicial.rightUnitCompositionFunctor A B ≅
      𝟭 (ResourceModelHom A B)
  /-- Simplicial right-unit homotopy on every full local nerve. -/
  horizontalRightUnitorHomotopy :
    ∀ A B : ResourceModel.{uR, vR, wR},
      SSet.Homotopy
        (CategoryTheory.nerveMap
          (TotalModelSimplicial.rightUnitCompositionFunctor A B))
        (𝟙 (TotalModelSimplicial.MappingNerve A B))
  /-- The associator homotopies retain the pointwise pentagon equation. -/
  horizontalPentagon :
    ∀ {A B C D E : ResourceModel.{uR, vR, wR}}
      (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (i : D ⟶ E),
      (CategoryTheory.Bicategory.associator f g h).hom ▷ i ≫
          (CategoryTheory.Bicategory.associator f (g ≫ h) i).hom ≫
            f ◁ (CategoryTheory.Bicategory.associator g h i).hom =
        (CategoryTheory.Bicategory.associator (f ≫ g) h i).hom ≫
          (CategoryTheory.Bicategory.associator f g (h ≫ i)).hom
  /-- The associator and unitor homotopies retain the pointwise triangle
  equation. -/
  horizontalTriangle :
    ∀ {A B C : ResourceModel.{uR, vR, wR}}
      (f : A ⟶ B) (g : B ⟶ C),
      (CategoryTheory.Bicategory.associator f (𝟙 B) g).hom ≫
          f ◁ (CategoryTheory.Bicategory.leftUnitor g).hom =
        (CategoryTheory.Bicategory.rightUnitor f).hom ▷ g

/-- Package the complete object/equivalence core together with every full
local mapping nerve and exact horizontal composition. -/
noncomputable def higherCompleteSegalCore :
    HigherCompleteSegalCore.{uR, vR, wR} where
  rezk := RezkCore.segalCompletenessCore
    SmallHomotopyCategory.{uR, vR, wR}
  objectVertex := rezkObjectVertex
  mappingVertexEquiv := TotalModelSimplicial.mappingNerveVertexEquiv
  mappingEdgeEquiv := TotalModelSimplicial.mappingNerveEdgeEquiv
  transformationEncodeDecode :=
    TotalModelSimplicial.mappingNerveEdgeEquiv_transformationEdge
  transformationNoninvertible := fun α hα => by
    simpa using hα
  mappingStrictSegal := TotalModelSimplicial.mappingNerveStrictSegal
  mappingQuasicategory := fun _ _ => inferInstance
  mappingTwoCoskeletal := fun _ _ => inferInstance
  horizontalComposition := TotalModelSimplicial.horizontalCompositionNerveMap
  horizontalAssociator := TotalModelSimplicial.horizontalAssociatorNatIso
  horizontalAssociatorHomotopy :=
    TotalModelSimplicial.horizontalAssociatorNerveHomotopy
  horizontalLeftUnitor := TotalModelSimplicial.horizontalLeftUnitorNatIso
  horizontalLeftUnitorHomotopy :=
    TotalModelSimplicial.horizontalLeftUnitorNerveHomotopy
  horizontalRightUnitor := TotalModelSimplicial.horizontalRightUnitorNatIso
  horizontalRightUnitorHomotopy :=
    TotalModelSimplicial.horizontalRightUnitorNerveHomotopy
  horizontalPentagon := totalModel_pentagon
  horizontalTriangle := totalModel_triangle

/-- Packaged total-model vertical Kan, outer strict-Segal, categorical
completeness, actual zero-degeneracy homotopy, degree-one standard Reedy data,
and degree-two triangular-boundary data. -/
noncomputable def segalCompletenessCore :
    RezkCore.SegalCompletenessCore
      SmallHomotopyCategory.{uR, vR, wR} :=
  RezkCore.segalCompletenessCore
    SmallHomotopyCategory.{uR, vR, wR}

end TotalModelCompleteSegal

end Ript.Higher
