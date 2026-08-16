import Mathlib.CategoryTheory.Localization.Predicate
import Ript.ForMathlib.CategoryTheory.Bicategory.HomotopyCategory
import Ript.Higher.Equivalence

/-!
# Localization of resource-indexed process models

The bicategory of process models cannot be used directly with Mathlib's
ordinary-category localization API: composition of model morphisms is only
associative up to an invertible monoidal 2-cell.  We first pass to the
homotopy 1-category, which identifies model morphisms related by an invertible
monoidal natural transformation.

Inside that category, `costExactMorphisms R` marks precisely the classes that
have a cost-reflecting representative.  Every representative is already
resource-nonincreasing by the definition of `ModelHom`, so reflection makes
its process costs exact.  The property contains identities and is closed
under composition.  Mathlib's Gabriel--Zisman construction then supplies a
category and functor that formally invert all marked morphisms, together with
the standard functor-category universal property.

This is an ordinary localization of a homotopy 1-category.  It does not retain
noninvertible model 2-cells and is not a bicategorical, Dwyer--Kan, simplicial,
or Rezk localization.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Higher

open CategoryTheory
open CategoryTheory.Bicategory

universe u v w u' v'

variable {R : Type w} [AddCommMonoid R] [PartialOrder R]

/-- The ordinary homotopy 1-category of resource-indexed process models. -/
abbrev ModelHomotopyCategory (R : Type w) [AddCommMonoid R] [PartialOrder R] :=
  HomotopyCategory (ProcessModel.{u, v, w} R)

/-- Cost-exact arrows in the model homotopy category are the quotient classes
that have a cost-reflecting representative. -/
def costExactMorphisms (R : Type w) [AddCommMonoid R] [PartialOrder R] :
    MorphismProperty (ModelHomotopyCategory.{u, v, w} R) :=
  fun M N f ↦ ∃ F : ModelHom M.as N.as,
    CostReflecting F ∧ HomotopyCategory.homMk F = f

/-- A represented cost-reflecting model morphism belongs to the marked class. -/
theorem costExactMorphisms_homMk {M N : ProcessModel.{u, v, w} R}
    (F : ModelHom M N) [CostReflecting F] :
    costExactMorphisms R (HomotopyCategory.homMk F) :=
  ⟨F, ‹CostReflecting F›, rfl⟩

/-- The marked cost-exact arrows contain identities and are closed under
composition. -/
instance costExactMorphisms_isMultiplicative :
    (costExactMorphisms R :
      MorphismProperty (ModelHomotopyCategory.{u, v, w} R)).IsMultiplicative where
  id_mem M := by
    refine ⟨ModelHom.id M.as, inferInstance, ?_⟩
    exact HomotopyCategory.homMk_id M.as
  comp_mem f g hf hg := by
    obtain ⟨F, hF, rfl⟩ := hf
    obtain ⟨G, hG, rfl⟩ := hg
    let _ : CostReflecting F := hF
    let _ : CostReflecting G := hG
    exact ⟨ModelHom.comp F G, inferInstance, rfl⟩

/-- A cost-exact bicategorical equivalence has a marked forward arrow. -/
theorem CostExactModelEquivalence.hom_mem
    {M N : ProcessModel.{u, v, w} R} (e : CostExactModelEquivalence M N) :
    costExactMorphisms R
      (HomotopyCategory.homMk e.toEquivalence.hom) :=
  costExactMorphisms_homMk e.toEquivalence.hom

/-- A cost-exact bicategorical equivalence has a marked inverse arrow. -/
theorem CostExactModelEquivalence.inv_mem
    {M N : ProcessModel.{u, v, w} R} (e : CostExactModelEquivalence M N) :
    costExactMorphisms R
      (HomotopyCategory.homMk e.toEquivalence.inv) :=
  costExactMorphisms_homMk e.toEquivalence.inv

/-- A cost-exact bicategorical equivalence is already an isomorphism in the
model homotopy category, before any formal localization is performed. -/
instance CostExactModelEquivalence.hom_isIso
    {M N : ProcessModel.{u, v, w} R} (e : CostExactModelEquivalence M N) :
    IsIso (HomotopyCategory.homMk e.toEquivalence.hom) :=
  (HomotopyCategory.isoOfEquivalence e.toEquivalence).isIso_hom

/-- The Gabriel--Zisman category obtained by formally inverting every marked
cost-exact model morphism. -/
abbrev CostExactLocalization (R : Type w) [AddCommMonoid R] [PartialOrder R] :=
  (costExactMorphisms R :
    MorphismProperty (ModelHomotopyCategory.{u, v, w} R)).Localization

/-- The canonical functor from the model homotopy category to its cost-exact
localization. -/
abbrev costExactLocalizationFunctor (R : Type w) [AddCommMonoid R]
    [PartialOrder R] :
    ModelHomotopyCategory.{u, v, w} R ⥤ CostExactLocalization.{u, v, w} R :=
  (costExactMorphisms R :
    MorphismProperty (ModelHomotopyCategory.{u, v, w} R)).Q

/-- The canonical functor is a Mathlib localization functor at the marked
cost-exact model morphisms. -/
noncomputable instance costExactLocalizationFunctor_isLocalization :
    (costExactLocalizationFunctor (R := R) :
      ModelHomotopyCategory.{u, v, w} R ⥤ CostExactLocalization.{u, v, w} R).IsLocalization
        (costExactMorphisms R) :=
  inferInstance

/-- Every marked model morphism becomes invertible in the canonical
localization. -/
theorem costExactLocalizationFunctor_inverts :
    (costExactMorphisms R :
      MorphismProperty (ModelHomotopyCategory.{u, v, w} R)).IsInvertedBy
        (costExactLocalizationFunctor R) :=
  CategoryTheory.Localization.inverts _ _

/-- Precomposition with the canonical localization functor identifies target
functors with functors out of the model homotopy category that invert every
marked cost-exact morphism. -/
noncomputable def costExactLocalizationFunctorEquivalence
    (E : Type u') [Category.{v'} E] :
    (CostExactLocalization.{u, v, w} R ⥤ E) ≌
      (costExactMorphisms R :
        MorphismProperty (ModelHomotopyCategory.{u, v, w} R)).FunctorsInverting E :=
  CategoryTheory.Localization.functorEquivalence
    (costExactLocalizationFunctor R) (costExactMorphisms R) E

end Ript.Higher
