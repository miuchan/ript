import Mathlib.CategoryTheory.Localization.Predicate
import Ript.ForMathlib.CategoryTheory.Bicategory.Localization
import Ript.ForMathlib.CategoryTheory.Bicategory.PithToHomotopy
import Ript.Higher.Equivalence

/-!
# Localization of resource-indexed process models

The bicategory of process models cannot be used directly with Mathlib's
ordinary-category localization API: composition of model morphisms is only
associative up to an invertible monoidal 2-cell.  We first pass to the
homotopy 1-category, which identifies model morphisms related by an invertible
monoidal natural transformation.

The raw bicategorical marking `costReflectingArrows R` records exactly the
model morphisms that reflect costs.  It is multiplicative, but it is not
silently asserted to be invariant under arbitrary monoidal natural
isomorphisms.  The marking `costExactArrows R` is its explicit closure under
invertible 2-cells.  Passing to the homotopy category marks precisely the
classes that have a cost-reflecting representative.

Mathlib's Gabriel--Zisman construction then supplies a category and functor
that formally invert all marked morphisms, together with the standard
functor-category universal property.

This is an ordinary localization of a homotopy 1-category.  It does not retain
noninvertible model 2-cells and is not a bicategorical, Dwyer--Kan, simplicial,
or Rezk localization.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Higher

open CategoryTheory
open CategoryTheory.Bicategory

universe u v w u' v' w'

variable {R : Type w} [AddCommMonoid R] [PartialOrder R]

/-- The ordinary homotopy 1-category of resource-indexed process models. -/
abbrev ModelHomotopyCategory (R : Type w) [AddCommMonoid R] [PartialOrder R] :=
  HomotopyCategory (ProcessModel.{u, v, w} R)

/-- The raw bicategorical marking of model morphisms that reflect process
costs.  This property is deliberately representative-sensitive. -/
def costReflectingArrows (R : Type w) [AddCommMonoid R] [PartialOrder R] :
    Bicategory.MorphismProperty (ProcessModel.{u, v, w} R) :=
  fun {_ _} F ↦ CostReflecting F

/-- Cost-reflecting model morphisms contain identities and are closed under
composition. -/
instance costReflectingArrows_isMultiplicative :
    Bicategory.MorphismProperty.IsMultiplicative
      (costReflectingArrows (R := R) :
        Bicategory.MorphismProperty (ProcessModel.{u, v, w} R)) where
  id_mem M := by
    change CostReflecting (ModelHom.id M)
    infer_instance
  comp_mem F G hF hG := by
    let _ : CostReflecting F := hF
    let _ : CostReflecting G := hG
    change CostReflecting (ModelHom.comp F G)
    infer_instance

/-- The cost-exact marking on the bicategory is the closure of raw cost
reflection under invertible monoidal 2-cells. -/
def costExactArrows (R : Type w) [AddCommMonoid R] [PartialOrder R] :
    Bicategory.MorphismProperty (ProcessModel.{u, v, w} R) :=
  (costReflectingArrows R).saturate

/-- A cost-reflecting model morphism is cost-exact. -/
theorem costReflectingArrows_le_costExactArrows :
    ∀ {M N : ProcessModel.{u, v, w} R} (F : ModelHom M N),
      costReflectingArrows R F → costExactArrows R F :=
  fun _ hF ↦ Bicategory.MorphismProperty.mem_saturate _ hF

/-- The exact bicategorical marking is invariant under invertible 2-cells. -/
instance costExactArrows_respectsIso :
    Bicategory.MorphismProperty.RespectsIso
      (costExactArrows (R := R) :
        Bicategory.MorphismProperty (ProcessModel.{u, v, w} R)) :=
  by
    change Bicategory.MorphismProperty.RespectsIso (costReflectingArrows R).saturate
    infer_instance

/-- The exact bicategorical marking contains identities and is closed under
composition. -/
instance costExactArrows_isMultiplicative :
    Bicategory.MorphismProperty.IsMultiplicative
      (costExactArrows (R := R) :
        Bicategory.MorphismProperty (ProcessModel.{u, v, w} R)) :=
  by
    change Bicategory.MorphismProperty.IsMultiplicative (costReflectingArrows R).saturate
    infer_instance

/-- The exact research target for a higher cost-exact localization.  A
pseudofunctor satisfying this predicate must retain the full bicategory of
model 2-cells, send every saturated cost-exact 1-morphism to an adjoint
equivalence, and satisfy the pseudofunctor/strong-transformation/modification
universal property.  No existence claim is bundled into this abbreviation. -/
abbrev IsCostExactBicategoricalLocalization
    {L : Type u'} [Bicategory.{w', v'} L]
    (Q : ProcessModel.{u, v, w} R ⥤ᵖ L) : Prop :=
  Bicategory.MorphismProperty.IsBicategoricalLocalization.{
    _, _, _, u', v', w', u', v', w'} (costExactArrows R) Q

/-- Any genuine higher cost-exact localization inverts the saturated
bicategorical marking by definition. -/
theorem IsCostExactBicategoricalLocalization.map_isEquivalence
    {L : Type u'} [Bicategory.{w', v'} L]
    {Q : ProcessModel.{u, v, w} R ⥤ᵖ L}
    (hQ : IsCostExactBicategoricalLocalization Q)
    {M N : ProcessModel.{u, v, w} R} (F : M ⟶ N)
    (hF : costExactArrows R F) : Bicategory.IsEquivalence (Q.map F) :=
  hQ.inverts F hF

/-- Raw cost reflection is enough for inversion by any genuine higher
cost-exact localization because the higher marking is its explicit
invertible-2-cell saturation. -/
theorem IsCostExactBicategoricalLocalization.map_costReflecting_isEquivalence
    {L : Type u'} [Bicategory.{w', v'} L]
    {Q : ProcessModel.{u, v, w} R ⥤ᵖ L}
    (hQ : IsCostExactBicategoricalLocalization Q)
    {M N : ProcessModel.{u, v, w} R} (F : M ⟶ N)
    (hF : costReflectingArrows R F) : Bicategory.IsEquivalence (Q.map F) :=
  hQ.inverts F (Bicategory.MorphismProperty.mem_saturate _ hF)

/-- The identity pseudofunctor is a higher cost-exact localization exactly in
the degenerate case where every saturated cost-exact model morphism is already
an adjoint equivalence.  Thus any genuinely new formal inverse forces the
localization construction to change the source bicategory nontrivially. -/
theorem costExactIdentity_isBicategoricalLocalization_iff :
    IsCostExactBicategoricalLocalization
      (Pseudofunctor.id (ProcessModel.{u, v, w} R)) ↔
      ∀ {M N : ProcessModel.{u, v, w} R} (F : M ⟶ N),
        costExactArrows R F → Bicategory.IsEquivalence F :=
  Bicategory.MorphismProperty.isBicategoricalLocalization_id_iff
    (costExactArrows R)

/-- Cost-exact arrows in the model homotopy category are the quotient classes
that have a cost-reflecting representative. -/
def costExactMorphisms (R : Type w) [AddCommMonoid R] [PartialOrder R] :
    MorphismProperty (ModelHomotopyCategory.{u, v, w} R) :=
  (costReflectingArrows R).toHomotopy

/-- A represented cost-reflecting model morphism belongs to the marked class. -/
theorem costExactMorphisms_homMk {M N : ProcessModel.{u, v, w} R}
    (F : ModelHom M N) [CostReflecting F] :
    costExactMorphisms R (HomotopyCategory.homMk F) :=
  ⟨F, ‹CostReflecting F›, rfl⟩

/-- A represented model morphism is marked in the homotopy category precisely
when it belongs to the 2-isomorphism-saturated bicategorical marking. -/
theorem costExactMorphisms_homMk_iff {M N : ProcessModel.{u, v, w} R}
    (F : ModelHom M N) :
    costExactMorphisms R (HomotopyCategory.homMk F) ↔ costExactArrows R F :=
  Bicategory.MorphismProperty.toHomotopy_homMk_iff (costReflectingArrows R) F

/-- The marked cost-exact arrows in the homotopy category contain identities
and are closed under composition. -/
instance costExactMorphisms_isMultiplicative :
    (costExactMorphisms R :
      MorphismProperty (ModelHomotopyCategory.{u, v, w} R)).IsMultiplicative :=
  by
    change ((costReflectingArrows R).toHomotopy :
      MorphismProperty (ModelHomotopyCategory.{u, v, w} R)).IsMultiplicative
    infer_instance

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

/-- The canonical higher-to-ordinary bridge: first discard noninvertible
2-cells by passing to the pith, then pass to the homotopy category, and finally
apply the ordinary cost-exact localization functor. -/
noncomputable def costExactPithLocalization (R : Type w) [AddCommMonoid R]
    [PartialOrder R] :
    Pith (ProcessModel.{u, v, w} R) ⥤ᵖ
      LocallyDiscrete (CostExactLocalization.{u, v, w} R) :=
  (HomotopyCategory.pithToHomotopy (ProcessModel.{u, v, w} R)).comp
    (costExactLocalizationFunctor R).toPseudofunctor

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

/-- Every arrow in the saturated bicategorical marking is sent to an
isomorphism by the ordinary localization functor. -/
theorem costExactLocalizationFunctor_map_isIso
    {M N : ProcessModel.{u, v, w} R} (F : ModelHom M N)
    (hF : costExactArrows R F) :
    IsIso ((costExactLocalizationFunctor R).map
      (HomotopyCategory.homMk F)) :=
  costExactLocalizationFunctor_inverts _
    ((costExactMorphisms_homMk_iff F).2 hF)

/-- On the pith, every marked model morphism is mapped to an ordinary
isomorphism.  The statement is about the underlying arrow of the locally
discrete target. -/
theorem costExactPithLocalization_map_isIso
    {M N : Pith (ProcessModel.{u, v, w} R)} (F : M ⟶ N)
    (hF : costExactArrows R F.of) :
    IsIso ((costExactPithLocalization R).map F).as := by
  change IsIso ((costExactLocalizationFunctor R).map
    (HomotopyCategory.homMk F.of))
  exact costExactLocalizationFunctor_map_isIso F.of hF

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
