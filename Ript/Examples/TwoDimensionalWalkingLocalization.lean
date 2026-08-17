import Mathlib.CategoryTheory.Bicategory.SingleObj
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Ript.Examples.WalkingLocalization
import Ript.ForMathlib.CategoryTheory.Bicategory.Product

/-!
# A walking localization that retains a noninvertible 2-cell

This file advances the walking-arrow localization from a locally discrete
slice to a genuinely two-dimensional parameterized slice.  The source is the
product of the locally discrete walking arrow with the single-object
bicategory induced by the cartesian monoidal category of types.  Its second
coordinate therefore has types as 1-morphisms and functions as 2-morphisms.

The localization freely groupoid-completes only the walking-arrow coordinate
and leaves the function-valued coordinate unchanged.  The generating walking
arrow acquires an explicit inverse, while Boolean discard remains a
noninvertible 2-cell.  The pseudofunctor is faithful on every source
2-morphism, and its target is formally proved not to be locally discrete.

This is still a parameterized vertical slice, not the full bicategorical
localization of Ript's resource-process bicategory.  In particular, the
biessential factorization and local-equivalence fields of the general
localization predicate are not claimed here.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Examples.TwoDimensionalWalkingLocalization

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Prod
open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe u v w

/-- A one-object bicategory whose 1-cells are types and whose 2-cells are
functions. -/
abbrev Cell := MonoidalSingleObj (Type)

/-- The walking-arrow source paired with genuine function-valued 2-cells. -/
abbrev Source :=
  LocallyDiscrete Ript.Examples.WalkingLocalization.Arrow × Cell

/-- The free-groupoid completion paired with the unchanged 2-cell
coordinate. -/
abbrev Target :=
  LocallyDiscrete Ript.Examples.WalkingLocalization.Completion × Cell

/-- Localize the walking-arrow coordinate and leave the two-dimensional
coordinate unchanged. -/
noncomputable abbrev inclusion : Source ⥤ᵖ Target :=
  Ript.Examples.WalkingLocalization.inclusion.prod (Pseudofunctor.id Cell)

/-- The source object over the domain of the walking arrow. -/
def sourceZero : Source :=
  (LocallyDiscrete.mk (0 : Ript.Examples.WalkingLocalization.Arrow),
    MonoidalSingleObj.star (Type))

/-- The source object over the codomain of the walking arrow. -/
def sourceOne : Source :=
  (LocallyDiscrete.mk (1 : Ript.Examples.WalkingLocalization.Arrow),
    MonoidalSingleObj.star (Type))

/-- The generating walking arrow paired with the identity in the retained
coordinate. -/
def markedArrow : sourceZero ⟶ sourceOne :=
  Ript.Examples.WalkingLocalization.arrow.toLoc ×ₘ 𝟙 _

/-- Mark every first-coordinate arrow, provided the unchanged second
coordinate is already an adjoint equivalence. -/
def marking : Bicategory.MorphismProperty Source :=
  fun {_ _} f => IsEquivalence f.2

/-- The generating product arrow belongs to the marking. -/
theorem markedArrow_mem : marking markedArrow :=
  Bicategory.isEquivalence_hom (Bicategory.Equivalence.id _)

/-- The parameterized inclusion sends every marked 1-morphism to an adjoint
equivalence. -/
theorem inclusion_inverts : marking.IsInvertedBy inclusion := by
  intro X Y f hf
  obtain ⟨⟨e₁, he₁⟩⟩ :=
    Ript.Examples.WalkingLocalization.inclusion_inverts f.1 trivial
  obtain ⟨⟨e₂, he₂⟩⟩ := hf
  refine ⟨⟨e₁.prod e₂, ?_⟩⟩
  exact Prod.ext he₁ he₂

/-- The marked generator is not an adjoint equivalence before
localization. -/
theorem markedArrow_not_isEquivalence : ¬ IsEquivalence markedArrow := by
  intro h
  obtain ⟨⟨e, he⟩⟩ := h
  have hFirst : IsEquivalence markedArrow.1 := by
    refine ⟨⟨(Bicategory.Prod.fst _ _).mapEquivalence e, ?_⟩⟩
    simpa using congrArg Prod.fst he
  exact Ript.Examples.WalkingLocalization.arrow_not_isEquivalence hFirst

/-- The marked generator is an adjoint equivalence after localization. -/
theorem inclusion_map_markedArrow_isEquivalence :
    IsEquivalence (inclusion.map markedArrow) :=
  inclusion_inverts markedArrow markedArrow_mem

/-- The inverse adjoined in the walking coordinate, paired with the unchanged
identity 1-morphism. -/
noncomputable def inverse : inclusion.obj sourceOne ⟶ inclusion.obj sourceZero :=
  Ript.Examples.WalkingLocalization.inverse ×ₘ 𝟙 _

/-- The localized generator followed by its explicit inverse is
2-isomorphic to the identity. -/
noncomputable def inclusionMapMarkedArrowCompInverseIso :
    inclusion.map markedArrow ≫ inverse ≅ 𝟙 _ :=
  Iso.prod
    (eqToIso Ript.Examples.WalkingLocalization.inclusion_map_arrow_comp_inverse)
    (ρ_ (𝟙 _))

/-- The explicit inverse followed by the localized generator is
2-isomorphic to the identity. -/
noncomputable def inverseCompInclusionMapMarkedArrowIso :
    inverse ≫ inclusion.map markedArrow ≅ 𝟙 _ :=
  Iso.prod
    (eqToIso Ript.Examples.WalkingLocalization.inverse_comp_inclusion_map_arrow)
    (ρ_ (𝟙 _))

/-- A Boolean-valued endomorphism 1-cell supporting a noninvertible discard
2-cell. -/
def boolCell : sourceZero ⟶ sourceZero :=
  𝟙 _ ×ₘ Bool

/-- A unit-valued endomorphism 1-cell. -/
def unitCell : sourceZero ⟶ sourceZero :=
  𝟙 _ ×ₘ PUnit.{1}

/-- Boolean discard as a 2-cell in the retained coordinate. -/
def discardTwoCell : boolCell ⟶ unitCell :=
  𝟙 _ ×ₘ TypeCat.ofHom (fun _ : Bool => PUnit.unit : Bool → PUnit.{1})

/-- Boolean discard is not an invertible 2-cell in the source. -/
theorem discardTwoCell_not_isIso : ¬ IsIso discardTwoCell := by
  intro h
  have hSecond : IsIso discardTwoCell.2 :=
    (isIso_prod_iff (f := discardTwoCell)).1 h |>.2
  have hInjective := (isIso_iff_bijective discardTwoCell.2).1 hSecond |>.1
  change Function.Injective (fun _ : Bool => PUnit.unit) at hInjective
  exact Bool.false_ne_true (hInjective rfl)

/-- The parameterized inclusion is faithful on all source 2-cells. -/
theorem inclusion_map₂_injective {X Y : Source} {f g : X ⟶ Y}
    (η θ : f ⟶ g) (h : inclusion.map₂ η = inclusion.map₂ θ) : η = θ := by
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · have hSecond := congrArg (fun k => k.2) h
    exact hSecond

/-- The image of Boolean discard remains a noninvertible 2-cell. -/
theorem inclusion_map₂_discardTwoCell_not_isIso :
    ¬ IsIso (inclusion.map₂ discardTwoCell) := by
  intro h
  have hSecond : IsIso (inclusion.map₂ discardTwoCell).2 :=
    (isIso_prod_iff (f := inclusion.map₂ discardTwoCell)).1 h |>.2
  have hInjective :=
    (isIso_iff_bijective (inclusion.map₂ discardTwoCell).2).1 hSecond |>.1
  change Function.Injective (fun _ : Bool => PUnit.unit) at hInjective
  exact Bool.false_ne_true (hInjective rfl)

/-- The target remains genuinely two-dimensional rather than becoming
locally discrete. -/
theorem target_not_isLocallyDiscrete : ¬ IsLocallyDiscrete Target := by
  intro h
  let _ : IsDiscrete (inclusion.obj sourceZero ⟶ inclusion.obj sourceZero) := h _ _
  exact inclusion_map₂_discardTwoCell_not_isIso inferInstance

/-- The construction simultaneously adds the missing 1-cell inverse and
retains a genuinely noninvertible 2-cell. -/
theorem inclusion_adds_inverse_and_retains_noninvertible_twoCell :
    (¬ IsEquivalence markedArrow) ∧
      IsEquivalence (inclusion.map markedArrow) ∧
        (¬ IsIso discardTwoCell) ∧
          ¬ IsIso (inclusion.map₂ discardTwoCell) :=
  ⟨markedArrow_not_isEquivalence, inclusion_map_markedArrow_isEquivalence,
    discardTwoCell_not_isIso, inclusion_map₂_discardTwoCell_not_isIso⟩

/-- The parameterized walking localization is surjective on objects.  The
free groupoid adds arrows but no new objects, and the retained coordinate is
unchanged. -/
theorem inclusion_obj_surjective : Function.Surjective inclusion.obj := by
  rintro ⟨⟨X⟩, Y⟩
  rw [CategoryTheory.FreeGroupoid.eq_mk X]
  cases Y
  exact ⟨(LocallyDiscrete.mk X.as.as, MonoidalSingleObj.star (Type)), rfl⟩

section RetainedCoordinateLift

variable {E : Type u} [Bicategory.{w, v} E]

/-- Precomposition by the parameterized walking localization is faithful on
every category of strong transformations and modifications.  This proves the
faithfulness component of the still-open `local_equivalence` field. -/
theorem inclusion_localPrecomposition_faithful
    (F G : Target ⥤ᵖ E) :
    (inclusion.localPrecomposition F G).Faithful :=
  Pseudofunctor.localPrecomposition_faithful_of_obj_surjective
    inclusion inclusion_obj_surjective F G

/-- A source pseudofunctor obtained by applying `H` only to the retained
function-valued coordinate. -/
noncomputable def retainedSource (H : Cell ⥤ᵖ E) : Source ⥤ᵖ E :=
  Pseudofunctor.sndComp
    (LocallyDiscrete Ript.Examples.WalkingLocalization.Arrow) H

/-- The corresponding pseudofunctor on the localization target. -/
noncomputable def retainedLift (H : Cell ⥤ᵖ E) : Target ⥤ᵖ E :=
  Pseudofunctor.sndComp
    (LocallyDiscrete Ript.Examples.WalkingLocalization.Completion) H

/-- Every pseudofunctor which depends only on the retained coordinate sends
the marking to adjoint equivalences. -/
theorem retainedSource_inverts (H : Cell ⥤ᵖ E) :
    marking.IsInvertedBy (retainedSource H) := by
  intro X Y f hf
  obtain ⟨⟨e, he⟩⟩ := hf
  refine ⟨⟨H.mapEquivalence e, ?_⟩⟩
  change H.map e.hom = H.map f.2
  rw [he]

/-- The retained-coordinate source pseudofunctor factors through the
two-dimensional walking localization up to an adjoint equivalence of
pseudofunctors. -/
noncomputable def retainedFactorization (H : Cell ⥤ᵖ E) :
    inclusion.comp (retainedLift H) ≌ retainedSource H :=
  Pseudofunctor.prodIdSndCompEquivalence
    Ript.Examples.WalkingLocalization.inclusion H

/-- A family of concrete witnesses for the `lift` shape in the
bicategorical-localization predicate: every retained-coordinate
pseudofunctor has an explicit factor through the target. -/
theorem retainedSource_has_factorization (H : Cell ⥤ᵖ E) :
    ∃ G : Target ⥤ᵖ E, Nonempty (inclusion.comp G ≌ retainedSource H) :=
  ⟨retainedLift H, ⟨retainedFactorization H⟩⟩

/-- The second projection from the source, retaining all function-valued
2-cells. -/
noncomputable abbrev retainedCoordinate : Source ⥤ᵖ Cell :=
  retainedSource (Pseudofunctor.id Cell)

/-- The second projection from the target, providing the explicit lift of
`retainedCoordinate`. -/
noncomputable abbrev retainedCoordinateLift : Target ⥤ᵖ Cell :=
  retainedLift (Pseudofunctor.id Cell)

/-- The lifted retained coordinate still sees Boolean discard as a
noninvertible 2-cell. -/
theorem retainedCoordinate_map₂_discardTwoCell_not_isIso :
    ¬ IsIso (retainedCoordinate.map₂ discardTwoCell) := by
  intro h
  have hInjective :=
    (isIso_iff_bijective (retainedCoordinate.map₂ discardTwoCell)).1 h |>.1
  change Function.Injective (fun _ : Bool => PUnit.unit) at hInjective
  exact Bool.false_ne_true (hInjective rfl)

/-- One explicit marking-inverting pseudofunctor both factors through the
localization target and retains the chosen noninvertible 2-cell.  This proves
a genuine family of the `lift` obligations without claiming the universal
quantification required by `IsBicategoricalLocalization`. -/
theorem retainedCoordinate_inverts_factors_and_retains_discard :
    marking.IsInvertedBy retainedCoordinate ∧
      (∃ G : Target ⥤ᵖ Cell,
        Nonempty (inclusion.comp G ≌ retainedCoordinate)) ∧
          ¬ IsIso (retainedCoordinate.map₂ discardTwoCell) :=
  ⟨retainedSource_inverts _, retainedSource_has_factorization _,
    retainedCoordinate_map₂_discardTwoCell_not_isIso⟩

end RetainedCoordinateLift

end Ript.Examples.TwoDimensionalWalkingLocalization
