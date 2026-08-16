import Mathlib.CategoryTheory.Localization.Predicate
import Ript.Univalent.Presheaf

/-!
# One-categorical localization of the internal interface groupoid

The internal interface category is already a groupoid: its morphisms are
internal identities, and every such identity has an inverse.  Consequently
localizing at all of its morphisms does not add new arrows.  Mathlib's
`Functor.IsLocalization` API makes that precise and supplies the full functor-
category universal property.

This file proves that three concrete functors are localization models for the
property of being an internal identity morphism:

* the identity functor on the interface groupoid;
* the functor to its categorical skeleton;
* the fully faithful Yoneda functor with codomain restricted to the essential
  image of representables.

The last two results upgrade the earlier bare equivalences of functor
categories: their forward functors are now identified as precomposition with
actual localization functors, and their codomain records the obligation to
invert every internal identity.

This is an exact ordinary-category localization theorem for an already
groupoidal source.  It is not a localization of the full resource-process
bicategory, a presheaf localization, or a higher/Rezk universal property.
-/

set_option autoImplicit false

namespace Ript.Univalent

open CategoryTheory

universe u v w

namespace UniverseModel

variable {Atom : Type u} (M : UniverseModel Atom)

/-- The morphism property consisting of every internal identity morphism.
Every morphism of `M.Object` has this meaning by construction. -/
abbrev InterfaceIdentities : MorphismProperty M.Object :=
  ⊤

/-- Since the interface category is a groupoid, its internal identity
morphisms are exactly its isomorphisms. -/
theorem interfaceIdentities_eq_isomorphisms :
    M.InterfaceIdentities = MorphismProperty.isomorphisms M.Object := by
  symm
  exact (isGroupoid_iff_isomorphisms_eq_top M.Object).1 inferInstance

/-- Every internal identity belongs to the isomorphism morphism property. -/
theorem interfaceIdentities_le_isomorphisms :
    M.InterfaceIdentities ≤ MorphismProperty.isomorphisms M.Object := by
  rw [interfaceIdentities_eq_isomorphisms]

/-- Every functor out of the interface groupoid inverts all internal
identities.  This is a theorem, not an extra condition imposed on targets. -/
theorem interfaceIdentities_isInvertedBy
    {E : Type v} [Category.{w} E] (F : M.Object ⥤ E) :
    M.InterfaceIdentities.IsInvertedBy F := by
  intro X Y f _
  have : IsIso f := inferInstance
  infer_instance

/-- The identity functor is a localization of the interface groupoid at all
internal identities. -/
noncomputable instance interfaceIdentityIsLocalization :
    (𝟭 M.Object).IsLocalization M.InterfaceIdentities :=
  Functor.IsLocalization.for_id M.InterfaceIdentities
    (interfaceIdentities_le_isomorphisms M)

/-- Strict fixed-target form of the identity-localization universal property. -/
def interfaceIdentityStrictUniversalProperty
    (E : Type v) [Category.{w} E] :
    Localization.StrictUniversalPropertyFixedTarget
      (𝟭 M.Object) M.InterfaceIdentities E :=
  Localization.strictUniversalPropertyFixedTargetId
    M.InterfaceIdentities E (interfaceIdentities_le_isomorphisms M)

/-- Precomposition with the identity localization identifies all functors out
of the interface groupoid with the full subcategory of functors that invert
every internal identity. -/
noncomputable def interfaceIdentityLocalizationUniversal
    (E : Type v) [Category.{w} E] :
    (M.Object ⥤ E) ≌ M.InterfaceIdentities.FunctorsInverting E :=
  Localization.functorEquivalence (𝟭 M.Object) M.InterfaceIdentities E

/-- The functor to the categorical skeleton is the inverse functor of
Mathlib's skeleton equivalence. -/
noncomputable instance toSkeletalCompletionIsEquivalence :
    (toSkeletalCompletion M).IsEquivalence := by
  change (CategoryTheory.skeletonEquivalence M.Object).inverse.IsEquivalence
  infer_instance

/-- The categorical skeleton functor is a localization model for all internal
identities.  It is an equivalence, so no morphism information is discarded. -/
noncomputable instance toSkeletalCompletionIsLocalization :
    (toSkeletalCompletion M).IsLocalization M.InterfaceIdentities :=
  Functor.IsLocalization.of_isEquivalence
    (toSkeletalCompletion M) M.InterfaceIdentities
    (interfaceIdentities_le_isomorphisms M)

/-- Universal property of the skeletal completion in localization form.  The
forward functor is precomposition with `toSkeletalCompletion M`. -/
noncomputable def skeletalCompletionLocalizationUniversal
    (E : Type v) [Category.{w} E] :
    (M.SkeletalCompletion ⥤ E) ≌
      M.InterfaceIdentities.FunctorsInverting E :=
  Localization.functorEquivalence
    (toSkeletalCompletion M) M.InterfaceIdentities E

/-- The Yoneda essential-image functor is a localization model for all
internal identities.  Its target is restricted to representables, so the
functor is an equivalence rather than a localization into the whole presheaf
category. -/
noncomputable instance toYonedaEnvelopeIsLocalization :
    (toYonedaEnvelope M).IsLocalization M.InterfaceIdentities :=
  Functor.IsLocalization.of_isEquivalence
    (toYonedaEnvelope M) M.InterfaceIdentities
    (interfaceIdentities_le_isomorphisms M)

/-- Universal property of the Yoneda envelope in localization form.  For any
target category `E`, precomposition with `toYonedaEnvelope M` is an
equivalence onto the functors that invert every internal identity. -/
noncomputable def yonedaEnvelopeLocalizationUniversal
    (E : Type v) [Category.{w} E] :
    (M.YonedaEnvelope ⥤ E) ≌
      M.InterfaceIdentities.FunctorsInverting E :=
  Localization.functorEquivalence
    (toYonedaEnvelope M) M.InterfaceIdentities E

end UniverseModel

end Ript.Univalent
