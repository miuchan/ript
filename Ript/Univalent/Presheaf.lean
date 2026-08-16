import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Yoneda
import Ript.Univalent.Completion

/-!
# Presheaf semantics for the internal interface groupoid

This file takes the next Stage-12 step after the truncated object and skeletal
completions.  It embeds the internal interface groupoid into its category of
type-valued presheaves and isolates the full subcategory of presheaves that are
isomorphic to representables.

The construction proves three precise facts.

* The Yoneda embedding is fully faithful, so internal identities are exactly
  natural transformations between the corresponding representable
  presheaves.
* Because the source is a groupoid, those natural transformations are all
  natural isomorphisms.  Internal structural equivalences therefore also
  correspond exactly to natural isomorphisms of representables.
* The essential image, called `YonedaEnvelope`, is categorically equivalent to
  the original groupoid and satisfies the induced equivalence of functor
  categories.

`YonedaEnvelope` is intentionally not called a Rezk completion.  It is an
ordinary 1-categorical essential image inside a presheaf category.  Its
objects still use Lean's external equality, and the construction supplies no
higher paths, Segal objects, localization, or external univalence principle.
The equivalence with the essential image uses chosen witnesses and is confined
to this noncomputable semantic layer.
-/

set_option autoImplicit false

namespace Ript.Univalent

open CategoryTheory

universe u v w

namespace UniverseModel

variable {Atom : Type u} (M : UniverseModel Atom)
variable {A B C : Code Atom}

/-- Type-valued presheaves on the interpreted internal interface groupoid. -/
abbrev PresheafUniverse := M.Objectᵒᵖ ⥤ Type u

/-- The representable presheaf associated with a raw interface code. -/
def representablePresheaf (A : Code Atom) : M.PresheafUniverse :=
  (yoneda (C := M.Object)).obj (⟨A⟩ : M.Object)

/-- The Yoneda embedding of the internal interface groupoid. -/
def yonedaEmbedding : M.Object ⥤ M.PresheafUniverse :=
  yoneda

/-- The internal Yoneda embedding is fully faithful. -/
def yonedaEmbeddingFullyFaithful : (yonedaEmbedding M).FullyFaithful :=
  Yoneda.fullyFaithful

/-- The internal Yoneda embedding is full. -/
instance yonedaEmbeddingFull : (yonedaEmbedding M).Full :=
  (yonedaEmbeddingFullyFaithful M).full

/-- The internal Yoneda embedding is faithful. -/
instance yonedaEmbeddingFaithful : (yonedaEmbedding M).Faithful :=
  (yonedaEmbeddingFullyFaithful M).faithful

/-- Sections of the representable at `A`, evaluated at `B`, are exactly
internal identities from `B` to `A`.  The direction records presheaf
contravariance. -/
def representableSectionEquiv (A B : Code Atom) :
    (representablePresheaf M A).obj (Opposite.op (⟨B⟩ : M.Object)) ≃
      M.Identity B A :=
  Equiv.refl _

/-- Internal identities are exactly natural transformations between the
corresponding representable presheaves. -/
def representableTransformationEquiv (A B : Code Atom) :
    M.Identity A B ≃
      (representablePresheaf M A ⟶ representablePresheaf M B) :=
  (yonedaEmbeddingFullyFaithful M).homEquiv

@[simp]
theorem representableTransformationEquiv_apply (path : M.Identity A B) :
    representableTransformationEquiv M A B path =
      (yonedaEmbedding M).map path :=
  rfl

/-- Internal reflexivity is sent to the identity natural transformation. -/
@[simp]
theorem representableTransformationEquiv_refl (A : Code Atom) :
    (yonedaEmbedding M).map (Identity.refl M A) =
      𝟙 (representablePresheaf M A) := by
  change (yoneda (C := M.Object)).map (𝟙 (⟨A⟩ : M.Object)) =
    𝟙 ((yoneda (C := M.Object)).obj (⟨A⟩ : M.Object))
  exact Functor.map_id _ _

/-- Internal path composition is sent to vertical composition of natural
transformations. -/
@[simp]
theorem representableTransformationEquiv_trans
    (first : M.Identity A B) (second : M.Identity B C) :
    (yonedaEmbedding M).map (Identity.trans M first second) =
      (yonedaEmbedding M).map first ≫ (yonedaEmbedding M).map second := by
  change (yoneda (C := M.Object)).map (first ≫ second) =
    (yoneda (C := M.Object)).map first ≫ (yoneda (C := M.Object)).map second
  exact Functor.map_comp _ _ _

/-- In the internal groupoid, an identity morphism and an isomorphism of
interpreted interface objects carry exactly the same data. -/
def identityIsoEquiv (A B : Code Atom) :
    M.Identity A B ≃ ((⟨A⟩ : M.Object) ≅ (⟨B⟩ : M.Object)) :=
  (Groupoid.isoEquivHom (⟨A⟩ : M.Object) (⟨B⟩ : M.Object)).symm

/-- Internal identities are exactly natural isomorphisms between
representable presheaves. -/
def representableNaturalIsoEquiv (A B : Code Atom) :
    M.Identity A B ≃
      (representablePresheaf M A ≅ representablePresheaf M B) :=
  (identityIsoEquiv M A B).trans
    (yonedaEmbeddingFullyFaithful M).isoEquiv

/-- By internal univalence, internal structural equivalences are exactly
natural isomorphisms between representable presheaves. -/
def representableEquivNaturalIsoEquiv (A B : Code Atom) :
    M.InternalEquiv A B ≃
      (representablePresheaf M A ≅ representablePresheaf M B) :=
  (internalUnivalence M A B).symm.trans
    (representableNaturalIsoEquiv M A B)

/-- Every natural transformation between internal representables is an
isomorphism, because Yoneda is fully faithful and the source is a groupoid. -/
theorem representableTransformation_isIso
    (η : representablePresheaf M A ⟶ representablePresheaf M B) :
    IsIso η := by
  let path := (representableTransformationEquiv M A B).symm η
  have hη : (yonedaEmbedding M).map path = η :=
    (representableTransformationEquiv M A B).apply_symm_apply η
  rw [← hη]
  change IsIso ((yoneda (C := M.Object)).map path)
  infer_instance

/-- The full subcategory of presheaves isomorphic to internal
representables.  This is the ordinary categorical Yoneda envelope, not a
higher or externally univalent completion. -/
abbrev YonedaEnvelope := (yonedaEmbedding M).EssImageSubcategory

/-- Factor the Yoneda embedding through its essential image. -/
def toYonedaEnvelope : M.Object ⥤ M.YonedaEnvelope :=
  (yonedaEmbedding M).toEssImage

/-- Include the Yoneda envelope into the full presheaf universe. -/
def yonedaEnvelopeInclusion : M.YonedaEnvelope ⥤ M.PresheafUniverse :=
  (yonedaEmbedding M).essImage.ι

/-- The essential-image factorization recovers the original Yoneda
embedding up to natural isomorphism. -/
def yonedaEnvelopeFactorization :
    toYonedaEnvelope M ⋙ yonedaEnvelopeInclusion M ≅ yonedaEmbedding M :=
  (yonedaEmbedding M).toEssImageCompι

/-- The fully faithful Yoneda embedding becomes an equivalence after its
codomain is restricted to the essential image. -/
noncomputable instance toYonedaEnvelopeIsEquivalence :
    (toYonedaEnvelope M).IsEquivalence := by
  change ((yonedaEmbedding M).toEssImage).IsEquivalence
  infer_instance

/-- The original internal groupoid is categorically equivalent to its Yoneda
essential-image envelope. -/
noncomputable def yonedaEnvelopeEquivalence : M.Object ≌ M.YonedaEnvelope :=
  (toYonedaEnvelope M).asEquivalence

/-- The Yoneda envelope is a groupoid: every morphism between essentially
representable presheaves is invertible. -/
noncomputable instance yonedaEnvelopeGroupoid : Groupoid M.YonedaEnvelope :=
  Groupoid.ofFullyFaithfulToGroupoid
    (yonedaEnvelopeEquivalence M).inverse
    (yonedaEnvelopeEquivalence M).fullyFaithfulInverse

/-- Categorical universal consequence of the Yoneda-envelope equivalence:
for every target category, the two functor categories are equivalent. -/
noncomputable def yonedaEnvelopeUniversal
    (E : Type v) [Category.{w} E] :
    (M.YonedaEnvelope ⥤ E) ≌ (M.Object ⥤ E) :=
  (yonedaEnvelopeEquivalence M).symm.congrLeft

end UniverseModel

end Ript.Univalent
