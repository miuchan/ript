import Mathlib.CategoryTheory.Bicategory.SingleObj
import Mathlib.CategoryTheory.CodiscreteCategory
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.Tactic.FinCases
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

The freely completed walking coordinate is further normalized here: every
arrow is uniquely determined by its two endpoints, and the completion is
equivalent to the codiscrete groupoid on `Fin 2`.  This removes path ambiguity
without making the product target locally discrete, because the retained
function-valued coordinate still has noninvertible 2-cells.

This is still a parameterized vertical slice, not the full bicategorical
localization of Ript's resource-process bicategory.  Local precomposition is
fully faithful.  For the next local-essential-surjectivity step, the source
constraints now determine strong-naturality isomorphisms for every target
1-morphism: forward arrows reuse source naturality with arbitrary retained
coordinates, while reverse arrows use an explicit invertible mate.  The
identity coherence law is now proved, as is 2-cell naturality for every
endpoint-normalized arrow, including the freely adjoined inverse.  The
endpoint constraint is now also proved equal to the canonical identity
constraint, so the public all-arrow constraint is natural across its strict
identity branch.  Composition coherence is proved whenever both arrows lie
in the inclusion image, and hence for every canonical forward-forward pair.
The mixed cases involving the freely adjoined inverse, local essential
surjectivity, and arbitrary nonseparable biessential factorization remain
open.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Examples.TwoDimensionalWalkingLocalization

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Prod
open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe u v w u₂ v₂ w₂

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

section LocalizedCoordinateLift

variable {G : Type u} [Groupoid.{v} G]

/-- A source pseudofunctor obtained from an arbitrary functor out of the
walking arrow while ignoring the retained coordinate.  The groupoid target
makes every image 1-morphism an adjoint equivalence. -/
noncomputable def localizedCoordinateSource
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G) :
    Source ⥤ᵖ LocallyDiscrete G :=
  Pseudofunctor.fstComp Cell K.toPseudofunctor

/-- Extend a groupoid-valued walking-arrow functor across the freely adjoined
inverse, then ignore the retained coordinate. -/
noncomputable def localizedCoordinateLift
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G) :
    Target ⥤ᵖ LocallyDiscrete G :=
  Pseudofunctor.fstComp Cell
    (CategoryTheory.FreeGroupoid.lift K).toPseudofunctor

/-- The forward strong transformation witnessing the free-groupoid
factorization of a localized-coordinate pseudofunctor. -/
noncomputable def localizedCoordinateFactorizationHom
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G) :
    inclusion.comp (localizedCoordinateLift K) ⟶
      localizedCoordinateSource K where
  app X := 𝟙 _
  naturality f := eqToIso (by
    apply Discrete.ext
    change (CategoryTheory.FreeGroupoid.lift K).map
        ((CategoryTheory.FreeGroupoid.of _).map f.1.as) ≫ 𝟙 _ =
      𝟙 _ ≫ K.map f.1.as
    simp)
  naturality_naturality η := by cat_disch
  naturality_id X := by cat_disch
  naturality_comp f g := by cat_disch

/-- The inverse strong transformation for the free-groupoid factorization. -/
noncomputable def localizedCoordinateFactorizationInv
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G) :
    localizedCoordinateSource K ⟶
      inclusion.comp (localizedCoordinateLift K) where
  app X := 𝟙 _
  naturality f := eqToIso (by
    apply Discrete.ext
    change K.map f.1.as ≫ 𝟙 _ =
      𝟙 _ ≫ (CategoryTheory.FreeGroupoid.lift K).map
        ((CategoryTheory.FreeGroupoid.of _).map f.1.as)
    simp)
  naturality_naturality η := by cat_disch
  naturality_id X := by cat_disch
  naturality_comp f g := by cat_disch

/-- Every groupoid-valued pseudofunctor depending only on the coordinate
being localized factors through the two-dimensional walking localization up
to an adjoint equivalence of pseudofunctors. -/
noncomputable def localizedCoordinateFactorization
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G) :
    inclusion.comp (localizedCoordinateLift K) ≌
      localizedCoordinateSource K :=
  Bicategory.Equivalence.mkOfAdjointifyCounit
    (Pseudofunctor.StrongTrans.isoMk
      (η := 𝟙 (inclusion.comp (localizedCoordinateLift K)))
      (θ := localizedCoordinateFactorizationHom K ≫
        localizedCoordinateFactorizationInv K)
      (fun X =>
        (ρ_ (𝟙 ((inclusion.comp (localizedCoordinateLift K)).obj X))).symm)
      (by
        intro a b f
        dsimp [localizedCoordinateFactorizationHom,
          localizedCoordinateFactorizationInv]
        cat_disch))
    (Pseudofunctor.StrongTrans.isoMk
      (η := localizedCoordinateFactorizationInv K ≫
        localizedCoordinateFactorizationHom K)
      (θ := 𝟙 (localizedCoordinateSource K))
      (fun X => ρ_ (𝟙 ((localizedCoordinateSource K).obj X)))
      (by
        intro a b f
        dsimp [localizedCoordinateFactorizationHom,
          localizedCoordinateFactorizationInv]
        cat_disch))

/-- Every groupoid-valued localized-coordinate pseudofunctor inverts the
whole product marking. -/
theorem localizedCoordinateSource_inverts
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G) :
    marking.IsInvertedBy (localizedCoordinateSource K) := by
  intro X Y f _
  exact LocallyDiscrete.isEquivalence_of_groupoid _

/-- A second, orthogonal family of witnesses for the `lift` shape: arbitrary
groupoid-valued functors of the coordinate being localized factor through
the target.  Unlike `retainedSource_has_factorization`, this family uses the
formal inverse adjoined by the free groupoid. -/
theorem localizedCoordinateSource_has_factorization
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G) :
    ∃ H : Target ⥤ᵖ LocallyDiscrete G,
      Nonempty (inclusion.comp H ≌ localizedCoordinateSource K) :=
  ⟨localizedCoordinateLift K, ⟨localizedCoordinateFactorization K⟩⟩

/-- The extended pseudofunctor sends the formally adjoined inverse to the
actual inverse of the original walking-arrow image. -/
theorem localizedCoordinateLift_map_inverse
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G) :
    (localizedCoordinateLift K).map inverse =
      (inv (K.map Ript.Examples.WalkingLocalization.arrow)).toLoc := by
  apply Discrete.ext
  change (CategoryTheory.FreeGroupoid.lift K).map
      (inv (CategoryTheory.FreeGroupoid.homMk
        Ript.Examples.WalkingLocalization.arrow)) =
    inv (K.map Ript.Examples.WalkingLocalization.arrow)
  simp

/-- A groupoid-valued pseudofunctor of the localized coordinate both
inverts the marking and factors through the target, with the new inverse
mapped to the chosen groupoid inverse. -/
theorem localizedCoordinate_inverts_factors_and_maps_inverse
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G) :
    marking.IsInvertedBy (localizedCoordinateSource K) ∧
      (∃ H : Target ⥤ᵖ LocallyDiscrete G,
        Nonempty (inclusion.comp H ≌ localizedCoordinateSource K)) ∧
      (localizedCoordinateLift K).map inverse =
        (inv (K.map Ript.Examples.WalkingLocalization.arrow)).toLoc :=
  ⟨localizedCoordinateSource_inverts K,
    localizedCoordinateSource_has_factorization K,
    localizedCoordinateLift_map_inverse K⟩

end LocalizedCoordinateLift

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

/-- Choose the unique source object underlying a target object.  The free
groupoid completion changes 1-morphisms but not objects. -/
def sourceOfTarget : Target → Source
  | ⟨⟨X⟩, _⟩ =>
      (LocallyDiscrete.mk X.as.as, MonoidalSingleObj.star (Type))

/-- The canonical source object maps back to the target object from which it
was extracted. -/
theorem inclusion_obj_sourceOfTarget (X : Target) :
    inclusion.obj (sourceOfTarget X) = X := by
  rcases X with ⟨⟨X⟩, Y⟩
  rw [CategoryTheory.FreeGroupoid.eq_mk X]
  cases Y
  rfl

variable {F G : Target ⥤ᵖ E} {η θ : F ⟶ G}

/-- Recover a candidate target modification component from a modification
after precomposition, using the canonical source representative of the
target object. -/
noncomputable def liftedModificationApp
    (Γ : (inclusion.localPrecomposition F G).obj η ⟶
      (inclusion.localPrecomposition F G).obj θ)
    (X : Target) : η.app X ⟶ θ.app X := by
  rw [← inclusion_obj_sourceOfTarget X]
  exact Γ.as.app (sourceOfTarget X)

/-- Recovered modification components restrict to the original components
on source objects. -/
theorem liftedModificationApp_inclusionObj
    (Γ : (inclusion.localPrecomposition F G).obj η ⟶
      (inclusion.localPrecomposition F G).obj θ)
    (X : Source) :
    liftedModificationApp Γ (inclusion.obj X) = Γ.as.app X := by
  rcases X with ⟨⟨X⟩, Y⟩
  cases Y
  rfl

/-- The recovered components satisfy naturality on every 1-morphism in the
image of the inclusion. -/
theorem liftedModificationApp_naturality_map
    (Γ : (inclusion.localPrecomposition F G).obj η ⟶
      (inclusion.localPrecomposition F G).obj θ)
    {X Y : Source} (f : X ⟶ Y) :
    Pseudofunctor.StrongTrans.NaturalityAt η θ
      (liftedModificationApp Γ) (inclusion.map f) := by
  simp only [Pseudofunctor.StrongTrans.NaturalityAt]
  rw [liftedModificationApp_inclusionObj,
    liftedModificationApp_inclusionObj]
  exact Γ.as.naturality f

/-- The canonical source object over a walking-arrow endpoint. -/
def canonicalSourceObject
    (X : Ript.Examples.WalkingLocalization.Arrow) : Source :=
  (LocallyDiscrete.mk X, MonoidalSingleObj.star (Type))

/-- The corresponding canonical object after free-groupoid completion. -/
def canonicalTargetObject
    (X : Ript.Examples.WalkingLocalization.Arrow) : Target :=
  (LocallyDiscrete.mk (CategoryTheory.FreeGroupoid.mk X),
    MonoidalSingleObj.star (Type))

/-- A source walking arrow equipped with an arbitrary retained-coordinate
1-morphism. -/
def canonicalSourceHom
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    canonicalSourceObject X ⟶ canonicalSourceObject Y :=
  f.toLoc ×ₘ A

/-- The canonical forward image of a source arrow with an arbitrary retained
coordinate. -/
def canonicalForwardHom
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    canonicalTargetObject X ⟶ canonicalTargetObject Y :=
  (CategoryTheory.FreeGroupoid.homMk f).toLoc ×ₘ A

/-- The target adjoint equivalence generated by a walking-arrow morphism,
with the retained coordinate fixed at the identity. -/
noncomputable def generatorEquivalence
    {X Y : Ript.Examples.WalkingLocalization.Arrow} (f : X ⟶ Y) :
    (LocallyDiscrete.mk (CategoryTheory.FreeGroupoid.mk X),
        MonoidalSingleObj.star (Type)) ≌
      (LocallyDiscrete.mk (CategoryTheory.FreeGroupoid.mk Y),
        MonoidalSingleObj.star (Type)) :=
  (LocallyDiscrete.equivalenceOfIsIso
    (CategoryTheory.FreeGroupoid.homMk f)).prod
      (Bicategory.Equivalence.id _)

/-- The generator equivalence has the expected forward product morphism. -/
@[simp]
theorem generatorEquivalence_hom
    {X Y : Ript.Examples.WalkingLocalization.Arrow} (f : X ⟶ Y) :
    (generatorEquivalence f).hom =
      (CategoryTheory.FreeGroupoid.homMk f).toLoc ×ₘ 𝟙 _ :=
  rfl

/-- The generator equivalence has the freely adjoined inverse as its inverse
product morphism. -/
@[simp]
theorem generatorEquivalence_inv
    {X Y : Ript.Examples.WalkingLocalization.Arrow} (f : X ⟶ Y) :
    (generatorEquivalence f).inv =
      (inv (CategoryTheory.FreeGroupoid.homMk f)).toLoc ×ₘ 𝟙 _ :=
  rfl

/-- Recover the object component of a prospective target strong
transformation from a strong transformation after precomposition.  The free
groupoid completion changes arrows but not objects. -/
noncomputable def liftedStrongTransApp
    (σ : inclusion.comp F ⟶ inclusion.comp G) (X : Target) :
    F.obj X ⟶ G.obj X := by
  rw [← inclusion_obj_sourceOfTarget X]
  exact σ.app (sourceOfTarget X)

/-- Recovered strong-transformation components restrict exactly to the source
components on objects in the image of the inclusion. -/
@[simp]
theorem liftedStrongTransApp_inclusionObj
    (σ : inclusion.comp F ⟶ inclusion.comp G) (X : Source) :
    liftedStrongTransApp σ (inclusion.obj X) = σ.app X := by
  rcases X with ⟨⟨X⟩, Y⟩
  cases Y
  rfl

/-- Source strong naturality transports directly to every canonical forward
target arrow, with no restriction on its retained-coordinate 1-morphism. -/
noncomputable def liftedStrongTransForwardNaturality
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    F.map (canonicalForwardHom f A) ≫
        liftedStrongTransApp σ (canonicalTargetObject Y) ≅
      liftedStrongTransApp σ (canonicalTargetObject X) ≫
        G.map (canonicalForwardHom f A) := by
  change F.map (canonicalForwardHom f A) ≫
      σ.app (canonicalSourceObject Y) ≅
    σ.app (canonicalSourceObject X) ≫ G.map (canonicalForwardHom f A)
  exact σ.naturality (canonicalSourceHom f A)

/-- The canonical forward constraint is definitionally the original source
strong-naturality constraint. -/
theorem liftedStrongTransForwardNaturality_eq_source
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    liftedStrongTransForwardNaturality σ f A =
      σ.naturality (canonicalSourceHom f A) :=
  rfl

/-- A retained-coordinate 2-morphism between canonical source arrows with a
fixed walking coordinate. -/
def canonicalSourceTwoCell
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    canonicalSourceHom f A ⟶ canonicalSourceHom f B :=
  (𝟙 _, η)

/-- The corresponding retained-coordinate 2-morphism between canonical
forward target arrows. -/
def canonicalForwardTwoCell
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    canonicalForwardHom f A ⟶ canonicalForwardHom f B :=
  (𝟙 _, η)

/-- Forward lifted constraints are natural in every retained-coordinate
2-morphism. -/
theorem liftedStrongTransForwardNaturality_naturality
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    F.map₂ (canonicalForwardTwoCell f η) ▷
          liftedStrongTransApp σ (canonicalTargetObject Y) ≫
          (liftedStrongTransForwardNaturality σ f B).hom =
      (liftedStrongTransForwardNaturality σ f A).hom ≫
        liftedStrongTransApp σ (canonicalTargetObject X) ◁
          G.map₂ (canonicalForwardTwoCell f η) :=
  σ.naturality_naturality (canonicalSourceTwoCell f η)

/-- The source naturality isomorphism at a walking generator transports to
the corresponding forward generator in the completion. -/
noncomputable def liftedStrongTransGeneratorNaturality
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow} (f : X ⟶ Y) :
    F.map (generatorEquivalence f).hom ≫
        liftedStrongTransApp σ
          (LocallyDiscrete.mk (CategoryTheory.FreeGroupoid.mk Y),
            MonoidalSingleObj.star (Type)) ≅
      liftedStrongTransApp σ
          (LocallyDiscrete.mk (CategoryTheory.FreeGroupoid.mk X),
            MonoidalSingleObj.star (Type)) ≫
        G.map (generatorEquivalence f).hom := by
  change F.map (generatorEquivalence f).hom ≫
      σ.app (LocallyDiscrete.mk Y, MonoidalSingleObj.star (Type)) ≅
    σ.app (LocallyDiscrete.mk X, MonoidalSingleObj.star (Type)) ≫
      G.map (generatorEquivalence f).hom
  exact Pseudofunctor.StrongTrans.naturalityIsoOfIso F G _ _
    (σ.naturality
      (f.toLoc ×ₘ 𝟙 (MonoidalSingleObj.star (Type))))
    (Iso.prod (Iso.refl _)
      ((Pseudofunctor.id Cell).mapId (MonoidalSingleObj.star (Type))))

/-- The forward generator constraint canonically determines an invertible
strong-naturality constraint at the freely adjoined inverse.  This is the
object-level extension datum needed for local essential surjectivity; the
remaining obligation is compatibility with all retained-coordinate arrows
and compositions. -/
noncomputable def liftedStrongTransGeneratorInverseNaturality
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow} (f : X ⟶ Y) :
    F.map (generatorEquivalence f).inv ≫
        liftedStrongTransApp σ
          (LocallyDiscrete.mk (CategoryTheory.FreeGroupoid.mk X),
            MonoidalSingleObj.star (Type)) ≅
      liftedStrongTransApp σ
          (LocallyDiscrete.mk (CategoryTheory.FreeGroupoid.mk Y),
            MonoidalSingleObj.star (Type)) ≫
        G.map (generatorEquivalence f).inv :=
  Pseudofunctor.StrongTrans.inverseNaturalityIso F G
    (generatorEquivalence f) _ _
      (liftedStrongTransGeneratorNaturality σ f)

/-- The hom of the inverse-generator constraint is exactly the bicategorical
mate of the inverse forward constraint. -/
theorem liftedStrongTransGeneratorInverseNaturality_hom
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow} (f : X ⟶ Y) :
    (liftedStrongTransGeneratorInverseNaturality σ f).hom =
      mateEquiv
        (F.mapAdjunction (generatorEquivalence f).toAdjunction)
        (G.mapAdjunction (generatorEquivalence f).toAdjunction)
        (liftedStrongTransGeneratorNaturality σ f).inv :=
  Pseudofunctor.StrongTrans.inverseNaturalityIso_hom F G
    (generatorEquivalence f) _ _ _

/-- The canonical inverse target arrow with an arbitrary retained-coordinate
1-morphism. -/
noncomputable def canonicalInverseHom
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    canonicalTargetObject Y ⟶ canonicalTargetObject X :=
  (inv (CategoryTheory.FreeGroupoid.homMk f)).toLoc ×ₘ A

/-- A retained-coordinate 2-morphism between canonical inverse target
arrows. -/
noncomputable def canonicalInverseTwoCell
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    canonicalInverseHom f A ⟶ canonicalInverseHom f B :=
  (𝟙 _, η)

/-- Composing the inverse generator with a retained-coordinate endomorphism
is canonically isomorphic to the corresponding inverse target arrow. -/
noncomputable def canonicalInverseComparison
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (generatorEquivalence f).inv ≫ canonicalForwardHom (𝟙 X) A ≅
      canonicalInverseHom f A :=
  Iso.prod (eqToIso (by
    apply Discrete.ext
    change inv (CategoryTheory.FreeGroupoid.homMk f) ≫
        CategoryTheory.FreeGroupoid.homMk (𝟙 X) =
      inv (CategoryTheory.FreeGroupoid.homMk f)
    simp))
    (by
      change (𝟙 (MonoidalSingleObj.star (Type))) ≫ A ≅ A
      exact MonoidalCategory.leftUnitor A)

/-- The inverse-arrow comparison is natural in every retained-coordinate
2-morphism. -/
theorem canonicalInverseComparison_naturality
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    (canonicalInverseComparison f A).hom ≫
        canonicalInverseTwoCell f η =
      ((generatorEquivalence f).inv ◁
          canonicalForwardTwoCell (𝟙 X) η) ≫
        (canonicalInverseComparison f B).hom := by
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · change (@leftUnitor Cell _ _ _ A).hom ≫ η =
      (𝟙 (MonoidalSingleObj.star (Type)) ◁ η) ≫
        (@leftUnitor Cell _ _ _ B).hom
    exact (leftUnitor_naturality (B := Cell) η).symm

/-- Compose the inverse-generator mate with the retained-coordinate
constraint before transporting along `canonicalInverseComparison`. -/
noncomputable def liftedStrongTransInverseCompositeNaturality
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    F.map ((generatorEquivalence f).inv ≫
          canonicalForwardHom (𝟙 X) A) ≫
        liftedStrongTransApp σ (canonicalTargetObject X) ≅
      liftedStrongTransApp σ (canonicalTargetObject Y) ≫
        G.map ((generatorEquivalence f).inv ≫
          canonicalForwardHom (𝟙 X) A) :=
  Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
    (generatorEquivalence f).inv
    (canonicalForwardHom (𝟙 X) A)
    (liftedStrongTransApp σ (canonicalTargetObject Y))
    (liftedStrongTransApp σ (canonicalTargetObject X))
    (liftedStrongTransApp σ (canonicalTargetObject X))
    (liftedStrongTransGeneratorInverseNaturality σ f)
    (liftedStrongTransForwardNaturality σ (𝟙 X) A)

/-- The composite inverse constraint is natural in every retained-coordinate
2-morphism. -/
theorem liftedStrongTransInverseCompositeNaturality_naturality
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    F.map₂ ((generatorEquivalence f).inv ◁
          canonicalForwardTwoCell (𝟙 X) η) ▷
          liftedStrongTransApp σ (canonicalTargetObject X) ≫
        (liftedStrongTransInverseCompositeNaturality σ f B).hom =
      (liftedStrongTransInverseCompositeNaturality σ f A).hom ≫
        liftedStrongTransApp σ (canonicalTargetObject Y) ◁
          G.map₂ ((generatorEquivalence f).inv ◁
            canonicalForwardTwoCell (𝟙 X) η) :=
  Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos_naturality_right
    F G (generatorEquivalence f).inv
      (canonicalForwardTwoCell (𝟙 X) η)
      (liftedStrongTransApp σ (canonicalTargetObject Y))
      (liftedStrongTransApp σ (canonicalTargetObject X))
      (liftedStrongTransApp σ (canonicalTargetObject X))
      (liftedStrongTransGeneratorInverseNaturality σ f)
      (liftedStrongTransForwardNaturality σ (𝟙 X) A)
      (liftedStrongTransForwardNaturality σ (𝟙 X) B)
      (liftedStrongTransForwardNaturality_naturality σ (𝟙 X) η)

/-- Extend the inverse-generator mate to an arbitrary retained-coordinate
1-morphism.  The inverse constraint is composed with source naturality at the
endpoint and then transported across the product left unitor. -/
noncomputable def liftedStrongTransInverseNaturality
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    F.map (canonicalInverseHom f A) ≫
        liftedStrongTransApp σ (canonicalTargetObject X) ≅
      liftedStrongTransApp σ (canonicalTargetObject Y) ≫
        G.map (canonicalInverseHom f A) :=
  Pseudofunctor.StrongTrans.naturalityIsoOfIso F G _ _
    (liftedStrongTransInverseCompositeNaturality σ f A)
    (canonicalInverseComparison f A)

/-- Lifted constraints on inverse target arrows are natural in every
retained-coordinate 2-morphism. -/
theorem liftedStrongTransInverseNaturality_naturality
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    F.map₂ (canonicalInverseTwoCell f η) ▷
          liftedStrongTransApp σ (canonicalTargetObject X) ≫
        (liftedStrongTransInverseNaturality σ f B).hom =
      (liftedStrongTransInverseNaturality σ f A).hom ≫
        liftedStrongTransApp σ (canonicalTargetObject Y) ◁
          G.map₂ (canonicalInverseTwoCell f η) := by
  exact Pseudofunctor.StrongTrans.naturalityIsoOfIso_naturality F G
    ((generatorEquivalence f).inv ◁
      canonicalForwardTwoCell (𝟙 X) η)
    (canonicalInverseTwoCell f η)
    (liftedStrongTransApp σ (canonicalTargetObject Y))
    (liftedStrongTransApp σ (canonicalTargetObject X))
    (liftedStrongTransInverseCompositeNaturality σ f A)
    (liftedStrongTransInverseCompositeNaturality σ f B)
    (canonicalInverseComparison f A)
    (canonicalInverseComparison f B)
    (liftedStrongTransInverseCompositeNaturality_naturality σ f η)
    (canonicalInverseComparison_naturality f η)

/-- Naturality holds on forward free-groupoid generators. -/
theorem liftedModificationApp_naturality_generator
    (Γ : (inclusion.localPrecomposition F G).obj η ⟶
      (inclusion.localPrecomposition F G).obj θ)
    {X Y : Ript.Examples.WalkingLocalization.Arrow} (f : X ⟶ Y) :
    Pseudofunctor.StrongTrans.NaturalityAt η θ
      (liftedModificationApp Γ)
      ((CategoryTheory.FreeGroupoid.homMk f).toLoc ×ₘ
        𝟙 (MonoidalSingleObj.star (Type))) := by
  apply Pseudofunctor.StrongTrans.naturalityAt_of_iso η θ
    (liftedModificationApp Γ)
    (Iso.prod (Iso.refl _)
      ((Pseudofunctor.id Cell).mapId (MonoidalSingleObj.star (Type))))
  exact liftedModificationApp_naturality_map Γ
    (f.toLoc ×ₘ 𝟙 (MonoidalSingleObj.star (Type)))

/-- Naturality on a forward generator forces naturality on its freely
adjoined inverse by the mates calculation. -/
theorem liftedModificationApp_naturality_generatorInv
    (Γ : (inclusion.localPrecomposition F G).obj η ⟶
      (inclusion.localPrecomposition F G).obj θ)
    {X Y : Ript.Examples.WalkingLocalization.Arrow} (f : X ⟶ Y) :
    Pseudofunctor.StrongTrans.NaturalityAt η θ
      (liftedModificationApp Γ)
      ((inv (CategoryTheory.FreeGroupoid.homMk f)).toLoc ×ₘ
        𝟙 (MonoidalSingleObj.star (Type))) := by
  exact Pseudofunctor.StrongTrans.naturalityAt_inv η θ
    (liftedModificationApp Γ) (generatorEquivalence f)
      (liftedModificationApp_naturality_generator Γ f)

/-- Embed a path in the symmetrized walking-arrow quiver into its categorical
free-groupoid completion. -/
def pathToCompletion
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (p : Quiver.Path (V := Quiver.Symmetrify
      Ript.Examples.WalkingLocalization.Arrow) X Y) :
    CategoryTheory.FreeGroupoid.mk X ⟶
      CategoryTheory.FreeGroupoid.mk Y :=
  Quot.mk _ (Quot.mk _ p)

/-- The empty signed path maps to the identity of the free-groupoid
completion. -/
@[simp]
theorem pathToCompletion_nil
    (X : Ript.Examples.WalkingLocalization.Arrow) :
    pathToCompletion (Quiver.Path.nil : Quiver.Path
      (V := Quiver.Symmetrify Ript.Examples.WalkingLocalization.Arrow) X X) =
      𝟙 _ :=
  rfl

/-- Mapping a concatenated signed path preserves composition. -/
@[simp]
theorem pathToCompletion_comp
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (p : Quiver.Path (V := Quiver.Symmetrify
      Ript.Examples.WalkingLocalization.Arrow) X Y)
    (q : Quiver.Path (V := Quiver.Symmetrify
      Ript.Examples.WalkingLocalization.Arrow) Y Z) :
    pathToCompletion (p.comp q) =
      pathToCompletion p ≫ pathToCompletion q :=
  rfl

/-- A positive signed edge maps to the corresponding free-groupoid
generator. -/
@[simp]
theorem pathToCompletion_pos
    {X Y : Ript.Examples.WalkingLocalization.Arrow} (f : X ⟶ Y) :
    pathToCompletion f.toPosPath =
      CategoryTheory.FreeGroupoid.homMk f :=
  rfl

/-- A negative signed edge maps to the inverse of the corresponding
free-groupoid generator. -/
@[simp]
theorem pathToCompletion_neg
    {X Y : Ript.Examples.WalkingLocalization.Arrow} (f : X ⟶ Y) :
    pathToCompletion f.toNegPath =
      inv (CategoryTheory.FreeGroupoid.homMk f) :=
  by
    let p : (Quiver.FreeGroupoid.of
        Ript.Examples.WalkingLocalization.Arrow).obj X ⟶
        (Quiver.FreeGroupoid.of
          Ript.Examples.WalkingLocalization.Arrow).obj Y :=
      Quot.mk _ f.toPosPath
    change (CategoryTheory.Quotient.functor
        (CategoryTheory.FreeGroupoid.homRel
          Ript.Examples.WalkingLocalization.Arrow)).map
        (Quot.mk _ f.toNegPath) =
      inv ((CategoryTheory.Quotient.functor
        (CategoryTheory.FreeGroupoid.homRel
          Ript.Examples.WalkingLocalization.Arrow)).map
        p)
    have h := Functor.map_inv
      (CategoryTheory.Quotient.functor
        (CategoryTheory.FreeGroupoid.homRel
          Ript.Examples.WalkingLocalization.Arrow))
      p
    rw [← h]
    change (CategoryTheory.Quotient.functor
        (CategoryTheory.FreeGroupoid.homRel
          Ript.Examples.WalkingLocalization.Arrow)).map
        (Quot.mk _ f.toNegPath) =
      (CategoryTheory.Quotient.functor
        (CategoryTheory.FreeGroupoid.homRel
          Ript.Examples.WalkingLocalization.Arrow)).map (inv p)
    congr 1
    rw [← Groupoid.inv_eq_inv]
    rfl

/-- The canonical morphism between two endpoints of the walking-arrow
completion.  It is the original forward arrow when the endpoints are
ordered, and the inverse of the reverse ordered arrow otherwise. -/
noncomputable def canonicalCompletionHom
    (X Y : Ript.Examples.WalkingLocalization.Arrow) :
    CategoryTheory.FreeGroupoid.mk X ⟶
      CategoryTheory.FreeGroupoid.mk Y :=
  if h : X ≤ Y then
    CategoryTheory.FreeGroupoid.homMk (homOfLE h)
  else
    inv (CategoryTheory.FreeGroupoid.homMk
      (homOfLE (le_of_not_ge h)))

/-- The canonical completion endomorphism is the identity. -/
@[simp]
theorem canonicalCompletionHom_self
    (X : Ript.Examples.WalkingLocalization.Arrow) :
    canonicalCompletionHom X X = CategoryStruct.id _ := by
  simp [canonicalCompletionHom]

/-- Every forward generator is the canonical morphism between its
endpoints. -/
theorem homMk_eq_canonicalCompletionHom
    {X Y : Ript.Examples.WalkingLocalization.Arrow} (f : X ⟶ Y) :
    CategoryTheory.FreeGroupoid.homMk f =
      canonicalCompletionHom X Y := by
  rw [canonicalCompletionHom, dif_pos f.le]
  congr

/-- The inverse of every forward generator is the canonical morphism in the
opposite direction. -/
theorem inv_homMk_eq_canonicalCompletionHom
    {X Y : Ript.Examples.WalkingLocalization.Arrow} (f : X ⟶ Y) :
    inv (CategoryTheory.FreeGroupoid.homMk f) =
      canonicalCompletionHom Y X := by
  rw [homMk_eq_canonicalCompletionHom]
  fin_cases X <;> fin_cases Y <;> simp [canonicalCompletionHom]

/-- Canonical completion morphisms compose by their endpoints. -/
@[simp]
theorem canonicalCompletionHom_comp
    (X Y Z : Ript.Examples.WalkingLocalization.Arrow) :
    canonicalCompletionHom X Y ≫ canonicalCompletionHom Y Z =
      canonicalCompletionHom X Z := by
  fin_cases X <;> fin_cases Y <;> fin_cases Z <;>
    simp [canonicalCompletionHom]

/-- Every signed path in the walking arrow reduces to the canonical morphism
between its endpoints. -/
theorem pathToCompletion_eq_canonicalCompletionHom
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (p : Quiver.Path (V := Quiver.Symmetrify
      Ript.Examples.WalkingLocalization.Arrow) X Y) :
    pathToCompletion p = canonicalCompletionHom X Y := by
  induction p with
  | nil =>
      exact (pathToCompletion_nil X).trans
        (canonicalCompletionHom_self X).symm
  | @cons Y Z p q ih =>
      cases q with
      | inl f =>
          change pathToCompletion p ≫
              CategoryTheory.FreeGroupoid.homMk f =
            canonicalCompletionHom X Z
          rw [ih, homMk_eq_canonicalCompletionHom]
          exact canonicalCompletionHom_comp X Y Z
      | inr f =>
          let qneg : Quiver.Path (V := Quiver.Symmetrify
              Ript.Examples.WalkingLocalization.Arrow) Y Z :=
            f.toNegPath
          change pathToCompletion p ≫ pathToCompletion qneg =
            canonicalCompletionHom X Z
          have hneg : pathToCompletion qneg =
              inv (CategoryTheory.FreeGroupoid.homMk f) :=
            pathToCompletion_neg f
          rw [ih, hneg, inv_homMk_eq_canonicalCompletionHom]
          exact canonicalCompletionHom_comp X Y Z

/-- Every morphism in the walking-arrow completion is determined by its two
endpoints. -/
theorem completion_hom_eq_canonical
    {X Y : Ript.Examples.WalkingLocalization.Completion} (f : X ⟶ Y) :
    f = canonicalCompletionHom X.as.as Y.as.as := by
  apply CategoryTheory.Quotient.induction
    (CategoryTheory.FreeGroupoid.homRel
      Ript.Examples.WalkingLocalization.Arrow)
    (P := fun {X Y} f ↦
      f = canonicalCompletionHom X.as.as Y.as.as)
  intro X Y f
  apply CategoryTheory.Quotient.induction
    (@Quiver.FreeGroupoid.redStep
      Ript.Examples.WalkingLocalization.Arrow _)
    (P := fun {X Y} f ↦
      (CategoryTheory.Quotient.functor
        (CategoryTheory.FreeGroupoid.homRel
          Ript.Examples.WalkingLocalization.Arrow)).map f =
            canonicalCompletionHom X.as Y.as)
  intro X Y p
  exact pathToCompletion_eq_canonicalCompletionHom p

/-- The canonical strong-naturality isomorphism forced at a target identity
1-morphism.  This is the identity constraint used by every strong
transformation, expressed directly in terms of the two target
pseudofunctors' unit comparisons. -/
noncomputable def liftedStrongTransIdentityNaturality
    (σ : inclusion.comp F ⟶ inclusion.comp G) (X : Target) :
    F.map (𝟙 X) ≫ liftedStrongTransApp σ X ≅
      liftedStrongTransApp σ X ≫ G.map (𝟙 X) :=
  whiskerRightIso (F.mapId X) (liftedStrongTransApp σ X) ≪≫
    (λ_ (liftedStrongTransApp σ X)) ≪≫
    (ρ_ (liftedStrongTransApp σ X)).symm ≪≫
    whiskerLeftIso (liftedStrongTransApp σ X) (G.mapId X).symm

/-- Choose a fallback strong-naturality isomorphism for every target
1-morphism by endpoint normalization.  The original source constraint is
used in the forward case and the extended invertible mate in the reverse
case.  `liftedStrongTransNaturality` below replaces its value on strict
target identities by the canonical identity constraint. -/
noncomputable def liftedStrongTransEndpointNaturality
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Target} (f : X ⟶ Y) :
    F.map f ≫ liftedStrongTransApp σ Y ≅
      liftedStrongTransApp σ X ≫ G.map f := by
  rcases X with ⟨⟨X⟩, X'⟩
  rcases Y with ⟨⟨Y⟩, Y'⟩
  cases X'
  cases Y'
  let x : Ript.Examples.WalkingLocalization.Arrow := X.as.as
  let y : Ript.Examples.WalkingLocalization.Arrow := Y.as.as
  have hx : X.as.as = x := rfl
  have hy : Y.as.as = y := rfl
  have hX : X = CategoryTheory.FreeGroupoid.mk x :=
    CategoryTheory.FreeGroupoid.eq_mk X
  have hY : Y = CategoryTheory.FreeGroupoid.mk y :=
    CategoryTheory.FreeGroupoid.eq_mk Y
  cases hX
  cases hY
  rcases f with ⟨⟨f⟩, A⟩
  by_cases h : x ≤ y
  · have hf : f = CategoryTheory.FreeGroupoid.homMk (homOfLE h) := by
      have hf' := completion_hom_eq_canonical f
      simpa [canonicalCompletionHom, hx, hy, h] using hf'
    rw [hf]
    exact liftedStrongTransForwardNaturality σ (homOfLE h) A
  · have hf : f = inv (CategoryTheory.FreeGroupoid.homMk
        (homOfLE (le_of_not_ge h))) := by
      have hf' := completion_hom_eq_canonical f
      simpa [canonicalCompletionHom, hx, hy, h] using hf'
    rw [hf]
    exact liftedStrongTransInverseNaturality σ
      (homOfLE (le_of_not_ge h)) A

set_option backward.isDefEq.respectTransparency false in
/-- Endpoint normalization agrees with the original forward constraint on
every canonical image arrow. -/
theorem liftedStrongTransEndpointNaturality_forward
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {x y : Ript.Examples.WalkingLocalization.Arrow}
    (f : x ⟶ y) (A : Type) :
    liftedStrongTransEndpointNaturality σ (canonicalForwardHom f A) =
      liftedStrongTransForwardNaturality σ f A := by
  let h : x ≤ y := leOfHom f
  have hf : f = homOfLE h := (homOfLE_leOfHom f).symm
  clear_value h
  rw [hf]
  have hx : (CategoryTheory.FreeGroupoid.mk x :
      Ript.Examples.WalkingLocalization.Completion).as.as = x := rfl
  have hy : (CategoryTheory.FreeGroupoid.mk y :
      Ript.Examples.WalkingLocalization.Completion).as.as = y := rfl
  ext
  simp [liftedStrongTransEndpointNaturality, canonicalTargetObject,
    canonicalForwardHom, hx, hy, h]
  change (liftedStrongTransForwardNaturality σ (homOfLE h) A).hom =
    (liftedStrongTransForwardNaturality σ (homOfLE h) A).hom
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- On a genuinely reverse canonical arrow, endpoint normalization agrees
with the inverse constraint obtained by mates.  The strict endpoint-order
hypothesis excludes the degenerate inverse of an identity. -/
theorem liftedStrongTransEndpointNaturality_inverse_of_not_le
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {x y : Ript.Examples.WalkingLocalization.Arrow}
    (f : x ⟶ y) (h : ¬ y ≤ x) (A : Type) :
    liftedStrongTransEndpointNaturality σ (canonicalInverseHom f A) =
      liftedStrongTransInverseNaturality σ f A := by
  have hx : (CategoryTheory.FreeGroupoid.mk y :
      Ript.Examples.WalkingLocalization.Completion).as.as = y := rfl
  have hy : (CategoryTheory.FreeGroupoid.mk x :
      Ript.Examples.WalkingLocalization.Completion).as.as = x := rfl
  ext
  simp [liftedStrongTransEndpointNaturality, canonicalInverseHom,
    canonicalTargetObject, hx, hy, h]
  change (liftedStrongTransInverseNaturality σ
      (homOfLE (le_of_not_ge h)) A).hom =
    (liftedStrongTransInverseNaturality σ f A).hom
  congr 2

set_option backward.isDefEq.respectTransparency false in
/-- On every arrow in the image of the inclusion, endpoint normalization is
exactly the original source strong-naturality constraint. -/
theorem liftedStrongTransEndpointNaturality_inclusion
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {S T : Source} (p : S ⟶ T) :
    liftedStrongTransEndpointNaturality σ (inclusion.map p) =
      σ.naturality p := by
  rcases S with ⟨⟨x⟩, X'⟩
  rcases T with ⟨⟨y⟩, Y'⟩
  cases X'
  cases Y'
  rcases p with ⟨⟨f⟩, A⟩
  change liftedStrongTransEndpointNaturality σ
      (canonicalForwardHom f A) =
    σ.naturality (canonicalSourceHom f A)
  rw [liftedStrongTransEndpointNaturality_forward,
    liftedStrongTransForwardNaturality_eq_source]

/-- The inclusion-image theorem specializes to source identities. -/
theorem liftedStrongTransEndpointNaturality_inclusion_id
    (σ : inclusion.comp F ⟶ inclusion.comp G) (S : Source) :
    liftedStrongTransEndpointNaturality σ (inclusion.map (𝟙 S)) =
      σ.naturality (𝟙 S) := by
  exact liftedStrongTransEndpointNaturality_inclusion σ (𝟙 S)

set_option backward.isDefEq.respectTransparency false in
/-- Endpoint-normalized lifted constraints are natural in every target
2-morphism.  Thinness of the completed walking coordinate reduces its
component to an identity; the retained component is then handled by the
forward or inverse canonical naturality theorem according to the endpoints. -/
theorem liftedStrongTransEndpointNaturality_naturality
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Target} {f g : X ⟶ Y} (η : f ⟶ g) :
    F.map₂ η ▷ liftedStrongTransApp σ Y ≫
        (liftedStrongTransEndpointNaturality σ g).hom =
      (liftedStrongTransEndpointNaturality σ f).hom ≫
        liftedStrongTransApp σ X ◁ G.map₂ η := by
  rcases X with ⟨⟨X⟩, X'⟩
  rcases Y with ⟨⟨Y⟩, Y'⟩
  cases X'
  cases Y'
  let x : Ript.Examples.WalkingLocalization.Arrow := X.as.as
  let y : Ript.Examples.WalkingLocalization.Arrow := Y.as.as
  have hx : X.as.as = x := rfl
  have hy : Y.as.as = y := rfl
  have hX : X = CategoryTheory.FreeGroupoid.mk x :=
    CategoryTheory.FreeGroupoid.eq_mk X
  have hY : Y = CategoryTheory.FreeGroupoid.mk y :=
    CategoryTheory.FreeGroupoid.eq_mk Y
  clear_value x
  clear_value y
  cases hX
  cases hY
  rcases f with ⟨⟨f⟩, A⟩
  rcases g with ⟨⟨g⟩, B⟩
  rcases η with ⟨ηfg, ηAB⟩
  have hfg := LocallyDiscrete.eq_of_hom ηfg
  cases hfg
  have hηfg : ηfg = 𝟙 _ := Subsingleton.elim _ _
  rw [hηfg]
  by_cases h : x ≤ y
  · have hf : f = CategoryTheory.FreeGroupoid.homMk (homOfLE h) := by
      have hf' := completion_hom_eq_canonical f
      simpa [canonicalCompletionHom, hx, hy, h] using hf'
    subst f
    simp [liftedStrongTransEndpointNaturality, hx, hy, h]
    change F.map₂ (canonicalForwardTwoCell (homOfLE h) ηAB) ▷
          liftedStrongTransApp σ (canonicalTargetObject y) ≫
        (liftedStrongTransForwardNaturality σ (homOfLE h) B).hom =
      (liftedStrongTransForwardNaturality σ (homOfLE h) A).hom ≫
        liftedStrongTransApp σ (canonicalTargetObject x) ◁
          G.map₂ (canonicalForwardTwoCell (homOfLE h) ηAB)
    exact liftedStrongTransForwardNaturality_naturality σ
      (homOfLE h) ηAB
  · have hf : f = inv (CategoryTheory.FreeGroupoid.homMk
        (homOfLE (le_of_not_ge h))) := by
      have hf' := completion_hom_eq_canonical f
      simpa [canonicalCompletionHom, hx, hy, h] using hf'
    subst f
    simp [liftedStrongTransEndpointNaturality, hx, hy, h]
    change F.map₂ (canonicalInverseTwoCell
          (homOfLE (le_of_not_ge h)) ηAB) ▷
          liftedStrongTransApp σ (canonicalTargetObject y) ≫
        (liftedStrongTransInverseNaturality σ
          (homOfLE (le_of_not_ge h)) B).hom =
      (liftedStrongTransInverseNaturality σ
          (homOfLE (le_of_not_ge h)) A).hom ≫
        liftedStrongTransApp σ (canonicalTargetObject x) ◁
          G.map₂ (canonicalInverseTwoCell
            (homOfLE (le_of_not_ge h)) ηAB)
    exact liftedStrongTransInverseNaturality_naturality σ
      (homOfLE (le_of_not_ge h)) ηAB

set_option backward.isDefEq.respectTransparency false in
/-- Endpoint-normalized constraints transport canonically across every
2-isomorphism between parallel target 1-morphisms. -/
theorem liftedStrongTransEndpointNaturality_iso
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Target} {f g : X ⟶ Y} (e : f ≅ g) :
    Pseudofunctor.StrongTrans.naturalityIsoOfIso F G
        (liftedStrongTransApp σ X) (liftedStrongTransApp σ Y)
        (liftedStrongTransEndpointNaturality σ f) e =
      liftedStrongTransEndpointNaturality σ g := by
  apply Iso.ext
  rw [← cancel_epi (F.map₂ e.hom ▷ liftedStrongTransApp σ Y)]
  dsimp [Pseudofunctor.StrongTrans.naturalityIsoOfIso]
  simp only [whiskerRightIso_hom, whiskerLeftIso_hom,
    Iso.symm_hom, PrelaxFunctor.map₂Iso_hom]
  change F.map₂ e.hom ▷ liftedStrongTransApp σ Y ≫
      F.map₂ e.inv ▷ liftedStrongTransApp σ Y ≫
        (liftedStrongTransEndpointNaturality σ f).hom ≫
          liftedStrongTransApp σ X ◁ G.map₂ e.hom =
    F.map₂ e.hom ▷ liftedStrongTransApp σ Y ≫
      (liftedStrongTransEndpointNaturality σ g).hom
  rw [← Category.assoc, ← comp_whiskerRight, ← F.map₂_comp]
  simp only [Iso.hom_inv_id, F.map₂_id, id_whiskerRight,
    Category.id_comp]
  exact (liftedStrongTransEndpointNaturality_naturality σ e.hom).symm

set_option backward.isDefEq.respectTransparency false in
/-- Endpoint-normalized constraints satisfy composition coherence whenever
both factors lie in the image of the inclusion.  Naturality across the
inclusion's compositor cancels the extra mapped compositor from the source
strong-transformation law. -/
theorem liftedStrongTransEndpointNaturality_comp_inclusion
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {S T U : Source} (p : S ⟶ T) (q : T ⟶ U) :
    (liftedStrongTransEndpointNaturality σ
        (inclusion.map p ≫ inclusion.map q)).hom ≫
          liftedStrongTransApp σ (inclusion.obj S) ◁
            (G.mapComp (inclusion.map p) (inclusion.map q)).hom =
      (F.mapComp (inclusion.map p) (inclusion.map q)).hom ▷
            liftedStrongTransApp σ (inclusion.obj U) ≫
        (α_ _ _ _).hom ≫
        F.map (inclusion.map p) ◁
          (liftedStrongTransEndpointNaturality σ (inclusion.map q)).hom ≫
        (α_ _ _ _).inv ≫
        (liftedStrongTransEndpointNaturality σ (inclusion.map p)).hom ▷
            G.map (inclusion.map q) ≫
        (α_ _ _ _).hom := by
  rcases S with ⟨⟨x⟩, X'⟩
  rcases T with ⟨⟨y⟩, Y'⟩
  rcases U with ⟨⟨z⟩, Z'⟩
  cases X'
  cases Y'
  cases Z'
  change
    (liftedStrongTransEndpointNaturality σ
        (inclusion.map p ≫ inclusion.map q)).hom ≫
          σ.app (LocallyDiscrete.mk x, PUnit.unit) ◁
            (G.mapComp (inclusion.map p) (inclusion.map q)).hom =
      (F.mapComp (inclusion.map p) (inclusion.map q)).hom ▷
          σ.app (LocallyDiscrete.mk z, PUnit.unit) ≫
        (α_ (F.map (inclusion.map p)) (F.map (inclusion.map q))
          (σ.app (LocallyDiscrete.mk z, PUnit.unit))).hom ≫
        F.map (inclusion.map p) ◁
          (liftedStrongTransEndpointNaturality σ (inclusion.map q)).hom ≫
        (α_ (F.map (inclusion.map p))
          (σ.app (LocallyDiscrete.mk y, PUnit.unit))
          (G.map (inclusion.map q))).inv ≫
        (liftedStrongTransEndpointNaturality σ (inclusion.map p)).hom ▷
            G.map (inclusion.map q) ≫
        (α_ (σ.app (LocallyDiscrete.mk x, PUnit.unit))
          (G.map (inclusion.map p)) (G.map (inclusion.map q))).hom
  let θ := (inclusion.mapComp p q).hom
  have hη := liftedStrongTransEndpointNaturality_naturality σ θ
  rw [liftedStrongTransEndpointNaturality_inclusion] at hη
  change
    F.map₂ θ ▷ σ.app (LocallyDiscrete.mk z, PUnit.unit) ≫
        (liftedStrongTransEndpointNaturality σ
          (inclusion.map p ≫ inclusion.map q)).hom =
      (σ.naturality (p ≫ q)).hom ≫
        σ.app (LocallyDiscrete.mk x, PUnit.unit) ◁ G.map₂ θ at hη
  have hcomp := σ.naturality_comp p q
  have hp := congrArg Iso.hom
    (liftedStrongTransEndpointNaturality_inclusion σ p)
  have hq := congrArg Iso.hom
    (liftedStrongTransEndpointNaturality_inclusion σ q)
  rw [hp, hq]
  rw [← cancel_epi (F.map₂ (inclusion.mapComp p q).hom ▷
    σ.app (LocallyDiscrete.mk z, PUnit.unit))]
  rw [← Category.assoc]
  rw [hη]
  simpa [Pseudofunctor.comp, PrelaxFunctor.comp,
    PrelaxFunctorStruct.comp, Prefunctor.comp, θ, Category.assoc,
    whiskerLeft_comp, comp_whiskerRight] using hcomp

set_option backward.isDefEq.respectTransparency false in
/-- Endpoint normalization satisfies the target identity law on every
object in the image of the inclusion.  The proof transports the source
identity law through the inclusion's pseudofunctorial unit comparison. -/
theorem liftedStrongTransEndpointNaturality_id_inclusion
    (σ : inclusion.comp F ⟶ inclusion.comp G) (S : Source) :
    (liftedStrongTransEndpointNaturality σ (𝟙 (inclusion.obj S))).hom ≫
          liftedStrongTransApp σ (inclusion.obj S) ◁
            (G.mapId (inclusion.obj S)).hom =
      (F.mapId (inclusion.obj S)).hom ▷
          liftedStrongTransApp σ (inclusion.obj S) ≫
        (λ_ (liftedStrongTransApp σ (inclusion.obj S))).hom ≫
        (ρ_ (liftedStrongTransApp σ (inclusion.obj S))).inv := by
  rcases S with ⟨⟨x⟩, X'⟩
  cases X'
  let S : Source :=
    (LocallyDiscrete.mk x, MonoidalSingleObj.star Type)
  change
    (liftedStrongTransEndpointNaturality σ (𝟙 (inclusion.obj S))).hom ≫
          σ.app S ◁ (G.mapId (inclusion.obj S)).hom =
      (F.mapId (inclusion.obj S)).hom ▷ σ.app S ≫
        (λ_ (σ.app S)).hom ≫ (ρ_ (σ.app S)).inv
  let θ := (inclusion.mapId S).hom
  have hη := liftedStrongTransEndpointNaturality_naturality σ θ
  rw [liftedStrongTransEndpointNaturality_inclusion_id] at hη
  have hid := σ.naturality_id S
  change
    F.map₂ θ ▷ σ.app S ≫
        (liftedStrongTransEndpointNaturality σ (𝟙 (inclusion.obj S))).hom =
      (σ.naturality (𝟙 S)).hom ≫ σ.app S ◁ G.map₂ θ at hη
  rw [← cancel_epi (F.map₂ (inclusion.mapId S).hom ▷ σ.app S)]
  rw [← Category.assoc]
  rw [hη]
  simpa [θ, Category.assoc,
    whiskerLeft_comp, comp_whiskerRight] using hid

set_option backward.isDefEq.respectTransparency false in
/-- Endpoint normalization satisfies the strong-transformation identity
coherence law on every target object. -/
theorem liftedStrongTransEndpointNaturality_id
    (σ : inclusion.comp F ⟶ inclusion.comp G) (X : Target) :
    (liftedStrongTransEndpointNaturality σ (𝟙 X)).hom ≫
          liftedStrongTransApp σ X ◁ (G.mapId X).hom =
      (F.mapId X).hom ▷ liftedStrongTransApp σ X ≫
        (λ_ (liftedStrongTransApp σ X)).hom ≫
        (ρ_ (liftedStrongTransApp σ X)).inv := by
  rw [← inclusion_obj_sourceOfTarget X]
  exact liftedStrongTransEndpointNaturality_id_inclusion σ
    (sourceOfTarget X)

set_option backward.isDefEq.respectTransparency false in
/-- The endpoint-normalized constraint at a strict identity is the canonical
identity constraint. -/
theorem liftedStrongTransEndpointNaturality_id_eq
    (σ : inclusion.comp F ⟶ inclusion.comp G) (X : Target) :
    liftedStrongTransEndpointNaturality σ (𝟙 X) =
      liftedStrongTransIdentityNaturality σ X := by
  ext
  rw [← cancel_mono
    (liftedStrongTransApp σ X ◁ (G.mapId X).hom)]
  rw [liftedStrongTransEndpointNaturality_id]
  simp [liftedStrongTransIdentityNaturality, Category.assoc]

/-- Choose a strong-naturality isomorphism for every target 1-morphism.
Strict target identities use the canonical identity constraint, while every
other arrow uses endpoint normalization.  Consequently the identity
coherence law holds definitionally up to the standard bicategorical simp
lemmas.  The identity branch agrees with endpoint normalization, so the
2-cell naturality theorem above also applies to this public constraint.
Composition coherence remains a separate obligation. -/
noncomputable def liftedStrongTransNaturality
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Target} (f : X ⟶ Y) :
    F.map f ≫ liftedStrongTransApp σ Y ≅
      liftedStrongTransApp σ X ≫ G.map f := by
  classical
  by_cases hXY : X = Y
  · subst Y
    by_cases hf : f = 𝟙 X
    · subst f
      exact liftedStrongTransIdentityNaturality σ X
    · exact liftedStrongTransEndpointNaturality σ f
  · exact liftedStrongTransEndpointNaturality σ f

/-- The all-arrow constraint specializes to the canonical identity
constraint on every target object. -/
@[simp]
theorem liftedStrongTransNaturality_id_eq
    (σ : inclusion.comp F ⟶ inclusion.comp G) (X : Target) :
    liftedStrongTransNaturality σ (𝟙 X) =
      liftedStrongTransIdentityNaturality σ X := by
  simp [liftedStrongTransNaturality]

/-- The lifted all-arrow constraint satisfies the strong-transformation
identity coherence law. -/
theorem liftedStrongTransNaturality_id
    (σ : inclusion.comp F ⟶ inclusion.comp G) (X : Target) :
    (liftedStrongTransNaturality σ (𝟙 X)).hom ≫
          liftedStrongTransApp σ X ◁ (G.mapId X).hom =
      (F.mapId X).hom ▷ liftedStrongTransApp σ X ≫
        (λ_ (liftedStrongTransApp σ X)).hom ≫
        (ρ_ (liftedStrongTransApp σ X)).inv := by
  simp [liftedStrongTransNaturality,
    liftedStrongTransIdentityNaturality]

set_option backward.isDefEq.respectTransparency false in
/-- The public all-arrow constraint agrees with endpoint normalization on
every target 1-morphism, including strict identities. -/
theorem liftedStrongTransNaturality_eq_endpoint
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Target} (f : X ⟶ Y) :
    liftedStrongTransNaturality σ f =
      liftedStrongTransEndpointNaturality σ f := by
  classical
  by_cases hXY : X = Y
  · subst Y
    by_cases hf : f = 𝟙 X
    · subst f
      rw [liftedStrongTransNaturality_id_eq,
        liftedStrongTransEndpointNaturality_id_eq]
    · simp [liftedStrongTransNaturality, hf]
  · simp [liftedStrongTransNaturality, hXY]

/-- The public all-arrow constraints transport canonically across every
2-isomorphism between parallel target 1-morphisms. -/
theorem liftedStrongTransNaturality_iso
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Target} {f g : X ⟶ Y} (e : f ≅ g) :
    Pseudofunctor.StrongTrans.naturalityIsoOfIso F G
        (liftedStrongTransApp σ X) (liftedStrongTransApp σ Y)
        (liftedStrongTransNaturality σ f) e =
      liftedStrongTransNaturality σ g := by
  rw [liftedStrongTransNaturality_eq_endpoint,
    liftedStrongTransNaturality_eq_endpoint]
  exact liftedStrongTransEndpointNaturality_iso σ e

set_option backward.isDefEq.respectTransparency false in
/-- The public all-arrow lifted constraint is natural in every target
2-morphism, including 2-cells that meet its strict-identity branch. -/
theorem liftedStrongTransNaturality_naturality
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Target} {f g : X ⟶ Y} (η : f ⟶ g) :
    F.map₂ η ▷ liftedStrongTransApp σ Y ≫
        (liftedStrongTransNaturality σ g).hom =
      (liftedStrongTransNaturality σ f).hom ≫
        liftedStrongTransApp σ X ◁ G.map₂ η := by
  rw [liftedStrongTransNaturality_eq_endpoint,
    liftedStrongTransNaturality_eq_endpoint]
  exact liftedStrongTransEndpointNaturality_naturality σ η

set_option backward.isDefEq.respectTransparency false in
/-- The public all-arrow constraints satisfy composition coherence on any
pair of arrows in the image of the inclusion. -/
theorem liftedStrongTransNaturality_comp_inclusion
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {S T U : Source} (p : S ⟶ T) (q : T ⟶ U) :
    (liftedStrongTransNaturality σ
        (inclusion.map p ≫ inclusion.map q)).hom ≫
          liftedStrongTransApp σ (inclusion.obj S) ◁
            (G.mapComp (inclusion.map p) (inclusion.map q)).hom =
      (F.mapComp (inclusion.map p) (inclusion.map q)).hom ▷
            liftedStrongTransApp σ (inclusion.obj U) ≫
        (α_ _ _ _).hom ≫
        F.map (inclusion.map p) ◁
          (liftedStrongTransNaturality σ (inclusion.map q)).hom ≫
        (α_ _ _ _).inv ≫
        (liftedStrongTransNaturality σ (inclusion.map p)).hom ▷
            G.map (inclusion.map q) ≫
        (α_ _ _ _).hom := by
  rw [liftedStrongTransNaturality_eq_endpoint,
    liftedStrongTransNaturality_eq_endpoint,
    liftedStrongTransNaturality_eq_endpoint]
  exact liftedStrongTransEndpointNaturality_comp_inclusion σ p q

/-- In particular, the lifted constraints satisfy composition coherence on
every pair of canonical forward arrows, with arbitrary retained-coordinate
1-morphisms. -/
theorem liftedStrongTransNaturality_comp_forward
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {x y z : Ript.Examples.WalkingLocalization.Arrow}
    (f : x ⟶ y) (g : y ⟶ z) (A B : Type) :
    (liftedStrongTransNaturality σ
        (canonicalForwardHom f A ≫ canonicalForwardHom g B)).hom ≫
          liftedStrongTransApp σ (canonicalTargetObject x) ◁
            (G.mapComp (canonicalForwardHom f A)
              (canonicalForwardHom g B)).hom =
      (F.mapComp (canonicalForwardHom f A)
          (canonicalForwardHom g B)).hom ▷
            liftedStrongTransApp σ (canonicalTargetObject z) ≫
        (α_ _ _ _).hom ≫
        F.map (canonicalForwardHom f A) ◁
          (liftedStrongTransNaturality σ
            (canonicalForwardHom g B)).hom ≫
        (α_ _ _ _).inv ≫
        (liftedStrongTransNaturality σ
          (canonicalForwardHom f A)).hom ▷
            G.map (canonicalForwardHom g B) ≫
        (α_ _ _ _).hom := by
  exact liftedStrongTransNaturality_comp_inclusion σ
    (canonicalSourceHom f A) (canonicalSourceHom g B)

/-- The free groupoid on the walking arrow is thin: there is exactly one
morphism between each pair of objects. -/
noncomputable instance walkingCompletionIsThin :
    Quiver.IsThin Ript.Examples.WalkingLocalization.Completion :=
  fun _ _ ↦
    ⟨fun f g ↦ by
      rw [completion_hom_eq_canonical f,
        completion_hom_eq_canonical g]⟩

/-- Forget a completed walking-arrow object to its endpoint in the
codiscrete two-object category. -/
noncomputable def completionToCodiscrete :
    Ript.Examples.WalkingLocalization.Completion ⥤
      Codiscrete Ript.Examples.WalkingLocalization.Arrow :=
  Codiscrete.functor (fun X ↦ X.as.as)

/-- Realize the unique codiscrete arrow by the canonical arrow in the
walking-arrow completion. -/
noncomputable def codiscreteToCompletion :
    Codiscrete Ript.Examples.WalkingLocalization.Arrow ⥤
      Ript.Examples.WalkingLocalization.Completion where
  obj X := CategoryTheory.FreeGroupoid.mk X.as
  map {X Y} _ := canonicalCompletionHom X.as Y.as
  map_id X := canonicalCompletionHom_self X.as
  map_comp _ _ := (canonicalCompletionHom_comp _ _ _).symm

/-- The walking-arrow completion is exactly the codiscrete groupoid on its
two endpoints, up to categorical equivalence.  Thus the localization adds
one reverse arrow but no additional path ambiguity. -/
noncomputable def completionCodiscreteEquivalence :
    Ript.Examples.WalkingLocalization.Completion ≌
      Codiscrete Ript.Examples.WalkingLocalization.Arrow where
  functor := completionToCodiscrete
  inverse := codiscreteToCompletion
  unitIso := NatIso.ofComponents
    (fun X ↦ eqToIso (CategoryTheory.FreeGroupoid.eq_mk X))
    (fun _ ↦ Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun X ↦ Iso.refl X)
    (fun _ ↦ Subsingleton.elim _ _)

/-- Naturality extends from signed generators to every symmetrized path. -/
theorem liftedModificationApp_naturality_path
    (Γ : (inclusion.localPrecomposition F G).obj η ⟶
      (inclusion.localPrecomposition F G).obj θ)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (p : Quiver.Path (V := Quiver.Symmetrify
      Ript.Examples.WalkingLocalization.Arrow) X Y) :
    Pseudofunctor.StrongTrans.NaturalityAt η θ
      (liftedModificationApp Γ)
      ((pathToCompletion p).toLoc ×ₘ
        𝟙 (MonoidalSingleObj.star (Type))) := by
  induction p with
  | nil =>
      change Pseudofunctor.StrongTrans.NaturalityAt η θ
        (liftedModificationApp Γ) (𝟙
          (LocallyDiscrete.mk (CategoryTheory.FreeGroupoid.mk X),
            MonoidalSingleObj.star (Type)))
      exact Pseudofunctor.StrongTrans.naturalityAt_id η θ
        (liftedModificationApp Γ)
        (LocallyDiscrete.mk (CategoryTheory.FreeGroupoid.mk X),
          MonoidalSingleObj.star (Type))
  | @cons Y Z p q ih =>
      have hq : Pseudofunctor.StrongTrans.NaturalityAt η θ
          (liftedModificationApp Γ)
          ((pathToCompletion (@Quiver.Hom.toPath
            (Quiver.Symmetrify Ript.Examples.WalkingLocalization.Arrow)
            (Quiver.symmetrifyQuiver
              Ript.Examples.WalkingLocalization.Arrow) Y Z q)).toLoc ×ₘ
            𝟙 (MonoidalSingleObj.star (Type))) := by
        cases q with
        | inl f =>
            exact liftedModificationApp_naturality_generator Γ f
        | inr f =>
            simpa only [pathToCompletion_neg] using
              liftedModificationApp_naturality_generatorInv Γ f
      apply Pseudofunctor.StrongTrans.naturalityAt_of_iso η θ
        (liftedModificationApp Γ)
        (Iso.prod (Iso.refl _) (ρ_ (𝟙 (MonoidalSingleObj.star (Type)))))
      exact Pseudofunctor.StrongTrans.naturalityAt_comp η θ
        (liftedModificationApp Γ) ih hq

/-- Naturality holds for every free-groupoid 1-morphism when the retained
coordinate is the identity. -/
theorem liftedModificationApp_naturality_localizedOnly
    (Γ : (inclusion.localPrecomposition F G).obj η ⟶
      (inclusion.localPrecomposition F G).obj θ)
    {X Y : Ript.Examples.WalkingLocalization.Completion} (f : X ⟶ Y) :
    Pseudofunctor.StrongTrans.NaturalityAt η θ
      (liftedModificationApp Γ)
      (f.toLoc ×ₘ 𝟙 (MonoidalSingleObj.star (Type))) := by
  apply CategoryTheory.Quotient.induction
    (CategoryTheory.FreeGroupoid.homRel
      Ript.Examples.WalkingLocalization.Arrow)
    (P := fun {_ _} f =>
      Pseudofunctor.StrongTrans.NaturalityAt η θ
        (liftedModificationApp Γ)
        (f.toLoc ×ₘ 𝟙 (MonoidalSingleObj.star (Type))))
  intro X Y f
  apply CategoryTheory.Quotient.induction
    (@Quiver.FreeGroupoid.redStep
      Ript.Examples.WalkingLocalization.Arrow _)
    (P := fun {_ _} f =>
      Pseudofunctor.StrongTrans.NaturalityAt η θ
        (liftedModificationApp Γ)
        (((CategoryTheory.Quotient.functor
          (CategoryTheory.FreeGroupoid.homRel
            Ript.Examples.WalkingLocalization.Arrow)).map f).toLoc ×ₘ
          𝟙 (MonoidalSingleObj.star (Type))))
  intro X Y p
  exact liftedModificationApp_naturality_path Γ p

/-- A retained-coordinate endomorphism over a fixed localized object. -/
def retainedOnly (X : Ript.Examples.WalkingLocalization.Completion)
    (A : Type) :
    (LocallyDiscrete.mk X, MonoidalSingleObj.star (Type)) ⟶
      (LocallyDiscrete.mk X, MonoidalSingleObj.star (Type)) :=
  (𝟙 (LocallyDiscrete.mk X)) ×ₘ A

/-- Naturality holds for every retained-coordinate 1-morphism. -/
theorem liftedModificationApp_naturality_retainedOnly
    (Γ : (inclusion.localPrecomposition F G).obj η ⟶
      (inclusion.localPrecomposition F G).obj θ)
    (X : Ript.Examples.WalkingLocalization.Completion) (A : Type) :
    Pseudofunctor.StrongTrans.NaturalityAt η θ
      (liftedModificationApp Γ)
      (retainedOnly X A) := by
  let x : Ript.Examples.WalkingLocalization.Arrow := X.as.as
  rw [CategoryTheory.FreeGroupoid.eq_mk X]
  apply Pseudofunctor.StrongTrans.naturalityAt_of_iso η θ
    (liftedModificationApp Γ)
    (Iso.prod
      (Ript.Examples.WalkingLocalization.inclusion.mapId
        (LocallyDiscrete.mk x))
      (Iso.refl _))
  exact liftedModificationApp_naturality_map Γ
    (((𝟙 (LocallyDiscrete.mk x)) ×ₘ A) :
      (LocallyDiscrete.mk x, MonoidalSingleObj.star (Type)) ⟶
        (LocallyDiscrete.mk x, MonoidalSingleObj.star (Type)))

/-- Every target 1-morphism decomposes, up to unitors, into a localized-only
part followed by a retained-only part; hence the recovered components are
natural on the entire target. -/
theorem liftedModificationApp_naturality
    (Γ : (inclusion.localPrecomposition F G).obj η ⟶
      (inclusion.localPrecomposition F G).obj θ)
    {X Y : Target} (f : X ⟶ Y) :
    Pseudofunctor.StrongTrans.NaturalityAt η θ
      (liftedModificationApp Γ) f := by
  rcases X with ⟨⟨X⟩, X'⟩
  rcases Y with ⟨⟨Y⟩, Y'⟩
  cases X'
  cases Y'
  rcases f with ⟨⟨f⟩, A⟩
  apply Pseudofunctor.StrongTrans.naturalityAt_of_iso η θ
    (liftedModificationApp Γ)
    (Iso.prod (ρ_ f.toLoc) (λ_ A))
  exact Pseudofunctor.StrongTrans.naturalityAt_comp η θ
    (liftedModificationApp Γ)
    (liftedModificationApp_naturality_localizedOnly Γ f)
    (liftedModificationApp_naturality_retainedOnly Γ Y A)

/-- Lift a modification across the freely adjoined inverse. -/
noncomputable def liftModification
    (Γ : (inclusion.localPrecomposition F G).obj η ⟶
      (inclusion.localPrecomposition F G).obj θ) :
    Pseudofunctor.StrongTrans.Modification η θ where
  app := liftedModificationApp Γ
  naturality := liftedModificationApp_naturality Γ

/-- Precomposition by the parameterized walking localization is full on
every local category: modifications extend uniquely across the free-groupoid
coordinate. -/
theorem inclusion_localPrecomposition_full
    (F G : Target ⥤ᵖ E) :
    (inclusion.localPrecomposition F G).Full :=
  { map_surjective := by
      intro η θ Γ
      refine ⟨⟨liftModification Γ⟩, ?_⟩
      apply Pseudofunctor.StrongTrans.homCategory.ext
      intro X
      exact liftedModificationApp_inclusionObj Γ X }

/-- Precomposition is fully faithful on every local category of strong
transformations and modifications.  This closes the full-faithfulness half
of the local-equivalence field for the parameterized walking localization. -/
noncomputable def inclusionLocalPrecompositionFullyFaithful
    (F G : Target ⥤ᵖ E) :
    (inclusion.localPrecomposition F G).FullyFaithful := by
  letI : (inclusion.localPrecomposition F G).Full :=
    inclusion_localPrecomposition_full F G
  letI : (inclusion.localPrecomposition F G).Faithful :=
    inclusion_localPrecomposition_faithful F G
  exact Functor.FullyFaithful.ofFullyFaithful _

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

section SeparableMixedCoordinateLift

variable {G : Type u} [Groupoid.{v} G]
variable {E : Type u₂} [Bicategory.{w₂, v₂} E]

/-- A separable mixed-coordinate pseudofunctor.  Its first component is an
arbitrary groupoid-valued functor of the coordinate being localized, while
its second component is an arbitrary pseudofunctor of the retained
coordinate.  Unlike either preceding lift family, this construction depends
on both coordinates. -/
noncomputable def separableMixedSource
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G)
    (H : Cell ⥤ᵖ E) : Source ⥤ᵖ (LocallyDiscrete G × E) :=
  (localizedCoordinateSource K).pair (retainedSource H)

/-- Extend the localized component across the free groupoid and retain the
second component unchanged. -/
noncomputable def separableMixedLift
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G)
    (H : Cell ⥤ᵖ E) : Target ⥤ᵖ (LocallyDiscrete G × E) :=
  (localizedCoordinateLift K).pair (retainedLift H)

/-- A separable mixed-coordinate pseudofunctor factors through the
two-dimensional walking localization.  The equivalence is the componentwise
pairing of the localized- and retained-coordinate factorizations. -/
noncomputable def separableMixedFactorization
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G)
    (H : Cell ⥤ᵖ E) :
    inclusion.comp (separableMixedLift K H) ≌ separableMixedSource K H := by
  change ((inclusion.comp (localizedCoordinateLift K)).pair
      (inclusion.comp (retainedLift H))) ≌
    (localizedCoordinateSource K).pair (retainedSource H)
  exact Pseudofunctor.pairEquivalence
    (localizedCoordinateFactorization K) (retainedFactorization H)

/-- Every separable mixed-coordinate pseudofunctor sends the product marking
to adjoint equivalences. -/
theorem separableMixedSource_inverts
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G)
    (H : Cell ⥤ᵖ E) :
    marking.IsInvertedBy (separableMixedSource K H) := by
  intro X Y f hf
  obtain ⟨⟨e₁, he₁⟩⟩ := localizedCoordinateSource_inverts K f hf
  obtain ⟨⟨e₂, he₂⟩⟩ := retainedSource_inverts H f hf
  exact ⟨⟨e₁.prod e₂, Prod.ext he₁ he₂⟩⟩

/-- A separable family of genuinely mixed-coordinate witnesses for the
`lift` field of bicategorical localization. -/
theorem separableMixedSource_has_factorization
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G)
    (H : Cell ⥤ᵖ E) :
    ∃ L : Target ⥤ᵖ (LocallyDiscrete G × E),
      Nonempty (inclusion.comp L ≌ separableMixedSource K H) :=
  ⟨separableMixedLift K H, ⟨separableMixedFactorization K H⟩⟩

/-- The replete separable mixed family consists of arbitrary source
pseudofunctors that are adjoint equivalent to a separable mixed source.  A
member need not be definitionally a componentwise pair: only its
two-dimensional pseudofunctor semantics must lie in the same equivalence
class. -/
def IsRepleteSeparableMixedSource
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G)
    (H : Cell ⥤ᵖ E)
    (F : Source ⥤ᵖ (LocallyDiscrete G × E)) : Prop :=
  Nonempty (F ≌ separableMixedSource K H)

/-- Every syntactically separable mixed source belongs to its replete
closure. -/
theorem separableMixedSource_isReplete
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G)
    (H : Cell ⥤ᵖ E) :
    IsRepleteSeparableMixedSource K H (separableMixedSource K H) :=
  ⟨Bicategory.Equivalence.id _⟩

/-- Factorization extends from the literal componentwise pair to its entire
replete closure.  Thus the source `F` may have arbitrary, non-product
implementation data as long as it is adjoint equivalent to the compiled
separable mixed semantics. -/
theorem repleteSeparableMixedSource_has_factorization
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G)
    (H : Cell ⥤ᵖ E)
    (F : Source ⥤ᵖ (LocallyDiscrete G × E))
    (hF : IsRepleteSeparableMixedSource K H F) :
    inclusion.FactorsThrough F := by
  obtain ⟨e⟩ := hF
  exact Pseudofunctor.FactorsThrough.trans
    (separableMixedSource_has_factorization K H) e.symm

/-- Marking inversion also extends from the componentwise pair to its
replete closure.  It is transported through the chosen adjoint equivalence
of source pseudofunctors. -/
theorem repleteSeparableMixedSource_inverts
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G)
    (H : Cell ⥤ᵖ E)
    (F : Source ⥤ᵖ (LocallyDiscrete G × E))
    (hF : IsRepleteSeparableMixedSource K H F) :
    marking.IsInvertedBy F := by
  obtain ⟨e⟩ := hF
  exact Bicategory.MorphismProperty.IsInvertedBy.of_equivalence
    marking (separableMixedSource_inverts K H) e

/-- Every member of the replete separable mixed family satisfies both the
premise and the factorization conclusion of the localization `lift` field.
This is strictly more flexible than requiring the source to be definitionally
the pair `K × H`, while still stopping short of arbitrary mixed-coordinate
pseudofunctors. -/
theorem repleteSeparableMixedSource_inverts_and_factors
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G)
    (H : Cell ⥤ᵖ E)
    (F : Source ⥤ᵖ (LocallyDiscrete G × E))
    (hF : IsRepleteSeparableMixedSource K H F) :
    marking.IsInvertedBy F ∧ inclusion.FactorsThrough F :=
  ⟨repleteSeparableMixedSource_inverts K H F hF,
    repleteSeparableMixedSource_has_factorization K H F hF⟩

/-- The mixed lift interprets the formally adjoined inverse correctly in its
localized first component, independently of the retained component. -/
theorem separableMixedLift_map_inverse_fst
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G)
    (H : Cell ⥤ᵖ E) :
    ((separableMixedLift K H).map inverse).1 =
      (inv (K.map Ript.Examples.WalkingLocalization.arrow)).toLoc := by
  change (localizedCoordinateLift K).map inverse = _
  exact localizedCoordinateLift_map_inverse K

/-- Pairing with the identity retained coordinate preserves the concrete
noninvertible Boolean discard 2-cell. -/
theorem separableMixedIdentity_map₂_discardTwoCell_not_isIso
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G) :
    ¬ IsIso ((separableMixedSource K (Pseudofunctor.id Cell)).map₂
      discardTwoCell) := by
  intro h
  have hSecond :
      IsIso (((separableMixedSource K (Pseudofunctor.id Cell)).map₂
        discardTwoCell).2) :=
    (isIso_prod_iff
      (f := (separableMixedSource K (Pseudofunctor.id Cell)).map₂
        discardTwoCell)).1 h |>.2
  have hInjective :=
    (isIso_iff_bijective
      ((separableMixedSource K (Pseudofunctor.id Cell)).map₂
        discardTwoCell).2).1 hSecond |>.1
  change Function.Injective (fun _ : Bool => PUnit.unit) at hInjective
  exact Bool.false_ne_true (hInjective rfl)

/-- The separable mixed family simultaneously supplies marking inversion,
factorization, correct interpretation of the new inverse, and retention of a
noninvertible 2-cell.  This is a mixed-coordinate fragment of the universal
property, not the still-open arbitrary mixed-coordinate lift. -/
theorem separableMixedIdentity_inverts_factors_maps_inverse_and_retains_discard
    (K : Ript.Examples.WalkingLocalization.Arrow ⥤ G) :
    marking.IsInvertedBy
        (separableMixedSource K (Pseudofunctor.id Cell)) ∧
      (∃ L : Target ⥤ᵖ (LocallyDiscrete G × Cell),
        Nonempty (inclusion.comp L ≌
          separableMixedSource K (Pseudofunctor.id Cell))) ∧
      ((separableMixedLift K (Pseudofunctor.id Cell)).map inverse).1 =
        (inv (K.map Ript.Examples.WalkingLocalization.arrow)).toLoc ∧
      ¬ IsIso ((separableMixedSource K (Pseudofunctor.id Cell)).map₂
        discardTwoCell) :=
  ⟨separableMixedSource_inverts K _,
    separableMixedSource_has_factorization K _,
    separableMixedLift_map_inverse_fst K _,
    separableMixedIdentity_map₂_discardTwoCell_not_isIso K⟩

end SeparableMixedCoordinateLift

end Ript.Examples.TwoDimensionalWalkingLocalization
