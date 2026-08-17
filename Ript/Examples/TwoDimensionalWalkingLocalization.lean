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
At constructor level, the inverse-generator mate followed by an arbitrary
retained-coordinate constraint is now proved to recover the public constraint
on its raw composite.  Both inverse/retained orders now satisfy public-factor
composition coherence.  The inverse-generator/forward-generator cancellation
order is proved by a general mate-counit identity and transport injectivity;
the forward-generator/inverse-generator order is now proved symmetrically by
a mate-unit identity.  Candidate composition is associative after associator
transport and is stable under isomorphism of either factor.  These tools extend
both mixed orders to canonical inverse arrows and discharge both
endpoint-changing cancellation orders with arbitrary retained coordinates.
Thinness of the completed walking coordinate then reduces every target pair to
one of those compiled cases.  The result packages as a genuine target strong
transformation whose restriction is isomorphic to the source transformation;
modifications lift as well, so precomposition is an equivalence on every local
category.  For an arbitrary marking-inverting source pseudofunctor, the chosen
endpoint equivalences now also determine a compiled `PrelaxFunctor` action on
all target objects, 1-morphisms, and 2-morphisms.  Its equations on canonical
forward arrows and genuinely reverse arrows are explicit.  An identity
comparison is now defined at every target object.  Composition comparisons are
compiled for all eight endpoint-normalized pairs: forward/forward, both
retained/inverse orders, and both inverse/forward cancellation orders with
arbitrary retained coordinates.  Endpoint normalization now packages those
branches into one comparison for every composable target-arrow pair, with
compiled reduction equations exposing all eight branches.  Proving the
pseudofunctor coherence laws and constructing the resulting arbitrary
nonseparable biessential factorization still remain open;
consequently the global `lift` field of the bicategorical-localization
predicate is not yet claimed.
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

/-- The generator constraint is the forward constraint at the retained
identity, after the canonical identity-map comparison. -/
theorem liftedStrongTransGeneratorNaturality_eq_forward
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow} (f : X ⟶ Y) :
    liftedStrongTransGeneratorNaturality σ f =
      liftedStrongTransForwardNaturality σ f
        (𝟙 (MonoidalSingleObj.star (Type))) := by
  change Pseudofunctor.StrongTrans.naturalityIsoOfIso F G _ _
      (liftedStrongTransForwardNaturality σ f
        (𝟙 (MonoidalSingleObj.star (Type))))
      (Iso.prod (Iso.refl _)
        ((Pseudofunctor.id Cell).mapId
          (MonoidalSingleObj.star (Type)))) = _
  have he :
      (Iso.refl
          (CategoryTheory.FreeGroupoid.homMk f).toLoc).prod
          ((Pseudofunctor.id Cell).mapId
            (MonoidalSingleObj.star (Type))) =
        Iso.refl _ := by
    apply Iso.ext
    apply Prod.ext
    · rfl
    · rfl
  cases he
  exact Pseudofunctor.StrongTrans.naturalityIsoOfIso_refl F G
    _ _ _ _

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

/-- Composing a retained-coordinate endomorphism with the inverse generator
is canonically isomorphic to the corresponding inverse target arrow.  This is
the right-unitor counterpart of `canonicalInverseComparison`. -/
noncomputable def canonicalRetainedInverseComparison
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    canonicalForwardHom (𝟙 Y) A ≫ (generatorEquivalence f).inv ≅
      canonicalInverseHom f A :=
  Iso.prod (eqToIso (by
    apply Discrete.ext
    change CategoryTheory.FreeGroupoid.homMk (𝟙 Y) ≫
        inv (CategoryTheory.FreeGroupoid.homMk f) =
      inv (CategoryTheory.FreeGroupoid.homMk f)
    simp))
    (by
      change A ≫ 𝟙 (MonoidalSingleObj.star (Type)) ≅ A
      exact MonoidalCategory.rightUnitor A)

/-- A forward generator followed by a retained-coordinate endomorphism is
canonically isomorphic to the corresponding forward target arrow. -/
noncomputable def canonicalGeneratorRetainedComparison
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (generatorEquivalence f).hom ≫ canonicalForwardHom (𝟙 Y) A ≅
      canonicalForwardHom f A :=
  Iso.prod (eqToIso (by
    apply Discrete.ext
    change CategoryTheory.FreeGroupoid.homMk f ≫
        CategoryTheory.FreeGroupoid.homMk (𝟙 Y) =
      CategoryTheory.FreeGroupoid.homMk f
    simp))
    (by
      change (𝟙 (MonoidalSingleObj.star (Type))) ≫ A ≅ A
      exact MonoidalCategory.leftUnitor A)

/-- A retained-coordinate endomorphism followed by a forward generator is
canonically isomorphic to the corresponding forward target arrow. -/
noncomputable def canonicalRetainedGeneratorComparison
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    canonicalForwardHom (𝟙 X) A ≫ (generatorEquivalence f).hom ≅
      canonicalForwardHom f A :=
  Iso.prod (eqToIso (by
    apply Discrete.ext
    change CategoryTheory.FreeGroupoid.homMk (𝟙 X) ≫
        CategoryTheory.FreeGroupoid.homMk f =
      CategoryTheory.FreeGroupoid.homMk f
    simp))
    (by
      change A ≫ 𝟙 (MonoidalSingleObj.star (Type)) ≅ A
      exact MonoidalCategory.rightUnitor A)

/-- Two retained-coordinate endomorphisms compose to the retained product
type, while the walking coordinate remains the canonical identity arrow. -/
noncomputable def canonicalRetainedCompositionComparison
    (X : Ript.Examples.WalkingLocalization.Arrow) (A B : Type) :
    canonicalForwardHom (𝟙 X) A ≫ canonicalForwardHom (𝟙 X) B ≅
      canonicalForwardHom (𝟙 X) (A × B) :=
  Iso.prod (eqToIso (by
    apply Discrete.ext
    change CategoryTheory.FreeGroupoid.homMk (𝟙 X) ≫
        CategoryTheory.FreeGroupoid.homMk (𝟙 X) =
      CategoryTheory.FreeGroupoid.homMk (𝟙 X)
    simp)) (Iso.refl _)

/-- Cancelling a canonical inverse arrow against the forward generator
leaves its retained coordinate at the codomain endpoint. -/
noncomputable def canonicalInverseForwardCancellationComparison
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    canonicalInverseHom f A ≫ (generatorEquivalence f).hom ≅
      canonicalForwardHom (𝟙 Y) A :=
  Iso.prod (eqToIso (by
    apply Discrete.ext
    change inv (CategoryTheory.FreeGroupoid.homMk f) ≫
        CategoryTheory.FreeGroupoid.homMk f =
      CategoryTheory.FreeGroupoid.homMk (𝟙 Y)
    simp)) (MonoidalCategory.rightUnitor A)

/-- Cancelling a canonical forward arrow against the inverse generator
leaves its retained coordinate at the domain endpoint. -/
noncomputable def canonicalForwardInverseCancellationComparison
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    canonicalForwardHom f A ≫ (generatorEquivalence f).inv ≅
      canonicalForwardHom (𝟙 X) A :=
  Iso.prod (eqToIso (by
    apply Discrete.ext
    change CategoryTheory.FreeGroupoid.homMk f ≫
        inv (CategoryTheory.FreeGroupoid.homMk f) =
      CategoryTheory.FreeGroupoid.homMk (𝟙 X)
    simp)) (MonoidalCategory.rightUnitor A)

/-- Slide a retained-coordinate endomorphism across a forward generator.
Both composites normalize to the same canonical forward arrow. -/
noncomputable def canonicalForwardSlidingComparison
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    canonicalForwardHom (𝟙 X) A ≫ (generatorEquivalence f).hom ≅
      (generatorEquivalence f).hom ≫ canonicalForwardHom (𝟙 Y) A :=
  canonicalRetainedGeneratorComparison f A ≪≫
    (canonicalGeneratorRetainedComparison f A).symm

/-- Slide a retained-coordinate endomorphism across an inverse generator.
Both composites normalize to the same canonical inverse arrow. -/
noncomputable def canonicalInverseSlidingComparison
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (generatorEquivalence f).inv ≫ canonicalForwardHom (𝟙 X) A ≅
      canonicalForwardHom (𝟙 Y) A ≫ (generatorEquivalence f).inv :=
  canonicalInverseComparison f A ≪≫
    (canonicalRetainedInverseComparison f A).symm

set_option backward.isDefEq.respectTransparency false in
/-- The inverse sliding comparison is exactly the mate of the forward
sliding comparison.  Thus the product left- and right-unitor normalizations
are compatible with the chosen generator adjoint equivalence. -/
theorem canonicalInverseSlidingComparison_hom
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    mateEquiv (generatorEquivalence f).toAdjunction
        (generatorEquivalence f).toAdjunction
        (canonicalForwardSlidingComparison f A).hom =
      (canonicalInverseSlidingComparison f A).hom := by
  rw [mateEquiv_apply']
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · dsimp [canonicalForwardSlidingComparison,
      canonicalInverseSlidingComparison,
      canonicalRetainedGeneratorComparison,
      canonicalGeneratorRetainedComparison,
      canonicalInverseComparison,
      canonicalRetainedInverseComparison,
      generatorEquivalence, Bicategory.Equivalence.toAdjunction]
    rfl

/-- The canonical forward identity arrow is isomorphic to the strict target
identity through the inclusion pseudofunctor's unit comparison. -/
noncomputable def canonicalForwardIdentityComparison
    (X : Ript.Examples.WalkingLocalization.Arrow) :
    canonicalForwardHom (𝟙 X)
        (𝟙 (MonoidalSingleObj.star (Type))) ≅
      𝟙 (canonicalTargetObject X) :=
  inclusion.mapId (canonicalSourceObject X)

/-- Composing an inverse generator with the canonical forward identity and
then applying its identity comparison reduces to the inverse generator by
the right unitor. -/
noncomputable def canonicalInverseUnitComparison
    {X Y : Ript.Examples.WalkingLocalization.Arrow} (f : X ⟶ Y) :
    (generatorEquivalence f).inv ≫
        canonicalForwardHom (𝟙 X)
          (𝟙 (MonoidalSingleObj.star (Type))) ≅
      (generatorEquivalence f).inv :=
  whiskerLeftIso (generatorEquivalence f).inv
      (canonicalForwardIdentityComparison X) ≪≫
    ρ_ (generatorEquivalence f).inv

set_option backward.isDefEq.respectTransparency false in
/-- At the retained-coordinate identity, the product comparison used for
inverse arrows is exactly identity normalization followed by the right
unitor. -/
theorem canonicalInverseComparison_identity
    {X Y : Ript.Examples.WalkingLocalization.Arrow} (f : X ⟶ Y) :
    canonicalInverseComparison f
        (𝟙 (MonoidalSingleObj.star (Type))) =
      canonicalInverseUnitComparison f := by
  apply Iso.ext
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · dsimp [canonicalInverseComparison, canonicalInverseUnitComparison,
      canonicalForwardIdentityComparison, canonicalForwardHom,
      canonicalInverseHom]
    rfl

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

/-- Compose a retained-coordinate constraint with the inverse-generator mate.
This is the candidate constraint for the opposite mixed order from
`liftedStrongTransInverseCompositeNaturality`. -/
noncomputable def liftedStrongTransRetainedInverseCompositeNaturality
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    F.map (canonicalForwardHom (𝟙 Y) A ≫
          (generatorEquivalence f).inv) ≫
        liftedStrongTransApp σ (canonicalTargetObject X) ≅
      liftedStrongTransApp σ (canonicalTargetObject Y) ≫
        G.map (canonicalForwardHom (𝟙 Y) A ≫
          (generatorEquivalence f).inv) :=
  Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
    (canonicalForwardHom (𝟙 Y) A)
    (generatorEquivalence f).inv
    (liftedStrongTransApp σ (canonicalTargetObject Y))
    (liftedStrongTransApp σ (canonicalTargetObject Y))
    (liftedStrongTransApp σ (canonicalTargetObject X))
    (liftedStrongTransForwardNaturality σ (𝟙 Y) A)
    (liftedStrongTransGeneratorInverseNaturality σ f)

/-- Transport the retained-then-inverse composite constraint to the canonical
inverse arrow.  Proving that this agrees with
`liftedStrongTransInverseNaturality` is the mixed sliding law. -/
noncomputable def liftedStrongTransRetainedInverseNaturality
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    F.map (canonicalInverseHom f A) ≫
        liftedStrongTransApp σ (canonicalTargetObject X) ≅
      liftedStrongTransApp σ (canonicalTargetObject Y) ≫
        G.map (canonicalInverseHom f A) :=
  Pseudofunctor.StrongTrans.naturalityIsoOfIso F G _ _
    (liftedStrongTransRetainedInverseCompositeNaturality σ f A)
    (canonicalRetainedInverseComparison f A)

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
/-- The explicitly composed inverse-generator and retained-coordinate
constraint is the endpoint-normalized constraint on that raw composite.
Injectivity of transport across `canonicalInverseComparison` recovers the
constraint before normalization. -/
theorem liftedStrongTransEndpointNaturality_inverseComposite
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (h : ¬ Y ≤ X) (A : Type) :
    liftedStrongTransEndpointNaturality σ
        ((generatorEquivalence f).inv ≫
          canonicalForwardHom (𝟙 X) A) =
      liftedStrongTransInverseCompositeNaturality σ f A := by
  apply Pseudofunctor.StrongTrans.naturalityIsoOfIso_injective
    (F := F) (G := G)
    (liftedStrongTransApp σ (canonicalTargetObject Y))
    (liftedStrongTransApp σ (canonicalTargetObject X))
    (canonicalInverseComparison f A)
  dsimp only
  rw [liftedStrongTransEndpointNaturality_iso]
  change liftedStrongTransEndpointNaturality σ
      (canonicalInverseHom f A) =
    liftedStrongTransInverseNaturality σ f A
  exact liftedStrongTransEndpointNaturality_inverse_of_not_le σ f h A

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

/-- Transporting source naturality at the canonical forward identity across
the inclusion's unit comparison yields the target identity constraint. -/
theorem liftedStrongTransForwardIdentityNaturality_transport
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    (X : Ript.Examples.WalkingLocalization.Arrow) :
    Pseudofunctor.StrongTrans.naturalityIsoOfIso F G
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransForwardNaturality σ (𝟙 X)
          (𝟙 (MonoidalSingleObj.star (Type))))
        (canonicalForwardIdentityComparison X) =
      liftedStrongTransIdentityNaturality σ
        (canonicalTargetObject X) := by
  rw [← liftedStrongTransEndpointNaturality_forward]
  rw [liftedStrongTransEndpointNaturality_iso]
  exact liftedStrongTransEndpointNaturality_id_eq σ
    (canonicalTargetObject X)

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

/-- The public all-arrow constraint on every canonical forward arrow is the
original source strong-naturality constraint. -/
theorem liftedStrongTransNaturality_forward
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    liftedStrongTransNaturality σ (canonicalForwardHom f A) =
      liftedStrongTransForwardNaturality σ f A := by
  rw [liftedStrongTransNaturality_eq_endpoint]
  exact liftedStrongTransEndpointNaturality_forward σ f A

/-- On a forward walking generator, the public all-arrow constraint is the
generator constraint from which inverse naturality is obtained by mates. -/
theorem liftedStrongTransNaturality_generator
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) :
    liftedStrongTransNaturality σ (generatorEquivalence f).hom =
      liftedStrongTransGeneratorNaturality σ f := by
  change liftedStrongTransNaturality σ
      (canonicalForwardHom f
        (𝟙 (MonoidalSingleObj.star (Type)))) = _
  rw [liftedStrongTransNaturality_forward]
  exact (liftedStrongTransGeneratorNaturality_eq_forward σ f).symm

set_option backward.isDefEq.respectTransparency false in
/-- On a strict reverse walking arrow, the public all-arrow constraint is
exactly the mate-derived inverse-generator constraint.  The retained identity
inserted by endpoint normalization cancels by pseudofunctorial transport and
the bicategorical right-unit law. -/
theorem liftedStrongTransNaturality_generatorInverse
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (h : ¬ Y ≤ X) :
    liftedStrongTransNaturality σ (generatorEquivalence f).inv =
      liftedStrongTransGeneratorInverseNaturality σ f := by
  rw [liftedStrongTransNaturality_eq_endpoint]
  change liftedStrongTransEndpointNaturality σ
      (canonicalInverseHom f
        (𝟙 (MonoidalSingleObj.star (Type)))) = _
  rw [liftedStrongTransEndpointNaturality_inverse_of_not_le σ f h]
  dsimp [liftedStrongTransInverseNaturality]
  rw [canonicalInverseComparison_identity]
  dsimp [canonicalInverseUnitComparison]
  rw [Pseudofunctor.StrongTrans.naturalityIsoOfIso_trans]
  change
    Pseudofunctor.StrongTrans.naturalityIsoOfIso F G
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (Pseudofunctor.StrongTrans.naturalityIsoOfIso F G
          (liftedStrongTransApp σ (canonicalTargetObject Y))
          (liftedStrongTransApp σ (canonicalTargetObject X))
          (Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
            (generatorEquivalence f).inv
            (canonicalForwardHom (𝟙 X)
              (𝟙 (MonoidalSingleObj.star (Type))))
            (liftedStrongTransApp σ (canonicalTargetObject Y))
            (liftedStrongTransApp σ (canonicalTargetObject X))
            (liftedStrongTransApp σ (canonicalTargetObject X))
            (liftedStrongTransGeneratorInverseNaturality σ f)
            (liftedStrongTransForwardNaturality σ (𝟙 X)
              (𝟙 (MonoidalSingleObj.star (Type)))))
          (whiskerLeftIso (generatorEquivalence f).inv
            (canonicalForwardIdentityComparison X)))
        (ρ_ (generatorEquivalence f).inv) =
      liftedStrongTransGeneratorInverseNaturality σ f
  rw [Pseudofunctor.StrongTrans.naturalityIsoOfIso_comp_right]
  rw [liftedStrongTransForwardIdentityNaturality_transport]
  simpa only [liftedStrongTransIdentityNaturality,
    Pseudofunctor.StrongTrans.identityNaturalityIso,
    canonicalTargetObject] using
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos_right_id
      F G (generatorEquivalence f).inv
      (liftedStrongTransApp σ (canonicalTargetObject Y))
      (liftedStrongTransApp σ (canonicalTargetObject X))
      (liftedStrongTransGeneratorInverseNaturality σ f)

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

/-- The inverse-generator mate followed by its forward generator becomes the
canonical identity constraint after transport across the chosen adjoint
equivalence counit. -/
theorem liftedStrongTransGeneratorCancellation_counit
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) :
    Pseudofunctor.StrongTrans.naturalityIsoOfIso F G
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
          (generatorEquivalence f).inv (generatorEquivalence f).hom
          (liftedStrongTransApp σ (canonicalTargetObject Y))
          (liftedStrongTransApp σ (canonicalTargetObject X))
          (liftedStrongTransApp σ (canonicalTargetObject Y))
          (liftedStrongTransGeneratorInverseNaturality σ f)
          (liftedStrongTransGeneratorNaturality σ f))
        (generatorEquivalence f).counit =
      liftedStrongTransIdentityNaturality σ
        (canonicalTargetObject Y) := by
  exact Pseudofunctor.StrongTrans.inverseNaturalityIso_comp_hom_counit
    F G (generatorEquivalence f)
      (liftedStrongTransApp σ (canonicalTargetObject X))
      (liftedStrongTransApp σ (canonicalTargetObject Y))
      (liftedStrongTransGeneratorNaturality σ f)

/-- A forward generator followed by its mate-derived inverse becomes the
canonical identity constraint after transport across the inverse unit of the
chosen generator equivalence. -/
theorem liftedStrongTransGeneratorCancellation_unit
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) :
    Pseudofunctor.StrongTrans.naturalityIsoOfIso F G
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
          (generatorEquivalence f).hom (generatorEquivalence f).inv
          (liftedStrongTransApp σ (canonicalTargetObject X))
          (liftedStrongTransApp σ (canonicalTargetObject Y))
          (liftedStrongTransApp σ (canonicalTargetObject X))
          (liftedStrongTransGeneratorNaturality σ f)
          (liftedStrongTransGeneratorInverseNaturality σ f))
        (generatorEquivalence f).unit.symm =
      liftedStrongTransIdentityNaturality σ
        (canonicalTargetObject X) := by
  exact Pseudofunctor.StrongTrans.hom_comp_inverseNaturalityIso_unit
    F G (generatorEquivalence f)
      (liftedStrongTransApp σ (canonicalTargetObject X))
      (liftedStrongTransApp σ (canonicalTargetObject Y))
      (liftedStrongTransGeneratorNaturality σ f)

set_option backward.isDefEq.respectTransparency false in
/-- For a strict reverse walking generator, the canonical composition of its
public inverse and forward constraints is the public constraint on the raw
canceling composite.  Both sides are identified after transport across the
generator adjoint equivalence counit. -/
theorem liftedStrongTransNaturality_compIso_inverseGenerator_generator
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (h : ¬ Y ≤ X) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        (generatorEquivalence f).inv (generatorEquivalence f).hom
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransNaturality σ (generatorEquivalence f).inv)
        (liftedStrongTransNaturality σ (generatorEquivalence f).hom) =
      liftedStrongTransNaturality σ
        ((generatorEquivalence f).inv ≫
          (generatorEquivalence f).hom) := by
  apply Pseudofunctor.StrongTrans.naturalityIsoOfIso_injective F G
    (liftedStrongTransApp σ (canonicalTargetObject Y))
    (liftedStrongTransApp σ (canonicalTargetObject Y))
    (generatorEquivalence f).counit
  rw [liftedStrongTransNaturality_generatorInverse σ f h,
    liftedStrongTransNaturality_generator]
  have hleft := liftedStrongTransGeneratorCancellation_counit
    (F := F) (G := G) σ f
  have hright := liftedStrongTransNaturality_iso
    (F := F) (G := G) σ (generatorEquivalence f).counit
  rw [liftedStrongTransNaturality_id_eq] at hright
  exact hleft.trans hright.symm

set_option backward.isDefEq.respectTransparency false in
/-- The public all-arrow constraint satisfies the strong-transformation
composition equation for a strict inverse generator followed by its forward
generator. -/
theorem liftedStrongTransNaturality_comp_inverseGenerator_generator
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (h : ¬ Y ≤ X) :
    (liftedStrongTransNaturality σ
        ((generatorEquivalence f).inv ≫
          (generatorEquivalence f).hom)).hom ≫
        liftedStrongTransApp σ (canonicalTargetObject Y) ◁
          (G.mapComp (generatorEquivalence f).inv
            (generatorEquivalence f).hom).hom =
      (F.mapComp (generatorEquivalence f).inv
          (generatorEquivalence f).hom).hom ▷
          liftedStrongTransApp σ (canonicalTargetObject Y) ≫
        (α_ _ _ _).hom ≫
        F.map (generatorEquivalence f).inv ◁
          (liftedStrongTransNaturality σ
            (generatorEquivalence f).hom).hom ≫
        (α_ _ _ _).inv ≫
        (liftedStrongTransNaturality σ
          (generatorEquivalence f).inv).hom ▷
            G.map (generatorEquivalence f).hom ≫
        (α_ _ _ _).hom := by
  have hcomp :=
    liftedStrongTransNaturality_compIso_inverseGenerator_generator
      (F := F) (G := G) σ f h
  rw [← hcomp]
  simp [Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos,
    Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- For a strict walking generator, the canonical composition of its public
forward and inverse constraints is the public constraint on the raw canceling
composite.  Both sides are identified after transport across the inverse
generator unit. -/
theorem liftedStrongTransNaturality_compIso_generator_inverseGenerator
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (h : ¬ Y ≤ X) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        (generatorEquivalence f).hom (generatorEquivalence f).inv
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransNaturality σ (generatorEquivalence f).hom)
        (liftedStrongTransNaturality σ (generatorEquivalence f).inv) =
      liftedStrongTransNaturality σ
        ((generatorEquivalence f).hom ≫
          (generatorEquivalence f).inv) := by
  apply Pseudofunctor.StrongTrans.naturalityIsoOfIso_injective F G
    (liftedStrongTransApp σ (canonicalTargetObject X))
    (liftedStrongTransApp σ (canonicalTargetObject X))
    (generatorEquivalence f).unit.symm
  rw [liftedStrongTransNaturality_generator,
    liftedStrongTransNaturality_generatorInverse σ f h]
  have hleft := liftedStrongTransGeneratorCancellation_unit
    (F := F) (G := G) σ f
  have hright := liftedStrongTransNaturality_iso
    (F := F) (G := G) σ (generatorEquivalence f).unit.symm
  rw [liftedStrongTransNaturality_id_eq] at hright
  exact hleft.trans hright.symm

set_option backward.isDefEq.respectTransparency false in
/-- The public all-arrow constraint satisfies the strong-transformation
composition equation for a strict forward generator followed by its inverse
generator. -/
theorem liftedStrongTransNaturality_comp_generator_inverseGenerator
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (h : ¬ Y ≤ X) :
    (liftedStrongTransNaturality σ
        ((generatorEquivalence f).hom ≫
          (generatorEquivalence f).inv)).hom ≫
        liftedStrongTransApp σ (canonicalTargetObject X) ◁
          (G.mapComp (generatorEquivalence f).hom
            (generatorEquivalence f).inv).hom =
      (F.mapComp (generatorEquivalence f).hom
          (generatorEquivalence f).inv).hom ▷
          liftedStrongTransApp σ (canonicalTargetObject X) ≫
        (α_ _ _ _).hom ≫
        F.map (generatorEquivalence f).hom ◁
          (liftedStrongTransNaturality σ
            (generatorEquivalence f).inv).hom ≫
        (α_ _ _ _).inv ≫
        (liftedStrongTransNaturality σ
          (generatorEquivalence f).hom).hom ▷
            G.map (generatorEquivalence f).inv ≫
        (α_ _ _ _).hom := by
  have hcomp :=
    liftedStrongTransNaturality_compIso_generator_inverseGenerator
      (F := F) (G := G) σ f h
  rw [← hcomp]
  simp [Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos,
    Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The public constraint on the raw inverse-generator/retained composite is
the explicitly composed constraint. -/
theorem liftedStrongTransNaturality_inverseComposite
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (h : ¬ Y ≤ X) (A : Type) :
    liftedStrongTransNaturality σ
        ((generatorEquivalence f).inv ≫
          canonicalForwardHom (𝟙 X) A) =
      liftedStrongTransInverseCompositeNaturality σ f A := by
  rw [liftedStrongTransNaturality_eq_endpoint]
  exact liftedStrongTransEndpointNaturality_inverseComposite σ f h A

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

/-- The hom-level forward composition law packages as equality with the
canonical composite of the two public constraints. -/
theorem liftedStrongTransNaturality_compIso_forward
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {x y z : Ript.Examples.WalkingLocalization.Arrow}
    (f : x ⟶ y) (g : y ⟶ z) (A B : Type) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        (canonicalForwardHom f A) (canonicalForwardHom g B)
        (liftedStrongTransApp σ (canonicalTargetObject x))
        (liftedStrongTransApp σ (canonicalTargetObject y))
        (liftedStrongTransApp σ (canonicalTargetObject z))
        (liftedStrongTransNaturality σ (canonicalForwardHom f A))
        (liftedStrongTransNaturality σ (canonicalForwardHom g B)) =
      liftedStrongTransNaturality σ
        (canonicalForwardHom f A ≫ canonicalForwardHom g B) := by
  apply Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos_eq_of_coherence
  exact liftedStrongTransNaturality_comp_forward σ f g A B

/-- Composing the public forward-generator constraint with a retained
constraint and transporting across the product left unitor recovers the
public constraint on the combined forward arrow. -/
theorem liftedStrongTransNaturality_generatorRetained_transport
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    Pseudofunctor.StrongTrans.naturalityIsoOfIso F G
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
          (canonicalForwardHom f
            (𝟙 (MonoidalSingleObj.star (Type))))
          (canonicalForwardHom (𝟙 Y) A)
          (liftedStrongTransApp σ (canonicalTargetObject X))
          (liftedStrongTransApp σ (canonicalTargetObject Y))
          (liftedStrongTransApp σ (canonicalTargetObject Y))
          (liftedStrongTransNaturality σ
            (canonicalForwardHom f
              (𝟙 (MonoidalSingleObj.star (Type)))))
          (liftedStrongTransNaturality σ
            (canonicalForwardHom (𝟙 Y) A)))
        (canonicalGeneratorRetainedComparison f A) =
      liftedStrongTransNaturality σ (canonicalForwardHom f A) := by
  rw [liftedStrongTransNaturality_compIso_forward]
  exact liftedStrongTransNaturality_iso σ
    (canonicalGeneratorRetainedComparison f A)

/-- Composing a retained constraint with the public forward-generator
constraint and transporting across the product right unitor recovers the
same public constraint on the combined forward arrow. -/
theorem liftedStrongTransNaturality_retainedGenerator_transport
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    Pseudofunctor.StrongTrans.naturalityIsoOfIso F G
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
          (canonicalForwardHom (𝟙 X) A)
          (canonicalForwardHom f
            (𝟙 (MonoidalSingleObj.star (Type))))
          (liftedStrongTransApp σ (canonicalTargetObject X))
          (liftedStrongTransApp σ (canonicalTargetObject X))
          (liftedStrongTransApp σ (canonicalTargetObject Y))
          (liftedStrongTransNaturality σ
            (canonicalForwardHom (𝟙 X) A))
          (liftedStrongTransNaturality σ
            (canonicalForwardHom f
              (𝟙 (MonoidalSingleObj.star (Type))))))
        (canonicalRetainedGeneratorComparison f A) =
      liftedStrongTransNaturality σ (canonicalForwardHom f A) := by
  rw [liftedStrongTransNaturality_compIso_forward]
  exact liftedStrongTransNaturality_iso σ
    (canonicalRetainedGeneratorComparison f A)

set_option backward.isDefEq.respectTransparency false in
/-- Sliding a retained-coordinate constraint past the inverse generator
transports the retained-then-inverse composite candidate to the
inverse-then-retained composite candidate.  This is the concrete
walking-localization instance of `inverseNaturalityIso_sliding`. -/
theorem liftedStrongTransRetainedInverse_sliding
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    Pseudofunctor.StrongTrans.naturalityIsoOfIso F G
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransRetainedInverseCompositeNaturality σ f A)
        (canonicalInverseSlidingComparison f A).symm =
      liftedStrongTransInverseCompositeNaturality σ f A := by
  apply Pseudofunctor.StrongTrans.inverseNaturalityIso_sliding
    (generatorEquivalence f)
    (canonicalForwardHom (𝟙 X) A)
    (canonicalForwardHom (𝟙 Y) A)
    (canonicalForwardSlidingComparison f A)
    (canonicalInverseSlidingComparison f A).symm
    (liftedStrongTransApp σ (canonicalTargetObject X))
    (liftedStrongTransApp σ (canonicalTargetObject Y))
    (liftedStrongTransForwardNaturality σ (𝟙 X) A)
    (liftedStrongTransGeneratorNaturality σ f)
    (liftedStrongTransForwardNaturality σ (𝟙 Y) A)
  · dsimp [canonicalForwardSlidingComparison]
    have hLeft :=
      liftedStrongTransNaturality_retainedGenerator_transport
        (F := F) (G := G) σ f A
    simp only [liftedStrongTransNaturality_forward] at hLeft
    rw [← liftedStrongTransGeneratorNaturality_eq_forward] at hLeft
    have hRight :=
      liftedStrongTransNaturality_compIso_forward
        (F := F) (G := G) σ f (𝟙 Y)
          (𝟙 (MonoidalSingleObj.star (Type))) A
    simp only [liftedStrongTransNaturality_forward] at hRight
    rw [← liftedStrongTransGeneratorNaturality_eq_forward] at hRight
    rw [Pseudofunctor.StrongTrans.naturalityIsoOfIso_trans]
    change
      Pseudofunctor.StrongTrans.naturalityIsoOfIso F G
          (liftedStrongTransApp σ (canonicalTargetObject X))
          (liftedStrongTransApp σ (canonicalTargetObject Y))
          (Pseudofunctor.StrongTrans.naturalityIsoOfIso F G
            (liftedStrongTransApp σ (canonicalTargetObject X))
            (liftedStrongTransApp σ (canonicalTargetObject Y))
            (Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
              (canonicalForwardHom (𝟙 X) A)
              (canonicalForwardHom f
                (𝟙 (MonoidalSingleObj.star (Type))))
              (liftedStrongTransApp σ (canonicalTargetObject X))
              (liftedStrongTransApp σ (canonicalTargetObject X))
              (liftedStrongTransApp σ (canonicalTargetObject Y))
              (liftedStrongTransForwardNaturality σ (𝟙 X) A)
              (liftedStrongTransGeneratorNaturality σ f))
            (canonicalRetainedGeneratorComparison f A))
          (canonicalGeneratorRetainedComparison f A).symm =
        Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
          (canonicalForwardHom f
            (𝟙 (MonoidalSingleObj.star (Type))))
          (canonicalForwardHom (𝟙 Y) A)
          (liftedStrongTransApp σ (canonicalTargetObject X))
          (liftedStrongTransApp σ (canonicalTargetObject Y))
          (liftedStrongTransApp σ (canonicalTargetObject Y))
          (liftedStrongTransGeneratorNaturality σ f)
          (liftedStrongTransForwardNaturality σ (𝟙 Y) A)
    rw [hLeft]
    rw [← liftedStrongTransNaturality_forward]
    rw [liftedStrongTransNaturality_iso]
    exact hRight.symm
  · exact (canonicalInverseSlidingComparison_hom f A).symm

/-- The exact remaining public composition law for a retained-coordinate
endomorphism followed by the freely adjoined inverse generator.  It is kept
as a proposition until the mate-sliding proof is complete. -/
def LiftedStrongTransRetainedInverseCompositionCoherence
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) : Prop :=
  (liftedStrongTransNaturality σ
      (canonicalForwardHom (𝟙 Y) A ≫
        (generatorEquivalence f).inv)).hom ≫
      liftedStrongTransApp σ (canonicalTargetObject Y) ◁
        (G.mapComp (canonicalForwardHom (𝟙 Y) A)
          (generatorEquivalence f).inv).hom =
    (F.mapComp (canonicalForwardHom (𝟙 Y) A)
        (generatorEquivalence f).inv).hom ▷
        liftedStrongTransApp σ (canonicalTargetObject X) ≫
      (α_ _ _ _).hom ≫
      F.map (canonicalForwardHom (𝟙 Y) A) ◁
        (liftedStrongTransNaturality σ
          (generatorEquivalence f).inv).hom ≫
      (α_ _ _ _).inv ≫
      (liftedStrongTransNaturality σ
        (canonicalForwardHom (𝟙 Y) A)).hom ▷
          G.map (generatorEquivalence f).inv ≫
      (α_ _ _ _).hom

set_option backward.isDefEq.respectTransparency false in
/-- Constructor-level composition coherence holds for the inverse-generator
mate followed by an arbitrary retained-coordinate constraint.  The factors
on the right are exactly the mate and forward constraints used to construct
the public constraint on their raw composite. -/
theorem liftedStrongTransNaturality_comp_inverseGenerator_retained
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (h : ¬ Y ≤ X) (A : Type) :
    (liftedStrongTransNaturality σ
        ((generatorEquivalence f).inv ≫
          canonicalForwardHom (𝟙 X) A)).hom ≫
        liftedStrongTransApp σ (canonicalTargetObject Y) ◁
          (G.mapComp (generatorEquivalence f).inv
            (canonicalForwardHom (𝟙 X) A)).hom =
      (F.mapComp (generatorEquivalence f).inv
          (canonicalForwardHom (𝟙 X) A)).hom ▷
          liftedStrongTransApp σ (canonicalTargetObject X) ≫
        (α_ _ _ _).hom ≫
        F.map (generatorEquivalence f).inv ◁
          (liftedStrongTransForwardNaturality σ (𝟙 X) A).hom ≫
        (α_ _ _ _).inv ≫
        (liftedStrongTransGeneratorInverseNaturality σ f).hom ▷
          G.map (canonicalForwardHom (𝟙 X) A) ≫
        (α_ _ _ _).hom := by
  rw [liftedStrongTransNaturality_inverseComposite σ f h A]
  simp [liftedStrongTransInverseCompositeNaturality,
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos,
    Category.assoc]
  rfl

/-- Public-factor composition coherence holds for a strict inverse walking
generator followed by an arbitrary retained-coordinate arrow.  Unlike the
constructor-level theorem above, both factors on the right are the public
all-arrow constraints selected by `liftedStrongTransNaturality`. -/
theorem liftedStrongTransNaturality_comp_inverseGenerator_retained_public
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (h : ¬ Y ≤ X) (A : Type) :
    (liftedStrongTransNaturality σ
        ((generatorEquivalence f).inv ≫
          canonicalForwardHom (𝟙 X) A)).hom ≫
        liftedStrongTransApp σ (canonicalTargetObject Y) ◁
          (G.mapComp (generatorEquivalence f).inv
            (canonicalForwardHom (𝟙 X) A)).hom =
      (F.mapComp (generatorEquivalence f).inv
          (canonicalForwardHom (𝟙 X) A)).hom ▷
          liftedStrongTransApp σ (canonicalTargetObject X) ≫
        (α_ _ _ _).hom ≫
        F.map (generatorEquivalence f).inv ◁
          (liftedStrongTransNaturality σ
            (canonicalForwardHom (𝟙 X) A)).hom ≫
        (α_ _ _ _).inv ≫
        (liftedStrongTransNaturality σ
          (generatorEquivalence f).inv).hom ▷
            G.map (canonicalForwardHom (𝟙 X) A) ≫
        (α_ _ _ _).hom := by
  rw [liftedStrongTransNaturality_forward,
    liftedStrongTransNaturality_generatorInverse σ f h]
  exact liftedStrongTransNaturality_comp_inverseGenerator_retained
    σ f h A

/-- The public inverse-generator/retained composition law packages as
equality with the canonical composite of its two public constraints. -/
theorem liftedStrongTransNaturality_compIso_inverseGenerator_retained_public
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (h : ¬ Y ≤ X) (A : Type) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        (generatorEquivalence f).inv
        (canonicalForwardHom (𝟙 X) A)
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransNaturality σ (generatorEquivalence f).inv)
        (liftedStrongTransNaturality σ
          (canonicalForwardHom (𝟙 X) A)) =
      liftedStrongTransNaturality σ
        ((generatorEquivalence f).inv ≫
          canonicalForwardHom (𝟙 X) A) := by
  apply Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos_eq_of_coherence
  exact liftedStrongTransNaturality_comp_inverseGenerator_retained_public
    σ f h A

/-- After normalization to the canonical inverse arrow, the public
inverse-generator/retained composite is the public inverse-arrow constraint. -/
theorem liftedStrongTransNaturality_inverseGeneratorRetained_transport
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (h : ¬ Y ≤ X) (A : Type) :
    Pseudofunctor.StrongTrans.naturalityIsoOfIso F G
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
          (generatorEquivalence f).inv
          (canonicalForwardHom (𝟙 X) A)
          (liftedStrongTransApp σ (canonicalTargetObject Y))
          (liftedStrongTransApp σ (canonicalTargetObject X))
          (liftedStrongTransApp σ (canonicalTargetObject X))
          (liftedStrongTransNaturality σ (generatorEquivalence f).inv)
          (liftedStrongTransNaturality σ
            (canonicalForwardHom (𝟙 X) A)))
        (canonicalInverseComparison f A) =
      liftedStrongTransNaturality σ (canonicalInverseHom f A) := by
  rw [liftedStrongTransNaturality_compIso_inverseGenerator_retained_public
    σ f h A]
  exact liftedStrongTransNaturality_iso σ
    (canonicalInverseComparison f A)

set_option backward.isDefEq.respectTransparency false in
/-- For a strict reverse walking generator, the canonical composition of the
public retained and inverse constraints is the public constraint on their raw
composite.  The proof compares both mixed orders after transport to the
canonical inverse arrow and uses injectivity of isomorphism transport. -/
theorem liftedStrongTransNaturality_compIso_retainedInverse_public
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (h : ¬ Y ≤ X) (A : Type) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        (canonicalForwardHom (𝟙 Y) A)
        (generatorEquivalence f).inv
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransNaturality σ
          (canonicalForwardHom (𝟙 Y) A))
        (liftedStrongTransNaturality σ
          (generatorEquivalence f).inv) =
      liftedStrongTransNaturality σ
        (canonicalForwardHom (𝟙 Y) A ≫
          (generatorEquivalence f).inv) := by
  have hslide :=
    liftedStrongTransRetainedInverse_sliding
      (F := F) (G := G) σ f A
  dsimp [canonicalInverseSlidingComparison] at hslide
  rw [Pseudofunctor.StrongTrans.naturalityIsoOfIso_trans] at hslide
  have hcanonical :
      liftedStrongTransRetainedInverseNaturality σ f A =
        liftedStrongTransInverseNaturality σ f A := by
    apply Pseudofunctor.StrongTrans.naturalityIsoOfIso_injective F G
      (liftedStrongTransApp σ (canonicalTargetObject Y))
      (liftedStrongTransApp σ (canonicalTargetObject X))
      (canonicalInverseComparison f A).symm
    change
      Pseudofunctor.StrongTrans.naturalityIsoOfIso F G
          (liftedStrongTransApp σ (canonicalTargetObject Y))
          (liftedStrongTransApp σ (canonicalTargetObject X))
          (liftedStrongTransRetainedInverseNaturality σ f A)
          (canonicalInverseComparison f A).symm =
        Pseudofunctor.StrongTrans.naturalityIsoOfIso F G
          (liftedStrongTransApp σ (canonicalTargetObject Y))
          (liftedStrongTransApp σ (canonicalTargetObject X))
          (liftedStrongTransInverseNaturality σ f A)
          (canonicalInverseComparison f A).symm
    change _ = Pseudofunctor.StrongTrans.naturalityIsoOfIso F G _ _
      (Pseudofunctor.StrongTrans.naturalityIsoOfIso F G _ _
        (liftedStrongTransInverseCompositeNaturality σ f A)
        (canonicalInverseComparison f A))
      (canonicalInverseComparison f A).symm
    rw [← Pseudofunctor.StrongTrans.naturalityIsoOfIso_trans]
    have he :
        canonicalInverseComparison f A ≪≫
            (canonicalInverseComparison f A).symm =
          Iso.refl _ := by
      apply Iso.ext
      simp
    rw [he, Pseudofunctor.StrongTrans.naturalityIsoOfIso_refl]
    exact hslide
  have hInversePublic :=
    liftedStrongTransNaturality_inverseGeneratorRetained_transport
      (F := F) (G := G) σ f h A
  rw [liftedStrongTransNaturality_generatorInverse σ f h,
    liftedStrongTransNaturality_forward] at hInversePublic
  change liftedStrongTransInverseNaturality σ f A =
    liftedStrongTransNaturality σ (canonicalInverseHom f A) at hInversePublic
  have hcandidate :
      liftedStrongTransRetainedInverseCompositeNaturality σ f A =
        liftedStrongTransNaturality σ
          (canonicalForwardHom (𝟙 Y) A ≫
            (generatorEquivalence f).inv) := by
    apply Pseudofunctor.StrongTrans.naturalityIsoOfIso_injective F G
      (liftedStrongTransApp σ (canonicalTargetObject Y))
      (liftedStrongTransApp σ (canonicalTargetObject X))
      (canonicalRetainedInverseComparison f A)
    change liftedStrongTransRetainedInverseNaturality σ f A = _
    have hPublicTransport := liftedStrongTransNaturality_iso
      (F := F) (G := G) σ (canonicalRetainedInverseComparison f A)
    exact hcanonical.trans (hInversePublic.trans hPublicTransport.symm)
  rw [liftedStrongTransNaturality_forward,
    liftedStrongTransNaturality_generatorInverse σ f h]
  exact hcandidate

set_option backward.isDefEq.respectTransparency false in
/-- The public retained-then-inverse composition equation holds whenever the
inverse generator is a strict reverse walking arrow. -/
theorem liftedStrongTransNaturality_comp_retainedInverse_of_not_le
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (h : ¬ Y ≤ X) (A : Type) :
    LiftedStrongTransRetainedInverseCompositionCoherence
      (F := F) (G := G) σ f A := by
  have hcomp := liftedStrongTransNaturality_compIso_retainedInverse_public
    (F := F) (G := G) σ f h A
  change
    (liftedStrongTransNaturality σ
        (canonicalForwardHom (𝟙 Y) A ≫
          (generatorEquivalence f).inv)).hom ≫
        liftedStrongTransApp σ (canonicalTargetObject Y) ◁
          (G.mapComp (canonicalForwardHom (𝟙 Y) A)
            (generatorEquivalence f).inv).hom =
      (F.mapComp (canonicalForwardHom (𝟙 Y) A)
          (generatorEquivalence f).inv).hom ▷
          liftedStrongTransApp σ (canonicalTargetObject X) ≫
        (α_ _ _ _).hom ≫
        F.map (canonicalForwardHom (𝟙 Y) A) ◁
          (liftedStrongTransNaturality σ
            (generatorEquivalence f).inv).hom ≫
        (α_ _ _ _).inv ≫
        (liftedStrongTransNaturality σ
          (canonicalForwardHom (𝟙 Y) A)).hom ▷
            G.map (generatorEquivalence f).inv ≫
        (α_ _ _ _).hom
  rw [← hcomp]
  simp [Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos,
    Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- When the generator is an identity, retained-then-inverse coherence
reduces to the already proved forward-forward composition equation. -/
theorem liftedStrongTransNaturality_comp_retainedInverse_identity
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    (X : Ript.Examples.WalkingLocalization.Arrow) (A : Type) :
    LiftedStrongTransRetainedInverseCompositionCoherence
      (F := F) (G := G) σ (𝟙 X) A := by
  have hinv :
      (generatorEquivalence (𝟙 X)).inv =
        canonicalForwardHom (𝟙 X)
          (𝟙 (MonoidalSingleObj.star (Type))) := by
    apply Prod.ext
    · apply Discrete.ext
      change inv (CategoryTheory.FreeGroupoid.homMk (𝟙 X)) =
        CategoryTheory.FreeGroupoid.homMk (𝟙 X)
      simp
    · rfl
  change
    (liftedStrongTransNaturality σ
        (canonicalForwardHom (𝟙 X) A ≫
          (generatorEquivalence (𝟙 X)).inv)).hom ≫
        liftedStrongTransApp σ (canonicalTargetObject X) ◁
          (G.mapComp (canonicalForwardHom (𝟙 X) A)
            (generatorEquivalence (𝟙 X)).inv).hom =
      (F.mapComp (canonicalForwardHom (𝟙 X) A)
          (generatorEquivalence (𝟙 X)).inv).hom ▷
          liftedStrongTransApp σ (canonicalTargetObject X) ≫
        (α_ _ _ _).hom ≫
        F.map (canonicalForwardHom (𝟙 X) A) ◁
          (liftedStrongTransNaturality σ
            (generatorEquivalence (𝟙 X)).inv).hom ≫
        (α_ _ _ _).inv ≫
        (liftedStrongTransNaturality σ
          (canonicalForwardHom (𝟙 X) A)).hom ▷
            G.map (generatorEquivalence (𝟙 X)).inv ≫
        (α_ _ _ _).hom
  rw [hinv]
  exact liftedStrongTransNaturality_comp_forward
    (F := F) (G := G) σ (𝟙 X) (𝟙 X) A
      (𝟙 (MonoidalSingleObj.star (Type)))

set_option backward.isDefEq.respectTransparency false in
/-- The public all-arrow constraint satisfies composition coherence when an
arbitrary retained-coordinate endomorphism is followed by the freely
adjoined inverse generator.  The strict reverse case is the mate-sliding
calculation; the only remaining case is the identity generator and follows
from forward-forward coherence. -/
theorem liftedStrongTransNaturality_comp_retainedInverse
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    LiftedStrongTransRetainedInverseCompositionCoherence
      (F := F) (G := G) σ f A := by
  by_cases h : Y ≤ X
  · have hXY : X = Y := le_antisymm f.le h
    subst Y
    have hf : f = 𝟙 X := Subsingleton.elim _ _
    subst f
    exact liftedStrongTransNaturality_comp_retainedInverse_identity
      (F := F) (G := G) σ X A
  · exact liftedStrongTransNaturality_comp_retainedInverse_of_not_le
      (F := F) (G := G) σ f h A

set_option backward.isDefEq.respectTransparency false in
/-- Bootstrap the public composition law across three target arrows.  If it
is known for the left pair, the left-associated pair, and the right pair,
constructor associativity transports those three equations to the remaining
right-associated pair. -/
theorem liftedStrongTransNaturality_compIso_assoc_bootstrap
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {W X Y Z : Target} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (hfg :
      Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G f g
          (liftedStrongTransApp σ W) (liftedStrongTransApp σ X)
          (liftedStrongTransApp σ Y)
          (liftedStrongTransNaturality σ f)
          (liftedStrongTransNaturality σ g) =
        liftedStrongTransNaturality σ (f ≫ g))
    (hfgh :
      Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G (f ≫ g) h
          (liftedStrongTransApp σ W) (liftedStrongTransApp σ Y)
          (liftedStrongTransApp σ Z)
          (liftedStrongTransNaturality σ (f ≫ g))
          (liftedStrongTransNaturality σ h) =
        liftedStrongTransNaturality σ ((f ≫ g) ≫ h))
    (hgh :
      Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G g h
          (liftedStrongTransApp σ X) (liftedStrongTransApp σ Y)
          (liftedStrongTransApp σ Z)
          (liftedStrongTransNaturality σ g)
          (liftedStrongTransNaturality σ h) =
        liftedStrongTransNaturality σ (g ≫ h)) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G f (g ≫ h)
        (liftedStrongTransApp σ W) (liftedStrongTransApp σ X)
        (liftedStrongTransApp σ Z)
        (liftedStrongTransNaturality σ f)
        (liftedStrongTransNaturality σ (g ≫ h)) =
      liftedStrongTransNaturality σ (f ≫ (g ≫ h)) := by
  have hassoc :=
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos_assoc F G f g h
      (liftedStrongTransApp σ W) (liftedStrongTransApp σ X)
      (liftedStrongTransApp σ Y) (liftedStrongTransApp σ Z)
      (liftedStrongTransNaturality σ f)
      (liftedStrongTransNaturality σ g)
      (liftedStrongTransNaturality σ h)
  rw [hfg, hfgh, hgh] at hassoc
  rw [liftedStrongTransNaturality_iso] at hassoc
  exact hassoc.symm

set_option backward.isDefEq.respectTransparency false in
/-- Recover the left-associated composition law from the other three sides
of the constructor-associativity square.  Injectivity of transport across
the source associator turns the transported equation back into the desired
untransported constraint equality. -/
theorem liftedStrongTransNaturality_compIso_assoc_unbootstrap
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {W X Y Z : Target} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (hfg :
      Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G f g
          (liftedStrongTransApp σ W) (liftedStrongTransApp σ X)
          (liftedStrongTransApp σ Y)
          (liftedStrongTransNaturality σ f)
          (liftedStrongTransNaturality σ g) =
        liftedStrongTransNaturality σ (f ≫ g))
    (hgh :
      Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G g h
          (liftedStrongTransApp σ X) (liftedStrongTransApp σ Y)
          (liftedStrongTransApp σ Z)
          (liftedStrongTransNaturality σ g)
          (liftedStrongTransNaturality σ h) =
        liftedStrongTransNaturality σ (g ≫ h))
    (hfgh :
      Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G f (g ≫ h)
          (liftedStrongTransApp σ W) (liftedStrongTransApp σ X)
          (liftedStrongTransApp σ Z)
          (liftedStrongTransNaturality σ f)
          (liftedStrongTransNaturality σ (g ≫ h)) =
        liftedStrongTransNaturality σ (f ≫ (g ≫ h))) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G (f ≫ g) h
        (liftedStrongTransApp σ W) (liftedStrongTransApp σ Y)
        (liftedStrongTransApp σ Z)
        (liftedStrongTransNaturality σ (f ≫ g))
        (liftedStrongTransNaturality σ h) =
      liftedStrongTransNaturality σ ((f ≫ g) ≫ h) := by
  apply Pseudofunctor.StrongTrans.naturalityIsoOfIso_injective F G
    (liftedStrongTransApp σ W) (liftedStrongTransApp σ Z)
    (α_ f g h)
  have hassoc :=
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos_assoc F G f g h
      (liftedStrongTransApp σ W) (liftedStrongTransApp σ X)
      (liftedStrongTransApp σ Y) (liftedStrongTransApp σ Z)
      (liftedStrongTransNaturality σ f)
      (liftedStrongTransNaturality σ g)
      (liftedStrongTransNaturality σ h)
  rw [hfg, hgh, hfgh] at hassoc
  exact hassoc.trans
    (liftedStrongTransNaturality_iso
      (F := F) (G := G) σ (α_ f g h)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Composition coherence transports across an isomorphism of the first
factor.  Both the factor constraint and the composite constraint are
identified by the public all-arrow 2-cell naturality theorem. -/
theorem liftedStrongTransNaturality_compIso_of_iso_left
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y Z : Target} {f g : X ⟶ Y} (e : f ≅ g) (h : Y ⟶ Z)
    (hcomp :
      Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G f h
          (liftedStrongTransApp σ X) (liftedStrongTransApp σ Y)
          (liftedStrongTransApp σ Z)
          (liftedStrongTransNaturality σ f)
          (liftedStrongTransNaturality σ h) =
        liftedStrongTransNaturality σ (f ≫ h)) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G g h
        (liftedStrongTransApp σ X) (liftedStrongTransApp σ Y)
        (liftedStrongTransApp σ Z)
        (liftedStrongTransNaturality σ g)
        (liftedStrongTransNaturality σ h) =
      liftedStrongTransNaturality σ (g ≫ h) := by
  have htransport :=
    Pseudofunctor.StrongTrans.naturalityIsoOfIso_comp_left
      F G e h
      (liftedStrongTransApp σ X) (liftedStrongTransApp σ Y)
      (liftedStrongTransApp σ Z)
      (liftedStrongTransNaturality σ f)
      (liftedStrongTransNaturality σ h)
  rw [hcomp, liftedStrongTransNaturality_iso,
    liftedStrongTransNaturality_iso] at htransport
  exact htransport.symm

set_option backward.isDefEq.respectTransparency false in
/-- Composition coherence transports across an isomorphism of the second
factor.  This is the right-factor counterpart of
`liftedStrongTransNaturality_compIso_of_iso_left`. -/
theorem liftedStrongTransNaturality_compIso_of_iso_right
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y Z : Target} (f : X ⟶ Y) {g h : Y ⟶ Z} (e : g ≅ h)
    (hcomp :
      Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G f g
          (liftedStrongTransApp σ X) (liftedStrongTransApp σ Y)
          (liftedStrongTransApp σ Z)
          (liftedStrongTransNaturality σ f)
          (liftedStrongTransNaturality σ g) =
        liftedStrongTransNaturality σ (f ≫ g)) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G f h
        (liftedStrongTransApp σ X) (liftedStrongTransApp σ Y)
        (liftedStrongTransApp σ Z)
        (liftedStrongTransNaturality σ f)
        (liftedStrongTransNaturality σ h) =
      liftedStrongTransNaturality σ (f ≫ h) := by
  have htransport :=
    Pseudofunctor.StrongTrans.naturalityIsoOfIso_comp_right
      F G f e
      (liftedStrongTransApp σ X) (liftedStrongTransApp σ Y)
      (liftedStrongTransApp σ Z)
      (liftedStrongTransNaturality σ f)
      (liftedStrongTransNaturality σ g)
  rw [hcomp, liftedStrongTransNaturality_iso,
    liftedStrongTransNaturality_iso] at htransport
  exact htransport.symm

set_option backward.isDefEq.respectTransparency false in
/-- A canonical inverse arrow carrying an arbitrary retained coordinate
composes coherently with a further retained-coordinate endomorphism.  The
proof reassociates the inverse-generator construction, combines the two
retained coordinates, and transports back across the canonical inverse
comparison. -/
theorem liftedStrongTransNaturality_compIso_inverse_retained
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        (canonicalInverseHom f A) (canonicalForwardHom (𝟙 X) B)
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransNaturality σ (canonicalInverseHom f A))
        (liftedStrongTransNaturality σ (canonicalForwardHom (𝟙 X) B)) =
      liftedStrongTransNaturality σ
        (canonicalInverseHom f A ≫ canonicalForwardHom (𝟙 X) B) := by
  have hgenPairCanonical :=
    liftedStrongTransNaturality_compIso_inverseGenerator_retained_public
      (F := F) (G := G) σ f hf (A × B)
  have hgenPair :=
    liftedStrongTransNaturality_compIso_of_iso_right
      (F := F) (G := G) σ (generatorEquivalence f).inv
      (canonicalRetainedCompositionComparison X A B).symm
      hgenPairCanonical
  have hgenA :=
    liftedStrongTransNaturality_compIso_inverseGenerator_retained_public
      (F := F) (G := G) σ f hf A
  have hAB :=
    liftedStrongTransNaturality_compIso_forward
      (F := F) (G := G) σ (𝟙 X) (𝟙 X) A B
  have hraw :=
    liftedStrongTransNaturality_compIso_assoc_unbootstrap
      (F := F) (G := G) σ
      (generatorEquivalence f).inv
      (canonicalForwardHom (𝟙 X) A)
      (canonicalForwardHom (𝟙 X) B)
      hgenA hAB hgenPair
  exact liftedStrongTransNaturality_compIso_of_iso_left
    (F := F) (G := G) σ (canonicalInverseComparison f A)
    (canonicalForwardHom (𝟙 X) B) hraw

set_option backward.isDefEq.respectTransparency false in
/-- A retained-coordinate endomorphism composes coherently with a canonical
inverse arrow carrying another arbitrary retained coordinate.  This closes
the opposite mixed retained/inverse order by reassociation and transport. -/
theorem liftedStrongTransNaturality_compIso_retained_inverse
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        (canonicalForwardHom (𝟙 Y) A) (canonicalInverseHom f B)
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransNaturality σ (canonicalForwardHom (𝟙 Y) A))
        (liftedStrongTransNaturality σ (canonicalInverseHom f B)) =
      liftedStrongTransNaturality σ
        (canonicalForwardHom (𝟙 Y) A ≫ canonicalInverseHom f B) := by
  have hretGen :=
    liftedStrongTransNaturality_compIso_retainedInverse_public
      (F := F) (G := G) σ f hf A
  have hgenB :=
    liftedStrongTransNaturality_compIso_inverseGenerator_retained_public
      (F := F) (G := G) σ f hf B
  have hinvA_B :=
    liftedStrongTransNaturality_compIso_inverse_retained
      (F := F) (G := G) σ f hf A B
  have hrawLeft :=
    liftedStrongTransNaturality_compIso_of_iso_left
      (F := F) (G := G) σ (canonicalRetainedInverseComparison f A).symm
      (canonicalForwardHom (𝟙 X) B) hinvA_B
  have hraw :=
    liftedStrongTransNaturality_compIso_assoc_bootstrap
      (F := F) (G := G) σ
      (canonicalForwardHom (𝟙 Y) A)
      (generatorEquivalence f).inv
      (canonicalForwardHom (𝟙 X) B)
      hretGen hrawLeft hgenB
  exact liftedStrongTransNaturality_compIso_of_iso_right
    (F := F) (G := G) σ (canonicalForwardHom (𝟙 Y) A)
    (canonicalInverseComparison f B) hraw

/-- A strict target identity composes coherently with an arbitrary retained
endomorphism.  This is forward-forward coherence transported across the
canonical comparison from the included identity to the strict identity. -/
theorem liftedStrongTransNaturality_compIso_id_retained
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    (X : Ript.Examples.WalkingLocalization.Arrow) (A : Type) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        (𝟙 (canonicalTargetObject X))
        (canonicalForwardHom (𝟙 X) A)
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransNaturality σ (𝟙 (canonicalTargetObject X)))
        (liftedStrongTransNaturality σ (canonicalForwardHom (𝟙 X) A)) =
      liftedStrongTransNaturality σ
        (𝟙 (canonicalTargetObject X) ≫ canonicalForwardHom (𝟙 X) A) := by
  have hforward := liftedStrongTransNaturality_compIso_forward
    (F := F) (G := G) σ (𝟙 X) (𝟙 X)
      (𝟙 (MonoidalSingleObj.star (Type))) A
  exact liftedStrongTransNaturality_compIso_of_iso_left
    (F := F) (G := G) σ (canonicalForwardIdentityComparison X)
      (canonicalForwardHom (𝟙 X) A) hforward

/-- A raw inverse-generator/forward-generator cancellation composite can be
followed coherently by any retained endomorphism. -/
theorem liftedStrongTransNaturality_compIso_inverseGeneratorGenerator_retained
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        ((generatorEquivalence f).inv ≫ (generatorEquivalence f).hom)
        (canonicalForwardHom (𝟙 Y) A)
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransNaturality σ
          ((generatorEquivalence f).inv ≫ (generatorEquivalence f).hom))
        (liftedStrongTransNaturality σ (canonicalForwardHom (𝟙 Y) A)) =
      liftedStrongTransNaturality σ
        (((generatorEquivalence f).inv ≫ (generatorEquivalence f).hom) ≫
          canonicalForwardHom (𝟙 Y) A) := by
  exact liftedStrongTransNaturality_compIso_of_iso_left
    (F := F) (G := G) σ (generatorEquivalence f).counit.symm
      (canonicalForwardHom (𝟙 Y) A)
      (liftedStrongTransNaturality_compIso_id_retained
        (F := F) (G := G) σ Y A)

/-- Reassociation propagates inverse/forward cancellation through a retained
endomorphism on the codomain side. -/
theorem liftedStrongTransNaturality_compIso_generatorInverseGenerator_retained
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        (generatorEquivalence f).inv
        ((generatorEquivalence f).hom ≫ canonicalForwardHom (𝟙 Y) A)
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransNaturality σ (generatorEquivalence f).inv)
        (liftedStrongTransNaturality σ
          ((generatorEquivalence f).hom ≫ canonicalForwardHom (𝟙 Y) A)) =
      liftedStrongTransNaturality σ
        ((generatorEquivalence f).inv ≫
          ((generatorEquivalence f).hom ≫ canonicalForwardHom (𝟙 Y) A)) := by
  exact liftedStrongTransNaturality_compIso_assoc_bootstrap
    (F := F) (G := G) σ
      (generatorEquivalence f).inv (generatorEquivalence f).hom
      (canonicalForwardHom (𝟙 Y) A)
      (liftedStrongTransNaturality_compIso_inverseGenerator_generator
        (F := F) (G := G) σ f hf)
      (liftedStrongTransNaturality_compIso_inverseGeneratorGenerator_retained
        (F := F) (G := G) σ f A)
      (liftedStrongTransNaturality_compIso_forward
        (F := F) (G := G) σ f (𝟙 Y)
          (𝟙 (MonoidalSingleObj.star (Type))) A)

/-- Sliding the retained coordinate across the forward generator gives the
opposite association of the same cancellation-with-retained law. -/
theorem liftedStrongTransNaturality_compIso_inverseGenerator_retainedGenerator
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        (generatorEquivalence f).inv
        (canonicalForwardHom (𝟙 X) A ≫ (generatorEquivalence f).hom)
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransNaturality σ (generatorEquivalence f).inv)
        (liftedStrongTransNaturality σ
          (canonicalForwardHom (𝟙 X) A ≫ (generatorEquivalence f).hom)) =
      liftedStrongTransNaturality σ
        ((generatorEquivalence f).inv ≫
          (canonicalForwardHom (𝟙 X) A ≫ (generatorEquivalence f).hom)) := by
  exact liftedStrongTransNaturality_compIso_of_iso_right
    (F := F) (G := G) σ (generatorEquivalence f).inv
      (canonicalForwardSlidingComparison f A).symm
      (liftedStrongTransNaturality_compIso_generatorInverseGenerator_retained
        (F := F) (G := G) σ f hf A)

/-- The left-associated inverse-generator/retained/forward-generator triple
satisfies composition coherence. -/
theorem liftedStrongTransNaturality_compIso_inverseRetained_generator
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        ((generatorEquivalence f).inv ≫ canonicalForwardHom (𝟙 X) A)
        (generatorEquivalence f).hom
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransNaturality σ
          ((generatorEquivalence f).inv ≫ canonicalForwardHom (𝟙 X) A))
        (liftedStrongTransNaturality σ (generatorEquivalence f).hom) =
      liftedStrongTransNaturality σ
        (((generatorEquivalence f).inv ≫ canonicalForwardHom (𝟙 X) A) ≫
          (generatorEquivalence f).hom) := by
  exact liftedStrongTransNaturality_compIso_assoc_unbootstrap
    (F := F) (G := G) σ
      (generatorEquivalence f).inv (canonicalForwardHom (𝟙 X) A)
      (generatorEquivalence f).hom
      (liftedStrongTransNaturality_compIso_inverseGenerator_retained_public
        (F := F) (G := G) σ f hf A)
      (liftedStrongTransNaturality_compIso_forward
        (F := F) (G := G) σ (𝟙 X) f A
          (𝟙 (MonoidalSingleObj.star (Type))))
      (liftedStrongTransNaturality_compIso_inverseGenerator_retainedGenerator
        (F := F) (G := G) σ f hf A)

/-- A canonical inverse arrow with an arbitrary retained coordinate cancels
coherently against the forward generator. -/
theorem liftedStrongTransNaturality_compIso_canonicalInverse_generator
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        (canonicalInverseHom f A) (generatorEquivalence f).hom
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransNaturality σ (canonicalInverseHom f A))
        (liftedStrongTransNaturality σ (generatorEquivalence f).hom) =
      liftedStrongTransNaturality σ
        (canonicalInverseHom f A ≫ (generatorEquivalence f).hom) := by
  exact liftedStrongTransNaturality_compIso_of_iso_left
    (F := F) (G := G) σ (canonicalInverseComparison f A)
      (generatorEquivalence f).hom
      (liftedStrongTransNaturality_compIso_inverseRetained_generator
        (F := F) (G := G) σ f hf A)

/-- A canonical inverse arrow cancels coherently against a forward generator
carrying an arbitrary retained coordinate. -/
theorem liftedStrongTransNaturality_compIso_canonicalInverse_generatorRetained
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        (canonicalInverseHom f A)
        ((generatorEquivalence f).hom ≫ canonicalForwardHom (𝟙 Y) B)
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransNaturality σ (canonicalInverseHom f A))
        (liftedStrongTransNaturality σ
          ((generatorEquivalence f).hom ≫ canonicalForwardHom (𝟙 Y) B)) =
      liftedStrongTransNaturality σ
        (canonicalInverseHom f A ≫
          ((generatorEquivalence f).hom ≫ canonicalForwardHom (𝟙 Y) B)) := by
  have hcancelRet := liftedStrongTransNaturality_compIso_of_iso_left
    (F := F) (G := G) σ
      (canonicalInverseForwardCancellationComparison f A).symm
      (canonicalForwardHom (𝟙 Y) B)
      (liftedStrongTransNaturality_compIso_forward
        (F := F) (G := G) σ (𝟙 Y) (𝟙 Y) A B)
  exact liftedStrongTransNaturality_compIso_assoc_bootstrap
    (F := F) (G := G) σ
      (canonicalInverseHom f A) (generatorEquivalence f).hom
      (canonicalForwardHom (𝟙 Y) B)
      (liftedStrongTransNaturality_compIso_canonicalInverse_generator
        (F := F) (G := G) σ f hf A)
      hcancelRet
      (liftedStrongTransNaturality_compIso_forward
        (F := F) (G := G) σ f (𝟙 Y)
          (𝟙 (MonoidalSingleObj.star (Type))) B)

/-- Endpoint-changing inverse/forward cancellation satisfies composition
coherence with arbitrary retained coordinates on both factors. -/
theorem liftedStrongTransNaturality_compIso_canonicalInverse_canonicalForward
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        (canonicalInverseHom f A) (canonicalForwardHom f B)
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransNaturality σ (canonicalInverseHom f A))
        (liftedStrongTransNaturality σ (canonicalForwardHom f B)) =
      liftedStrongTransNaturality σ
        (canonicalInverseHom f A ≫ canonicalForwardHom f B) := by
  exact liftedStrongTransNaturality_compIso_of_iso_right
    (F := F) (G := G) σ (canonicalInverseHom f A)
      (canonicalGeneratorRetainedComparison f B)
      (liftedStrongTransNaturality_compIso_canonicalInverse_generatorRetained
        (F := F) (G := G) σ f hf A B)

/-- A raw forward-generator/inverse-generator cancellation composite can be
followed coherently by any retained endomorphism. -/
theorem liftedStrongTransNaturality_compIso_generatorInverse_retained
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        ((generatorEquivalence f).hom ≫ (generatorEquivalence f).inv)
        (canonicalForwardHom (𝟙 X) A)
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransNaturality σ
          ((generatorEquivalence f).hom ≫ (generatorEquivalence f).inv))
        (liftedStrongTransNaturality σ (canonicalForwardHom (𝟙 X) A)) =
      liftedStrongTransNaturality σ
        (((generatorEquivalence f).hom ≫ (generatorEquivalence f).inv) ≫
          canonicalForwardHom (𝟙 X) A) := by
  exact liftedStrongTransNaturality_compIso_of_iso_left
    (F := F) (G := G) σ (generatorEquivalence f).unit
      (canonicalForwardHom (𝟙 X) A)
      (liftedStrongTransNaturality_compIso_id_retained
        (F := F) (G := G) σ X A)

/-- Reassociation propagates forward/inverse cancellation through a retained
endomorphism on the domain side. -/
theorem liftedStrongTransNaturality_compIso_generator_inverseGeneratorRetained
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        (generatorEquivalence f).hom
        ((generatorEquivalence f).inv ≫ canonicalForwardHom (𝟙 X) A)
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransNaturality σ (generatorEquivalence f).hom)
        (liftedStrongTransNaturality σ
          ((generatorEquivalence f).inv ≫ canonicalForwardHom (𝟙 X) A)) =
      liftedStrongTransNaturality σ
        ((generatorEquivalence f).hom ≫
          ((generatorEquivalence f).inv ≫ canonicalForwardHom (𝟙 X) A)) := by
  exact liftedStrongTransNaturality_compIso_assoc_bootstrap
    (F := F) (G := G) σ
      (generatorEquivalence f).hom (generatorEquivalence f).inv
      (canonicalForwardHom (𝟙 X) A)
      (liftedStrongTransNaturality_compIso_generator_inverseGenerator
        (F := F) (G := G) σ f hf)
      (liftedStrongTransNaturality_compIso_generatorInverse_retained
        (F := F) (G := G) σ f A)
      (liftedStrongTransNaturality_compIso_inverseGenerator_retained_public
        (F := F) (G := G) σ f hf A)

/-- Sliding a retained coordinate across the inverse generator gives the
opposite association of the forward/inverse cancellation law. -/
theorem liftedStrongTransNaturality_compIso_generator_retainedInverse
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        (generatorEquivalence f).hom
        (canonicalForwardHom (𝟙 Y) A ≫ (generatorEquivalence f).inv)
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransNaturality σ (generatorEquivalence f).hom)
        (liftedStrongTransNaturality σ
          (canonicalForwardHom (𝟙 Y) A ≫ (generatorEquivalence f).inv)) =
      liftedStrongTransNaturality σ
        ((generatorEquivalence f).hom ≫
          (canonicalForwardHom (𝟙 Y) A ≫ (generatorEquivalence f).inv)) := by
  exact liftedStrongTransNaturality_compIso_of_iso_right
    (F := F) (G := G) σ (generatorEquivalence f).hom
      (canonicalInverseSlidingComparison f A)
      (liftedStrongTransNaturality_compIso_generator_inverseGeneratorRetained
        (F := F) (G := G) σ f hf A)

/-- The left-associated forward-generator/retained/inverse-generator triple
satisfies composition coherence. -/
theorem liftedStrongTransNaturality_compIso_generatorRetained_inverse
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        ((generatorEquivalence f).hom ≫ canonicalForwardHom (𝟙 Y) A)
        (generatorEquivalence f).inv
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransNaturality σ
          ((generatorEquivalence f).hom ≫ canonicalForwardHom (𝟙 Y) A))
        (liftedStrongTransNaturality σ (generatorEquivalence f).inv) =
      liftedStrongTransNaturality σ
        (((generatorEquivalence f).hom ≫ canonicalForwardHom (𝟙 Y) A) ≫
          (generatorEquivalence f).inv) := by
  exact liftedStrongTransNaturality_compIso_assoc_unbootstrap
    (F := F) (G := G) σ
      (generatorEquivalence f).hom (canonicalForwardHom (𝟙 Y) A)
      (generatorEquivalence f).inv
      (liftedStrongTransNaturality_compIso_forward
        (F := F) (G := G) σ f (𝟙 Y)
          (𝟙 (MonoidalSingleObj.star (Type))) A)
      (liftedStrongTransNaturality_compIso_retainedInverse_public
        (F := F) (G := G) σ f hf A)
      (liftedStrongTransNaturality_compIso_generator_retainedInverse
        (F := F) (G := G) σ f hf A)

/-- A canonical forward arrow with an arbitrary retained coordinate cancels
coherently against the inverse generator. -/
theorem liftedStrongTransNaturality_compIso_canonicalForward_inverseGenerator
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        (canonicalForwardHom f A) (generatorEquivalence f).inv
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransNaturality σ (canonicalForwardHom f A))
        (liftedStrongTransNaturality σ (generatorEquivalence f).inv) =
      liftedStrongTransNaturality σ
        (canonicalForwardHom f A ≫ (generatorEquivalence f).inv) := by
  exact liftedStrongTransNaturality_compIso_of_iso_left
    (F := F) (G := G) σ (canonicalGeneratorRetainedComparison f A)
      (generatorEquivalence f).inv
      (liftedStrongTransNaturality_compIso_generatorRetained_inverse
        (F := F) (G := G) σ f hf A)

/-- A canonical forward arrow cancels coherently against an inverse generator
carrying an arbitrary retained coordinate. -/
theorem liftedStrongTransNaturality_compIso_canonicalForward_inverseRetained
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        (canonicalForwardHom f A)
        ((generatorEquivalence f).inv ≫ canonicalForwardHom (𝟙 X) B)
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransNaturality σ (canonicalForwardHom f A))
        (liftedStrongTransNaturality σ
          ((generatorEquivalence f).inv ≫ canonicalForwardHom (𝟙 X) B)) =
      liftedStrongTransNaturality σ
        (canonicalForwardHom f A ≫
          ((generatorEquivalence f).inv ≫ canonicalForwardHom (𝟙 X) B)) := by
  have hcancelRet := liftedStrongTransNaturality_compIso_of_iso_left
    (F := F) (G := G) σ
      (canonicalForwardInverseCancellationComparison f A).symm
      (canonicalForwardHom (𝟙 X) B)
      (liftedStrongTransNaturality_compIso_forward
        (F := F) (G := G) σ (𝟙 X) (𝟙 X) A B)
  exact liftedStrongTransNaturality_compIso_assoc_bootstrap
    (F := F) (G := G) σ
      (canonicalForwardHom f A) (generatorEquivalence f).inv
      (canonicalForwardHom (𝟙 X) B)
      (liftedStrongTransNaturality_compIso_canonicalForward_inverseGenerator
        (F := F) (G := G) σ f hf A)
      hcancelRet
      (liftedStrongTransNaturality_compIso_inverseGenerator_retained_public
        (F := F) (G := G) σ f hf B)

/-- Endpoint-changing forward/inverse cancellation satisfies composition
coherence with arbitrary retained coordinates on both factors. -/
theorem liftedStrongTransNaturality_compIso_canonicalForward_canonicalInverse
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G
        (canonicalForwardHom f A) (canonicalInverseHom f B)
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransApp σ (canonicalTargetObject Y))
        (liftedStrongTransApp σ (canonicalTargetObject X))
        (liftedStrongTransNaturality σ (canonicalForwardHom f A))
        (liftedStrongTransNaturality σ (canonicalInverseHom f B)) =
      liftedStrongTransNaturality σ
        (canonicalForwardHom f A ≫ canonicalInverseHom f B) := by
  exact liftedStrongTransNaturality_compIso_of_iso_right
    (F := F) (G := G) σ (canonicalForwardHom f A)
      (canonicalInverseComparison f B)
      (liftedStrongTransNaturality_compIso_canonicalForward_inverseRetained
        (F := F) (G := G) σ f hf A B)

/-- The free groupoid on the walking arrow is thin: there is exactly one
morphism between each pair of objects. -/
noncomputable instance walkingCompletionIsThin :
    Quiver.IsThin Ript.Examples.WalkingLocalization.Completion :=
  fun _ _ ↦
    ⟨fun f g ↦ by
      rw [completion_hom_eq_canonical f,
        completion_hom_eq_canonical g]⟩

/-- The public all-arrow constraints satisfy composition coherence for every
pair of target arrows.  Thinness normalizes the walking coordinate; the eight
endpoint triples then reduce to forward-forward, mixed retained/inverse, or
the two arbitrary-retained cancellation theorems above. -/
theorem liftedStrongTransNaturality_compIso
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y Z : Target} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos F G f g
        (liftedStrongTransApp σ X) (liftedStrongTransApp σ Y)
        (liftedStrongTransApp σ Z)
        (liftedStrongTransNaturality σ f)
        (liftedStrongTransNaturality σ g) =
      liftedStrongTransNaturality σ (f ≫ g) := by
  rcases X with ⟨⟨X⟩, X'⟩
  rcases Y with ⟨⟨Y⟩, Y'⟩
  rcases Z with ⟨⟨Z⟩, Z'⟩
  cases X'
  cases Y'
  cases Z'
  let x : Ript.Examples.WalkingLocalization.Arrow := X.as.as
  let y : Ript.Examples.WalkingLocalization.Arrow := Y.as.as
  let z : Ript.Examples.WalkingLocalization.Arrow := Z.as.as
  have hx : X.as.as = x := rfl
  have hy : Y.as.as = y := rfl
  have hz : Z.as.as = z := rfl
  have hX : X = CategoryTheory.FreeGroupoid.mk x :=
    CategoryTheory.FreeGroupoid.eq_mk X
  have hY : Y = CategoryTheory.FreeGroupoid.mk y :=
    CategoryTheory.FreeGroupoid.eq_mk Y
  have hZ : Z = CategoryTheory.FreeGroupoid.mk z :=
    CategoryTheory.FreeGroupoid.eq_mk Z
  clear_value x
  clear_value y
  clear_value z
  cases hX
  cases hY
  cases hZ
  rcases f with ⟨⟨f⟩, A⟩
  rcases g with ⟨⟨g⟩, B⟩
  have hf : f = canonicalCompletionHom x y := Subsingleton.elim _ _
  have hg : g = canonicalCompletionHom y z := Subsingleton.elim _ _
  rw [hf, hg]
  fin_cases x <;> fin_cases y <;> fin_cases z
  · simp [canonicalCompletionHom]
    exact liftedStrongTransNaturality_compIso_forward
      (F := F) (G := G) σ
        (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow))
        (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) A B
  · simp [canonicalCompletionHom]
    exact liftedStrongTransNaturality_compIso_forward
      (F := F) (G := G) σ
        (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow))
        Ript.Examples.WalkingLocalization.arrow A B
  · simp [canonicalCompletionHom]
    exact liftedStrongTransNaturality_compIso_canonicalForward_canonicalInverse
      (F := F) (G := G) σ Ript.Examples.WalkingLocalization.arrow
        (by decide) A B
  · simp [canonicalCompletionHom]
    exact liftedStrongTransNaturality_compIso_forward
      (F := F) (G := G) σ Ript.Examples.WalkingLocalization.arrow
        (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) A B
  · simp [canonicalCompletionHom]
    exact liftedStrongTransNaturality_compIso_inverse_retained
      (F := F) (G := G) σ Ript.Examples.WalkingLocalization.arrow
        (by decide) A B
  · simp [canonicalCompletionHom]
    exact liftedStrongTransNaturality_compIso_canonicalInverse_canonicalForward
      (F := F) (G := G) σ Ript.Examples.WalkingLocalization.arrow
        (by decide) A B
  · simp [canonicalCompletionHom]
    exact liftedStrongTransNaturality_compIso_retained_inverse
      (F := F) (G := G) σ Ript.Examples.WalkingLocalization.arrow
        (by decide) A B
  · simp [canonicalCompletionHom]
    exact liftedStrongTransNaturality_compIso_forward
      (F := F) (G := G) σ
        (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow))
        (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) A B

set_option backward.isDefEq.respectTransparency false in
/-- Hom-level composition coherence for the public all-arrow constraints. -/
theorem liftedStrongTransNaturality_comp
    (σ : inclusion.comp F ⟶ inclusion.comp G)
    {X Y Z : Target} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (liftedStrongTransNaturality σ (f ≫ g)).hom ≫
          liftedStrongTransApp σ X ◁ (G.mapComp f g).hom =
      (F.mapComp f g).hom ▷ liftedStrongTransApp σ Z ≫
        (α_ _ _ _).hom ≫
        F.map f ◁ (liftedStrongTransNaturality σ g).hom ≫
        (α_ _ _ _).inv ≫
        (liftedStrongTransNaturality σ f).hom ▷ G.map g ≫
        (α_ _ _ _).hom := by
  have hcomp := liftedStrongTransNaturality_compIso
    (F := F) (G := G) σ f g
  rw [← hcomp]
  simp [Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos,
    Category.assoc]

/-- Extend a source strong transformation uniquely up to modification to a
genuine strong transformation on the walking-localization target. -/
noncomputable def liftedStrongTrans
    (σ : inclusion.comp F ⟶ inclusion.comp G) : F ⟶ G where
  app := liftedStrongTransApp σ
  naturality := liftedStrongTransNaturality σ
  naturality_naturality := liftedStrongTransNaturality_naturality σ
  naturality_id := liftedStrongTransNaturality_id σ
  naturality_comp := liftedStrongTransNaturality_comp σ

/-- Objectwise comparison between the restriction of the lifted strong
transformation and the original source transformation. -/
noncomputable def liftedStrongTransRestrictionAppIso
    (σ : inclusion.comp F ⟶ inclusion.comp G) (X : Source) :
    (liftedStrongTrans σ).app (inclusion.obj X) ≅ σ.app X :=
  eqToIso (liftedStrongTransApp_inclusionObj σ X)

set_option backward.isDefEq.respectTransparency false in
/-- Precomposing the lifted target strong transformation recovers the source
strong transformation up to an invertible modification. -/
noncomputable def liftedStrongTransRestrictionIso
    (σ : inclusion.comp F ⟶ inclusion.comp G) :
    (inclusion.localPrecomposition F G).obj (liftedStrongTrans σ) ≅ σ :=
  Pseudofunctor.StrongTrans.isoMk
    (liftedStrongTransRestrictionAppIso σ) (by
      intro S T f
      have hS := liftedStrongTransApp_inclusionObj σ S
      have hT := liftedStrongTransApp_inclusionObj σ T
      dsimp [liftedStrongTransRestrictionAppIso,
        liftedStrongTrans, Pseudofunctor.localPrecomposition,
        Pseudofunctor.StrongTrans.prewhisker]
      simp only [Pseudofunctor.comp, PrelaxFunctor.comp,
        PrelaxFunctorStruct.comp, Prefunctor.comp] at hS hT ⊢
      cases hS
      cases hT
      rw [whiskerLeft_id, id_whiskerRight,
        Category.id_comp, Category.comp_id]
      simp
      rw [liftedStrongTransNaturality_eq_endpoint,
        liftedStrongTransEndpointNaturality_inclusion])

/-- Lifted modification components are natural on every canonical forward
target arrow. -/
theorem liftedModificationApp_naturality_forward
    {η θ : F ⟶ G}
    (Γ : (inclusion.localPrecomposition F G).obj η ⟶
      (inclusion.localPrecomposition F G).obj θ)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    Pseudofunctor.StrongTrans.NaturalityAt η θ
      (liftedModificationApp Γ) (canonicalForwardHom f A) := by
  exact liftedModificationApp_naturality_map Γ (canonicalSourceHom f A)

/-- Naturality of lifted modification components extends from a generator to
its chosen inverse by mates, and then to every canonical inverse arrow by
composition and isomorphism transport. -/
theorem liftedModificationApp_naturality_inverse
    {η θ : F ⟶ G}
    (Γ : (inclusion.localPrecomposition F G).obj η ⟶
      (inclusion.localPrecomposition F G).obj θ)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    Pseudofunctor.StrongTrans.NaturalityAt η θ
      (liftedModificationApp Γ) (canonicalInverseHom f A) := by
  have hforward :
      Pseudofunctor.StrongTrans.NaturalityAt η θ
        (liftedModificationApp Γ) (generatorEquivalence f).hom := by
    change Pseudofunctor.StrongTrans.NaturalityAt η θ
      (liftedModificationApp Γ)
      (canonicalForwardHom f
        (𝟙 (MonoidalSingleObj.star (Type))))
    exact liftedModificationApp_naturality_forward Γ f
      (𝟙 (MonoidalSingleObj.star (Type)))
  have hinverse := Pseudofunctor.StrongTrans.naturalityAt_inv
    η θ (liftedModificationApp Γ) (generatorEquivalence f) hforward
  have hretained := liftedModificationApp_naturality_forward Γ (𝟙 X) A
  have hcomp := Pseudofunctor.StrongTrans.naturalityAt_comp
    η θ (liftedModificationApp Γ) hinverse hretained
  exact Pseudofunctor.StrongTrans.naturalityAt_of_iso
    η θ (liftedModificationApp Γ) (canonicalInverseComparison f A) hcomp

set_option backward.isDefEq.respectTransparency false in
/-- Lifted modification components are natural on every target 1-morphism. -/
theorem liftedModificationApp_naturality_endpoint
    {η θ : F ⟶ G}
    (Γ : (inclusion.localPrecomposition F G).obj η ⟶
      (inclusion.localPrecomposition F G).obj θ)
    {X Y : Target} (f : X ⟶ Y) :
    Pseudofunctor.StrongTrans.NaturalityAt η θ
      (liftedModificationApp Γ) f := by
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
    subst f
    exact liftedModificationApp_naturality_forward Γ (homOfLE h) A
  · have hf : f = inv (CategoryTheory.FreeGroupoid.homMk
        (homOfLE (le_of_not_ge h))) := by
      have hf' := completion_hom_eq_canonical f
      simpa [canonicalCompletionHom, hx, hy, h] using hf'
    subst f
    exact liftedModificationApp_naturality_inverse Γ
      (homOfLE (le_of_not_ge h)) A

/-- Extend a source modification to a target modification. -/
noncomputable def liftedModification
    {η θ : F ⟶ G}
    (Γ : (inclusion.localPrecomposition F G).obj η ⟶
      (inclusion.localPrecomposition F G).obj θ) : η ⟶ θ :=
  ⟨{
    app := liftedModificationApp Γ
    naturality := liftedModificationApp_naturality_endpoint Γ
  }⟩

/-- Restricting the lifted modification recovers the original modification. -/
theorem map_liftedModification
    {η θ : F ⟶ G}
    (Γ : (inclusion.localPrecomposition F G).obj η ⟶
      (inclusion.localPrecomposition F G).obj θ) :
    (inclusion.localPrecomposition F G).map (liftedModification Γ) = Γ := by
  apply Pseudofunctor.StrongTrans.homCategory.ext
  intro X
  exact liftedModificationApp_inclusionObj Γ X

/-- Precomposition is full on strong transformations and modifications. -/
theorem inclusion_localPrecomposition_full_endpoint (F G : Target ⥤ᵖ E) :
    (inclusion.localPrecomposition F G).Full :=
  ⟨fun Γ ↦ ⟨liftedModification Γ, map_liftedModification Γ⟩⟩

/-- Every source strong transformation is isomorphic to the restriction of a
target strong transformation. -/
theorem inclusion_localPrecomposition_essSurj (F G : Target ⥤ᵖ E) :
    (inclusion.localPrecomposition F G).EssSurj where
  mem_essImage σ :=
    ⟨liftedStrongTrans σ, ⟨liftedStrongTransRestrictionIso σ⟩⟩

/-- Precomposition by the two-dimensional walking localization is an
equivalence on every local category of strong transformations and
modifications. -/
theorem inclusion_localPrecomposition_isEquivalence
    (F G : Target ⥤ᵖ E) :
    (inclusion.localPrecomposition F G).IsEquivalence where
  faithful := inclusion_localPrecomposition_faithful F G
  full := inclusion_localPrecomposition_full_endpoint F G
  essSurj := inclusion_localPrecomposition_essSurj F G

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

section ArbitraryLiftPrelaxAction

variable {E : Type u} [Bicategory.{w, v} E]

/-- A chosen adjoint equivalence carried by the image of any source walking
arrow paired with the retained-coordinate identity. -/
noncomputable def generalLiftSourceEquivalence
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow} (f : X ⟶ Y) :
    F.obj (canonicalSourceObject X) ≌
      F.obj (canonicalSourceObject Y) := by
  let g := canonicalSourceHom f (𝟙 (MonoidalSingleObj.star (Type)))
  have hg : marking g :=
    Bicategory.isEquivalence_hom (Bicategory.Equivalence.id _)
  let eData := Classical.choice (hF g hg)
  exact eData.1.replaceHom (eqToIso eData.2)

/-- The chosen equivalence has exactly the source pseudofunctor's image of the
marked walking arrow as its forward 1-morphism. -/
@[simp]
theorem generalLiftSourceEquivalence_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow} (f : X ⟶ Y) :
    (generalLiftSourceEquivalence F hF f).hom =
      F.map (canonicalSourceHom f
        (𝟙 (MonoidalSingleObj.star (Type)))) :=
  rfl

/-- On a forward target hom-category, reuse the source pseudofunctor after
discarding the unique completed walking-coordinate representative. -/
noncomputable def generalLiftForwardHomFunctor
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow} (f : X ⟶ Y) :
    (canonicalTargetObject X ⟶ canonicalTargetObject Y) ⥤
      (F.obj (canonicalSourceObject X) ⟶
        F.obj (canonicalSourceObject Y)) where
  obj g := F.map (canonicalSourceHom f g.2)
  map η := F.map₂ (canonicalSourceTwoCell f η.2)
  map_id g := by
    rw [← F.map₂_id (canonicalSourceHom f g.2)]
    congr 1
  map_comp η θ := by
    rw [← F.map₂_comp
      (canonicalSourceTwoCell f η.2) (canonicalSourceTwoCell f θ.2)]
    congr 1

/-- On a new reverse hom-category, use the inverse of the chosen image of the
marked generator and then apply the source pseudofunctor to the retained
coordinate at the lower endpoint. -/
noncomputable def generalLiftReverseHomFunctor
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow} (f : X ⟶ Y) :
    (canonicalTargetObject Y ⟶ canonicalTargetObject X) ⥤
      (F.obj (canonicalSourceObject Y) ⟶
        F.obj (canonicalSourceObject X)) where
  obj g := (generalLiftSourceEquivalence F hF f).inv ≫
    F.map (canonicalSourceHom (𝟙 X) g.2)
  map η := (generalLiftSourceEquivalence F hF f).inv ◁
    F.map₂ (canonicalSourceTwoCell (𝟙 X) η.2)
  map_id g := by
    change (generalLiftSourceEquivalence F hF f).inv ◁
        F.map₂ (canonicalSourceTwoCell (𝟙 X) (𝟙 g.2)) = _
    have hη : canonicalSourceTwoCell (𝟙 X) (𝟙 g.2) =
        𝟙 (canonicalSourceHom (𝟙 X) g.2) := rfl
    rw [hη, F.map₂_id]
    simp
  map_comp η θ := by
    change (generalLiftSourceEquivalence F hF f).inv ◁
        F.map₂ (canonicalSourceTwoCell (𝟙 X) (η.2 ≫ θ.2)) = _
    have hηθ : canonicalSourceTwoCell (𝟙 X) (η.2 ≫ θ.2) =
        canonicalSourceTwoCell (𝟙 X) η.2 ≫
          canonicalSourceTwoCell (𝟙 X) θ.2 := rfl
    rw [hηθ, F.map₂_comp]
    simp

/-- Object action of the arbitrary lift.  The free-groupoid completion adds
arrows but no objects. -/
def generalLiftObj (F : Source ⥤ᵖ E) (X : Target) : E :=
  F.obj (sourceOfTarget X)

/-- The hom-category action of the arbitrary lift, before identity and
composition comparison isomorphisms are supplied. -/
noncomputable def generalLiftHomFunctor
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) (X Y : Target) :
    (X ⟶ Y) ⥤ (generalLiftObj F X ⟶ generalLiftObj F Y) := by
  rcases X with ⟨⟨X⟩, X'⟩
  rcases Y with ⟨⟨Y⟩, Y'⟩
  cases X'
  cases Y'
  let x : Ript.Examples.WalkingLocalization.Arrow := X.as.as
  let y : Ript.Examples.WalkingLocalization.Arrow := Y.as.as
  have hX : X = CategoryTheory.FreeGroupoid.mk x :=
    CategoryTheory.FreeGroupoid.eq_mk X
  have hY : Y = CategoryTheory.FreeGroupoid.mk y :=
    CategoryTheory.FreeGroupoid.eq_mk Y
  clear_value x
  clear_value y
  cases hX
  cases hY
  by_cases h : x ≤ y
  · exact generalLiftForwardHomFunctor F (homOfLE h)
  · exact generalLiftReverseHomFunctor F hF
      (homOfLE (le_of_not_ge h))

/-- The arbitrary lift already defines a functor on every hom-category.  This
is the complete object/1-cell/2-cell action prior to pseudofunctor coherence. -/
noncomputable def generalLiftPrelaxFunctor
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) :
    PrelaxFunctor Target E :=
  PrelaxFunctor.mkOfHomFunctors (generalLiftObj F)
    (generalLiftHomFunctor F hF)

/-- The prelax action reuses the original pseudofunctor on every canonical
forward target arrow. -/
theorem generalLiftPrelaxFunctor_map_forward
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A) =
      F.map (canonicalSourceHom f A) := by
  change (generalLiftHomFunctor F hF
      (canonicalTargetObject X) (canonicalTargetObject Y)).obj
        (canonicalForwardHom f A) = _
  change (if h : X ≤ Y then
      generalLiftForwardHomFunctor F (homOfLE h)
    else
      generalLiftReverseHomFunctor F hF
        (homOfLE (le_of_not_ge h))).obj
      (canonicalForwardHom f A) = _
  rw [dif_pos f.le]
  dsimp [generalLiftForwardHomFunctor]
  congr 2

/-- For a genuinely reverse endpoint pair, the prelax action sends the formal
inverse to the inverse of the chosen source-image equivalence, followed by the
retained-coordinate action. -/
theorem generalLiftPrelaxFunctor_map_inverse
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type) :
    (generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A) =
      (generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) A) := by
  change (generalLiftHomFunctor F hF
      (canonicalTargetObject Y) (canonicalTargetObject X)).obj
        (canonicalInverseHom f A) = _
  change (if h : Y ≤ X then
      generalLiftForwardHomFunctor F (homOfLE h)
    else
      generalLiftReverseHomFunctor F hF
        (homOfLE (le_of_not_ge h))).obj
      (canonicalInverseHom f A) = _
  rw [dif_neg hf]
  dsimp [generalLiftReverseHomFunctor]
  congr 2

/-- The action on forward retained-coordinate 2-cells is the source action.
The heterogeneous equality records the already-proved equality of the
dependent 1-morphism endpoints. -/
theorem generalLiftPrelaxFunctor_map₂_forward
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    HEq ((generalLiftPrelaxFunctor F hF).map₂
        (canonicalForwardTwoCell f η))
      (F.map₂ (canonicalSourceTwoCell f η)) := by
  change HEq ((generalLiftHomFunctor F hF
      (canonicalTargetObject X) (canonicalTargetObject Y)).map
        (canonicalForwardTwoCell f η)) _
  change HEq ((if h : X ≤ Y then
      generalLiftForwardHomFunctor F (homOfLE h)
    else
      generalLiftReverseHomFunctor F hF
        (homOfLE (le_of_not_ge h))).map
      (canonicalForwardTwoCell f η)) _
  rw [dif_pos f.le]
  dsimp [generalLiftForwardHomFunctor]
  congr 2

/-- On a genuinely reverse endpoint pair, the action on a retained-coordinate
2-cell is left whiskering by the chosen inverse. -/
theorem generalLiftPrelaxFunctor_map₂_inverse
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) {A B : Type} (η : A ⟶ B) :
    HEq ((generalLiftPrelaxFunctor F hF).map₂
        (canonicalInverseTwoCell f η))
      ((generalLiftSourceEquivalence F hF f).inv ◁
        F.map₂ (canonicalSourceTwoCell (𝟙 X) η)) := by
  change HEq ((generalLiftHomFunctor F hF
      (canonicalTargetObject Y) (canonicalTargetObject X)).map
        (canonicalInverseTwoCell f η)) _
  change HEq ((if h : Y ≤ X then
      generalLiftForwardHomFunctor F (homOfLE h)
    else
      generalLiftReverseHomFunctor F hF
        (homOfLE (le_of_not_ge h))).map
      (canonicalInverseTwoCell f η)) _
  rw [dif_neg hf]
  dsimp [generalLiftReverseHomFunctor]
  congr 2

/-- The canonical source arrow with identity data in both coordinates is
isomorphic to the strict source identity. -/
noncomputable def canonicalSourceIdentityComparison
    (X : Ript.Examples.WalkingLocalization.Arrow) :
    canonicalSourceHom (𝟙 X)
        (𝟙 (MonoidalSingleObj.star (Type))) ≅
      𝟙 (canonicalSourceObject X) :=
  eqToIso (by rfl)

/-- Identity comparison for the arbitrary lift at a canonical endpoint.  It
normalizes the strict target identity to a canonical forward arrow, reuses the
source action, and then applies the source pseudofunctor's unit comparison. -/
noncomputable def generalLiftCanonicalMapId
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    (X : Ript.Examples.WalkingLocalization.Arrow) :
    (generalLiftPrelaxFunctor F hF).map
        (𝟙 (canonicalTargetObject X)) ≅
      𝟙 ((generalLiftPrelaxFunctor F hF).obj
        (canonicalTargetObject X)) :=
  (generalLiftPrelaxFunctor F hF).map₂Iso
      (canonicalForwardIdentityComparison X).symm ≪≫
    eqToIso (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X)
      (𝟙 (MonoidalSingleObj.star (Type)))) ≪≫
    F.map₂Iso (canonicalSourceIdentityComparison X) ≪≫
    F.mapId (canonicalSourceObject X)

/-- Identity comparison for the arbitrary lift at every target object.  Target
objects have canonical walking-arrow representatives, so no new object-level
choice is needed. -/
noncomputable def generalLiftMapId
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) (X : Target) :
    (generalLiftPrelaxFunctor F hF).map (𝟙 X) ≅
      𝟙 ((generalLiftPrelaxFunctor F hF).obj X) := by
  rcases X with ⟨⟨X⟩, X'⟩
  cases X'
  rw [CategoryTheory.FreeGroupoid.eq_mk X]
  exact generalLiftCanonicalMapId F hF X.as.as

/-- On a canonical target endpoint, the general identity comparison reduces
definitionally to its explicit four-stage normalization chain. -/
theorem generalLiftMapId_canonical
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    (X : Ript.Examples.WalkingLocalization.Arrow) :
    generalLiftMapId F hF (canonicalTargetObject X) =
      generalLiftCanonicalMapId F hF X := by
  rfl

/-- Canonical source arrows compose by composing their walking arrows and
forming the cartesian product of their retained coordinates. -/
noncomputable def canonicalSourceCompositionComparison
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A B : Type) :
    canonicalSourceHom f A ≫ canonicalSourceHom g B ≅
      canonicalSourceHom (f ≫ g) (A × B) :=
  eqToIso (by rfl)

/-- The analogous composition comparison after free-groupoid completion. -/
noncomputable def canonicalForwardCompositionComparison
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A B : Type) :
    canonicalForwardHom f A ≫ canonicalForwardHom g B ≅
      canonicalForwardHom (f ≫ g) (A × B) :=
  Iso.prod (eqToIso (by
    apply Discrete.ext
    exact ((CategoryTheory.FreeGroupoid.of
      Ript.Examples.WalkingLocalization.Arrow).map_comp f g).symm))
    (Iso.refl _)

/-- Source pseudofunctor composition, expressed on canonical source arrows. -/
noncomputable def generalLiftForwardMapCompSource
    (F : Source ⥤ᵖ E)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A B : Type) :
    F.map (canonicalSourceHom (f ≫ g) (A × B)) ≅
      F.map (canonicalSourceHom f A) ≫
        F.map (canonicalSourceHom g B) :=
  F.map₂Iso (canonicalSourceCompositionComparison f g A B).symm ≪≫
    F.mapComp (canonicalSourceHom f A) (canonicalSourceHom g B)

/-- Composition comparison for two canonical forward target arrows.  This
discharges all four endpoint triples whose two factors both come from the
walking-arrow source. -/
noncomputable def generalLiftMapCompForward
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A B : Type) :
    (generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom f A ≫ canonicalForwardHom g B) ≅
      (generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A) ≫
        (generalLiftPrelaxFunctor F hF).map (canonicalForwardHom g B) :=
  (generalLiftPrelaxFunctor F hF).map₂Iso
      (canonicalForwardCompositionComparison f g A B) ≪≫
    eqToIso (generalLiftPrelaxFunctor_map_forward F hF (f ≫ g) (A × B)) ≪≫
    generalLiftForwardMapCompSource F f g A B ≪≫
    whiskerRightIso
        (eqToIso (generalLiftPrelaxFunctor_map_forward F hF f A)).symm
        (F.map (canonicalSourceHom g B)) ≪≫
    whiskerLeftIso
      ((generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A))
      (eqToIso (generalLiftPrelaxFunctor_map_forward F hF g B)).symm

/-- A canonical inverse arrow followed by a retained-coordinate endomorphism
normalizes to one inverse arrow with product retained coordinate. -/
noncomputable def canonicalInverseRetainedCompositionComparison
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    canonicalInverseHom f A ≫ canonicalForwardHom (𝟙 X) B ≅
      canonicalInverseHom f (A × B) :=
  Iso.prod (eqToIso (by
    apply Discrete.ext
    change inv (CategoryTheory.FreeGroupoid.homMk f) ≫
        CategoryTheory.FreeGroupoid.homMk (𝟙 X) =
      inv (CategoryTheory.FreeGroupoid.homMk f)
    simp)) (Iso.refl _)

/-- Composition comparison for a genuine inverse arrow followed by a
retained-coordinate endomorphism. -/
noncomputable def generalLiftMapCompInverseRetained
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftPrelaxFunctor F hF).map
        (canonicalInverseHom f A ≫ canonicalForwardHom (𝟙 X) B) ≅
      (generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A) ≫
        (generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom (𝟙 X) B) :=
  (generalLiftPrelaxFunctor F hF).map₂Iso
      (canonicalInverseRetainedCompositionComparison f A B) ≪≫
    eqToIso (generalLiftPrelaxFunctor_map_inverse F hF f hf (A × B)) ≪≫
    whiskerLeftIso (generalLiftSourceEquivalence F hF f).inv
      (generalLiftForwardMapCompSource F (𝟙 X) (𝟙 X) A B) ≪≫
    (α_ (generalLiftSourceEquivalence F hF f).inv
      (F.map (canonicalSourceHom (𝟙 X) A))
      (F.map (canonicalSourceHom (𝟙 X) B))).symm ≪≫
    whiskerRightIso
      (eqToIso (generalLiftPrelaxFunctor_map_inverse F hF f hf A)).symm
      (F.map (canonicalSourceHom (𝟙 X) B)) ≪≫
    whiskerLeftIso
      ((generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A))
      (eqToIso (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X) B)).symm

/-- A source generator followed by a retained-coordinate endomorphism
normalizes through the cartesian left unitor. -/
noncomputable def canonicalSourceGeneratorRetainedComparison
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    canonicalSourceHom f (𝟙 (MonoidalSingleObj.star (Type))) ≫
        canonicalSourceHom (𝟙 Y) A ≅
      canonicalSourceHom f A :=
  Iso.prod (eqToIso (by
    apply Discrete.ext
    change f ≫ 𝟙 Y = f
    simp)) (MonoidalCategory.leftUnitor A)

/-- A retained-coordinate endomorphism followed by a source generator
normalizes through the cartesian right unitor. -/
noncomputable def canonicalSourceRetainedGeneratorComparison
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    canonicalSourceHom (𝟙 X) A ≫
        canonicalSourceHom f (𝟙 (MonoidalSingleObj.star (Type))) ≅
      canonicalSourceHom f A :=
  Iso.prod (eqToIso (by
    apply Discrete.ext
    change 𝟙 X ≫ f = f
    simp)) (MonoidalCategory.rightUnitor A)

/-- The source pseudofunctor's image of retained data slides across the image
of the marked forward generator. -/
noncomputable def generalLiftForwardSlidingSource
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (generalLiftSourceEquivalence F hF f).hom ≫
        F.map (canonicalSourceHom (𝟙 Y) A) ≅
      F.map (canonicalSourceHom (𝟙 X) A) ≫
        (generalLiftSourceEquivalence F hF f).hom :=
  (F.map₂Iso (canonicalSourceGeneratorRetainedComparison f A).symm ≪≫
    F.mapComp
      (canonicalSourceHom f (𝟙 (MonoidalSingleObj.star (Type))))
      (canonicalSourceHom (𝟙 Y) A)).symm ≪≫
  (F.map₂Iso (canonicalSourceRetainedGeneratorComparison f A).symm ≪≫
    F.mapComp
      (canonicalSourceHom (𝟙 X) A)
      (canonicalSourceHom f (𝟙 (MonoidalSingleObj.star (Type)))))

/-- Taking the invertible mate of forward sliding lets retained data slide
across the chosen inverse. -/
noncomputable def generalLiftInverseSlidingSource
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) A) ≅
      F.map (canonicalSourceHom (𝟙 Y) A) ≫
        (generalLiftSourceEquivalence F hF f).inv :=
  Pseudofunctor.StrongTrans.inverseNaturalityIso
    (Pseudofunctor.id E) (Pseudofunctor.id E)
    (generalLiftSourceEquivalence F hF f)
    (F.map (canonicalSourceHom (𝟙 X) A))
    (F.map (canonicalSourceHom (𝟙 Y) A))
    (generalLiftForwardSlidingSource F hF f A)

/-- A retained-coordinate endomorphism followed by a canonical inverse arrow
normalizes to one inverse arrow with product retained coordinate. -/
noncomputable def canonicalRetainedInverseCompositionComparison
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    canonicalForwardHom (𝟙 Y) A ≫ canonicalInverseHom f B ≅
      canonicalInverseHom f (A × B) :=
  Iso.prod (eqToIso (by
    apply Discrete.ext
    change CategoryTheory.FreeGroupoid.homMk (𝟙 Y) ≫
        inv (CategoryTheory.FreeGroupoid.homMk f) =
      inv (CategoryTheory.FreeGroupoid.homMk f)
    simp)) (Iso.refl _)

/-- Composition comparison for a retained-coordinate endomorphism followed by
a genuine inverse arrow. -/
noncomputable def generalLiftMapCompRetainedInverse
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom (𝟙 Y) A ≫ canonicalInverseHom f B) ≅
      (generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom (𝟙 Y) A) ≫
        (generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f B) :=
  (generalLiftPrelaxFunctor F hF).map₂Iso
      (canonicalRetainedInverseCompositionComparison f A B) ≪≫
    eqToIso (generalLiftPrelaxFunctor_map_inverse F hF f hf (A × B)) ≪≫
    whiskerLeftIso (generalLiftSourceEquivalence F hF f).inv
      (generalLiftForwardMapCompSource F (𝟙 X) (𝟙 X) A B) ≪≫
    (α_ (generalLiftSourceEquivalence F hF f).inv
      (F.map (canonicalSourceHom (𝟙 X) A))
      (F.map (canonicalSourceHom (𝟙 X) B))).symm ≪≫
    whiskerRightIso (generalLiftInverseSlidingSource F hF f A)
      (F.map (canonicalSourceHom (𝟙 X) B)) ≪≫
    α_ (F.map (canonicalSourceHom (𝟙 Y) A))
      (generalLiftSourceEquivalence F hF f).inv
      (F.map (canonicalSourceHom (𝟙 X) B)) ≪≫
    whiskerRightIso
      (eqToIso (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y) A)).symm
      ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) B)) ≪≫
    whiskerLeftIso
      ((generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom (𝟙 Y) A))
      (eqToIso (generalLiftPrelaxFunctor_map_inverse F hF f hf B)).symm

/-- The image of a source generator with retained data factors through the
chosen forward equivalence and retained data at its codomain. -/
noncomputable def generalLiftForwardFactorizationSource
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    F.map (canonicalSourceHom f A) ≅
      (generalLiftSourceEquivalence F hF f).hom ≫
        F.map (canonicalSourceHom (𝟙 Y) A) :=
  F.map₂Iso (canonicalSourceGeneratorRetainedComparison f A).symm ≪≫
    F.mapComp
      (canonicalSourceHom f (𝟙 (MonoidalSingleObj.star (Type))))
      (canonicalSourceHom (𝟙 Y) A)

/-- The same image also factors through retained data at the domain followed
by the chosen forward equivalence. -/
noncomputable def generalLiftRetainedForwardFactorizationSource
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    F.map (canonicalSourceHom f A) ≅
      F.map (canonicalSourceHom (𝟙 X) A) ≫
        (generalLiftSourceEquivalence F hF f).hom :=
  F.map₂Iso (canonicalSourceRetainedGeneratorComparison f A).symm ≪≫
    F.mapComp
      (canonicalSourceHom (𝟙 X) A)
      (canonicalSourceHom f (𝟙 (MonoidalSingleObj.star (Type))))

/-- A canonical inverse followed by the matching forward arrow cancels in the
completed walking coordinate and retains both coordinates at the codomain. -/
noncomputable def canonicalInverseForwardCompositionComparison
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    canonicalInverseHom f A ≫ canonicalForwardHom f B ≅
      canonicalForwardHom (𝟙 Y) (A × B) :=
  Iso.prod (eqToIso (by
    apply Discrete.ext
    change inv (CategoryTheory.FreeGroupoid.homMk f) ≫
        CategoryTheory.FreeGroupoid.homMk f =
      CategoryTheory.FreeGroupoid.homMk (𝟙 Y)
    simp)) (Iso.refl _)

/-- A canonical forward arrow followed by its matching inverse cancels in the
completed walking coordinate and retains both coordinates at the domain. -/
noncomputable def canonicalForwardInverseCompositionComparison
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    canonicalForwardHom f A ≫ canonicalInverseHom f B ≅
      canonicalForwardHom (𝟙 X) (A × B) :=
  Iso.prod (eqToIso (by
    apply Discrete.ext
    change CategoryTheory.FreeGroupoid.homMk f ≫
        inv (CategoryTheory.FreeGroupoid.homMk f) =
      CategoryTheory.FreeGroupoid.homMk (𝟙 X)
    simp)) (Iso.refl _)

/-- Composition comparison for a canonical inverse followed by the matching
forward arrow. -/
noncomputable def generalLiftMapCompInverseForward
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftPrelaxFunctor F hF).map
        (canonicalInverseHom f A ≫ canonicalForwardHom f B) ≅
      (generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A) ≫
        (generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f B) :=
  (generalLiftPrelaxFunctor F hF).map₂Iso
      (canonicalInverseForwardCompositionComparison f A B) ≪≫
    eqToIso (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y) (A × B)) ≪≫
    generalLiftForwardMapCompSource F (𝟙 Y) (𝟙 Y) A B ≪≫
    (λ_ (F.map (canonicalSourceHom (𝟙 Y) A) ≫
      F.map (canonicalSourceHom (𝟙 Y) B))).symm ≪≫
    whiskerRightIso (generalLiftSourceEquivalence F hF f).counit.symm
      (F.map (canonicalSourceHom (𝟙 Y) A) ≫
        F.map (canonicalSourceHom (𝟙 Y) B)) ≪≫
    α_ (generalLiftSourceEquivalence F hF f).inv
      (generalLiftSourceEquivalence F hF f).hom
      (F.map (canonicalSourceHom (𝟙 Y) A) ≫
        F.map (canonicalSourceHom (𝟙 Y) B)) ≪≫
    whiskerLeftIso (generalLiftSourceEquivalence F hF f).inv
      (α_ (generalLiftSourceEquivalence F hF f).hom
        (F.map (canonicalSourceHom (𝟙 Y) A))
        (F.map (canonicalSourceHom (𝟙 Y) B))).symm ≪≫
    whiskerLeftIso (generalLiftSourceEquivalence F hF f).inv
      (whiskerRightIso (generalLiftForwardSlidingSource F hF f A)
        (F.map (canonicalSourceHom (𝟙 Y) B))) ≪≫
    whiskerLeftIso (generalLiftSourceEquivalence F hF f).inv
      (α_ (F.map (canonicalSourceHom (𝟙 X) A))
        (generalLiftSourceEquivalence F hF f).hom
        (F.map (canonicalSourceHom (𝟙 Y) B))) ≪≫
    (α_ (generalLiftSourceEquivalence F hF f).inv
      (F.map (canonicalSourceHom (𝟙 X) A))
      ((generalLiftSourceEquivalence F hF f).hom ≫
        F.map (canonicalSourceHom (𝟙 Y) B))).symm ≪≫
    whiskerLeftIso
      ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) A))
      (generalLiftForwardFactorizationSource F hF f B).symm ≪≫
    whiskerRightIso
      (eqToIso (generalLiftPrelaxFunctor_map_inverse F hF f hf A)).symm
      (F.map (canonicalSourceHom f B)) ≪≫
    whiskerLeftIso
      ((generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A))
      (eqToIso (generalLiftPrelaxFunctor_map_forward F hF f B)).symm

/-- Composition comparison for a canonical forward arrow followed by the
matching inverse. -/
noncomputable def generalLiftMapCompForwardInverse
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom f A ≫ canonicalInverseHom f B) ≅
      (generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A) ≫
        (generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f B) :=
  (generalLiftPrelaxFunctor F hF).map₂Iso
      (canonicalForwardInverseCompositionComparison f A B) ≪≫
    eqToIso (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X) (A × B)) ≪≫
    generalLiftForwardMapCompSource F (𝟙 X) (𝟙 X) A B ≪≫
    whiskerLeftIso (F.map (canonicalSourceHom (𝟙 X) A))
      (λ_ (F.map (canonicalSourceHom (𝟙 X) B))).symm ≪≫
    whiskerLeftIso (F.map (canonicalSourceHom (𝟙 X) A))
      (whiskerRightIso (generalLiftSourceEquivalence F hF f).unit
        (F.map (canonicalSourceHom (𝟙 X) B))) ≪≫
    whiskerLeftIso (F.map (canonicalSourceHom (𝟙 X) A))
      (α_ (generalLiftSourceEquivalence F hF f).hom
        (generalLiftSourceEquivalence F hF f).inv
        (F.map (canonicalSourceHom (𝟙 X) B))) ≪≫
    (α_ (F.map (canonicalSourceHom (𝟙 X) A))
      (generalLiftSourceEquivalence F hF f).hom
      ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) B))).symm ≪≫
    whiskerRightIso
      (generalLiftRetainedForwardFactorizationSource F hF f A).symm
      ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) B)) ≪≫
    whiskerRightIso
      (eqToIso (generalLiftPrelaxFunctor_map_forward F hF f A)).symm
      ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) B)) ≪≫
    whiskerLeftIso
      ((generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A))
      (eqToIso (generalLiftPrelaxFunctor_map_inverse F hF f hf B)).symm

/-- A target arrow in the unique normal form determined by its two walking
endpoints and its retained-coordinate type. -/
noncomputable def canonicalEndpointHom
    (X Y : Ript.Examples.WalkingLocalization.Arrow) (A : Type) :
    canonicalTargetObject X ⟶ canonicalTargetObject Y :=
  (canonicalCompletionHom X Y).toLoc ×ₘ A

/-- Composition comparison for endpoint-normal target arrows.  Equality
tests, rather than large elimination from `Fin 2`, select the eight compiled
canonical branches.  This keeps the result in the target bicategory's full
universe and leaves each branch definitionally available for coherence. -/
noncomputable def generalLiftEndpointMapComp
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    (X Y Z : Ript.Examples.WalkingLocalization.Arrow) (A B : Type) :
    (generalLiftPrelaxFunctor F hF).map
        (canonicalEndpointHom X Y A ≫ canonicalEndpointHom Y Z B) ≅
      (generalLiftPrelaxFunctor F hF).map (canonicalEndpointHom X Y A) ≫
        (generalLiftPrelaxFunctor F hF).map
          (canonicalEndpointHom Y Z B) := by
  classical
  by_cases hX : X = 0
  · subst X
    by_cases hY : Y = 0
    · subst Y
      by_cases hZ : Z = 0
      · subst Z
        exact generalLiftMapCompForward F hF
          (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow))
          (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) A B
      · have hZ' : Z = 1 := by fin_cases Z <;> simp_all
        subst Z
        exact generalLiftMapCompForward F hF
          (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow))
          Ript.Examples.WalkingLocalization.arrow A B
    · have hY' : Y = 1 := by fin_cases Y <;> simp_all
      subst Y
      by_cases hZ : Z = 0
      · subst Z
        exact generalLiftMapCompForwardInverse F hF
          Ript.Examples.WalkingLocalization.arrow (by decide) A B
      · have hZ' : Z = 1 := by fin_cases Z <;> simp_all
        subst Z
        exact generalLiftMapCompForward F hF
          Ript.Examples.WalkingLocalization.arrow
          (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) A B
  · have hX' : X = 1 := by fin_cases X <;> simp_all
    subst X
    by_cases hY : Y = 0
    · subst Y
      by_cases hZ : Z = 0
      · subst Z
        exact generalLiftMapCompInverseRetained F hF
          Ript.Examples.WalkingLocalization.arrow (by decide) A B
      · have hZ' : Z = 1 := by fin_cases Z <;> simp_all
        subst Z
        exact generalLiftMapCompInverseForward F hF
          Ript.Examples.WalkingLocalization.arrow (by decide) A B
    · have hY' : Y = 1 := by fin_cases Y <;> simp_all
      subst Y
      by_cases hZ : Z = 0
      · subst Z
        exact generalLiftMapCompRetainedInverse F hF
          Ript.Examples.WalkingLocalization.arrow (by decide) A B
      · have hZ' : Z = 1 := by fin_cases Z <;> simp_all
        subst Z
        exact generalLiftMapCompForward F hF
          (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow))
          (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) A B

/-- The endpoint comparison at `0 → 0 → 0` is the forward/forward
branch. -/
theorem generalLiftEndpointMapComp_zero_zero_zero
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) (A B : Type) :
    generalLiftEndpointMapComp F hF 0 0 0 A B =
      generalLiftMapCompForward F hF
        (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow))
        (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) A B := by
  simp [generalLiftEndpointMapComp]
  congr

/-- The endpoint comparison at `0 → 0 → 1` is the forward/forward
branch. -/
theorem generalLiftEndpointMapComp_zero_zero_one
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) (A B : Type) :
    generalLiftEndpointMapComp F hF 0 0 1 A B =
      generalLiftMapCompForward F hF
        (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow))
        Ript.Examples.WalkingLocalization.arrow A B := by
  simp [generalLiftEndpointMapComp]
  congr

/-- The endpoint comparison at `0 → 1 → 0` is forward/inverse
cancellation. -/
theorem generalLiftEndpointMapComp_zero_one_zero
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) (A B : Type) :
    generalLiftEndpointMapComp F hF 0 1 0 A B =
      generalLiftMapCompForwardInverse F hF
        Ript.Examples.WalkingLocalization.arrow (by decide) A B := by
  simp [generalLiftEndpointMapComp]
  congr

/-- The endpoint comparison at `0 → 1 → 1` is the forward/forward
branch. -/
theorem generalLiftEndpointMapComp_zero_one_one
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) (A B : Type) :
    generalLiftEndpointMapComp F hF 0 1 1 A B =
      generalLiftMapCompForward F hF
        Ript.Examples.WalkingLocalization.arrow
        (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) A B := by
  simp [generalLiftEndpointMapComp]
  congr

/-- The endpoint comparison at `1 → 0 → 0` is the inverse/retained
branch. -/
theorem generalLiftEndpointMapComp_one_zero_zero
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) (A B : Type) :
    generalLiftEndpointMapComp F hF 1 0 0 A B =
      generalLiftMapCompInverseRetained F hF
        Ript.Examples.WalkingLocalization.arrow (by decide) A B := by
  simp [generalLiftEndpointMapComp]
  congr

/-- The endpoint comparison at `1 → 0 → 1` is inverse/forward
cancellation. -/
theorem generalLiftEndpointMapComp_one_zero_one
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) (A B : Type) :
    generalLiftEndpointMapComp F hF 1 0 1 A B =
      generalLiftMapCompInverseForward F hF
        Ript.Examples.WalkingLocalization.arrow (by decide) A B := by
  simp [generalLiftEndpointMapComp]
  congr

/-- The endpoint comparison at `1 → 1 → 0` is the retained/inverse
branch. -/
theorem generalLiftEndpointMapComp_one_one_zero
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) (A B : Type) :
    generalLiftEndpointMapComp F hF 1 1 0 A B =
      generalLiftMapCompRetainedInverse F hF
        Ript.Examples.WalkingLocalization.arrow (by decide) A B := by
  simp [generalLiftEndpointMapComp]
  congr

/-- The endpoint comparison at `1 → 1 → 1` is the forward/forward
branch. -/
theorem generalLiftEndpointMapComp_one_one_one
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) (A B : Type) :
    generalLiftEndpointMapComp F hF 1 1 1 A B =
      generalLiftMapCompForward F hF
        (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow))
        (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) A B := by
  simp [generalLiftEndpointMapComp]
  congr

/-- Composition comparison for every composable pair of target arrows.
Objects are first rewritten to their canonical free-groupoid representatives;
thinness then rewrites both walking-coordinate arrows to their endpoint normal
forms, where `generalLiftEndpointMapComp` supplies the relevant one of the
eight compiled comparisons. -/
noncomputable def generalLiftMapComp
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Target} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (generalLiftPrelaxFunctor F hF).map (f ≫ g) ≅
      (generalLiftPrelaxFunctor F hF).map f ≫
        (generalLiftPrelaxFunctor F hF).map g := by
  rcases X with ⟨⟨X⟩, X'⟩
  rcases Y with ⟨⟨Y⟩, Y'⟩
  rcases Z with ⟨⟨Z⟩, Z'⟩
  cases X'
  cases Y'
  cases Z'
  let x : Ript.Examples.WalkingLocalization.Arrow := X.as.as
  let y : Ript.Examples.WalkingLocalization.Arrow := Y.as.as
  let z : Ript.Examples.WalkingLocalization.Arrow := Z.as.as
  have hX : X = CategoryTheory.FreeGroupoid.mk x :=
    CategoryTheory.FreeGroupoid.eq_mk X
  have hY : Y = CategoryTheory.FreeGroupoid.mk y :=
    CategoryTheory.FreeGroupoid.eq_mk Y
  have hZ : Z = CategoryTheory.FreeGroupoid.mk z :=
    CategoryTheory.FreeGroupoid.eq_mk Z
  cases hX
  cases hY
  cases hZ
  rcases f with ⟨⟨f⟩, A⟩
  rcases g with ⟨⟨g⟩, B⟩
  have hf : f = canonicalCompletionHom x y :=
    completion_hom_eq_canonical f
  have hg : g = canonicalCompletionHom y z :=
    completion_hom_eq_canonical g
  cases hf
  cases hg
  exact generalLiftEndpointMapComp F hF x y z A B

/-- On endpoint-normal arrows, the all-arrow comparison reduces
definitionally to the explicit eight-branch comparison. -/
theorem generalLiftMapComp_endpoint
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    (X Y Z : Ript.Examples.WalkingLocalization.Arrow) (A B : Type) :
    generalLiftMapComp F hF (canonicalEndpointHom X Y A)
        (canonicalEndpointHom Y Z B) =
      generalLiftEndpointMapComp F hF X Y Z A B := by
  rfl

end ArbitraryLiftPrelaxAction

end Ript.Examples.TwoDimensionalWalkingLocalization
