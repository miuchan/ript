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
compiled reduction equations exposing all eight branches.  The
source-normalized forward-forward three-fold associativity core, the canonical
target comparison square, its image under the arbitrary target action, and
the seven-endpoint transport law now compile.  Target normalization is now
composed with that transport into the exact oplax associativity equation for
every triple of canonical forward arrows.  The first genuinely inverse
endpoint sequence, inverse followed by two retained arrows, now satisfies the
same exact equation through an inverse-whiskered source law and seven endpoint
transports.  The retained/retained/inverse target-normalization square,
inverse-sliding multiplicativity, normalized source law, seven-endpoint
transport, and exact all-arrow associativity equation are now compiled too;
the mixed retained/inverse/retained sequence now compiles by the same layered
target/source/transport method.  The forward/retained/inverse,
retained/forward/inverse, forward/inverse/retained,
inverse/forward/retained, inverse/retained/forward, and
retained/inverse/forward cancellation sequences now compile through the same
target, source, endpoint-transport, and all-arrow layers.
The dual inverse/forward/inverse sequence now also compiles through all four
layers.  Endpoint normalization reduces every arbitrary triple to these
sixteen cases, so the action packages as `generalLiftPseudofunctor` for an
arbitrary destination bicategory; the locally thin construction remains as a
specialized corollary.  The resulting arbitrary nonseparable biessential
factorization still remains open;
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

/-- The arbitrary hom-category action at `0 → 0` is the forward action for
the walking identity. -/
theorem generalLiftHomFunctor_zero_zero
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) :
    generalLiftHomFunctor F hF (canonicalTargetObject 0)
        (canonicalTargetObject 0) =
      generalLiftForwardHomFunctor F
        (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) := by
  simp [generalLiftHomFunctor, canonicalTargetObject]
  congr

/-- The arbitrary hom-category action at `0 → 1` is the forward action for
the walking generator. -/
theorem generalLiftHomFunctor_zero_one
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) :
    generalLiftHomFunctor F hF (canonicalTargetObject 0)
        (canonicalTargetObject 1) =
      generalLiftForwardHomFunctor F
        Ript.Examples.WalkingLocalization.arrow := by
  simp [generalLiftHomFunctor, canonicalTargetObject]
  congr

/-- The arbitrary hom-category action at `1 → 0` is the reverse action for
the walking generator. -/
theorem generalLiftHomFunctor_one_zero
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) :
    generalLiftHomFunctor F hF (canonicalTargetObject 1)
        (canonicalTargetObject 0) =
      generalLiftReverseHomFunctor F hF
        Ript.Examples.WalkingLocalization.arrow := by
  simp [generalLiftHomFunctor, canonicalTargetObject]
  congr

/-- The arbitrary hom-category action at `1 → 1` is the forward action for
the walking identity. -/
theorem generalLiftHomFunctor_one_one
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) :
    generalLiftHomFunctor F hF (canonicalTargetObject 1)
        (canonicalTargetObject 1) =
      generalLiftForwardHomFunctor F
        (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) := by
  simp [generalLiftHomFunctor, canonicalTargetObject]
  congr

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

/-- The canonical source composition comparisons satisfy the three-fold
associativity square, with the cartesian-product associator recording the
change of retained-coordinate bracketing.  This is the source-level core of
the lift compositor associativity proof. -/
theorem canonicalSourceCompositionComparison_associativity
    {X Y Z W : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (A B C : Type) :
    ((canonicalSourceCompositionComparison f g A B).hom ▷
          canonicalSourceHom h C) ≫
        (canonicalSourceCompositionComparison (f ≫ g) h (A × B) C).hom ≫
        canonicalSourceTwoCell ((f ≫ g) ≫ h)
          (MonoidalCategory.associator A B C).hom =
      (α_ (canonicalSourceHom f A) (canonicalSourceHom g B)
          (canonicalSourceHom h C)).hom ≫
        (canonicalSourceHom f A ◁
          (canonicalSourceCompositionComparison g h B C).hom) ≫
          (canonicalSourceCompositionComparison f (g ≫ h) A (B × C)).hom := by
  rfl

/-- Inverse-oriented form of the canonical source associativity square.  Its
orientation is the one needed to move from a normalized three-fold composite
to the raw parenthesized composite before applying pseudofunctor
associativity. -/
theorem canonicalSourceCompositionComparison_associativity_inv
    {X Y Z W : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (A B C : Type) :
    canonicalSourceTwoCell ((f ≫ g) ≫ h)
          (MonoidalCategory.associator A B C).hom ≫
        (canonicalSourceCompositionComparison f (g ≫ h)
          A (B × C)).symm.hom ≫
        (canonicalSourceHom f A ◁
          (canonicalSourceCompositionComparison g h B C).symm.hom) =
      (canonicalSourceCompositionComparison (f ≫ g) h
          (A × B) C).symm.hom ≫
        ((canonicalSourceCompositionComparison f g A B).symm.hom ▷
          canonicalSourceHom h C) ≫
        (α_ (canonicalSourceHom f A) (canonicalSourceHom g B)
          (canonicalSourceHom h C)).hom := by
  rfl

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

/-- The canonical target forward composition comparisons satisfy the same
three-fold associativity square as their source counterparts.  The completed
walking coordinate is locally discrete, while the retained coordinate records
the cartesian-product associator. -/
theorem canonicalForwardCompositionComparison_associativity
    {X Y Z W : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (A B C : Type) :
    ((canonicalForwardCompositionComparison f g A B).hom ▷
          canonicalForwardHom h C) ≫
        (canonicalForwardCompositionComparison (f ≫ g) h (A × B) C).hom ≫
        canonicalForwardTwoCell ((f ≫ g) ≫ h)
          (MonoidalCategory.associator A B C).hom =
      (α_ (canonicalForwardHom f A) (canonicalForwardHom g B)
          (canonicalForwardHom h C)).hom ≫
        (canonicalForwardHom f A ◁
          (canonicalForwardCompositionComparison g h B C).hom) ≫
        (canonicalForwardCompositionComparison f (g ≫ h) A (B × C)).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- Inverse-oriented form of the canonical target forward associativity
square.  This is the direction used when an arbitrary raw three-fold
composite is normalized before its endpoint transports are applied. -/
theorem canonicalForwardCompositionComparison_associativity_inv
    {X Y Z W : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (A B C : Type) :
    canonicalForwardTwoCell ((f ≫ g) ≫ h)
          (MonoidalCategory.associator A B C).hom ≫
        (canonicalForwardCompositionComparison f (g ≫ h)
          A (B × C)).symm.hom ≫
        (canonicalForwardHom f A ◁
          (canonicalForwardCompositionComparison g h B C).symm.hom) =
      (canonicalForwardCompositionComparison (f ≫ g) h
          (A × B) C).symm.hom ≫
        ((canonicalForwardCompositionComparison f g A B).symm.hom ▷
          canonicalForwardHom h C) ≫
        (α_ (canonicalForwardHom f A) (canonicalForwardHom g B)
          (canonicalForwardHom h C)).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- Applying the arbitrary target action to the canonical forward
associativity square preserves its three vertical composites. -/
theorem generalLiftForwardMapCompTarget_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z W : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          ((canonicalForwardCompositionComparison f g A B).hom ▷
            canonicalForwardHom h C) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardCompositionComparison (f ≫ g) h
            (A × B) C).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell ((f ≫ g) ≫ h)
            (MonoidalCategory.associator A B C).hom) =
      (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalForwardHom f A) (canonicalForwardHom g B)
            (canonicalForwardHom h C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardHom f A ◁
            (canonicalForwardCompositionComparison g h B C).hom) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardCompositionComparison f (g ≫ h)
            A (B × C)).hom := by
  simpa only [(generalLiftPrelaxFunctor F hF).map₂_comp] using
    congrArg (fun η => (generalLiftPrelaxFunctor F hF).map₂ η)
      (canonicalForwardCompositionComparison_associativity f g h A B C)

/-- The forward composition comparison is natural in a retained-coordinate
2-morphism on its right factor. -/
theorem canonicalForwardCompositionComparison_naturality_right
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    (canonicalForwardHom f A ◁ canonicalForwardTwoCell g η) ≫
          (canonicalForwardCompositionComparison f g A C).hom =
      (canonicalForwardCompositionComparison f g A B).hom ≫
        canonicalForwardTwoCell (f ≫ g)
          (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η) := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- Mapping the right naturality square through the arbitrary lift preserves
its vertical composite. -/
theorem generalLiftForwardMapCompTarget_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardHom f A ◁ canonicalForwardTwoCell g η) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardCompositionComparison f g A C).hom =
      (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardCompositionComparison f g A B).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (f ≫ g)
            (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η)) := by
  rw [← (generalLiftPrelaxFunctor F hF).map₂_comp,
    canonicalForwardCompositionComparison_naturality_right,
    (generalLiftPrelaxFunctor F hF).map₂_comp]

/-- The source composition comparison has the same right naturality square
before free-groupoid completion. -/
theorem canonicalSourceCompositionComparison_naturality_right
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    (canonicalSourceHom f A ◁ canonicalSourceTwoCell g η) ≫
          (canonicalSourceCompositionComparison f g A C).hom =
      (canonicalSourceCompositionComparison f g A B).hom ≫
        canonicalSourceTwoCell (f ≫ g)
          (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η) := by
  rfl

/-- Inverse form of right naturality, oriented for the first stage of the
source pseudofunctor's composition comparison. -/
theorem canonicalSourceCompositionComparison_naturality_right_inv
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    canonicalSourceTwoCell (f ≫ g)
          (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η) ≫
        (canonicalSourceCompositionComparison f g A C).symm.hom =
      (canonicalSourceCompositionComparison f g A B).symm.hom ≫
        (canonicalSourceHom f A ◁ canonicalSourceTwoCell g η) := by
  rfl

/-- The forward composition comparison is natural in a retained-coordinate
2-morphism on its left factor. -/
theorem canonicalForwardCompositionComparison_naturality_left
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    (canonicalForwardTwoCell f η ▷ canonicalForwardHom g B) ≫
          (canonicalForwardCompositionComparison f g C B).hom =
      (canonicalForwardCompositionComparison f g A B).hom ≫
        canonicalForwardTwoCell (f ≫ g)
          (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B)) := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- Mapping the left naturality square through the arbitrary lift preserves
its vertical composite. -/
theorem generalLiftForwardMapCompTarget_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell f η ▷ canonicalForwardHom g B) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardCompositionComparison f g C B).hom =
      (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardCompositionComparison f g A B).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (f ≫ g)
            (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B))) := by
  rw [← (generalLiftPrelaxFunctor F hF).map₂_comp,
    canonicalForwardCompositionComparison_naturality_left,
    (generalLiftPrelaxFunctor F hF).map₂_comp]

/-- The source composition comparison has the corresponding left naturality
square before free-groupoid completion. -/
theorem canonicalSourceCompositionComparison_naturality_left
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    (canonicalSourceTwoCell f η ▷ canonicalSourceHom g B) ≫
          (canonicalSourceCompositionComparison f g C B).hom =
      (canonicalSourceCompositionComparison f g A B).hom ≫
        canonicalSourceTwoCell (f ≫ g)
          (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B)) := by
  rfl

/-- Inverse form of left naturality, oriented for the first stage of the
source pseudofunctor's composition comparison. -/
theorem canonicalSourceCompositionComparison_naturality_left_inv
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    canonicalSourceTwoCell (f ≫ g)
          (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B)) ≫
        (canonicalSourceCompositionComparison f g C B).symm.hom =
      (canonicalSourceCompositionComparison f g A B).symm.hom ≫
        (canonicalSourceTwoCell f η ▷ canonicalSourceHom g B) := by
  rfl

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

/-- The source-side forward composition comparison is natural in its right
retained-coordinate 2-morphism. -/
theorem generalLiftForwardMapCompSource_naturality_right
    (F : Source ⥤ᵖ E)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    F.map₂ (canonicalSourceTwoCell (f ≫ g)
          (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η)) ≫
        (generalLiftForwardMapCompSource F f g A C).hom =
      (generalLiftForwardMapCompSource F f g A B).hom ≫
        F.map (canonicalSourceHom f A) ◁
          F.map₂ (canonicalSourceTwoCell g η) := by
  simp only [generalLiftForwardMapCompSource, Iso.trans_hom,
    PrelaxFunctor.map₂Iso_hom]
  have hmapComp :
      F.map₂ (canonicalSourceHom f A ◁ canonicalSourceTwoCell g η) ≫
          (F.mapComp (canonicalSourceHom f A)
            (canonicalSourceHom g C)).hom =
        (F.mapComp (canonicalSourceHom f A)
            (canonicalSourceHom g B)).hom ≫
          F.map (canonicalSourceHom f A) ◁
            F.map₂ (canonicalSourceTwoCell g η) :=
    F.toOplax.mapComp_naturality_right
      (canonicalSourceHom f A) (canonicalSourceTwoCell g η)
  rw [← Category.assoc, ← F.map₂_comp,
    canonicalSourceCompositionComparison_naturality_right_inv,
    F.map₂_comp, Category.assoc, hmapComp, ← Category.assoc]

/-- The source-side forward composition comparison is natural in its left
retained-coordinate 2-morphism. -/
theorem generalLiftForwardMapCompSource_naturality_left
    (F : Source ⥤ᵖ E)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    F.map₂ (canonicalSourceTwoCell (f ≫ g)
          (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B))) ≫
        (generalLiftForwardMapCompSource F f g C B).hom =
      (generalLiftForwardMapCompSource F f g A B).hom ≫
        F.map₂ (canonicalSourceTwoCell f η) ▷
          F.map (canonicalSourceHom g B) := by
  simp only [generalLiftForwardMapCompSource, Iso.trans_hom,
    PrelaxFunctor.map₂Iso_hom]
  have hmapComp :
      F.map₂ (canonicalSourceTwoCell f η ▷ canonicalSourceHom g B) ≫
          (F.mapComp (canonicalSourceHom f C)
            (canonicalSourceHom g B)).hom =
        (F.mapComp (canonicalSourceHom f A)
            (canonicalSourceHom g B)).hom ≫
          F.map₂ (canonicalSourceTwoCell f η) ▷
            F.map (canonicalSourceHom g B) :=
    F.toOplax.mapComp_naturality_left
      (canonicalSourceTwoCell f η) (canonicalSourceHom g B)
  rw [← Category.assoc, ← F.map₂_comp,
    canonicalSourceCompositionComparison_naturality_left_inv,
    F.map₂_comp, Category.assoc, hmapComp, ← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The source pseudofunctor's normalized forward composition comparisons
satisfy the three-fold associativity law.  The retained-coordinate associator
first changes `(A × B) × C` to `A × (B × C)`; both normalized factorization
routes then agree with the target bicategory associator. -/
theorem generalLiftForwardMapCompSource_associativity
    (F : Source ⥤ᵖ E)
    {X Y Z W : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (A B C : Type) :
    F.map₂ (canonicalSourceTwoCell ((f ≫ g) ≫ h)
          (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftForwardMapCompSource F f (g ≫ h) A (B × C)).hom ≫
        F.map (canonicalSourceHom f A) ◁
          (generalLiftForwardMapCompSource F g h B C).hom =
      (generalLiftForwardMapCompSource F (f ≫ g) h (A × B) C).hom ≫
        (generalLiftForwardMapCompSource F f g A B).hom ▷
          F.map (canonicalSourceHom h C) ≫
        (α_ (F.map (canonicalSourceHom f A))
          (F.map (canonicalSourceHom g B))
          (F.map (canonicalSourceHom h C))).hom := by
  simp only [generalLiftForwardMapCompSource, Iso.trans_hom,
    PrelaxFunctor.map₂Iso_hom, Bicategory.whiskerLeft_comp,
    Bicategory.comp_whiskerRight]
  have hright :
      F.map₂ (canonicalSourceHom f A ◁
            (canonicalSourceCompositionComparison g h B C).symm.hom) ≫
          (F.mapComp (canonicalSourceHom f A)
            (canonicalSourceHom g B ≫ canonicalSourceHom h C)).hom =
        (F.mapComp (canonicalSourceHom f A)
            (canonicalSourceHom (g ≫ h) (B × C))).hom ≫
          F.map (canonicalSourceHom f A) ◁
            F.map₂ (canonicalSourceCompositionComparison g h B C).symm.hom :=
    F.toOplax.mapComp_naturality_right
      (canonicalSourceHom f A)
      (canonicalSourceCompositionComparison g h B C).symm.hom
  have hleft :
      F.map₂ ((canonicalSourceCompositionComparison f g A B).symm.hom ▷
            canonicalSourceHom h C) ≫
          (F.mapComp
            (canonicalSourceHom f A ≫ canonicalSourceHom g B)
            (canonicalSourceHom h C)).hom =
        (F.mapComp (canonicalSourceHom (f ≫ g) (A × B))
            (canonicalSourceHom h C)).hom ≫
          F.map₂ (canonicalSourceCompositionComparison f g A B).symm.hom ▷
            F.map (canonicalSourceHom h C) :=
    F.toOplax.mapComp_naturality_left
      (canonicalSourceCompositionComparison f g A B).symm.hom
      (canonicalSourceHom h C)
  have hassoc :
      F.map₂ (α_ (canonicalSourceHom f A) (canonicalSourceHom g B)
            (canonicalSourceHom h C)).hom ≫
          (F.mapComp (canonicalSourceHom f A)
            (canonicalSourceHom g B ≫ canonicalSourceHom h C)).hom ≫
          F.map (canonicalSourceHom f A) ◁
            (F.mapComp (canonicalSourceHom g B)
              (canonicalSourceHom h C)).hom =
        (F.mapComp
            (canonicalSourceHom f A ≫ canonicalSourceHom g B)
            (canonicalSourceHom h C)).hom ≫
          (F.mapComp (canonicalSourceHom f A)
            (canonicalSourceHom g B)).hom ▷
              F.map (canonicalSourceHom h C) ≫
          (α_ (F.map (canonicalSourceHom f A))
            (F.map (canonicalSourceHom g B))
            (F.map (canonicalSourceHom h C))).hom :=
    F.toOplax.map₂_associator
      (canonicalSourceHom f A) (canonicalSourceHom g B)
      (canonicalSourceHom h C)
  have hsourceMap :
      F.map₂ (canonicalSourceTwoCell ((f ≫ g) ≫ h)
            (MonoidalCategory.associator A B C).hom) ≫
          F.map₂ (canonicalSourceCompositionComparison f (g ≫ h)
            A (B × C)).symm.hom ≫
          F.map₂ (canonicalSourceHom f A ◁
            (canonicalSourceCompositionComparison g h B C).symm.hom) =
        F.map₂ (canonicalSourceCompositionComparison (f ≫ g) h
            (A × B) C).symm.hom ≫
          F.map₂ ((canonicalSourceCompositionComparison f g A B).symm.hom ▷
            canonicalSourceHom h C) ≫
          F.map₂ (α_ (canonicalSourceHom f A)
            (canonicalSourceHom g B) (canonicalSourceHom h C)).hom := by
    simpa only [F.map₂_comp] using congrArg (fun η => F.map₂ η)
      (canonicalSourceCompositionComparison_associativity_inv f g h A B C)
  have hwalking : (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
    Category.assoc f g h
  rw [hwalking] at hsourceMap ⊢
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [← hright]
  calc
    _ =
        F.map₂ (canonicalSourceCompositionComparison (f ≫ g) h
            (A × B) C).symm.hom ≫
          F.map₂ ((canonicalSourceCompositionComparison f g A B).symm.hom ▷
            canonicalSourceHom h C) ≫
          F.map₂ (α_ (canonicalSourceHom f A)
            (canonicalSourceHom g B) (canonicalSourceHom h C)).hom ≫
          (F.mapComp (canonicalSourceHom f A)
            (canonicalSourceHom g B ≫ canonicalSourceHom h C)).hom ≫
          F.map (canonicalSourceHom f A) ◁
            (F.mapComp (canonicalSourceHom g B)
              (canonicalSourceHom h C)).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫
          (F.mapComp (canonicalSourceHom f A)
            (canonicalSourceHom g B ≫ canonicalSourceHom h C)).hom ≫
          F.map (canonicalSourceHom f A) ◁
            (F.mapComp (canonicalSourceHom g B)
              (canonicalSourceHom h C)).hom) hsourceMap
    _ = _ := by
      slice_lhs 3 6 => rw [hassoc]
      slice_lhs 2 3 => rw [hleft]
      simp only [Category.assoc]

/-- The source associator 2-cell is heterogeneously unchanged when the
walking arrow is followed twice by its identity. -/
theorem canonicalSourceTwoCell_rightIdentities_heq
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    HEq (canonicalSourceTwoCell ((f ≫ 𝟙 Y) ≫ 𝟙 Y) η)
      (canonicalSourceTwoCell f η) := by
  have h : (f ≫ 𝟙 Y) ≫ 𝟙 Y = f := Subsingleton.elim _ _
  cases h
  rfl

/-- Mapping preserves the heterogeneous right-identity transport of source
2-cells. -/
theorem generalLiftMap₂SourceTwoCell_rightIdentities_heq
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    HEq (F.map₂ (canonicalSourceTwoCell ((f ≫ 𝟙 Y) ≫ 𝟙 Y) η))
      (F.map₂ (canonicalSourceTwoCell f η)) := by
  have h : (f ≫ 𝟙 Y) ≫ 𝟙 Y = f := Subsingleton.elim _ _
  cases h
  rfl

/-- The normalized compositor is heterogeneously unchanged when its second
walking arrow is itself a composite of two identities. -/
theorem generalLiftForwardMapCompSource_rightIdentities_heq
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    HEq (generalLiftForwardMapCompSource F f (𝟙 Y ≫ 𝟙 Y) A B)
      (generalLiftForwardMapCompSource F f (𝟙 Y) A B) := by
  have h : 𝟙 Y ≫ 𝟙 Y = 𝟙 Y := Subsingleton.elim _ _
  cases h
  rfl

/-- The normalized compositor is heterogeneously unchanged when its first
walking arrow is followed by the identity. -/
theorem generalLiftForwardMapCompSource_firstRightIdentity_heq
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    HEq (generalLiftForwardMapCompSource F (f ≫ 𝟙 Y) (𝟙 Y) A B)
      (generalLiftForwardMapCompSource F f (𝟙 Y) A B) := by
  have h : f ≫ 𝟙 Y = f := Subsingleton.elim _ _
  cases h
  rfl

/-- The source associator 2-cell is heterogeneously unchanged when the
walking arrow is preceded twice by its identity. -/
theorem canonicalSourceTwoCell_leftIdentities_heq
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    HEq (canonicalSourceTwoCell ((𝟙 X ≫ 𝟙 X) ≫ f) η)
      (canonicalSourceTwoCell f η) := by
  have h : (𝟙 X ≫ 𝟙 X) ≫ f = f := Subsingleton.elim _ _
  cases h
  rfl

/-- Mapping preserves the heterogeneous left-identity transport of source
2-cells. -/
theorem generalLiftMap₂SourceTwoCell_leftIdentities_heq
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    HEq (F.map₂ (canonicalSourceTwoCell ((𝟙 X ≫ 𝟙 X) ≫ f) η))
      (F.map₂ (canonicalSourceTwoCell f η)) := by
  have h : (𝟙 X ≫ 𝟙 X) ≫ f = f := Subsingleton.elim _ _
  cases h
  rfl

/-- The normalized compositor is heterogeneously unchanged when its first
walking arrow is a composite of two identities. -/
theorem generalLiftForwardMapCompSource_leftIdentities_heq
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    HEq (generalLiftForwardMapCompSource F (𝟙 X ≫ 𝟙 X) f A B)
      (generalLiftForwardMapCompSource F (𝟙 X) f A B) := by
  have h : 𝟙 X ≫ 𝟙 X = 𝟙 X := Subsingleton.elim _ _
  cases h
  rfl

/-- The normalized compositor is heterogeneously unchanged when its second
walking arrow is preceded by the identity. -/
theorem generalLiftForwardMapCompSource_secondLeftIdentity_heq
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    HEq (generalLiftForwardMapCompSource F (𝟙 X) (𝟙 X ≫ f) A B)
      (generalLiftForwardMapCompSource F (𝟙 X) f A B) := by
  have h : 𝟙 X ≫ f = f := Subsingleton.elim _ _
  cases h
  rfl

/-- The source associator 2-cell is heterogeneously unchanged when the
walking arrow is preceded and followed by identities. -/
theorem canonicalSourceTwoCell_leftRightIdentities_heq
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    HEq (canonicalSourceTwoCell ((𝟙 X ≫ f) ≫ 𝟙 Y) η)
      (canonicalSourceTwoCell f η) := by
  have h : (𝟙 X ≫ f) ≫ 𝟙 Y = f := Subsingleton.elim _ _
  cases h
  rfl

/-- Mapping preserves the heterogeneous two-sided identity transport. -/
theorem generalLiftMap₂SourceTwoCell_leftRightIdentities_heq
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    HEq (F.map₂ (canonicalSourceTwoCell ((𝟙 X ≫ f) ≫ 𝟙 Y) η))
      (F.map₂ (canonicalSourceTwoCell f η)) := by
  have h : (𝟙 X ≫ f) ≫ 𝟙 Y = f := Subsingleton.elim _ _
  cases h
  rfl

/-- The normalized compositor is heterogeneously unchanged when its second
walking arrow is followed by the identity. -/
theorem generalLiftForwardMapCompSource_secondRightIdentity_heq
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    HEq (generalLiftForwardMapCompSource F (𝟙 X) (f ≫ 𝟙 Y) A B)
      (generalLiftForwardMapCompSource F (𝟙 X) f A B) := by
  have h : f ≫ 𝟙 Y = f := Subsingleton.elim _ _
  cases h
  rfl

/-- The normalized compositor is heterogeneously unchanged when its first
walking arrow is preceded by the identity. -/
theorem generalLiftForwardMapCompSource_firstLeftIdentity_heq
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    HEq (generalLiftForwardMapCompSource F (𝟙 X ≫ f) (𝟙 Y) A B)
      (generalLiftForwardMapCompSource F f (𝟙 Y) A B) := by
  have h : 𝟙 X ≫ f = f := Subsingleton.elim _ _
  cases h
  rfl

/-- Associativity of a compositor is preserved when every one-arrow and
composite endpoint is transported through a chosen isomorphism.  This
isolates the bicategorical associator naturality needed by the arbitrary
lift's forward compositor. -/
private theorem transportCompositor_associativity
    {a b c d : E}
    {q₀ p₀ : a ⟶ b} {q₁ p₁ : b ⟶ c} {q₂ p₂ : c ⟶ d}
    {q₀₁ p₀₁ : a ⟶ c} {q₁₂ p₁₂ : b ⟶ d}
    {qL pL qR pR : a ⟶ d}
    (e₀ : q₀ ≅ p₀) (e₁ : q₁ ≅ p₁) (e₂ : q₂ ≅ p₂)
    (e₀₁ : q₀₁ ≅ p₀₁) (e₁₂ : q₁₂ ≅ p₁₂)
    (eL : qL ≅ pL) (eR : qR ≅ pR)
    (c₀₁ : p₀₁ ⟶ p₀ ≫ p₁) (c₁₂ : p₁₂ ⟶ p₁ ≫ p₂)
    (cL : pL ⟶ p₀₁ ≫ p₂) (cR : pR ⟶ p₀ ≫ p₁₂)
    (aP : pL ⟶ pR) (aQ : qL ⟶ qR)
    (ha : aQ ≫ eR.hom = eL.hom ≫ aP)
    (hc : aP ≫ cR ≫ (p₀ ◁ c₁₂) =
      cL ≫ (c₀₁ ▷ p₂) ≫ (α_ p₀ p₁ p₂).hom) :
    aQ ≫
        (eR.hom ≫ cR ≫ (e₀.inv ▷ p₁₂) ≫ (q₀ ◁ e₁₂.inv)) ≫
        (q₀ ◁
          (e₁₂.hom ≫ c₁₂ ≫ (e₁.inv ▷ p₂) ≫ (q₁ ◁ e₂.inv))) =
      (eL.hom ≫ cL ≫ (e₀₁.inv ▷ p₂) ≫ (q₀₁ ◁ e₂.inv)) ≫
        ((e₀₁.hom ≫ c₀₁ ≫ (e₀.inv ▷ p₁) ≫ (q₀ ◁ e₁.inv)) ▷ q₂) ≫
        (α_ q₀ q₁ q₂).hom := by
  simp only [Bicategory.whiskerLeft_comp,
    Bicategory.comp_whiskerRight, Category.assoc]
  rw [← Category.assoc, ha]
  simp
  rw [← whisker_exchange_assoc e₀.inv c₁₂]
  slice_lhs 1 3 => rw [hc]
  simp
  rw [← whisker_exchange_assoc e₀₁.inv e₂.inv]
  simp
  rw [whisker_exchange_assoc c₀₁ e₂.inv]
  rw [← associator_naturality_middle_assoc q₀ e₁.inv p₂]
  rw [← associator_naturality_right q₀ q₁ e₂.inv]
  rw [← associator_naturality_middle q₀ e₁.inv q₂]
  slice_lhs 3 4 => rw [← Bicategory.comp_whiskerRight]
  slice_rhs 4 5 => rw [← Bicategory.comp_whiskerRight]
  slice_lhs 3 4 => rw [← whisker_exchange]
  simp only [Category.assoc]

private theorem comp_naturality_of_squares
    {C : Type u₂} [Category.{v₂} C]
    {X₀ X₁ X₂ Y₀ Y₁ Y₂ : C}
    {p : X₀ ⟶ Y₀}
    {fX : X₀ ⟶ X₁} {fY : Y₀ ⟶ Y₁} {q : X₁ ⟶ Y₁}
    {gX : X₁ ⟶ X₂} {gY : Y₁ ⟶ Y₂} {r : X₂ ⟶ Y₂}
    (hf : p ≫ fY = fX ≫ q)
    (hg : q ≫ gY = gX ≫ r) :
    p ≫ (fY ≫ gY) = (fX ≫ gX) ≫ r := by
  rw [← Category.assoc, hf, Category.assoc, hg, ← Category.assoc]

private theorem whiskerLeft_naturality_of_square
    {C : Type u₂} [Bicategory.{w₂, v₂} C]
    {W X Y : C} (f : W ⟶ X)
    {a b c d : X ⟶ Y}
    {p : a ⟶ b} {q : a ⟶ c} {r : b ⟶ d} {s : c ⟶ d}
    (h : p ≫ r = q ≫ s) :
    (f ◁ p) ≫ (f ◁ r) = (f ◁ q) ≫ (f ◁ s) := by
  simpa only [Bicategory.whiskerLeft_comp] using
    congrArg (fun k => f ◁ k) h

private theorem whiskerRight_naturality_of_square
    {C : Type u₂} [Bicategory.{w₂, v₂} C]
    {W X Y : C} (g : X ⟶ Y)
    {a b c d : W ⟶ X}
    {p : a ⟶ b} {q : a ⟶ c} {r : b ⟶ d} {s : c ⟶ d}
    (h : p ≫ r = q ≫ s) :
    (p ▷ g) ≫ (r ▷ g) = (q ▷ g) ≫ (s ▷ g) := by
  simpa only [Bicategory.comp_whiskerRight] using
    congrArg (fun k => k ▷ g) h

private theorem eqToHom_naturality_of_heq
    {C : Type u₂} [Category.{v₂} C]
    {X Y X' Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) :
    f ≫ eqToHom hY = eqToHom hX ≫ g := by
  subst X'
  subst Y'
  simpa using eq_of_heq h

/-- Normalize the source compositor along the unique right-identity equality
in the walking preorder.  Unlike the raw compositor, this isomorphism starts
at the chosen representative `f` rather than the propositionally equal
composite `f ≫ 𝟙 Y`. -/
noncomputable def generalLiftForwardMapCompSourceRightIdentity
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    F.map (canonicalSourceHom f (A × B)) ≅
      F.map (canonicalSourceHom f A) ≫
        F.map (canonicalSourceHom (𝟙 Y) B) :=
  eqToIso (congrArg
      (fun k => F.map (canonicalSourceHom k (A × B)))
      (Subsingleton.elim f (f ≫ 𝟙 Y))) ≪≫
    generalLiftForwardMapCompSource F f (𝟙 Y) A B

/-- Hom expansion of the right-identity-normalized source compositor. -/
theorem generalLiftForwardMapCompSourceRightIdentity_hom
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftForwardMapCompSourceRightIdentity F f A B).hom =
      eqToHom (congrArg
        (fun k => F.map (canonicalSourceHom k (A × B)))
        (Subsingleton.elim f (f ≫ 𝟙 Y))) ≫
      (generalLiftForwardMapCompSource F f (𝟙 Y) A B).hom := by
  rfl

/-- Right-identity-normalized source composition is natural in its first
retained coordinate. -/
theorem generalLiftForwardMapCompSourceRightIdentity_naturality_left
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A C : Type} (η : A ⟶ C) (B : Type) :
    F.map₂ (canonicalSourceTwoCell f
          (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B))) ≫
        (generalLiftForwardMapCompSourceRightIdentity F f C B).hom =
      (generalLiftForwardMapCompSourceRightIdentity F f A B).hom ≫
        F.map₂ (canonicalSourceTwoCell f η) ▷
          F.map (canonicalSourceHom (𝟙 Y) B) := by
  rw [generalLiftForwardMapCompSourceRightIdentity_hom,
    generalLiftForwardMapCompSourceRightIdentity_hom]
  simp only [Category.assoc]
  simp
  have h := generalLiftForwardMapCompSource_naturality_left F
    f (𝟙 Y) η B
  have hid : f ≫ 𝟙 Y = f := Subsingleton.elim _ _
  rw [hid] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The right-identity-normalized source compositors satisfy the general
three-fold associativity law.  The proof transports the raw pseudofunctor law
across all seven dependent endpoints and uses heterogeneous naturality for
the two nontrivial outer compositor changes. -/
private theorem generalLiftForwardMapCompSourceRightIdentity3_associativity
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (U A B : Type) :
    F.map₂ (canonicalSourceTwoCell f
          (MonoidalCategory.associator U A B).hom) ≫
        (generalLiftForwardMapCompSourceRightIdentity F f
          U (A × B)).hom ≫
        F.map (canonicalSourceHom f U) ◁
          (generalLiftForwardMapCompSourceRightIdentity F
            (𝟙 Y) A B).hom =
      (generalLiftForwardMapCompSourceRightIdentity F f
          (U × A) B).hom ≫
        ((generalLiftForwardMapCompSourceRightIdentity F f
          U A).hom ▷
          F.map (canonicalSourceHom (𝟙 Y) B)) ≫
        (α_ (F.map (canonicalSourceHom f U))
          (F.map (canonicalSourceHom (𝟙 Y) A))
          (F.map (canonicalSourceHom (𝟙 Y) B))).hom := by
  let e₀₁ :
      F.map (canonicalSourceHom f (U × A)) ≅
        F.map (canonicalSourceHom (f ≫ 𝟙 Y) (U × A)) :=
    eqToIso (congrArg
      (fun k => F.map (canonicalSourceHom k (U × A)))
      (Subsingleton.elim f (f ≫ 𝟙 Y)))
  let e₁₂ :
      F.map (canonicalSourceHom (𝟙 Y) (A × B)) ≅
        F.map (canonicalSourceHom (𝟙 Y ≫ 𝟙 Y) (A × B)) :=
    eqToIso (congrArg
      (fun k => F.map (canonicalSourceHom k (A × B)))
      (Subsingleton.elim (𝟙 Y) (𝟙 Y ≫ 𝟙 Y)))
  let hL :
      F.map (canonicalSourceHom f ((U × A) × B)) =
        F.map (canonicalSourceHom ((f ≫ 𝟙 Y) ≫ 𝟙 Y)
          ((U × A) × B)) :=
    congrArg
      (fun k => F.map (canonicalSourceHom k ((U × A) × B)))
      (Subsingleton.elim f ((f ≫ 𝟙 Y) ≫ 𝟙 Y))
  let eL :
      F.map (canonicalSourceHom f ((U × A) × B)) ≅
        F.map (canonicalSourceHom ((f ≫ 𝟙 Y) ≫ 𝟙 Y)
          ((U × A) × B)) :=
    eqToIso hL
  let hR :
      F.map (canonicalSourceHom f (U × (A × B))) =
        F.map (canonicalSourceHom (f ≫ (𝟙 Y ≫ 𝟙 Y))
          (U × (A × B))) :=
    congrArg
      (fun k => F.map (canonicalSourceHom k (U × (A × B))))
      (Subsingleton.elim f (f ≫ (𝟙 Y ≫ 𝟙 Y)))
  let eR :
      F.map (canonicalSourceHom f (U × (A × B))) ≅
        F.map (canonicalSourceHom (f ≫ (𝟙 Y ≫ 𝟙 Y))
          (U × (A × B))) :=
    eqToIso hR
  have ha :
      F.map₂ (canonicalSourceTwoCell f
            (MonoidalCategory.associator U A B).hom) ≫ eR.hom =
        eL.hom ≫
          F.map₂ (canonicalSourceTwoCell ((f ≫ 𝟙 Y) ≫ 𝟙 Y)
            (MonoidalCategory.associator U A B).hom) := by
    exact eqToHom_naturality_of_heq hL hR
      (generalLiftMap₂SourceTwoCell_rightIdentities_heq F f
        (MonoidalCategory.associator U A B).hom).symm
  have htransport := transportCompositor_associativity
    (e₀ := Iso.refl (F.map (canonicalSourceHom f U)))
    (e₁ := Iso.refl (F.map (canonicalSourceHom (𝟙 Y) A)))
    (e₂ := Iso.refl (F.map (canonicalSourceHom (𝟙 Y) B)))
    (e₀₁ := e₀₁) (e₁₂ := e₁₂) (eL := eL) (eR := eR)
    (c₀₁ := (generalLiftForwardMapCompSource F f (𝟙 Y) U A).hom)
    (c₁₂ := (generalLiftForwardMapCompSource F (𝟙 Y) (𝟙 Y) A B).hom)
    (cL := (generalLiftForwardMapCompSource F (f ≫ 𝟙 Y) (𝟙 Y)
      (U × A) B).hom)
    (cR := (generalLiftForwardMapCompSource F f (𝟙 Y ≫ 𝟙 Y)
      U (A × B)).hom)
    (aP := F.map₂ (canonicalSourceTwoCell ((f ≫ 𝟙 Y) ≫ 𝟙 Y)
      (MonoidalCategory.associator U A B).hom))
    (aQ := F.map₂ (canonicalSourceTwoCell f
      (MonoidalCategory.associator U A B).hom))
    (ha := ha)
    (hc := generalLiftForwardMapCompSource_associativity F
      f (𝟙 Y) (𝟙 Y) U A B)
  simp at htransport
  have hcompR : HEq
      (generalLiftForwardMapCompSource F f (𝟙 Y)
        U (A × B)).hom
      (generalLiftForwardMapCompSource F f (𝟙 Y ≫ 𝟙 Y)
        U (A × B)).hom := by
    have h := (generalLiftForwardMapCompSource_rightIdentities_heq
      F f U (A × B)).symm
    cases h
    rfl
  let hXR :
      F.map (canonicalSourceHom (f ≫ 𝟙 Y) (U × (A × B))) =
        F.map (canonicalSourceHom (f ≫ (𝟙 Y ≫ 𝟙 Y))
          (U × (A × B))) :=
    congrArg
      (fun k => F.map (canonicalSourceHom k (U × (A × B))))
      (Subsingleton.elim (f ≫ 𝟙 Y) (f ≫ (𝟙 Y ≫ 𝟙 Y)))
  let hYR :
      F.map (canonicalSourceHom f U) ≫
          F.map (canonicalSourceHom (𝟙 Y) (A × B)) =
        F.map (canonicalSourceHom f U) ≫
          F.map (canonicalSourceHom (𝟙 Y ≫ 𝟙 Y) (A × B)) :=
    congrArg
      (fun k => F.map (canonicalSourceHom f U) ≫
        F.map (canonicalSourceHom k (A × B)))
      (Subsingleton.elim (𝟙 Y) (𝟙 Y ≫ 𝟙 Y))
  have hnatR := eqToHom_naturality_of_heq hXR hYR hcompR
  have hright :
      (generalLiftForwardMapCompSourceRightIdentity F f
          U (A × B)).hom ≫
        (F.map (canonicalSourceHom f U) ◁ e₁₂.hom) =
      eR.hom ≫
        (generalLiftForwardMapCompSource F f (𝟙 Y ≫ 𝟙 Y)
          U (A × B)).hom := by
    rw [generalLiftForwardMapCompSourceRightIdentity_hom]
    simp only [Category.assoc]
    simpa [eR, e₁₂, hR, hXR, hYR] using congrArg
      (fun k =>
        eqToHom (congrArg
          (fun m => F.map (canonicalSourceHom m (U × (A × B))))
          (Subsingleton.elim f (f ≫ 𝟙 Y))) ≫ k)
      hnatR
  have hcompL : HEq
      (generalLiftForwardMapCompSource F f (𝟙 Y)
        (U × A) B).hom
      (generalLiftForwardMapCompSource F (f ≫ 𝟙 Y) (𝟙 Y)
        (U × A) B).hom := by
    have h := (generalLiftForwardMapCompSource_firstRightIdentity_heq
      F f (U × A) B).symm
    cases h
    rfl
  let hXL :
      F.map (canonicalSourceHom (f ≫ 𝟙 Y) ((U × A) × B)) =
        F.map (canonicalSourceHom ((f ≫ 𝟙 Y) ≫ 𝟙 Y)
          ((U × A) × B)) :=
    congrArg
      (fun k => F.map (canonicalSourceHom k ((U × A) × B)))
      (Subsingleton.elim (f ≫ 𝟙 Y) ((f ≫ 𝟙 Y) ≫ 𝟙 Y))
  let hYL :
      F.map (canonicalSourceHom f (U × A)) ≫
          F.map (canonicalSourceHom (𝟙 Y) B) =
        F.map (canonicalSourceHom (f ≫ 𝟙 Y) (U × A)) ≫
          F.map (canonicalSourceHom (𝟙 Y) B) :=
    congrArg
      (fun k => F.map (canonicalSourceHom k (U × A)) ≫
        F.map (canonicalSourceHom (𝟙 Y) B))
      (Subsingleton.elim f (f ≫ 𝟙 Y))
  have hnatL := eqToHom_naturality_of_heq hXL hYL hcompL
  have hleft :
      (generalLiftForwardMapCompSourceRightIdentity F f
          (U × A) B).hom ≫
        (e₀₁.hom ▷ F.map (canonicalSourceHom (𝟙 Y) B)) =
      eL.hom ≫
        (generalLiftForwardMapCompSource F (f ≫ 𝟙 Y) (𝟙 Y)
          (U × A) B).hom := by
    rw [generalLiftForwardMapCompSourceRightIdentity_hom]
    simp only [Category.assoc]
    simpa [eL, e₀₁, hL, hXL, hYL] using congrArg
      (fun k =>
        eqToHom (congrArg
          (fun m => F.map (canonicalSourceHom m ((U × A) × B)))
          (Subsingleton.elim f (f ≫ 𝟙 Y))) ≫ k)
      hnatL
  rw [generalLiftForwardMapCompSourceRightIdentity_hom
      F (𝟙 Y) A B,
    generalLiftForwardMapCompSourceRightIdentity_hom
      F f U A]
  simp only [Bicategory.whiskerLeft_comp,
    Bicategory.comp_whiskerRight, Category.assoc]
  change
    F.map₂ (canonicalSourceTwoCell f
          (MonoidalCategory.associator U A B).hom) ≫
        (generalLiftForwardMapCompSourceRightIdentity F f
          U (A × B)).hom ≫
        (F.map (canonicalSourceHom f U) ◁ e₁₂.hom) ≫
        (F.map (canonicalSourceHom f U) ◁
          (generalLiftForwardMapCompSource F (𝟙 Y) (𝟙 Y) A B).hom) =
      (generalLiftForwardMapCompSourceRightIdentity F f
          (U × A) B).hom ≫
        (e₀₁.hom ▷ F.map (canonicalSourceHom (𝟙 Y) B)) ≫
        ((generalLiftForwardMapCompSource F f (𝟙 Y) U A).hom ▷
          F.map (canonicalSourceHom (𝟙 Y) B)) ≫
        (α_ (F.map (canonicalSourceHom f U))
          (F.map (canonicalSourceHom (𝟙 Y) A))
          (F.map (canonicalSourceHom (𝟙 Y) B))).hom
  slice_lhs 2 3 => rw [hright]
  slice_rhs 1 2 => rw [hleft]
  simpa only [Category.assoc] using htransport

/-- Unit-coordinate specialization retained for the forward-factorization
proofs that use the marked generator's chosen unit representative. -/
theorem generalLiftForwardMapCompSourceRightIdentity_associativity
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    F.map₂ (canonicalSourceTwoCell f
          (MonoidalCategory.associator
            (𝟙 (MonoidalSingleObj.star Type)) A B).hom) ≫
        (generalLiftForwardMapCompSourceRightIdentity F f
          (𝟙 (MonoidalSingleObj.star Type)) (A × B)).hom ≫
        F.map (canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star Type))) ◁
          (generalLiftForwardMapCompSourceRightIdentity F
            (𝟙 Y) A B).hom =
      (generalLiftForwardMapCompSourceRightIdentity F f
          ((𝟙 (MonoidalSingleObj.star Type)) × A) B).hom ≫
        ((generalLiftForwardMapCompSourceRightIdentity F f
          (𝟙 (MonoidalSingleObj.star Type)) A).hom ▷
          F.map (canonicalSourceHom (𝟙 Y) B)) ≫
        (α_ (F.map (canonicalSourceHom f
            (𝟙 (MonoidalSingleObj.star Type))))
          (F.map (canonicalSourceHom (𝟙 Y) A))
          (F.map (canonicalSourceHom (𝟙 Y) B))).hom := by
  exact generalLiftForwardMapCompSourceRightIdentity3_associativity
    F f (𝟙 (MonoidalSingleObj.star Type)) A B

/-- Normalize the source compositor along the unique left-identity equality
in the walking preorder. -/
noncomputable def generalLiftForwardMapCompSourceLeftIdentity
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    F.map (canonicalSourceHom f (A × B)) ≅
      F.map (canonicalSourceHom (𝟙 X) A) ≫
        F.map (canonicalSourceHom f B) :=
  eqToIso (congrArg
      (fun k => F.map (canonicalSourceHom k (A × B)))
      (Subsingleton.elim f (𝟙 X ≫ f))) ≪≫
    generalLiftForwardMapCompSource F (𝟙 X) f A B

/-- Hom expansion of the left-identity-normalized source compositor. -/
theorem generalLiftForwardMapCompSourceLeftIdentity_hom
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftForwardMapCompSourceLeftIdentity F f A B).hom =
      eqToHom (congrArg
        (fun k => F.map (canonicalSourceHom k (A × B)))
        (Subsingleton.elim f (𝟙 X ≫ f))) ≫
      (generalLiftForwardMapCompSource F (𝟙 X) f A B).hom := by
  rfl

/-- Left-identity-normalized source composition is natural in its second
retained coordinate. -/
theorem generalLiftForwardMapCompSourceLeftIdentity_naturality_right
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) {B C : Type} (η : B ⟶ C) :
    F.map₂ (canonicalSourceTwoCell f
          (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η)) ≫
        (generalLiftForwardMapCompSourceLeftIdentity F f A C).hom =
      (generalLiftForwardMapCompSourceLeftIdentity F f A B).hom ≫
        F.map (canonicalSourceHom (𝟙 X) A) ◁
          F.map₂ (canonicalSourceTwoCell f η) := by
  rw [generalLiftForwardMapCompSourceLeftIdentity_hom,
    generalLiftForwardMapCompSourceLeftIdentity_hom]
  simp only [Category.assoc]
  simp
  have h := generalLiftForwardMapCompSource_naturality_right F
    (𝟙 X) f A η
  have hid : 𝟙 X ≫ f = f := Subsingleton.elim _ _
  rw [hid] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The left-identity-normalized source compositors satisfy the symmetric
three-fold associativity law after seven dependent endpoint transports. -/
theorem generalLiftForwardMapCompSourceLeftIdentity_associativity
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    F.map₂ (canonicalSourceTwoCell f
          (MonoidalCategory.associator A B
            (𝟙 (MonoidalSingleObj.star Type))).hom) ≫
        (generalLiftForwardMapCompSourceLeftIdentity F f
          A (B × 𝟙 (MonoidalSingleObj.star Type))).hom ≫
        F.map (canonicalSourceHom (𝟙 X) A) ◁
          (generalLiftForwardMapCompSourceLeftIdentity F
            f B (𝟙 (MonoidalSingleObj.star Type))).hom =
      (generalLiftForwardMapCompSourceLeftIdentity F f
          (A × B) (𝟙 (MonoidalSingleObj.star Type))).hom ≫
        ((generalLiftForwardMapCompSourceLeftIdentity F
          (𝟙 X) A B).hom ▷
          F.map (canonicalSourceHom f
            (𝟙 (MonoidalSingleObj.star Type)))) ≫
        (α_ (F.map (canonicalSourceHom (𝟙 X) A))
          (F.map (canonicalSourceHom (𝟙 X) B))
          (F.map (canonicalSourceHom f
            (𝟙 (MonoidalSingleObj.star Type))))).hom := by
  let U : Type := 𝟙 (MonoidalSingleObj.star Type)
  let e₀₁ :
      F.map (canonicalSourceHom (𝟙 X) (A × B)) ≅
        F.map (canonicalSourceHom (𝟙 X ≫ 𝟙 X) (A × B)) :=
    eqToIso (congrArg
      (fun k => F.map (canonicalSourceHom k (A × B)))
      (Subsingleton.elim (𝟙 X) (𝟙 X ≫ 𝟙 X)))
  let e₁₂ :
      F.map (canonicalSourceHom f (B × U)) ≅
        F.map (canonicalSourceHom (𝟙 X ≫ f) (B × U)) :=
    eqToIso (congrArg
      (fun k => F.map (canonicalSourceHom k (B × U)))
      (Subsingleton.elim f (𝟙 X ≫ f)))
  let hL :
      F.map (canonicalSourceHom f ((A × B) × U)) =
        F.map (canonicalSourceHom ((𝟙 X ≫ 𝟙 X) ≫ f)
          ((A × B) × U)) :=
    congrArg
      (fun k => F.map (canonicalSourceHom k ((A × B) × U)))
      (Subsingleton.elim f ((𝟙 X ≫ 𝟙 X) ≫ f))
  let eL :
      F.map (canonicalSourceHom f ((A × B) × U)) ≅
        F.map (canonicalSourceHom ((𝟙 X ≫ 𝟙 X) ≫ f)
          ((A × B) × U)) :=
    eqToIso hL
  let hR :
      F.map (canonicalSourceHom f (A × (B × U))) =
        F.map (canonicalSourceHom (𝟙 X ≫ (𝟙 X ≫ f))
          (A × (B × U))) :=
    congrArg
      (fun k => F.map (canonicalSourceHom k (A × (B × U))))
      (Subsingleton.elim f (𝟙 X ≫ (𝟙 X ≫ f)))
  let eR :
      F.map (canonicalSourceHom f (A × (B × U))) ≅
        F.map (canonicalSourceHom (𝟙 X ≫ (𝟙 X ≫ f))
          (A × (B × U))) :=
    eqToIso hR
  have ha :
      F.map₂ (canonicalSourceTwoCell f
            (MonoidalCategory.associator A B U).hom) ≫ eR.hom =
        eL.hom ≫
          F.map₂ (canonicalSourceTwoCell ((𝟙 X ≫ 𝟙 X) ≫ f)
            (MonoidalCategory.associator A B U).hom) := by
    exact eqToHom_naturality_of_heq hL hR
      (generalLiftMap₂SourceTwoCell_leftIdentities_heq F f
        (MonoidalCategory.associator A B U).hom).symm
  have htransport := transportCompositor_associativity
    (e₀ := Iso.refl (F.map (canonicalSourceHom (𝟙 X) A)))
    (e₁ := Iso.refl (F.map (canonicalSourceHom (𝟙 X) B)))
    (e₂ := Iso.refl (F.map (canonicalSourceHom f U)))
    (e₀₁ := e₀₁) (e₁₂ := e₁₂) (eL := eL) (eR := eR)
    (c₀₁ := (generalLiftForwardMapCompSource F (𝟙 X) (𝟙 X) A B).hom)
    (c₁₂ := (generalLiftForwardMapCompSource F (𝟙 X) f B U).hom)
    (cL := (generalLiftForwardMapCompSource F (𝟙 X ≫ 𝟙 X) f
      (A × B) U).hom)
    (cR := (generalLiftForwardMapCompSource F (𝟙 X) (𝟙 X ≫ f)
      A (B × U)).hom)
    (aP := F.map₂ (canonicalSourceTwoCell ((𝟙 X ≫ 𝟙 X) ≫ f)
      (MonoidalCategory.associator A B U).hom))
    (aQ := F.map₂ (canonicalSourceTwoCell f
      (MonoidalCategory.associator A B U).hom))
    (ha := ha)
    (hc := generalLiftForwardMapCompSource_associativity F
      (𝟙 X) (𝟙 X) f A B U)
  simp at htransport
  have hcompR : HEq
      (generalLiftForwardMapCompSource F (𝟙 X) f
        A (B × U)).hom
      (generalLiftForwardMapCompSource F (𝟙 X) (𝟙 X ≫ f)
        A (B × U)).hom := by
    have h := (generalLiftForwardMapCompSource_secondLeftIdentity_heq
      F f A (B × U)).symm
    cases h
    rfl
  let hXR :
      F.map (canonicalSourceHom (𝟙 X ≫ f) (A × (B × U))) =
        F.map (canonicalSourceHom (𝟙 X ≫ (𝟙 X ≫ f))
          (A × (B × U))) :=
    congrArg
      (fun k => F.map (canonicalSourceHom k (A × (B × U))))
      (Subsingleton.elim (𝟙 X ≫ f) (𝟙 X ≫ (𝟙 X ≫ f)))
  let hYR :
      F.map (canonicalSourceHom (𝟙 X) A) ≫
          F.map (canonicalSourceHom f (B × U)) =
        F.map (canonicalSourceHom (𝟙 X) A) ≫
          F.map (canonicalSourceHom (𝟙 X ≫ f) (B × U)) :=
    congrArg
      (fun k => F.map (canonicalSourceHom (𝟙 X) A) ≫
        F.map (canonicalSourceHom k (B × U)))
      (Subsingleton.elim f (𝟙 X ≫ f))
  have hnatR := eqToHom_naturality_of_heq hXR hYR hcompR
  have hright :
      (generalLiftForwardMapCompSourceLeftIdentity F f
          A (B × U)).hom ≫
        (F.map (canonicalSourceHom (𝟙 X) A) ◁ e₁₂.hom) =
      eR.hom ≫
        (generalLiftForwardMapCompSource F (𝟙 X) (𝟙 X ≫ f)
          A (B × U)).hom := by
    rw [generalLiftForwardMapCompSourceLeftIdentity_hom]
    simp only [Category.assoc]
    simpa [eR, e₁₂, hR, hXR, hYR] using congrArg
      (fun k =>
        eqToHom (congrArg
          (fun m => F.map (canonicalSourceHom m (A × (B × U))))
          (Subsingleton.elim f (𝟙 X ≫ f))) ≫ k)
      hnatR
  have hcompL : HEq
      (generalLiftForwardMapCompSource F (𝟙 X) f
        (A × B) U).hom
      (generalLiftForwardMapCompSource F (𝟙 X ≫ 𝟙 X) f
        (A × B) U).hom := by
    have h := (generalLiftForwardMapCompSource_leftIdentities_heq
      F f (A × B) U).symm
    cases h
    rfl
  let hXL :
      F.map (canonicalSourceHom (𝟙 X ≫ f) ((A × B) × U)) =
        F.map (canonicalSourceHom ((𝟙 X ≫ 𝟙 X) ≫ f)
          ((A × B) × U)) :=
    congrArg
      (fun k => F.map (canonicalSourceHom k ((A × B) × U)))
      (Subsingleton.elim (𝟙 X ≫ f) ((𝟙 X ≫ 𝟙 X) ≫ f))
  let hYL :
      F.map (canonicalSourceHom (𝟙 X) (A × B)) ≫
          F.map (canonicalSourceHom f U) =
        F.map (canonicalSourceHom (𝟙 X ≫ 𝟙 X) (A × B)) ≫
          F.map (canonicalSourceHom f U) :=
    congrArg
      (fun k => F.map (canonicalSourceHom k (A × B)) ≫
        F.map (canonicalSourceHom f U))
      (Subsingleton.elim (𝟙 X) (𝟙 X ≫ 𝟙 X))
  have hnatL := eqToHom_naturality_of_heq hXL hYL hcompL
  have hleft :
      (generalLiftForwardMapCompSourceLeftIdentity F f
          (A × B) U).hom ≫
        (e₀₁.hom ▷ F.map (canonicalSourceHom f U)) =
      eL.hom ≫
        (generalLiftForwardMapCompSource F (𝟙 X ≫ 𝟙 X) f
          (A × B) U).hom := by
    rw [generalLiftForwardMapCompSourceLeftIdentity_hom]
    simp only [Category.assoc]
    simpa [eL, e₀₁, hL, hXL, hYL] using congrArg
      (fun k =>
        eqToHom (congrArg
          (fun m => F.map (canonicalSourceHom m ((A × B) × U)))
          (Subsingleton.elim f (𝟙 X ≫ f))) ≫ k)
      hnatL
  rw [generalLiftForwardMapCompSourceLeftIdentity_hom
      F f B U,
    generalLiftForwardMapCompSourceLeftIdentity_hom
      F (𝟙 X) A B]
  simp only [Bicategory.whiskerLeft_comp,
    Bicategory.comp_whiskerRight, Category.assoc]
  change
    F.map₂ (canonicalSourceTwoCell f
          (MonoidalCategory.associator A B U).hom) ≫
        (generalLiftForwardMapCompSourceLeftIdentity F f
          A (B × U)).hom ≫
        (F.map (canonicalSourceHom (𝟙 X) A) ◁ e₁₂.hom) ≫
        (F.map (canonicalSourceHom (𝟙 X) A) ◁
          (generalLiftForwardMapCompSource F (𝟙 X) f B U).hom) =
      (generalLiftForwardMapCompSourceLeftIdentity F f
          (A × B) U).hom ≫
        (e₀₁.hom ▷ F.map (canonicalSourceHom f U)) ≫
        ((generalLiftForwardMapCompSource F (𝟙 X) (𝟙 X) A B).hom ▷
          F.map (canonicalSourceHom f U)) ≫
        (α_ (F.map (canonicalSourceHom (𝟙 X) A))
          (F.map (canonicalSourceHom (𝟙 X) B))
          (F.map (canonicalSourceHom f U))).hom
  slice_lhs 2 3 => rw [hright]
  slice_rhs 1 2 => rw [hleft]
  simpa only [Category.assoc] using htransport

set_option backward.isDefEq.respectTransparency false in
/-- Mixed left/right identity normalization satisfies associativity.  This is
the exact source square needed to compare the two canonical forward
factorizations before proving sliding multiplicativity. -/
theorem generalLiftForwardMapCompSourceMixedIdentity_associativity
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    F.map₂ (canonicalSourceTwoCell f
          (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftForwardMapCompSourceLeftIdentity F f
          A (B × C)).hom ≫
        F.map (canonicalSourceHom (𝟙 X) A) ◁
          (generalLiftForwardMapCompSourceRightIdentity F f B C).hom =
      (generalLiftForwardMapCompSourceRightIdentity F f
          (A × B) C).hom ≫
        ((generalLiftForwardMapCompSourceLeftIdentity F f A B).hom ▷
          F.map (canonicalSourceHom (𝟙 Y) C)) ≫
        (α_ (F.map (canonicalSourceHom (𝟙 X) A))
          (F.map (canonicalSourceHom f B))
          (F.map (canonicalSourceHom (𝟙 Y) C))).hom := by
  let e₀₁ :
      F.map (canonicalSourceHom f (A × B)) ≅
        F.map (canonicalSourceHom (𝟙 X ≫ f) (A × B)) :=
    eqToIso (congrArg
      (fun k => F.map (canonicalSourceHom k (A × B)))
      (Subsingleton.elim f (𝟙 X ≫ f)))
  let e₁₂ :
      F.map (canonicalSourceHom f (B × C)) ≅
        F.map (canonicalSourceHom (f ≫ 𝟙 Y) (B × C)) :=
    eqToIso (congrArg
      (fun k => F.map (canonicalSourceHom k (B × C)))
      (Subsingleton.elim f (f ≫ 𝟙 Y)))
  let hL :
      F.map (canonicalSourceHom f ((A × B) × C)) =
        F.map (canonicalSourceHom ((𝟙 X ≫ f) ≫ 𝟙 Y)
          ((A × B) × C)) :=
    congrArg
      (fun k => F.map (canonicalSourceHom k ((A × B) × C)))
      (Subsingleton.elim f ((𝟙 X ≫ f) ≫ 𝟙 Y))
  let eL :
      F.map (canonicalSourceHom f ((A × B) × C)) ≅
        F.map (canonicalSourceHom ((𝟙 X ≫ f) ≫ 𝟙 Y)
          ((A × B) × C)) :=
    eqToIso hL
  let hR :
      F.map (canonicalSourceHom f (A × (B × C))) =
        F.map (canonicalSourceHom (𝟙 X ≫ (f ≫ 𝟙 Y))
          (A × (B × C))) :=
    congrArg
      (fun k => F.map (canonicalSourceHom k (A × (B × C))))
      (Subsingleton.elim f (𝟙 X ≫ (f ≫ 𝟙 Y)))
  let eR :
      F.map (canonicalSourceHom f (A × (B × C))) ≅
        F.map (canonicalSourceHom (𝟙 X ≫ (f ≫ 𝟙 Y))
          (A × (B × C))) :=
    eqToIso hR
  have ha :
      F.map₂ (canonicalSourceTwoCell f
            (MonoidalCategory.associator A B C).hom) ≫ eR.hom =
        eL.hom ≫
          F.map₂ (canonicalSourceTwoCell ((𝟙 X ≫ f) ≫ 𝟙 Y)
            (MonoidalCategory.associator A B C).hom) := by
    exact eqToHom_naturality_of_heq hL hR
      (generalLiftMap₂SourceTwoCell_leftRightIdentities_heq F f
        (MonoidalCategory.associator A B C).hom).symm
  have htransport := transportCompositor_associativity
    (e₀ := Iso.refl (F.map (canonicalSourceHom (𝟙 X) A)))
    (e₁ := Iso.refl (F.map (canonicalSourceHom f B)))
    (e₂ := Iso.refl (F.map (canonicalSourceHom (𝟙 Y) C)))
    (e₀₁ := e₀₁) (e₁₂ := e₁₂) (eL := eL) (eR := eR)
    (c₀₁ := (generalLiftForwardMapCompSource F (𝟙 X) f A B).hom)
    (c₁₂ := (generalLiftForwardMapCompSource F f (𝟙 Y) B C).hom)
    (cL := (generalLiftForwardMapCompSource F (𝟙 X ≫ f) (𝟙 Y)
      (A × B) C).hom)
    (cR := (generalLiftForwardMapCompSource F (𝟙 X) (f ≫ 𝟙 Y)
      A (B × C)).hom)
    (aP := F.map₂ (canonicalSourceTwoCell ((𝟙 X ≫ f) ≫ 𝟙 Y)
      (MonoidalCategory.associator A B C).hom))
    (aQ := F.map₂ (canonicalSourceTwoCell f
      (MonoidalCategory.associator A B C).hom))
    (ha := ha)
    (hc := generalLiftForwardMapCompSource_associativity F
      (𝟙 X) f (𝟙 Y) A B C)
  simp at htransport
  have hcompR : HEq
      (generalLiftForwardMapCompSource F (𝟙 X) f
        A (B × C)).hom
      (generalLiftForwardMapCompSource F (𝟙 X) (f ≫ 𝟙 Y)
        A (B × C)).hom := by
    have h := (generalLiftForwardMapCompSource_secondRightIdentity_heq
      F f A (B × C)).symm
    cases h
    rfl
  let hXR :
      F.map (canonicalSourceHom (𝟙 X ≫ f) (A × (B × C))) =
        F.map (canonicalSourceHom (𝟙 X ≫ (f ≫ 𝟙 Y))
          (A × (B × C))) :=
    congrArg
      (fun k => F.map (canonicalSourceHom k (A × (B × C))))
      (Subsingleton.elim (𝟙 X ≫ f) (𝟙 X ≫ (f ≫ 𝟙 Y)))
  let hYR :
      F.map (canonicalSourceHom (𝟙 X) A) ≫
          F.map (canonicalSourceHom f (B × C)) =
        F.map (canonicalSourceHom (𝟙 X) A) ≫
          F.map (canonicalSourceHom (f ≫ 𝟙 Y) (B × C)) :=
    congrArg
      (fun k => F.map (canonicalSourceHom (𝟙 X) A) ≫
        F.map (canonicalSourceHom k (B × C)))
      (Subsingleton.elim f (f ≫ 𝟙 Y))
  have hnatR := eqToHom_naturality_of_heq hXR hYR hcompR
  have hright :
      (generalLiftForwardMapCompSourceLeftIdentity F f
          A (B × C)).hom ≫
        (F.map (canonicalSourceHom (𝟙 X) A) ◁ e₁₂.hom) =
      eR.hom ≫
        (generalLiftForwardMapCompSource F (𝟙 X) (f ≫ 𝟙 Y)
          A (B × C)).hom := by
    rw [generalLiftForwardMapCompSourceLeftIdentity_hom]
    simp only [Category.assoc]
    simpa [eR, e₁₂, hR, hXR, hYR] using congrArg
      (fun k =>
        eqToHom (congrArg
          (fun m => F.map (canonicalSourceHom m (A × (B × C))))
          (Subsingleton.elim f (𝟙 X ≫ f))) ≫ k)
      hnatR
  have hcompL : HEq
      (generalLiftForwardMapCompSource F f (𝟙 Y)
        (A × B) C).hom
      (generalLiftForwardMapCompSource F (𝟙 X ≫ f) (𝟙 Y)
        (A × B) C).hom := by
    have h := (generalLiftForwardMapCompSource_firstLeftIdentity_heq
      F f (A × B) C).symm
    cases h
    rfl
  let hXL :
      F.map (canonicalSourceHom (f ≫ 𝟙 Y) ((A × B) × C)) =
        F.map (canonicalSourceHom ((𝟙 X ≫ f) ≫ 𝟙 Y)
          ((A × B) × C)) :=
    congrArg
      (fun k => F.map (canonicalSourceHom k ((A × B) × C)))
      (Subsingleton.elim (f ≫ 𝟙 Y) ((𝟙 X ≫ f) ≫ 𝟙 Y))
  let hYL :
      F.map (canonicalSourceHom f (A × B)) ≫
          F.map (canonicalSourceHom (𝟙 Y) C) =
        F.map (canonicalSourceHom (𝟙 X ≫ f) (A × B)) ≫
          F.map (canonicalSourceHom (𝟙 Y) C) :=
    congrArg
      (fun k => F.map (canonicalSourceHom k (A × B)) ≫
        F.map (canonicalSourceHom (𝟙 Y) C))
      (Subsingleton.elim f (𝟙 X ≫ f))
  have hnatL := eqToHom_naturality_of_heq hXL hYL hcompL
  have hleft :
      (generalLiftForwardMapCompSourceRightIdentity F f
          (A × B) C).hom ≫
        (e₀₁.hom ▷ F.map (canonicalSourceHom (𝟙 Y) C)) =
      eL.hom ≫
        (generalLiftForwardMapCompSource F (𝟙 X ≫ f) (𝟙 Y)
          (A × B) C).hom := by
    rw [generalLiftForwardMapCompSourceRightIdentity_hom]
    simp only [Category.assoc]
    simpa [eL, e₀₁, hL, hXL, hYL] using congrArg
      (fun k =>
        eqToHom (congrArg
          (fun m => F.map (canonicalSourceHom m ((A × B) × C)))
          (Subsingleton.elim f (f ≫ 𝟙 Y))) ≫ k)
      hnatL
  rw [generalLiftForwardMapCompSourceRightIdentity_hom F f B C,
    generalLiftForwardMapCompSourceLeftIdentity_hom F f A B]
  simp only [Bicategory.whiskerLeft_comp,
    Bicategory.comp_whiskerRight, Category.assoc]
  change
    F.map₂ (canonicalSourceTwoCell f
          (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftForwardMapCompSourceLeftIdentity F f
          A (B × C)).hom ≫
        (F.map (canonicalSourceHom (𝟙 X) A) ◁ e₁₂.hom) ≫
        (F.map (canonicalSourceHom (𝟙 X) A) ◁
          (generalLiftForwardMapCompSource F f (𝟙 Y) B C).hom) =
      (generalLiftForwardMapCompSourceRightIdentity F f
          (A × B) C).hom ≫
        (e₀₁.hom ▷ F.map (canonicalSourceHom (𝟙 Y) C)) ≫
        ((generalLiftForwardMapCompSource F (𝟙 X) f A B).hom ▷
          F.map (canonicalSourceHom (𝟙 Y) C)) ≫
        (α_ (F.map (canonicalSourceHom (𝟙 X) A))
          (F.map (canonicalSourceHom f B))
          (F.map (canonicalSourceHom (𝟙 Y) C))).hom
  slice_lhs 2 3 => rw [hright]
  slice_rhs 1 2 => rw [hleft]
  simpa only [Category.assoc] using htransport

/-- At a walking identity, left- and right-identity normalization choose the
same compositor. -/
theorem generalLiftForwardMapCompSource_identityNormalizations_eq
    (F : Source ⥤ᵖ E)
    (X : Ript.Examples.WalkingLocalization.Arrow)
    (A B : Type) :
    generalLiftForwardMapCompSourceLeftIdentity F (𝟙 X) A B =
      generalLiftForwardMapCompSourceRightIdentity F (𝟙 X) A B := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The normalized compositor for three retained factors satisfies the full
associativity law. -/
theorem generalLiftForwardMapCompSourceIdentity_associativity
    (F : Source ⥤ᵖ E)
    (X : Ript.Examples.WalkingLocalization.Arrow)
    (A B C : Type) :
    F.map₂ (canonicalSourceTwoCell (𝟙 X)
          (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X)
          A (B × C)).hom ≫
        F.map (canonicalSourceHom (𝟙 X) A) ◁
          (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X) B C).hom =
      (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X)
          (A × B) C).hom ≫
        ((generalLiftForwardMapCompSourceRightIdentity F (𝟙 X) A B).hom ▷
          F.map (canonicalSourceHom (𝟙 X) C)) ≫
        (α_ (F.map (canonicalSourceHom (𝟙 X) A))
          (F.map (canonicalSourceHom (𝟙 X) B))
          (F.map (canonicalSourceHom (𝟙 X) C))).hom := by
  simpa [generalLiftForwardMapCompSource_identityNormalizations_eq] using
    generalLiftForwardMapCompSourceMixedIdentity_associativity
      F (𝟙 X) A B C

private theorem iso_inv_naturality_of_square
    {C : Type u₂} [Category.{v₂} C]
    {X₀ X₁ Y₀ Y₁ : C} (e₀ : X₀ ≅ Y₀) (e₁ : X₁ ≅ Y₁)
    {p : X₀ ⟶ X₁} {q : Y₀ ⟶ Y₁}
    (h : p ≫ e₁.hom = e₀.hom ≫ q) :
    q ≫ e₁.inv = e₀.inv ≫ p := by
  rw [← cancel_epi e₀.hom]
  simp only [Iso.hom_inv_id_assoc]
  calc
    e₀.hom ≫ q ≫ e₁.inv = (e₀.hom ≫ q) ≫ e₁.inv :=
      (Category.assoc _ _ _).symm
    _ = (p ≫ e₁.hom) ≫ e₁.inv := by rw [h]
    _ = p := by simp

private noncomputable def equivalenceCounitInsertion
    {C : Type u₂} [Bicategory.{w₂, v₂} C]
    {a b : C} (e : a ≌ b) (T : b ⟶ b) :
    T ≅ e.inv ≫ (e.hom ≫ T) :=
  (leftUnitor T).symm ≪≫
    whiskerRightIso e.counit.symm T ≪≫
    α_ e.inv e.hom T

private theorem equivalenceCounitInsertion_hom
    {C : Type u₂} [Bicategory.{w₂, v₂} C]
    {a b : C} (e : a ≌ b) (T : b ⟶ b) :
    (equivalenceCounitInsertion e T).hom =
      (leftUnitor T).inv ≫ (e.counit.inv ▷ T) ≫
        (associator e.inv e.hom T).hom := by
  rfl

private theorem equivalenceCounitInsertion_naturality
    {C : Type u₂} [Bicategory.{w₂, v₂} C]
    {a b : C} (e : a ≌ b) {T S : b ⟶ b} (η : T ⟶ S) :
    η ≫ (equivalenceCounitInsertion e S).hom =
      (equivalenceCounitInsertion e T).hom ≫
        (e.inv ◁ (e.hom ◁ η)) := by
  rw [equivalenceCounitInsertion_hom,
    equivalenceCounitInsertion_hom]
  exact comp_naturality_of_squares
    (leftUnitor_inv_naturality η)
    (comp_naturality_of_squares
      (whisker_exchange e.counit.inv η)
      (associator_naturality_right e.inv e.hom η))

set_option backward.isDefEq.respectTransparency false in
/-- Counit insertion on a composite is the right whiskering of counit
insertion on its first factor, up to the canonical reassociation. -/
@[reassoc]
private theorem equivalenceCounitInsertion_rightWhisker
    {a b : E} (e : a ≌ b) (T S : b ⟶ b) :
    (equivalenceCounitInsertion e (T ≫ S)).hom ≫
        (α_ e.inv e.hom (T ≫ S)).inv ≫
        (α_ (e.inv ≫ e.hom) T S).inv ≫
        ((α_ e.inv e.hom T).hom ▷ S) =
      ((equivalenceCounitInsertion e T).hom ▷ S) := by
  rw [equivalenceCounitInsertion_hom,
    equivalenceCounitInsertion_hom]
  bicategory

set_option backward.isDefEq.respectTransparency false in
/-- The counit-insertion, forward-sliding, and forward-factorization pasting
is compatible with adding an arbitrary retained tail on the right. -/
private theorem inverseForward_rightWhisker
    {a b : E} (e : a ≌ b)
    {yA yB yBC yC : b ⟶ b} {xA : a ⟶ a} {zB : a ⟶ b}
    (sA : e.hom ≫ yA ⟶ xA ≫ e.hom)
    (qB : e.hom ≫ yB ⟶ zB) (k : yBC ⟶ yB ≫ yC) :
    (equivalenceCounitInsertion e (yA ≫ yBC)).hom ≫
        (e.inv ◁ (α_ e.hom yA yBC).inv) ≫
        (e.inv ◁ (sA ▷ yBC)) ≫
        (e.inv ◁ (α_ xA e.hom yBC).hom) ≫
        (α_ e.inv xA (e.hom ≫ yBC)).inv ≫
        ((e.inv ≫ xA) ◁ (e.hom ◁ k)) ≫
        ((e.inv ≫ xA) ◁ (α_ e.hom yB yC).inv) ≫
        ((e.inv ≫ xA) ◁ (qB ▷ yC)) =
      (yA ◁ k) ≫
        (α_ yA yB yC).inv ≫
        ((equivalenceCounitInsertion e (yA ≫ yB)).hom ▷ yC) ≫
        ((e.inv ◁ (α_ e.hom yA yB).inv) ▷ yC) ≫
        ((e.inv ◁ (sA ▷ yB)) ▷ yC) ≫
        ((e.inv ◁ (α_ xA e.hom yB).hom) ▷ yC) ≫
        ((α_ e.inv xA (e.hom ≫ yB)).inv ▷ yC) ≫
        (((e.inv ≫ xA) ◁ qB) ▷ yC) ≫
        (α_ (e.inv ≫ xA) zB yC).hom := by
  let η := (yA ◁ k) ≫ (α_ yA yB yC).inv
  let bridge :=
    (α_ e.inv e.hom ((yA ≫ yB) ≫ yC)).symm ≪≫
      (α_ (e.inv ≫ e.hom) (yA ≫ yB) yC).symm ≪≫
      whiskerRightIso (α_ e.inv e.hom (yA ≫ yB)) yC
  let postTail :=
    ((e.inv ◁ (α_ e.hom yA yB).inv) ▷ yC) ≫
      ((e.inv ◁ (sA ▷ yB)) ▷ yC) ≫
      ((e.inv ◁ (α_ xA e.hom yB).hom) ▷ yC) ≫
      ((α_ e.inv xA (e.hom ≫ yB)).inv ▷ yC) ≫
      (((e.inv ≫ xA) ◁ qB) ▷ yC) ≫
      (α_ (e.inv ≫ xA) zB yC).hom
  let post := bridge.hom ≫ postTail
  have hnat := equivalenceCounitInsertion_naturality e η
  have hnatPost := congrArg (fun u => u ≫ post) hnat
  dsimp [η, post, postTail, bridge] at hnatPost
  convert hnatPost.symm using 1
  · simp only [Category.assoc]
    rw [cancel_epi (equivalenceCounitInsertion e (yA ≫ yBC)).hom]
    let pre := e.inv ◁ (α_ e.hom yA yBC).inv
    let after :=
      (e.inv ◁ (α_ xA e.hom (yB ≫ yC)).hom) ≫
        (α_ e.inv xA (e.hom ≫ (yB ≫ yC))).inv ≫
        ((e.inv ≫ xA) ◁ (α_ e.hom yB yC).inv) ≫
        ((e.inv ≫ xA) ◁ (qB ▷ yC))
    have hex := whisker_exchange sA k
    have hexW := congrArg (fun u => e.inv ◁ u) hex
    have hexContext := congrArg
      (fun u => pre ≫ u ≫ after) hexW
    dsimp [pre, after] at hexContext
    convert hexContext.symm using 1
    · bicategory
    · simp only [whiskerRightIso_hom]
      bicategory
  · have hright :=
      equivalenceCounitInsertion_rightWhisker e (yA ≫ yB) yC
    have hrightContext := congrArg
      (fun u => η ≫ u ≫ postTail) hright.symm
    dsimp [η, postTail, bridge] at hrightContext
    simpa only [whiskerRightIso_hom, Category.assoc] using hrightContext

set_option backward.isDefEq.respectTransparency false in
/-- The right-whiskering law remains valid when the retained tail is finally
collapsed through a second forward factorization. -/
private theorem inverseForward_rightWhisker_factorization
    {a b : E} (e : a ≌ b)
    {yA yB yBC yC : b ⟶ b} {xA xB : a ⟶ a}
    {zC : a ⟶ b}
    (sA : e.hom ≫ yA ⟶ xA ≫ e.hom)
    (sB : e.hom ≫ yB ⟶ xB ≫ e.hom)
    (qC : e.hom ≫ yC ⟶ zC) (k : yBC ⟶ yB ≫ yC) :
    (equivalenceCounitInsertion e (yA ≫ yBC)).hom ≫
        (e.inv ◁ (α_ e.hom yA yBC).inv) ≫
        (e.inv ◁ (sA ▷ yBC)) ≫
        (e.inv ◁ (α_ xA e.hom yBC).hom) ≫
        (α_ e.inv xA (e.hom ≫ yBC)).inv ≫
        ((e.inv ≫ xA) ◁ (e.hom ◁ k)) ≫
        ((e.inv ≫ xA) ◁ (α_ e.hom yB yC).inv) ≫
        ((e.inv ≫ xA) ◁ (sB ▷ yC)) ≫
        ((e.inv ≫ xA) ◁ (α_ xB e.hom yC).hom) ≫
        ((e.inv ≫ xA) ◁ (xB ◁ qC)) =
      (yA ◁ k) ≫
        (α_ yA yB yC).inv ≫
        ((equivalenceCounitInsertion e (yA ≫ yB)).hom ▷ yC) ≫
        ((e.inv ◁ (α_ e.hom yA yB).inv) ▷ yC) ≫
        ((e.inv ◁ (sA ▷ yB)) ▷ yC) ≫
        ((e.inv ◁ (α_ xA e.hom yB).hom) ▷ yC) ≫
        ((α_ e.inv xA (e.hom ≫ yB)).inv ▷ yC) ≫
        (((e.inv ≫ xA) ◁ sB) ▷ yC) ≫
        (α_ (e.inv ≫ xA) (xB ≫ e.hom) yC).hom ≫
        ((e.inv ≫ xA) ◁ (α_ xB e.hom yC).hom) ≫
        ((e.inv ≫ xA) ◁ (xB ◁ qC)) := by
  have h := inverseForward_rightWhisker e sA sB k
  let post :=
    ((e.inv ≫ xA) ◁ (α_ xB e.hom yC).hom) ≫
      ((e.inv ≫ xA) ◁ (xB ◁ qC))
  have hpost := congrArg (fun u => u ≫ post) h
  dsimp [post] at hpost
  convert hpost using 1
  · bicategory
  · bicategory

private noncomputable def equivalenceUnitInsertion
    {C : Type u₂} [Bicategory.{w₂, v₂} C]
    {a b : C} (e : a ≌ b) (T : a ⟶ a) :
    T ≅ e.hom ≫ (e.inv ≫ T) :=
  (leftUnitor T).symm ≪≫
    whiskerRightIso e.unit T ≪≫
    α_ e.hom e.inv T

private theorem equivalenceUnitInsertion_hom
    {C : Type u₂} [Bicategory.{w₂, v₂} C]
    {a b : C} (e : a ≌ b) (T : a ⟶ a) :
    (equivalenceUnitInsertion e T).hom =
      (leftUnitor T).inv ≫ (e.unit.hom ▷ T) ≫
        (associator e.hom e.inv T).hom := by
  rfl

private theorem equivalenceUnitInsertion_inv
    {C : Type u₂} [Bicategory.{w₂, v₂} C]
    {a b : C} (e : a ≌ b) (T : a ⟶ a) :
    (equivalenceUnitInsertion e T).inv =
      (associator e.hom e.inv T).inv ≫
        (e.unit.inv ▷ T) ≫
        (leftUnitor T).hom := by
  simp [equivalenceUnitInsertion]

private theorem equivalenceUnitInsertion_naturality
    {C : Type u₂} [Bicategory.{w₂, v₂} C]
    {a b : C} (e : a ≌ b) {T S : a ⟶ a} (η : T ⟶ S) :
    η ≫ (equivalenceUnitInsertion e S).hom =
      (equivalenceUnitInsertion e T).hom ≫
        (e.hom ◁ (e.inv ◁ η)) := by
  rw [equivalenceUnitInsertion_hom,
    equivalenceUnitInsertion_hom]
  exact comp_naturality_of_squares
    (leftUnitor_inv_naturality η)
    (comp_naturality_of_squares
      (whisker_exchange e.unit.hom η)
      (associator_naturality_right e.hom e.inv η))

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of unit insertion after a fixed left factor and a comparison
out of that factor followed by the chosen equivalence. -/
private theorem equivalenceUnitInsertion_whisker_naturality
    {C : Type u₂} [Bicategory.{w₂, v₂} C]
    {a b : C} (e : a ≌ b)
    {x : a ⟶ a} {y : a ⟶ b}
    (p : x ≫ e.hom ⟶ y)
    {T S : a ⟶ a} (η : T ⟶ S) :
    (x ◁ η) ≫
        (x ◁ (equivalenceUnitInsertion e S).hom) ≫
        (α_ x e.hom (e.inv ≫ S)).inv ≫
        (p ▷ (e.inv ≫ S)) =
      (x ◁ (equivalenceUnitInsertion e T).hom) ≫
        (α_ x e.hom (e.inv ≫ T)).inv ≫
        (p ▷ (e.inv ≫ T)) ≫
        (y ◁ (e.inv ◁ η)) := by
  simpa only [Category.assoc] using
    comp_naturality_of_squares
      (whiskerLeft_naturality_of_square x
        (equivalenceUnitInsertion_naturality e η))
      (comp_naturality_of_squares
        (associator_inv_naturality_right x e.hom (e.inv ◁ η))
        (whisker_exchange p (e.inv ◁ η)))

set_option backward.isDefEq.respectTransparency false in
/-- Unit insertion is compatible with passing a left-adjoint square through
its right-adjoint mate, including an arbitrary retained tail. -/
private theorem equivalenceUnitInsertion_mate_vcomp
    {C : Type u₂} [Bicategory.{w₂, v₂} C]
    {a b : C} (e : a ≌ b)
    {x z : a ⟶ a} {y : b ⟶ b}
    (α : x ≫ e.hom ⟶ e.hom ≫ y) :
    (equivalenceUnitInsertion e (x ≫ z)).hom ≫
        (e.hom ◁ (α_ e.inv x z).inv) ≫
        (e.hom ◁
          (mateEquiv e.toAdjunction e.toAdjunction α ▷ z)) ≫
        (e.hom ◁ (α_ y e.inv z).hom) =
      (x ◁ (equivalenceUnitInsertion e z).hom) ≫
        (α_ x e.hom (e.inv ≫ z)).inv ≫
        (α ▷ (e.inv ≫ z)) ≫
        (α_ e.hom y (e.inv ≫ z)).hom := by
  have h := (mateEquiv_eq_iff e.toAdjunction e.toAdjunction α
    (mateEquiv e.toAdjunction e.toAdjunction α)).mp rfl
  rw [Adjunction.homEquiv₁_symm_apply,
    Adjunction.homEquiv₂_apply] at h
  let post :=
    (α_ e.hom (y ≫ e.inv) z).hom ≫
      (e.hom ◁ (α_ y e.inv z).hom)
  have hz := congrArg (fun k => (k ▷ z) ≫ post) h
  dsimp [post] at hz
  rw [equivalenceUnitInsertion_hom, equivalenceUnitInsertion_hom]
  convert hz using 1
  · bicategory
  · bicategory

set_option backward.isDefEq.respectTransparency false in
/-- Reassociate a cancellation unit past a comparison that splits the
retained prefix. -/
private theorem forwardCancellation_prefix
    {a b : E}
    {xAB x bPart cPart : a ⟶ a}
    {e : a ⟶ b} {t : b ⟶ a}
    (c : xAB ⟶ x ≫ bPart) (u : cPart ⟶ e ≫ t) :
    (xAB ◁ u) ≫
        (α_ xAB e t).inv ≫
        ((c ▷ e) ▷ t) ≫
        ((α_ x bPart e).hom ▷ t) =
      (c ▷ cPart) ≫
        (α_ x bPart cPart).hom ≫
        (x ◁ (bPart ◁ u)) ≫
        (x ◁ (α_ bPart e t).inv) ≫
        (α_ x (bPart ≫ e) t).inv := by
  calc
    _ = (xAB ◁ u) ≫ (c ▷ (e ≫ t)) ≫
        (α_ (x ≫ bPart) e t).inv ≫
        ((α_ x bPart e).hom ▷ t) := by bicategory
    _ = (c ▷ cPart) ≫ ((x ≫ bPart) ◁ u) ≫
        (α_ (x ≫ bPart) e t).inv ≫
        ((α_ x bPart e).hom ▷ t) := by
      have hex := congrArg
        (fun k => k ≫ (α_ (x ≫ bPart) e t).inv ≫
          ((α_ x bPart e).hom ▷ t))
        (whisker_exchange c u)
      simpa only [Category.assoc] using hex
    _ = _ := by bicategory

set_option backward.isDefEq.respectTransparency false in
/-- Reassociate the forward-sliding and fixed-factorization suffix of a
cancellation pasting. -/
private theorem forwardCancellation_suffix
    {a b c : E}
    {x : a ⟶ a} {e : a ⟶ b} {y : b ⟶ b}
    {z : a ⟶ b} {bPart : a ⟶ a}
    (s : bPart ≫ e ⟶ e ≫ y) (p : x ≫ e ⟶ z)
    (t : b ⟶ c) :
    (x ◁ (s ▷ t)) ≫
        (x ◁ (α_ e y t).hom) ≫
        (α_ x e (y ≫ t)).inv ≫
      (p ▷ (y ≫ t)) =
      (α_ x (bPart ≫ e) t).inv ≫
        ((x ◁ s) ▷ t) ≫
        ((α_ x e y).inv ▷ t) ≫
        ((p ▷ y) ▷ t) ≫
        (α_ z y t).hom := by
  bicategory

set_option backward.isDefEq.respectTransparency false in
/-- Reassociate a retained-forward factorization after whiskering by a
retained prefix and a cancellation tail. -/
private theorem forwardCancellation_factorizationSuffix
    {a b c : E}
    {x bPart : a ⟶ a} {e : a ⟶ b} {z : a ⟶ b}
    (p : bPart ≫ e ⟶ z) (t : b ⟶ c) :
    x ◁ (p ▷ t) =
      (α_ x (bPart ≫ e) t).inv ≫
        ((x ◁ p) ▷ t) ≫
        (α_ x z t).hom := by
  bicategory

set_option backward.isDefEq.respectTransparency false in
/-- Move a fixed forward factorization across an arbitrary comparison on
its retained tail. -/
private theorem forwardCancellation_tail
    {a b c : E}
    {x : a ⟶ a} {e : a ⟶ b} {z : a ⟶ b}
    (p : x ≫ e ⟶ z) {T S : b ⟶ c} (k : T ⟶ S) :
    (α_ x e T).inv ≫ (p ▷ T) ≫ (z ◁ k) =
      (x ◁ (e ◁ k)) ≫ (α_ x e S).inv ≫ (p ▷ S) := by
  rw [← whisker_exchange p k]
  rw [← Category.assoc, ← associator_inv_naturality_right]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Conjugating a whiskered 2-cell by an isomorphism cancels, including an
arbitrary fixed left prefix. -/
@[reassoc]
private theorem whiskerLeft_iso_conjugation
    {a b c d : E} (r : a ⟶ b)
    {x y : b ⟶ c} (e : x ≅ y)
    {s t : c ⟶ d} (q : s ⟶ t) :
    (r ◁ (e.inv ▷ s)) ≫
        (r ◁ (x ◁ q)) ≫
        (r ◁ (e.hom ▷ t)) =
      r ◁ (y ◁ q) := by
  have hbase :
      (e.inv ▷ s) ≫ (x ◁ q) ≫ (e.hom ▷ t) =
        y ◁ q := by
    rw [whisker_exchange e.hom q]
    simp
  simpa only [Bicategory.whiskerLeft_comp] using
    congrArg (fun u => r ◁ u) hbase

set_option backward.isDefEq.respectTransparency false in
/-- Bicategorical reassociation form of `whiskerLeft_iso_conjugation`, suited
to a split retained prefix and a composite tail. -/
@[reassoc]
private theorem whiskerLeft_iso_conjugation_bicategorical
    {w a b c : E} (r : w ⟶ a)
    {x y₁ y₂ : a ⟶ a} (e : x ≅ y₁ ≫ y₂)
    {l : a ⟶ b} {t : b ⟶ c} {z : a ⟶ c}
    (q : l ≫ t ⟶ z) :
    (r ◁ (α_ y₁ (y₂ ≫ l) t).inv) ≫
        (r ◁ ((α_ y₁ y₂ l).inv ▷ t)) ≫
        (r ◁ ((e.inv ▷ l) ▷ t)) ≫
        (r ◁ (α_ x l t).hom) ≫
        (r ◁ (x ◁ q)) ≫
        (r ◁ (e.hom ▷ z)) ≫
        (r ◁ (α_ y₁ y₂ z).hom) ≫
        (α_ r y₁ (y₂ ≫ z)).inv =
      (r ◁ (y₁ ◁ (α_ y₂ l t).hom)) ≫
        (r ◁ (y₁ ◁ (y₂ ◁ q))) ≫
        (α_ r y₁ (y₂ ≫ z)).inv := by
  have hbase :
      (e.inv ▷ (l ≫ t)) ≫ (x ◁ q) ≫ (e.hom ▷ z) =
        (y₁ ≫ y₂) ◁ q := by
    rw [whisker_exchange e.hom q]
    simp
  have h := congrArg (fun u => r ◁ u) hbase
  let pre :=
    (r ◁ (y₁ ◁ (α_ y₂ l t).hom)) ≫
      (r ◁ (α_ y₁ y₂ (l ≫ t)).inv)
  let post :=
    (r ◁ (α_ y₁ y₂ z).hom) ≫
      (α_ r y₁ (y₂ ≫ z)).inv
  have hcontext := congrArg (fun u => pre ≫ u ≫ post) h
  dsimp [pre, post] at hcontext
  convert hcontext using 1
  · bicategory
  · bicategory

set_option backward.isDefEq.respectTransparency false in
/-- Bicategorical reassociation form of iso conjugation without an additional
left prefix.  It cancels a split compositor around an arbitrary composite
tail. -/
private theorem iso_conjugation_bicategorical
    {a b c : E} {x y₁ y₂ : a ⟶ a} (e : x ≅ y₁ ≫ y₂)
    {l : a ⟶ b} {t : b ⟶ c} {z : a ⟶ c}
    (q : l ≫ t ⟶ z) :
    (α_ y₁ (y₂ ≫ l) t).inv ≫
        ((α_ y₁ y₂ l).inv ▷ t) ≫
        ((e.inv ▷ l) ▷ t) ≫
        (α_ x l t).hom ≫
        (x ◁ q) ≫
        (e.hom ▷ z) ≫
        (α_ y₁ y₂ z).hom =
      (y₁ ◁ (α_ y₂ l t).hom) ≫
        (y₁ ◁ (y₂ ◁ q)) := by
  have hbase :
      (e.inv ▷ (l ≫ t)) ≫ (x ◁ q) ≫ (e.hom ▷ z) =
        (y₁ ≫ y₂) ◁ q := by
    rw [whisker_exchange e.hom q]
    simp
  let pre :=
    (y₁ ◁ (α_ y₂ l t).hom) ≫
      (α_ y₁ y₂ (l ≫ t)).inv
  let post := (α_ y₁ y₂ z).hom
  have hcontext := congrArg (fun u => pre ≫ u ≫ post) hbase
  dsimp [pre, post] at hcontext
  convert hcontext using 1
  · bicategory
  · bicategory

set_option backward.isDefEq.respectTransparency false in
/-- Inner segment of `iso_conjugation_bicategorical`, with the two outer
associators moved to the result. -/
private theorem iso_conjugation_bicategorical_inner
    {a b c : E} {x y₁ y₂ : a ⟶ a} (e : x ≅ y₁ ≫ y₂)
    {l : a ⟶ b} {t : b ⟶ c} {z : a ⟶ c}
    (q : l ≫ t ⟶ z) :
    ((α_ y₁ y₂ l).inv ▷ t) ≫
        ((e.inv ▷ l) ▷ t) ≫
        (α_ x l t).hom ≫
        (x ◁ q) ≫
        (e.hom ▷ z) =
      (α_ y₁ (y₂ ≫ l) t).hom ≫
        (y₁ ◁ (α_ y₂ l t).hom) ≫
        (y₁ ◁ (y₂ ◁ q)) ≫
        (α_ y₁ y₂ z).inv := by
  rw [← cancel_epi (α_ y₁ (y₂ ≫ l) t).inv]
  rw [← cancel_mono (α_ y₁ y₂ z).hom]
  simp only [Category.assoc]
  simp
  exact iso_conjugation_bicategorical e q

/-- Transport an equality of right-whiskered tails across an isomorphism of
their fixed left factors. -/
private theorem iso_whisker_transport_of_eq
    {a b : E} {r s : a ⟶ b} (p : r ≅ s)
    {U V : b ⟶ b} {kL kR : U ⟶ V} (h : kL = kR) :
    (p.inv ▷ U) ≫ (r ◁ kL) =
      (s ◁ kR) ≫ (p.inv ▷ V) := by
  calc
    _ = (s ◁ kL) ≫ (p.inv ▷ V) :=
      (whisker_exchange p.inv kL).symm
    _ = _ := by rw [h]

/-- Transport a tail across an isomorphic left factor when the comparison is
known only after whiskering by the exposed inner left factor. -/
private theorem iso_whisker_transport_of_whiskered_eq
    {a b : E} {r x : a ⟶ b} {xA : a ⟶ a} (p : r ≅ xA ≫ x)
    {U V : b ⟶ b} {kL : U ⟶ V} {kR : x ≫ U ⟶ x ≫ V}
    (h : (x ◁ kL) = kR) :
    (p.inv ▷ U) ≫ (r ◁ kL) =
      (α_ xA x U).hom ≫
        (xA ◁ kR) ≫
        (α_ xA x V).inv ≫
        (p.inv ▷ V) := by
  rw [← whisker_exchange p.inv kL]
  rw [← h]
  bicategory

set_option backward.isDefEq.respectTransparency false in
/-- Reversing an adjoint equivalence preserves the original inverse unit as
its counit; the adjointification inserted by `Equivalence.symm` cancels by
the second triangle identity. -/
private theorem equivalenceSymm_counit_eq_unit_symm
    {a b : E} (e : a ≌ b) :
    e.symm.counit = e.unit.symm := by
  apply Iso.ext
  dsimp [Bicategory.Equivalence.symm,
    Bicategory.Equivalence.mkOfAdjointifyCounit,
    adjointifyCounit]
  rw [e.right_triangle]
  simp

private theorem equivalenceSymm_unit_eq_counit_symm
    {a b : E} (e : a ≌ b) :
    e.symm.unit = e.counit.symm := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Counit insertion for the reversed equivalence is unit insertion for the
original equivalence. -/
private theorem equivalenceCounitInsertion_symm_eq_unitInsertion
    {a b : E} (e : a ≌ b) (T : a ⟶ a) :
    equivalenceCounitInsertion e.symm T =
      equivalenceUnitInsertion e T := by
  apply Iso.ext
  rw [equivalenceCounitInsertion_hom,
    equivalenceUnitInsertion_hom]
  rw [equivalenceSymm_counit_eq_unit_symm]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Unit insertion for the reversed equivalence is counit insertion for the
original equivalence. -/
private theorem equivalenceUnitInsertion_symm_eq_counitInsertion
    {a b : E} (e : a ≌ b) (T : b ⟶ b) :
    equivalenceUnitInsertion e.symm T =
      equivalenceCounitInsertion e T := by
  apply Iso.ext
  rw [equivalenceUnitInsertion_hom,
    equivalenceCounitInsertion_hom]
  rw [equivalenceSymm_unit_eq_counit_symm]
  rfl

/-- The adjunction obtained by reversing a chosen adjoint equivalence, with
the endpoints exposed definitionally. -/
private noncomputable def reverseEquivalenceAdjunction
    {a b : E} (e : a ≌ b) : e.inv ⊣ e.hom := by
  simpa only [Bicategory.Equivalence.symm_hom,
    Bicategory.Equivalence.symm_inv] using e.symm.toAdjunction

private theorem reverseEquivalenceAdjunction_unit
    {a b : E} (e : a ≌ b) :
    (reverseEquivalenceAdjunction e).unit = e.counit.inv := by
  rfl

private theorem reverseEquivalenceAdjunction_counit
    {a b : E} (e : a ≌ b) :
    (reverseEquivalenceAdjunction e).counit = e.unit.inv := by
  exact congrArg Iso.hom (equivalenceSymm_counit_eq_unit_symm e)

set_option backward.isDefEq.respectTransparency false in
/-- Taking the mate of the inverse of an invertible right-adjoint square
along the reversed equivalence recovers the original forward square. -/
private theorem reverseMate_inv
    {a b : E} (e : a ≌ b) {x : a ⟶ a} {y : b ⟶ b}
    (s : e.hom ≫ y ≅ x ≫ e.hom)
    (β : e.inv ≫ x ≅ y ≫ e.inv)
    (hβ : β.hom =
      mateEquiv e.toAdjunction e.toAdjunction s.inv) :
    mateEquiv (reverseEquivalenceAdjunction e)
        (reverseEquivalenceAdjunction e) β.inv = s.hom := by
  rw [← cancel_mono s.inv]
  simp only [Iso.hom_inv_id]
  have hs : s.inv =
      (mateEquiv e.toAdjunction e.toAdjunction).symm β.hom := by
    rw [hβ, Equiv.symm_apply_apply]
  rw [hs, mateEquiv_apply', mateEquiv_symm_apply']
  rw [reverseEquivalenceAdjunction_unit,
    reverseEquivalenceAdjunction_counit]
  bicategory_nf
  have hunit : e.toAdjunction.unit = e.unit.hom := rfl
  have hcounit : e.toAdjunction.counit = e.counit.hom := rfl
  rw [hunit, hcounit]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Counit insertion is compatible with an invertible inverse-sliding
square and its mate, with an arbitrary retained tail. -/
private theorem equivalenceCounitInsertion_reverseMate_vcomp
    {a b : E} (e : a ≌ b)
    {x : a ⟶ a} {y z : b ⟶ b}
    (β : e.inv ≫ x ≅ y ≫ e.inv) :
    (equivalenceCounitInsertion e (y ≫ z)).hom ≫
        (e.inv ◁ (α_ e.hom y z).inv) ≫
        (e.inv ◁
          (mateEquiv (reverseEquivalenceAdjunction e)
            (reverseEquivalenceAdjunction e) β.inv ▷ z)) ≫
        (e.inv ◁ (α_ x e.hom z).hom) =
      (y ◁ (equivalenceCounitInsertion e z).hom) ≫
        (α_ y e.inv (e.hom ≫ z)).inv ≫
        (β.inv ▷ (e.hom ≫ z)) ≫
        (α_ e.inv x (e.hom ≫ z)).hom := by
  let adj := reverseEquivalenceAdjunction e
  have h := (mateEquiv_eq_iff adj adj β.inv
    (mateEquiv adj adj β.inv)).mp rfl
  rw [Adjunction.homEquiv₁_symm_apply,
    Adjunction.homEquiv₂_apply] at h
  let post :=
    (α_ e.inv (x ≫ e.hom) z).hom ≫
      (e.inv ◁ (α_ x e.hom z).hom)
  have hz := congrArg (fun k => (k ▷ z) ≫ post) h
  dsimp [post, adj] at hz
  rw [reverseEquivalenceAdjunction_unit] at hz
  rw [equivalenceCounitInsertion_hom,
    equivalenceCounitInsertion_hom]
  convert hz using 1
  · bicategory
  · bicategory

set_option backward.isDefEq.respectTransparency false in
/-- Splitting a fixed left factor commutes with counit insertion in the tail,
including the associators needed to expose the inverse-equivalence factor. -/
private theorem equivalenceCounitInsertion_splitLeft_naturality
    {a b : E} (e : a ≌ b)
    {xAB xA xB : b ⟶ b} (η : xAB ⟶ xA ≫ xB)
    (z : b ⟶ b) :
    (η ▷ z) ≫
        (α_ xA xB z).hom ≫
        (xA ◁ (xB ◁ (equivalenceCounitInsertion e z).hom)) ≫
        (xA ◁ (α_ xB e.inv (e.hom ≫ z)).inv) =
      (xAB ◁ (equivalenceCounitInsertion e z).hom) ≫
        (α_ xAB e.inv (e.hom ≫ z)).inv ≫
        (((η ▷ e.inv) ≫ (α_ xA xB e.inv).hom) ▷
          (e.hom ≫ z)) ≫
        (α_ xA (xB ≫ e.inv) (e.hom ≫ z)).hom := by
  have h := whisker_exchange η (equivalenceCounitInsertion e z).hom
  let post :=
    (α_ xA xB (e.inv ≫ (e.hom ≫ z))).hom ≫
      (xA ◁ (α_ xB e.inv (e.hom ≫ z)).inv)
  have hpost := congrArg (fun u => u ≫ post) h
  dsimp [post] at hpost
  convert hpost.symm using 1
  · bicategory
  · bicategory

set_option backward.isDefEq.respectTransparency false in
/-- The two ways to expose an alternating `hom/inv/hom` segment agree: one
may insert the counit in the codomain tail, or first slide the retained factor
through `hom` and then insert the unit in the domain factor. -/
private theorem equivalenceUnitCounit_alternating
    {a b : E} (e : a ≌ b)
    {x : a ⟶ a} {y z : b ⟶ b} {w : a ⟶ b}
    (s : e.hom ≫ y ≅ x ≫ e.hom) (q : e.hom ≫ z ≅ w) :
    (e.hom ◁ (equivalenceCounitInsertion e (y ≫ z)).hom) ≫
        (e.hom ◁ (e.inv ◁ (α_ e.hom y z).inv)) ≫
        (e.hom ◁ (e.inv ◁ (s.hom ▷ z))) ≫
        (e.hom ◁ (e.inv ◁ (α_ x e.hom z).hom)) ≫
        (e.hom ◁ (α_ e.inv x (e.hom ≫ z)).inv) ≫
        (e.hom ◁ ((e.inv ≫ x) ◁ q.hom)) =
      (α_ e.hom y z).inv ≫
        (s.hom ▷ z) ≫
        (α_ x e.hom z).hom ≫
        (x ◁ q.hom) ≫
        ((equivalenceUnitInsertion e x).hom ▷ w) ≫
        (α_ e.hom (e.inv ≫ x) w).hom := by
  let insert : x ≫ w ≅ e.hom ≫ ((e.inv ≫ x) ≫ w) :=
    whiskerRightIso (equivalenceUnitInsertion e x) w ≪≫
      α_ e.hom (e.inv ≫ x) w
  let collapse := insert.symm
  have hsymm := congrArg Iso.symm e.left_triangle
  have htriangleRaw :
      rightZigzag e.counit.inv e.unit.inv =
        (λ_ e.hom ≪≫ (ρ_ e.hom).symm).inv := by
    have hhom := congrArg Iso.hom hsymm
    simpa only [leftZigzagIso_symm, rightZigzagIso_hom,
      Iso.symm_hom] using hhom
  have htriangle :
      (ρ_ e.hom).inv ≫
          rightZigzag e.counit.inv e.unit.inv ≫
          (λ_ e.hom).hom =
        𝟙 e.hom := by
    rw [htriangleRaw]
    dsimp [bicategoricalIsoComp]
    simp
  rw [← cancel_mono collapse.hom]
  let direct :=
    (α_ e.hom y z).inv ≫
      (s.hom ▷ z) ≫
      (α_ x e.hom z).hom ≫
      (x ◁ q.hom)
  simp only [Category.assoc]
  slice_rhs 5 6 =>
    change insert.hom
    rfl
  rw [show collapse.hom = insert.inv by rfl]
  slice_rhs 5 6 =>
    rw [Iso.hom_inv_id]
  rw [equivalenceCounitInsertion_hom]
  rw [show insert.inv =
      (α_ e.hom (e.inv ≫ x) w).inv ≫
        ((equivalenceUnitInsertion e x).inv ▷ w) by rfl,
    equivalenceUnitInsertion_inv]
  simp only [Bicategory.comp_whiskerRight]
  have hcontext := congrArg
    (fun u : e.hom ⟶ e.hom => (u ▷ (y ≫ z)) ≫ direct) htriangle
  dsimp [direct, rightZigzag] at hcontext
  calc
    _ = (((ρ_ e.hom).inv ≫
          rightZigzag e.counit.inv e.unit.inv ≫
          (λ_ e.hom).hom) ▷ (y ≫ z)) ≫ direct := by
      have hex := whisker_exchange e.unit.inv direct
      let pre :=
        (e.hom ◁ (equivalenceCounitInsertion e (y ≫ z)).hom) ≫
          (α_ e.hom e.inv (e.hom ≫ (y ≫ z))).inv
      have hhex := congrArg
        (fun u => pre ≫ u ≫ (λ_ (x ≫ w)).hom) hex
      dsimp [pre] at hhex
      rw [equivalenceCounitInsertion_hom] at hhex
      convert hhex using 1
      · simp
        bicategory
      · dsimp [rightZigzag, bicategoricalComp]
        simp
        bicategory
    _ = ((𝟙 e.hom) ▷ (y ≫ z)) ≫ direct := hcontext
    _ = _ := by
      dsimp [direct]
      bicategory

set_option backward.isDefEq.respectTransparency false in
/-- Dual alternating triangle, obtained by applying
`equivalenceUnitCounit_alternating` to the reversed equivalence and then
identifying its insertions with those of the original equivalence. -/
private theorem equivalenceUnitCounit_alternating_dual
    {a b : E} (e : a ≌ b)
    {x : b ⟶ b} {y z : a ⟶ a}
    (s : e.inv ≫ y ≅ x ≫ e.inv) :
    (e.inv ◁ (equivalenceUnitInsertion e (y ≫ z)).hom) ≫
        (e.inv ◁ (e.hom ◁ (α_ e.inv y z).inv)) ≫
        (e.inv ◁ (e.hom ◁ (s.hom ▷ z))) ≫
        (e.inv ◁ (e.hom ◁ (α_ x e.inv z).hom)) ≫
        (e.inv ◁ (α_ e.hom x (e.inv ≫ z)).inv) =
      (α_ e.inv y z).inv ≫
        (s.hom ▷ z) ≫
        (α_ x e.inv z).hom ≫
        ((equivalenceCounitInsertion e x).hom ▷ (e.inv ≫ z)) ≫
        (α_ e.inv (e.hom ≫ x) (e.inv ≫ z)).hom := by
  have h := equivalenceUnitCounit_alternating e.symm s
    (Iso.refl (e.inv ≫ z))
  rw [equivalenceCounitInsertion_symm_eq_unitInsertion,
    equivalenceUnitInsertion_symm_eq_counitInsertion] at h
  simpa only [Bicategory.Equivalence.symm_hom,
    Bicategory.Equivalence.symm_inv, Iso.refl_hom,
    Bicategory.whiskerLeft_id, Bicategory.id_whiskerRight,
    Category.id_comp, Category.comp_id] using h

set_option backward.isDefEq.respectTransparency false in
/-- Mapping an adjunction through the identity pseudofunctor does not change
the mate operation.  This removes the compositor wrappers introduced by the
generic pseudofunctorial mate theorem. -/
private theorem identityPseudofunctor_mateEquiv
    {C : Type u₂} [Bicategory.{w₂, v₂} C]
    {a b : C} (e : a ≌ b)
    {x : a ⟶ a} {y : b ⟶ b}
    (α : x ≫ e.hom ⟶ e.hom ≫ y) :
    mateEquiv
        ((Pseudofunctor.id C).mapAdjunction e.toAdjunction)
        ((Pseudofunctor.id C).mapAdjunction e.toAdjunction) α =
      mateEquiv e.toAdjunction e.toAdjunction α := by
  have hleft :
      Pseudofunctor.mapLeftAdjointSquare (Pseudofunctor.id C) α = α := by
    change (𝟙 (x ≫ e.hom)) ≫ α ≫ (𝟙 (e.hom ≫ y)) = α
    simp
  have hright :
      Pseudofunctor.mapRightAdjointSquare (Pseudofunctor.id C)
          (mateEquiv e.toAdjunction e.toAdjunction α) =
        mateEquiv e.toAdjunction e.toAdjunction α := by
    change (𝟙 (e.inv ≫ x)) ≫
        mateEquiv e.toAdjunction e.toAdjunction α ≫
          (𝟙 (y ≫ e.inv)) = _
    simp
  have h := Pseudofunctor.map_mateEquiv (Pseudofunctor.id C)
    e.toAdjunction e.toAdjunction α
  rw [hleft, hright] at h
  exact h

private theorem mate_precomp
    {C : Type u₂} [Bicategory.{w₂, v₂} C]
    {a b : C} {l : a ⟶ b} {r : b ⟶ a} (adj : l ⊣ r)
    {g₀ g₁ : a ⟶ a} {h : b ⟶ b} (p : g₀ ⟶ g₁)
    (α : g₁ ≫ l ⟶ l ≫ h) :
    mateEquiv adj adj ((p ▷ l) ≫ α) =
      (r ◁ p) ≫ mateEquiv adj adj α := by
  rw [mateEquiv_apply', mateEquiv_apply']
  simp
  simp only [bicategoricalComp]
  simp
  have hp :
      (g₀ ◁ adj.unit) ≫ (p ▷ (l ≫ r)) =
        (p ▷ 𝟙 a) ≫ (g₁ ◁ adj.unit) := by
    exact whisker_exchange p adj.unit
  have hprefix :
      (rightUnitor (r ≫ g₀)).inv ≫
          (associator r g₀ (𝟙 a)).hom ≫
          (r ◁ g₀ ◁ adj.unit) ≫
          (r ◁ (associator g₀ l r).inv) ≫
          (r ◁ p ▷ l ▷ r) =
        (r ◁ p) ≫
          (rightUnitor (r ≫ g₁)).inv ≫
          (associator r g₁ (𝟙 a)).hom ≫
          (r ◁ g₁ ◁ adj.unit) ≫
          (r ◁ (associator g₁ l r).inv) := by
    calc
      _ = (rightUnitor (r ≫ g₀)).inv ≫
          (associator r g₀ (𝟙 a)).hom ≫
          (r ◁ ((g₀ ◁ adj.unit) ≫ (p ▷ (l ≫ r)))) ≫
          (r ◁ (associator g₁ l r).inv) := by
        bicategory
      _ = (rightUnitor (r ≫ g₀)).inv ≫
          (associator r g₀ (𝟙 a)).hom ≫
          (r ◁ ((p ▷ 𝟙 a) ≫ (g₁ ◁ adj.unit))) ≫
          (r ◁ (associator g₁ l r).inv) := by
        rw [hp]
      _ = _ := by
        bicategory
  slice_lhs 1 5 => rw [hprefix]
  simp only [Category.assoc]

private theorem mate_postcomp
    {C : Type u₂} [Bicategory.{w₂, v₂} C]
    {a b : C} {l : a ⟶ b} {r : b ⟶ a} (adj : l ⊣ r)
    {g : a ⟶ a} {h₀ h₁ : b ⟶ b} (q : h₀ ⟶ h₁)
    (α : g ≫ l ⟶ l ≫ h₀) :
    mateEquiv adj adj (α ≫ (l ◁ q)) =
      mateEquiv adj adj α ≫ (q ▷ r) := by
  rw [mateEquiv_apply', mateEquiv_apply']
  simp
  simp only [bicategoricalComp]
  simp
  have hq :
      ((r ≫ l) ◁ q) ≫ (adj.counit ▷ h₁) =
        (adj.counit ▷ h₀) ≫ ((𝟙 b) ◁ q) := by
    exact whisker_exchange adj.counit q
  have hsuffix :
      (r ◁ (associator l h₀ r).hom) ≫
          (r ◁ l ◁ q ▷ r) ≫
          (associator r l (h₁ ≫ r)).inv ≫
          (associator (r ≫ l) h₁ r).inv ≫
          (adj.counit ▷ h₁ ▷ r) ≫
          (associator (𝟙 b) h₁ r).hom ≫
          (leftUnitor (h₁ ≫ r)).hom =
        (associator r (l ≫ h₀) r).inv ≫
          ((associator r l h₀).inv ▷ r) ≫
          (adj.counit ▷ h₀ ▷ r) ≫
          (associator (𝟙 b) h₀ r).hom ≫
          (leftUnitor (h₀ ≫ r)).hom ≫
          (q ▷ r) := by
    calc
      _ = (associator r (l ≫ h₀) r).inv ≫
          ((associator r l h₀).inv ▷ r) ≫
          (((((r ≫ l) ◁ q) ≫ (adj.counit ▷ h₁)) ▷ r)) ≫
          ((leftUnitor h₁).hom ▷ r) := by
        bicategory
      _ = (associator r (l ≫ h₀) r).inv ≫
          ((associator r l h₀).inv ▷ r) ≫
          ((((adj.counit ▷ h₀) ≫ ((𝟙 b) ◁ q)) ▷ r)) ≫
          ((leftUnitor h₁).hom ▷ r) := by
        rw [hq]
      _ = _ := by
        bicategory
  slice_lhs 4 10 => rw [hsuffix]

private theorem mate_naturality_of_square
    {C : Type u₂} [Bicategory.{w₂, v₂} C]
    {a b : C} {l : a ⟶ b} {r : b ⟶ a} (adj : l ⊣ r)
    {g₀ g₁ : a ⟶ a} {h₀ h₁ : b ⟶ b}
    {p : g₀ ⟶ g₁} {q : h₀ ⟶ h₁}
    {α₀ : g₀ ≫ l ⟶ l ≫ h₀} {α₁ : g₁ ≫ l ⟶ l ≫ h₁}
    (h : (p ▷ l) ≫ α₁ = α₀ ≫ (l ◁ q)) :
    (r ◁ p) ≫ mateEquiv adj adj α₁ =
      mateEquiv adj adj α₀ ≫ (q ▷ r) := by
  rw [← mate_precomp adj p α₁,
    ← mate_postcomp adj q α₀, h]

/-- Transporting the lift's mapped forward 2-cell to the source endpoints
commutes with that 2-cell. -/
theorem generalLiftMap₂ForwardTransport
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell f η) ≫
        eqToHom (generalLiftPrelaxFunctor_map_forward F hF f B) =
      eqToHom (generalLiftPrelaxFunctor_map_forward F hF f A) ≫
        F.map₂ (canonicalSourceTwoCell f η) := by
  exact eqToHom_naturality_of_heq
    (generalLiftPrelaxFunctor_map_forward F hF f A)
    (generalLiftPrelaxFunctor_map_forward F hF f B)
    (generalLiftPrelaxFunctor_map₂_forward F hF f η)

/-- The same endpoint-transport square, oriented from source back to target. -/
theorem generalLiftMap₂ForwardTransportSymm
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    F.map₂ (canonicalSourceTwoCell f η) ≫
        eqToHom (generalLiftPrelaxFunctor_map_forward F hF f B).symm =
      eqToHom (generalLiftPrelaxFunctor_map_forward F hF f A).symm ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell f η) := by
  exact eqToHom_naturality_of_heq
    (generalLiftPrelaxFunctor_map_forward F hF f A).symm
    (generalLiftPrelaxFunctor_map_forward F hF f B).symm
    (generalLiftPrelaxFunctor_map₂_forward F hF f η).symm

/-- The central forward compositor stage: transport the mapped composite to
the source and then apply the source pseudofunctor's compositor. -/
noncomputable def generalLiftForwardMapCompCore
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A B : Type) :
    (generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom (f ≫ g) (A × B)) ≅
      F.map (canonicalSourceHom f A) ≫
        F.map (canonicalSourceHom g B) :=
  eqToIso (generalLiftPrelaxFunctor_map_forward F hF
      (f ≫ g) (A × B)) ≪≫
    generalLiftForwardMapCompSource F f g A B

theorem generalLiftForwardMapCompCore_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A B : Type) :
    (generalLiftForwardMapCompCore F hF f g A B).hom =
      eqToHom (generalLiftPrelaxFunctor_map_forward F hF
        (f ≫ g) (A × B)) ≫
        (generalLiftForwardMapCompSource F f g A B).hom := by
  rfl

/-- The central forward compositor stage is natural in its right retained
coordinate. -/
theorem generalLiftForwardMapCompCore_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (f ≫ g)
            (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η)) ≫
        (generalLiftForwardMapCompCore F hF f g A C).hom =
      (generalLiftForwardMapCompCore F hF f g A B).hom ≫
        F.map (canonicalSourceHom f A) ◁
          F.map₂ (canonicalSourceTwoCell g η) := by
  rw [generalLiftForwardMapCompCore_hom,
    generalLiftForwardMapCompCore_hom]
  exact comp_naturality_of_squares
    (generalLiftMap₂ForwardTransport F hF (f ≫ g)
      (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η))
    (generalLiftForwardMapCompSource_naturality_right F f g A η)

/-- The central forward compositor stage is natural in its left retained
coordinate. -/
theorem generalLiftForwardMapCompCore_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (f ≫ g)
            (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B))) ≫
        (generalLiftForwardMapCompCore F hF f g C B).hom =
      (generalLiftForwardMapCompCore F hF f g A B).hom ≫
        F.map₂ (canonicalSourceTwoCell f η) ▷
          F.map (canonicalSourceHom g B) := by
  rw [generalLiftForwardMapCompCore_hom,
    generalLiftForwardMapCompCore_hom]
  exact comp_naturality_of_squares
    (generalLiftMap₂ForwardTransport F hF (f ≫ g)
      (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B)))
    (generalLiftForwardMapCompSource_naturality_left F f g η B)

/-- The final forward compositor stage transports each source factor back to
the arbitrary lift's mapped forward factor. -/
noncomputable def generalLiftForwardMapCompFactors
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A B : Type) :
    F.map (canonicalSourceHom f A) ≫
        F.map (canonicalSourceHom g B) ≅
      (generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A) ≫
        (generalLiftPrelaxFunctor F hF).map (canonicalForwardHom g B) :=
  whiskerRightIso
      (eqToIso (generalLiftPrelaxFunctor_map_forward F hF f A)).symm
      (F.map (canonicalSourceHom g B)) ≪≫
    whiskerLeftIso
      ((generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A))
      (eqToIso (generalLiftPrelaxFunctor_map_forward F hF g B)).symm

theorem generalLiftForwardMapCompFactors_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A B : Type) :
    (generalLiftForwardMapCompFactors F hF f g A B).hom =
      (eqToHom (generalLiftPrelaxFunctor_map_forward F hF f A).symm ▷
          F.map (canonicalSourceHom g B)) ≫
        ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A) ◁
          eqToHom (generalLiftPrelaxFunctor_map_forward F hF g B).symm) := by
  rfl

/-- Factorwise endpoint transport is natural in the right retained
coordinate. -/
theorem generalLiftForwardMapCompFactors_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    (F.map (canonicalSourceHom f A) ◁
          F.map₂ (canonicalSourceTwoCell g η)) ≫
        (generalLiftForwardMapCompFactors F hF f g A C).hom =
      (generalLiftForwardMapCompFactors F hF f g A B).hom ≫
        (generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A) ◁
          (generalLiftPrelaxFunctor F hF).map₂
            (canonicalForwardTwoCell g η) := by
  rw [generalLiftForwardMapCompFactors_hom,
    generalLiftForwardMapCompFactors_hom]
  exact comp_naturality_of_squares
    (whisker_exchange
      (eqToHom
        (generalLiftPrelaxFunctor_map_forward F hF f A).symm)
      (F.map₂ (canonicalSourceTwoCell g η)))
    (whiskerLeft_naturality_of_square
      ((generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A))
      (generalLiftMap₂ForwardTransportSymm F hF g η))

/-- Factorwise endpoint transport is natural in the left retained
coordinate. -/
theorem generalLiftForwardMapCompFactors_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    (F.map₂ (canonicalSourceTwoCell f η) ▷
          F.map (canonicalSourceHom g B)) ≫
        (generalLiftForwardMapCompFactors F hF f g C B).hom =
      (generalLiftForwardMapCompFactors F hF f g A B).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
            (canonicalForwardTwoCell f η) ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom g B) := by
  rw [generalLiftForwardMapCompFactors_hom,
    generalLiftForwardMapCompFactors_hom]
  exact comp_naturality_of_squares
    (whiskerRight_naturality_of_square
      (F.map (canonicalSourceHom g B))
      (generalLiftMap₂ForwardTransportSymm F hF f η))
    (whisker_exchange
      ((generalLiftPrelaxFunctor F hF).map₂
        (canonicalForwardTwoCell f η))
      (eqToHom
        (generalLiftPrelaxFunctor_map_forward F hF g B).symm)).symm

/-- The complete post-comparison transport in the forward compositor,
separated so its two-variable naturality can be proved compositionally. -/
noncomputable def generalLiftForwardMapCompTransport
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A B : Type) :
    (generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom (f ≫ g) (A × B)) ≅
      (generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A) ≫
        (generalLiftPrelaxFunctor F hF).map (canonicalForwardHom g B) :=
  generalLiftForwardMapCompCore F hF f g A B ≪≫
    generalLiftForwardMapCompFactors F hF f g A B

theorem generalLiftForwardMapCompTransport_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A B : Type) :
    (generalLiftForwardMapCompTransport F hF f g A B).hom =
      (generalLiftForwardMapCompCore F hF f g A B).hom ≫
        (generalLiftForwardMapCompFactors F hF f g A B).hom := by
  rfl

/-- The complete post-comparison transport is natural in its right retained
coordinate. -/
theorem generalLiftForwardMapCompTransport_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (f ≫ g)
            (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η)) ≫
        (generalLiftForwardMapCompTransport F hF f g A C).hom =
      (generalLiftForwardMapCompTransport F hF f g A B).hom ≫
        (generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A) ◁
          (generalLiftPrelaxFunctor F hF).map₂
            (canonicalForwardTwoCell g η) := by
  rw [generalLiftForwardMapCompTransport_hom,
    generalLiftForwardMapCompTransport_hom]
  exact comp_naturality_of_squares
    (generalLiftForwardMapCompCore_naturality_right F hF f g A η)
    (generalLiftForwardMapCompFactors_naturality_right F hF f g A η)

/-- The complete post-comparison transport is natural in its left retained
coordinate. -/
theorem generalLiftForwardMapCompTransport_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (f ≫ g)
            (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B))) ≫
        (generalLiftForwardMapCompTransport F hF f g C B).hom =
      (generalLiftForwardMapCompTransport F hF f g A B).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
            (canonicalForwardTwoCell f η) ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom g B) := by
  rw [generalLiftForwardMapCompTransport_hom,
    generalLiftForwardMapCompTransport_hom]
  exact comp_naturality_of_squares
    (generalLiftForwardMapCompCore_naturality_left F hF f g η B)
    (generalLiftForwardMapCompFactors_naturality_left F hF f g η B)

set_option backward.isDefEq.respectTransparency false in
/-- The endpoint transport stage of the arbitrary lift's forward compositor
satisfies the three-fold associativity law.  The proof transports the already
established source associativity square through all seven canonical endpoint
isomorphisms. -/
theorem generalLiftForwardMapCompTransport_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z W : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell ((f ≫ g) ≫ h)
            (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftForwardMapCompTransport F hF f (g ≫ h)
          A (B × C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A) ◁
          (generalLiftForwardMapCompTransport F hF g h B C).hom =
      (generalLiftForwardMapCompTransport F hF (f ≫ g) h
          (A × B) C).hom ≫
        (generalLiftForwardMapCompTransport F hF f g A B).hom ▷
          (generalLiftPrelaxFunctor F hF).map (canonicalForwardHom h C) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom g B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom h C))).hom := by
  have hwalking : (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
    Category.assoc f g h
  rw [← hwalking]
  simp only [generalLiftForwardMapCompTransport_hom,
    generalLiftForwardMapCompCore_hom,
    generalLiftForwardMapCompFactors_hom, Category.assoc]
  simpa only [eqToIso.hom, eqToIso.inv, Category.assoc] using
    transportCompositor_associativity
    (e₀ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF f A))
    (e₁ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF g B))
    (e₂ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF h C))
    (e₀₁ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (f ≫ g) (A × B)))
    (e₁₂ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (g ≫ h) (B × C)))
    (eL := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF ((f ≫ g) ≫ h)
        ((A × B) × C)))
    (eR := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF ((f ≫ g) ≫ h)
        (A × (B × C))))
    (c₀₁ := (generalLiftForwardMapCompSource F f g A B).hom)
    (c₁₂ := (generalLiftForwardMapCompSource F g h B C).hom)
    (cL := (generalLiftForwardMapCompSource F (f ≫ g) h
      (A × B) C).hom)
    (cR := (generalLiftForwardMapCompSource F f (g ≫ h)
      A (B × C)).hom)
    (aP := F.map₂ (canonicalSourceTwoCell ((f ≫ g) ≫ h)
      (MonoidalCategory.associator A B C).hom))
    (aQ := (generalLiftPrelaxFunctor F hF).map₂
      (canonicalForwardTwoCell ((f ≫ g) ≫ h)
        (MonoidalCategory.associator A B C).hom))
    (ha := generalLiftMap₂ForwardTransport F hF ((f ≫ g) ≫ h)
      (MonoidalCategory.associator A B C).hom)
    (hc := generalLiftForwardMapCompSource_associativity F f g h A B C)

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
    generalLiftForwardMapCompTransport F hF f g A B

theorem generalLiftMapCompForward_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A B : Type) :
    (generalLiftMapCompForward F hF f g A B).hom =
      (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardCompositionComparison f g A B).hom ≫
        (generalLiftForwardMapCompTransport F hF f g A B).hom := by
  rfl

/-- The complete forward composition comparison is natural in every
retained-coordinate 2-morphism on its right factor. -/
theorem generalLiftMapCompForward_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardHom f A ◁ canonicalForwardTwoCell g η) ≫
        (generalLiftMapCompForward F hF f g A C).hom =
      (generalLiftMapCompForward F hF f g A B).hom ≫
        (generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A) ◁
          (generalLiftPrelaxFunctor F hF).map₂
            (canonicalForwardTwoCell g η) := by
  rw [generalLiftMapCompForward_hom,
    generalLiftMapCompForward_hom]
  exact comp_naturality_of_squares
    (generalLiftForwardMapCompTarget_naturality_right F hF f g A η)
    (generalLiftForwardMapCompTransport_naturality_right F hF f g A η)

/-- The complete forward composition comparison is natural in every
retained-coordinate 2-morphism on its left factor. -/
theorem generalLiftMapCompForward_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell f η ▷ canonicalForwardHom g B) ≫
        (generalLiftMapCompForward F hF f g C B).hom =
      (generalLiftMapCompForward F hF f g A B).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
            (canonicalForwardTwoCell f η) ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom g B) := by
  rw [generalLiftMapCompForward_hom,
    generalLiftMapCompForward_hom]
  exact comp_naturality_of_squares
    (generalLiftForwardMapCompTarget_naturality_left F hF f g η B)
    (generalLiftForwardMapCompTransport_naturality_left F hF f g η B)

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

/-- The inverse-then-retained target comparisons satisfy their three-fold
associativity square.  The freely adjoined inverse remains fixed while the
retained coordinates are reassociated from the left-bracketed product to the
right-bracketed product. -/
theorem canonicalInverseRetainedCompositionComparison_associativity
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    ((canonicalInverseRetainedCompositionComparison f A B).hom ▷
          canonicalForwardHom (𝟙 X) C) ≫
        (canonicalInverseRetainedCompositionComparison f (A × B) C).hom ≫
        canonicalInverseTwoCell f
          (MonoidalCategory.associator A B C).hom =
      (α_ (canonicalInverseHom f A)
          (canonicalForwardHom (𝟙 X) B)
          (canonicalForwardHom (𝟙 X) C)).hom ≫
        (canonicalInverseHom f A ◁
          (canonicalForwardCompositionComparison
            (𝟙 X) (𝟙 X) B C).hom) ≫
        (canonicalInverseRetainedCompositionComparison
          f A (B × C)).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- Applying the arbitrary target action preserves the
inverse/retained/retained target associativity square. -/
theorem generalLiftInverseRetainedMapCompTarget_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          ((canonicalInverseRetainedCompositionComparison f A B).hom ▷
            canonicalForwardHom (𝟙 X) C) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseRetainedCompositionComparison
            f (A × B) C).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f
            (MonoidalCategory.associator A B C).hom) =
      (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalInverseHom f A)
            (canonicalForwardHom (𝟙 X) B)
            (canonicalForwardHom (𝟙 X) C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseHom f A ◁
            (canonicalForwardCompositionComparison
              (𝟙 X) (𝟙 X) B C).hom) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseRetainedCompositionComparison
            f A (B × C)).hom := by
  simpa only [(generalLiftPrelaxFunctor F hF).map₂_comp] using
    congrArg (fun η => (generalLiftPrelaxFunctor F hF).map₂ η)
      (canonicalInverseRetainedCompositionComparison_associativity
        f A B C)

/-- The inverse-then-retained target comparison is natural in the retained
coordinate on its right factor. -/
theorem canonicalInverseRetainedCompositionComparison_naturality_right
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) {B C : Type} (η : B ⟶ C) :
    (canonicalInverseHom f A ◁
          canonicalForwardTwoCell (𝟙 X) η) ≫
        (canonicalInverseRetainedCompositionComparison f A C).hom =
      (canonicalInverseRetainedCompositionComparison f A B).hom ≫
        canonicalInverseTwoCell f
          (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η) := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- The inverse-then-retained target comparison is natural in the inverse
factor's retained coordinate. -/
theorem canonicalInverseRetainedCompositionComparison_naturality_left
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A C : Type} (η : A ⟶ C) (B : Type) :
    (canonicalInverseTwoCell f η ▷
          canonicalForwardHom (𝟙 X) B) ≫
        (canonicalInverseRetainedCompositionComparison f C B).hom =
      (canonicalInverseRetainedCompositionComparison f A B).hom ≫
        canonicalInverseTwoCell f
          (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B)) := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- Mapping right naturality of the inverse-then-retained target comparison
through the arbitrary lift preserves its vertical composite. -/
theorem generalLiftInverseRetainedMapCompTarget_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) {B C : Type} (η : B ⟶ C) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseHom f A ◁
            canonicalForwardTwoCell (𝟙 X) η) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseRetainedCompositionComparison f A C).hom =
      (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseRetainedCompositionComparison f A B).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f
            (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η)) := by
  rw [← (generalLiftPrelaxFunctor F hF).map₂_comp,
    canonicalInverseRetainedCompositionComparison_naturality_right,
    (generalLiftPrelaxFunctor F hF).map₂_comp]

/-- Mapping left naturality of the inverse-then-retained target comparison
through the arbitrary lift preserves its vertical composite. -/
theorem generalLiftInverseRetainedMapCompTarget_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A C : Type} (η : A ⟶ C) (B : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f η ▷
            canonicalForwardHom (𝟙 X) B) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseRetainedCompositionComparison f C B).hom =
      (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseRetainedCompositionComparison f A B).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f
            (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B))) := by
  rw [← (generalLiftPrelaxFunctor F hF).map₂_comp,
    canonicalInverseRetainedCompositionComparison_naturality_left,
    (generalLiftPrelaxFunctor F hF).map₂_comp]

/-- Transporting the lift's mapped inverse 2-cell to the chosen inverse and
source endpoints commutes with that 2-cell. -/
theorem generalLiftMap₂InverseTransport
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) {A B : Type} (η : A ⟶ B) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f η) ≫
        eqToHom (generalLiftPrelaxFunctor_map_inverse F hF f hf B) =
      eqToHom (generalLiftPrelaxFunctor_map_inverse F hF f hf A) ≫
        ((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X) η)) := by
  exact eqToHom_naturality_of_heq
    (generalLiftPrelaxFunctor_map_inverse F hF f hf A)
    (generalLiftPrelaxFunctor_map_inverse F hF f hf B)
    (generalLiftPrelaxFunctor_map₂_inverse F hF f hf η)

/-- The same inverse endpoint-transport square, oriented from the chosen
inverse and source endpoints back to the arbitrary lift. -/
theorem generalLiftMap₂InverseTransportSymm
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) {A B : Type} (η : A ⟶ B) :
    ((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X) η)) ≫
        eqToHom
          (generalLiftPrelaxFunctor_map_inverse F hF f hf B).symm =
      eqToHom
          (generalLiftPrelaxFunctor_map_inverse F hF f hf A).symm ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f η) := by
  exact eqToHom_naturality_of_heq
    (generalLiftPrelaxFunctor_map_inverse F hF f hf A).symm
    (generalLiftPrelaxFunctor_map_inverse F hF f hf B).symm
    (generalLiftPrelaxFunctor_map₂_inverse F hF f hf η).symm

set_option backward.isDefEq.respectTransparency false in
/-- Whiskering the retained source compositor by the chosen inverse preserves
its three-fold associativity law.  The final associator converts from
left-composition by the inverse to the bracketing used by the
inverse-then-retained compositor core. -/
theorem generalLiftInverseRetainedMapCompSource_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    ((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X)
            (MonoidalCategory.associator A B C).hom)) ≫
        (((generalLiftSourceEquivalence F hF f).inv ◁
            (generalLiftForwardMapCompSource F
              (𝟙 X) (𝟙 X) A (B × C)).hom) ≫
          (α_ (generalLiftSourceEquivalence F hF f).inv
            (F.map (canonicalSourceHom (𝟙 X) A))
            (F.map (canonicalSourceHom (𝟙 X) (B × C)))).inv) ≫
        (((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) A)) ◁
          (generalLiftForwardMapCompSource F
            (𝟙 X) (𝟙 X) B C).hom) =
      (((generalLiftSourceEquivalence F hF f).inv ◁
          (generalLiftForwardMapCompSource F
            (𝟙 X) (𝟙 X) (A × B) C).hom) ≫
        (α_ (generalLiftSourceEquivalence F hF f).inv
          (F.map (canonicalSourceHom (𝟙 X) (A × B)))
          (F.map (canonicalSourceHom (𝟙 X) C))).inv) ≫
        ((((generalLiftSourceEquivalence F hF f).inv ◁
            (generalLiftForwardMapCompSource F
              (𝟙 X) (𝟙 X) A B).hom) ≫
          (α_ (generalLiftSourceEquivalence F hF f).inv
            (F.map (canonicalSourceHom (𝟙 X) A))
            (F.map (canonicalSourceHom (𝟙 X) B))).inv) ▷
          F.map (canonicalSourceHom (𝟙 X) C)) ≫
        (α_
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) A))
          (F.map (canonicalSourceHom (𝟙 X) B))
          (F.map (canonicalSourceHom (𝟙 X) C))).hom := by
  have hsource :=
    generalLiftForwardMapCompSource_associativity F
      (𝟙 X) (𝟙 X) (𝟙 X) A B C
  have hid : (𝟙 X ≫ 𝟙 X) = 𝟙 X :=
    Subsingleton.elim _ _
  rw [hid] at hsource
  have hcell :
      canonicalSourceTwoCell (𝟙 X ≫ 𝟙 X)
          (MonoidalCategory.associator A B C).hom =
        canonicalSourceTwoCell (𝟙 X)
          (MonoidalCategory.associator A B C).hom := by
    rfl
  rw [hcell] at hsource
  calc
    _ =
        ((generalLiftSourceEquivalence F hF f).inv ◁
          (F.map₂ (canonicalSourceTwoCell (𝟙 X)
              (MonoidalCategory.associator A B C).hom) ≫
            (generalLiftForwardMapCompSource F
              (𝟙 X) (𝟙 X) A (B × C)).hom ≫
            F.map (canonicalSourceHom (𝟙 X) A) ◁
              (generalLiftForwardMapCompSource F
                (𝟙 X) (𝟙 X) B C).hom)) ≫
          (α_ (generalLiftSourceEquivalence F hF f).inv
            (F.map (canonicalSourceHom (𝟙 X) A))
            (F.map (canonicalSourceHom (𝟙 X) B) ≫
              F.map (canonicalSourceHom (𝟙 X) C))).inv := by
      bicategory
    _ =
        ((generalLiftSourceEquivalence F hF f).inv ◁
          ((generalLiftForwardMapCompSource F
              (𝟙 X) (𝟙 X) (A × B) C).hom ≫
            (generalLiftForwardMapCompSource F
              (𝟙 X) (𝟙 X) A B).hom ▷
                F.map (canonicalSourceHom (𝟙 X) C) ≫
            (α_
              (F.map (canonicalSourceHom (𝟙 X) A))
              (F.map (canonicalSourceHom (𝟙 X) B))
              (F.map (canonicalSourceHom (𝟙 X) C))).hom)) ≫
          (α_ (generalLiftSourceEquivalence F hF f).inv
            (F.map (canonicalSourceHom (𝟙 X) A))
            (F.map (canonicalSourceHom (𝟙 X) B) ≫
              F.map (canonicalSourceHom (𝟙 X) C))).inv := by
      rw [hsource]
    _ = _ := by
      bicategory

/-- The inverse-then-retained compositor core: transport the mapped inverse
composite to source data, apply the source compositor under the chosen
inverse, and reassociate. -/
noncomputable def generalLiftInverseRetainedMapCompCore
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftPrelaxFunctor F hF).map
        (canonicalInverseHom f (A × B)) ≅
      ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) A)) ≫
          F.map (canonicalSourceHom (𝟙 X) B) :=
  eqToIso (generalLiftPrelaxFunctor_map_inverse F hF f hf (A × B)) ≪≫
    (whiskerLeftIso (generalLiftSourceEquivalence F hF f).inv
        (generalLiftForwardMapCompSource F (𝟙 X) (𝟙 X) A B) ≪≫
      (α_ (generalLiftSourceEquivalence F hF f).inv
        (F.map (canonicalSourceHom (𝟙 X) A))
        (F.map (canonicalSourceHom (𝟙 X) B))).symm)

theorem generalLiftInverseRetainedMapCompCore_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftInverseRetainedMapCompCore F hF f hf A B).hom =
      eqToHom (generalLiftPrelaxFunctor_map_inverse F hF f hf (A × B)) ≫
        (((generalLiftSourceEquivalence F hF f).inv ◁
            (generalLiftForwardMapCompSource F (𝟙 X) (𝟙 X) A B).hom) ≫
          (α_ (generalLiftSourceEquivalence F hF f).inv
            (F.map (canonicalSourceHom (𝟙 X) A))
            (F.map (canonicalSourceHom (𝟙 X) B))).inv) := by
  rfl

/-- The inverse-then-retained compositor core is natural in its right
retained coordinate. -/
theorem generalLiftInverseRetainedMapCompCore_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f
            (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η)) ≫
        (generalLiftInverseRetainedMapCompCore F hF f hf A C).hom =
      (generalLiftInverseRetainedMapCompCore F hF f hf A B).hom ≫
        (((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) A)) ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X) η)) := by
  rw [generalLiftInverseRetainedMapCompCore_hom,
    generalLiftInverseRetainedMapCompCore_hom]
  exact comp_naturality_of_squares
    (generalLiftMap₂InverseTransport F hF f hf
      (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η))
    (comp_naturality_of_squares
      (whiskerLeft_naturality_of_square
        (generalLiftSourceEquivalence F hF f).inv
        (generalLiftForwardMapCompSource_naturality_right F
          (𝟙 X) (𝟙 X) A η))
      (associator_inv_naturality_right
        (generalLiftSourceEquivalence F hF f).inv
        (F.map (canonicalSourceHom (𝟙 X) A))
        (F.map₂ (canonicalSourceTwoCell (𝟙 X) η))))

/-- The inverse-then-retained compositor core is natural in its left
retained coordinate. -/
theorem generalLiftInverseRetainedMapCompCore_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f
            (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B))) ≫
        (generalLiftInverseRetainedMapCompCore F hF f hf C B).hom =
      (generalLiftInverseRetainedMapCompCore F hF f hf A B).hom ≫
        (((generalLiftSourceEquivalence F hF f).inv ◁
            F.map₂ (canonicalSourceTwoCell (𝟙 X) η)) ▷
          F.map (canonicalSourceHom (𝟙 X) B)) := by
  rw [generalLiftInverseRetainedMapCompCore_hom,
    generalLiftInverseRetainedMapCompCore_hom]
  exact comp_naturality_of_squares
    (generalLiftMap₂InverseTransport F hF f hf
      (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B)))
    (comp_naturality_of_squares
      (whiskerLeft_naturality_of_square
        (generalLiftSourceEquivalence F hF f).inv
        (generalLiftForwardMapCompSource_naturality_left F
          (𝟙 X) (𝟙 X) η B))
      (associator_inv_naturality_middle
        (generalLiftSourceEquivalence F hF f).inv
        (F.map₂ (canonicalSourceTwoCell (𝟙 X) η))
        (F.map (canonicalSourceHom (𝟙 X) B))))

/-- The factor-transport stage of the inverse-then-retained compositor. -/
noncomputable def generalLiftInverseRetainedMapCompFactors
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) A)) ≫
          F.map (canonicalSourceHom (𝟙 X) B) ≅
      (generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A) ≫
        (generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom (𝟙 X) B) :=
  whiskerRightIso
      (eqToIso
        (generalLiftPrelaxFunctor_map_inverse F hF f hf A)).symm
      (F.map (canonicalSourceHom (𝟙 X) B)) ≪≫
    whiskerLeftIso
      ((generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A))
      (eqToIso
        (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X) B)).symm

theorem generalLiftInverseRetainedMapCompFactors_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftInverseRetainedMapCompFactors F hF f hf A B).hom =
      (eqToHom
          (generalLiftPrelaxFunctor_map_inverse F hF f hf A).symm ▷
        F.map (canonicalSourceHom (𝟙 X) B)) ≫
      ((generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A) ◁
        eqToHom
          (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X) B).symm) := by
  rfl

/-- Factor transport in the inverse-then-retained compositor is natural in
the right retained coordinate. -/
theorem generalLiftInverseRetainedMapCompFactors_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    (((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) A)) ◁
        F.map₂ (canonicalSourceTwoCell (𝟙 X) η)) ≫
      (generalLiftInverseRetainedMapCompFactors F hF f hf A C).hom =
    (generalLiftInverseRetainedMapCompFactors F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A) ◁
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 X) η)) := by
  rw [generalLiftInverseRetainedMapCompFactors_hom,
    generalLiftInverseRetainedMapCompFactors_hom]
  exact comp_naturality_of_squares
    (whisker_exchange
      (eqToHom
        (generalLiftPrelaxFunctor_map_inverse F hF f hf A).symm)
      (F.map₂ (canonicalSourceTwoCell (𝟙 X) η)))
    (whiskerLeft_naturality_of_square
      ((generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A))
      (generalLiftMap₂ForwardTransportSymm F hF (𝟙 X) η))

/-- Factor transport in the inverse-then-retained compositor is natural in
the inverse factor's retained coordinate. -/
theorem generalLiftInverseRetainedMapCompFactors_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    (((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X) η)) ▷
        F.map (canonicalSourceHom (𝟙 X) B)) ≫
      (generalLiftInverseRetainedMapCompFactors F hF f hf C B).hom =
    (generalLiftInverseRetainedMapCompFactors F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f η) ▷
        (generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom (𝟙 X) B)) := by
  rw [generalLiftInverseRetainedMapCompFactors_hom,
    generalLiftInverseRetainedMapCompFactors_hom]
  exact comp_naturality_of_squares
    (whiskerRight_naturality_of_square
      (F.map (canonicalSourceHom (𝟙 X) B))
      (generalLiftMap₂InverseTransportSymm F hF f hf η))
    (whisker_exchange
      ((generalLiftPrelaxFunctor F hF).map₂
        (canonicalInverseTwoCell f η))
      (eqToHom
        (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X) B).symm)).symm

/-- The complete post-comparison transport for the inverse-then-retained
compositor. -/
noncomputable def generalLiftInverseRetainedMapCompTransport
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftPrelaxFunctor F hF).map
        (canonicalInverseHom f (A × B)) ≅
      (generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A) ≫
        (generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom (𝟙 X) B) :=
  generalLiftInverseRetainedMapCompCore F hF f hf A B ≪≫
    generalLiftInverseRetainedMapCompFactors F hF f hf A B

theorem generalLiftInverseRetainedMapCompTransport_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftInverseRetainedMapCompTransport F hF f hf A B).hom =
      (generalLiftInverseRetainedMapCompCore F hF f hf A B).hom ≫
        (generalLiftInverseRetainedMapCompFactors F hF f hf A B).hom := by
  rfl

/-- The complete inverse-then-retained transport is natural in its right
retained coordinate. -/
theorem generalLiftInverseRetainedMapCompTransport_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f
            (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η)) ≫
      (generalLiftInverseRetainedMapCompTransport F hF f hf A C).hom =
    (generalLiftInverseRetainedMapCompTransport F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A) ◁
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 X) η)) := by
  rw [generalLiftInverseRetainedMapCompTransport_hom,
    generalLiftInverseRetainedMapCompTransport_hom]
  exact comp_naturality_of_squares
    (generalLiftInverseRetainedMapCompCore_naturality_right
      F hF f hf A η)
    (generalLiftInverseRetainedMapCompFactors_naturality_right
      F hF f hf A η)

/-- The complete inverse-then-retained transport is natural in the inverse
factor's retained coordinate. -/
theorem generalLiftInverseRetainedMapCompTransport_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f
            (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B))) ≫
      (generalLiftInverseRetainedMapCompTransport F hF f hf C B).hom =
    (generalLiftInverseRetainedMapCompTransport F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f η) ▷
        (generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom (𝟙 X) B)) := by
  rw [generalLiftInverseRetainedMapCompTransport_hom,
    generalLiftInverseRetainedMapCompTransport_hom]
  exact comp_naturality_of_squares
    (generalLiftInverseRetainedMapCompCore_naturality_left
      F hF f hf η B)
    (generalLiftInverseRetainedMapCompFactors_naturality_left
      F hF f hf η B)

set_option backward.isDefEq.respectTransparency false in
/-- The endpoint transport stage for an inverse arrow followed by two retained
arrows satisfies the three-fold associativity law.  This transports the
inverse-whiskered source law through the seven canonical endpoint
isomorphisms. -/
theorem generalLiftInverseRetainedMapCompTransport_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f
            (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftInverseRetainedMapCompTransport F hF f hf
          A (B × C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A) ◁
          (generalLiftForwardMapCompTransport F hF
            (𝟙 X) (𝟙 X) B C).hom =
      (generalLiftInverseRetainedMapCompTransport F hF f hf
          (A × B) C).hom ≫
        (generalLiftInverseRetainedMapCompTransport F hF f hf A B).hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 X) C) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 X) B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 X) C))).hom := by
  simp only [generalLiftInverseRetainedMapCompTransport_hom,
    generalLiftInverseRetainedMapCompCore_hom,
    generalLiftInverseRetainedMapCompFactors_hom,
    generalLiftForwardMapCompTransport_hom,
    generalLiftForwardMapCompCore_hom,
    generalLiftForwardMapCompFactors_hom, Category.assoc]
  simpa only [eqToIso.hom, eqToIso.inv, Category.assoc] using
    transportCompositor_associativity
    (e₀ := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf A))
    (e₁ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X) B))
    (e₂ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X) C))
    (e₀₁ := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf (A × B)))
    (e₁₂ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X) (B × C)))
    (eL := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf ((A × B) × C)))
    (eR := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf (A × (B × C))))
    (c₀₁ :=
      ((generalLiftSourceEquivalence F hF f).inv ◁
          (generalLiftForwardMapCompSource F
            (𝟙 X) (𝟙 X) A B).hom) ≫
        (α_ (generalLiftSourceEquivalence F hF f).inv
          (F.map (canonicalSourceHom (𝟙 X) A))
          (F.map (canonicalSourceHom (𝟙 X) B))).inv)
    (c₁₂ := (generalLiftForwardMapCompSource F
      (𝟙 X) (𝟙 X) B C).hom)
    (cL :=
      ((generalLiftSourceEquivalence F hF f).inv ◁
          (generalLiftForwardMapCompSource F
            (𝟙 X) (𝟙 X) (A × B) C).hom) ≫
        (α_ (generalLiftSourceEquivalence F hF f).inv
          (F.map (canonicalSourceHom (𝟙 X) (A × B)))
          (F.map (canonicalSourceHom (𝟙 X) C))).inv)
    (cR :=
      ((generalLiftSourceEquivalence F hF f).inv ◁
          (generalLiftForwardMapCompSource F
            (𝟙 X) (𝟙 X) A (B × C)).hom) ≫
        (α_ (generalLiftSourceEquivalence F hF f).inv
          (F.map (canonicalSourceHom (𝟙 X) A))
          (F.map (canonicalSourceHom (𝟙 X) (B × C)))).inv)
    (aP := (generalLiftSourceEquivalence F hF f).inv ◁
      F.map₂ (canonicalSourceTwoCell (𝟙 X)
        (MonoidalCategory.associator A B C).hom))
    (aQ := (generalLiftPrelaxFunctor F hF).map₂
      (canonicalInverseTwoCell f
        (MonoidalCategory.associator A B C).hom))
    (ha := generalLiftMap₂InverseTransport F hF f hf
      (MonoidalCategory.associator A B C).hom)
    (hc := generalLiftInverseRetainedMapCompSource_associativity
      F hF f A B C)

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
    generalLiftInverseRetainedMapCompTransport F hF f hf A B

theorem generalLiftMapCompInverseRetained_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftMapCompInverseRetained F hF f hf A B).hom =
      (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseRetainedCompositionComparison f A B).hom ≫
        (generalLiftInverseRetainedMapCompTransport F hF f hf A B).hom := by
  rfl

/-- The complete inverse-then-retained composition comparison is natural in
retained-coordinate 2-cells on its right factor. -/
theorem generalLiftMapCompInverseRetained_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseHom f A ◁
            canonicalForwardTwoCell (𝟙 X) η) ≫
      (generalLiftMapCompInverseRetained F hF f hf A C).hom =
    (generalLiftMapCompInverseRetained F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A) ◁
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 X) η)) := by
  rw [generalLiftMapCompInverseRetained_hom,
    generalLiftMapCompInverseRetained_hom]
  exact comp_naturality_of_squares
    (generalLiftInverseRetainedMapCompTarget_naturality_right
      F hF f A η)
    (generalLiftInverseRetainedMapCompTransport_naturality_right
      F hF f hf A η)

/-- The complete inverse-then-retained composition comparison is natural in
retained-coordinate 2-cells on its inverse factor. -/
theorem generalLiftMapCompInverseRetained_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f η ▷
            canonicalForwardHom (𝟙 X) B) ≫
      (generalLiftMapCompInverseRetained F hF f hf C B).hom =
    (generalLiftMapCompInverseRetained F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f η) ▷
        (generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom (𝟙 X) B)) := by
  rw [generalLiftMapCompInverseRetained_hom,
    generalLiftMapCompInverseRetained_hom]
  exact comp_naturality_of_squares
    (generalLiftInverseRetainedMapCompTarget_naturality_left F hF f η B)
    (generalLiftInverseRetainedMapCompTransport_naturality_left
      F hF f hf η B)

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

/-- At the retained identity, generator/retained normalization is the
canonical source compositor followed by the retained right unitor. -/
theorem canonicalSourceGeneratorRetainedComparison_unit
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) :
    (canonicalSourceGeneratorRetainedComparison f
        (𝟙 (MonoidalSingleObj.star (Type)))).hom =
      (canonicalSourceCompositionComparison f (𝟙 Y)
          (𝟙 (MonoidalSingleObj.star (Type)))
          (𝟙 (MonoidalSingleObj.star (Type)))).hom ≫
        canonicalSourceTwoCell f
          (MonoidalCategory.rightUnitor
            (𝟙 (MonoidalSingleObj.star (Type)))).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- At the retained identity, retained/generator normalization is the
canonical source compositor followed by the retained left unitor. -/
theorem canonicalSourceRetainedGeneratorComparison_unit
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) :
    (canonicalSourceRetainedGeneratorComparison f
        (𝟙 (MonoidalSingleObj.star (Type)))).hom =
      (canonicalSourceCompositionComparison (𝟙 X) f
          (𝟙 (MonoidalSingleObj.star (Type)))
          (𝟙 (MonoidalSingleObj.star (Type)))).hom ≫
        canonicalSourceTwoCell f
          (MonoidalCategory.leftUnitor
            (𝟙 (MonoidalSingleObj.star (Type)))).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- Generator/retained normalization factors as the ordinary normalized
source compositor followed by the cartesian left unitor. -/
theorem canonicalSourceGeneratorRetainedComparison_factorization
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (canonicalSourceGeneratorRetainedComparison f A).hom =
      (canonicalSourceCompositionComparison f (𝟙 Y)
        (𝟙 (MonoidalSingleObj.star (Type))) A).hom ≫
      canonicalSourceTwoCell f (MonoidalCategory.leftUnitor A).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- Inverse orientation of generator/retained factorization. -/
theorem canonicalSourceGeneratorRetainedComparison_factorization_inv
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (canonicalSourceGeneratorRetainedComparison f A).inv =
      canonicalSourceTwoCell f (MonoidalCategory.leftUnitor A).inv ≫
      (canonicalSourceCompositionComparison f (𝟙 Y)
        (𝟙 (MonoidalSingleObj.star (Type))) A).inv := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- Retained/generator normalization factors as the ordinary normalized
source compositor followed by the cartesian right unitor. -/
theorem canonicalSourceRetainedGeneratorComparison_factorization
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (canonicalSourceRetainedGeneratorComparison f A).hom =
      (canonicalSourceCompositionComparison (𝟙 X) f A
        (𝟙 (MonoidalSingleObj.star (Type)))).hom ≫
      canonicalSourceTwoCell f (MonoidalCategory.rightUnitor A).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- Inverse orientation of retained/generator factorization. -/
theorem canonicalSourceRetainedGeneratorComparison_factorization_inv
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (canonicalSourceRetainedGeneratorComparison f A).inv =
      canonicalSourceTwoCell f (MonoidalCategory.rightUnitor A).inv ≫
      (canonicalSourceCompositionComparison (𝟙 X) f A
        (𝟙 (MonoidalSingleObj.star (Type)))).inv := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- The source pseudofunctor preserves generator/retained factorization. -/
theorem generalLiftSourceGeneratorRetainedComparison_factorization
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    F.map₂ (canonicalSourceGeneratorRetainedComparison f A).hom =
      F.map₂ (canonicalSourceCompositionComparison f (𝟙 Y)
        (𝟙 (MonoidalSingleObj.star (Type))) A).hom ≫
      F.map₂ (canonicalSourceTwoCell f
        (MonoidalCategory.leftUnitor A).hom) := by
  simpa only [F.map₂_comp] using congrArg (fun η ↦ F.map₂ η)
    (canonicalSourceGeneratorRetainedComparison_factorization f A)

/-- The source pseudofunctor preserves inverse generator/retained
factorization. -/
theorem generalLiftSourceGeneratorRetainedComparison_factorization_inv
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    F.map₂ (canonicalSourceGeneratorRetainedComparison f A).inv =
      F.map₂ (canonicalSourceTwoCell f
        (MonoidalCategory.leftUnitor A).inv) ≫
      F.map₂ (canonicalSourceCompositionComparison f (𝟙 Y)
        (𝟙 (MonoidalSingleObj.star (Type))) A).inv := by
  simpa only [F.map₂_comp] using congrArg (fun η ↦ F.map₂ η)
    (canonicalSourceGeneratorRetainedComparison_factorization_inv f A)

/-- The source pseudofunctor preserves retained/generator factorization. -/
theorem generalLiftSourceRetainedGeneratorComparison_factorization
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    F.map₂ (canonicalSourceRetainedGeneratorComparison f A).hom =
      F.map₂ (canonicalSourceCompositionComparison (𝟙 X) f A
        (𝟙 (MonoidalSingleObj.star (Type)))).hom ≫
      F.map₂ (canonicalSourceTwoCell f
        (MonoidalCategory.rightUnitor A).hom) := by
  simpa only [F.map₂_comp] using congrArg (fun η ↦ F.map₂ η)
    (canonicalSourceRetainedGeneratorComparison_factorization f A)

/-- The source pseudofunctor preserves inverse retained/generator
factorization. -/
theorem generalLiftSourceRetainedGeneratorComparison_factorization_inv
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    F.map₂ (canonicalSourceRetainedGeneratorComparison f A).inv =
      F.map₂ (canonicalSourceTwoCell f
        (MonoidalCategory.rightUnitor A).inv) ≫
      F.map₂ (canonicalSourceCompositionComparison (𝟙 X) f A
        (𝟙 (MonoidalSingleObj.star (Type)))).inv := by
  simpa only [F.map₂_comp] using congrArg (fun η ↦ F.map₂ η)
    (canonicalSourceRetainedGeneratorComparison_factorization_inv f A)

/-- The source 2-cell for the inverse left unitor on a retained product
decomposes into the inverse left unitor on the first factor followed by the
associator. -/
theorem canonicalSourceLeftUnitor_tensor_inv
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    canonicalSourceTwoCell f (MonoidalCategory.leftUnitor (A × B)).inv =
      canonicalSourceTwoCell f
          (CategoryTheory.MonoidalCategory.tensorHom
            (MonoidalCategory.leftUnitor A).inv (𝟙 B)) ≫
        canonicalSourceTwoCell f
          (MonoidalCategory.associator
            (𝟙 (MonoidalSingleObj.star (Type))) A B).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · exact MonoidalCategory.leftUnitor_tensor_inv A B

/-- The source 2-cell for the inverse right unitor on a retained product
decomposes through the second factor and inverse associator. -/
theorem canonicalSourceRightUnitor_tensor_inv
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    canonicalSourceTwoCell f (MonoidalCategory.rightUnitor (A × B)).inv =
      canonicalSourceTwoCell f
          (CategoryTheory.MonoidalCategory.tensorHom
            (𝟙 A) (MonoidalCategory.rightUnitor B).inv) ≫
        canonicalSourceTwoCell f
          (MonoidalCategory.associator A B
            (𝟙 (MonoidalSingleObj.star (Type)))).inv := by
  apply Prod.ext
  · apply Subsingleton.elim
  · exact MonoidalCategory.rightUnitor_tensor_inv A B

/-- Mapping preserves the inverse-left-unitor product decomposition. -/
theorem generalLiftSourceLeftUnitor_tensor_inv
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    F.map₂ (canonicalSourceTwoCell f
      (MonoidalCategory.leftUnitor (A × B)).inv) =
      F.map₂ (canonicalSourceTwoCell f
        (CategoryTheory.MonoidalCategory.tensorHom
          (MonoidalCategory.leftUnitor A).inv (𝟙 B))) ≫
      F.map₂ (canonicalSourceTwoCell f
        (MonoidalCategory.associator
          (𝟙 (MonoidalSingleObj.star (Type))) A B).hom) := by
  simpa only [F.map₂_comp] using congrArg (fun η ↦ F.map₂ η)
    (canonicalSourceLeftUnitor_tensor_inv f A B)

/-- Mapping preserves the inverse-right-unitor product decomposition. -/
theorem generalLiftSourceRightUnitor_tensor_inv
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    F.map₂ (canonicalSourceTwoCell f
      (MonoidalCategory.rightUnitor (A × B)).inv) =
      F.map₂ (canonicalSourceTwoCell f
        (CategoryTheory.MonoidalCategory.tensorHom
          (𝟙 A) (MonoidalCategory.rightUnitor B).inv)) ≫
      F.map₂ (canonicalSourceTwoCell f
        (MonoidalCategory.associator A B
          (𝟙 (MonoidalSingleObj.star (Type)))).inv) := by
  simpa only [F.map₂_comp] using congrArg (fun η ↦ F.map₂ η)
    (canonicalSourceRightUnitor_tensor_inv f A B)

/-- Generator/retained normalization is multiplicative in the retained
coordinate.  Decomposing `A × B`, normalizing the first retained factor, and
then recomposing agrees with normalizing the product at once. -/
theorem canonicalSourceGeneratorRetainedComparison_tensor
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star (Type))) ◁
        (canonicalSourceCompositionComparison
          (𝟙 Y) (𝟙 Y) A B).inv) ≫
      (α_ (canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star (Type))))
        (canonicalSourceHom (𝟙 Y) A)
        (canonicalSourceHom (𝟙 Y) B)).inv ≫
      ((canonicalSourceGeneratorRetainedComparison f A).hom ▷
        canonicalSourceHom (𝟙 Y) B) ≫
      (canonicalSourceCompositionComparison f (𝟙 Y) A B).hom =
    (canonicalSourceGeneratorRetainedComparison f (A × B)).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- Retained/generator normalization is multiplicative in the retained
coordinate.  Decomposing the retained product and normalizing its second
factor agrees with normalizing the product at once. -/
theorem canonicalSourceRetainedGeneratorComparison_tensor
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    ((canonicalSourceCompositionComparison
          (𝟙 X) (𝟙 X) A B).inv ▷
        canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star (Type)))) ≫
      (α_ (canonicalSourceHom (𝟙 X) A)
        (canonicalSourceHom (𝟙 X) B)
        (canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star (Type))))).hom ≫
      (canonicalSourceHom (𝟙 X) A ◁
        (canonicalSourceRetainedGeneratorComparison f B).hom) ≫
      (canonicalSourceCompositionComparison (𝟙 X) f A B).hom =
    (canonicalSourceRetainedGeneratorComparison f (A × B)).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- Mapping generator/retained multiplicativity through an arbitrary source
pseudofunctor preserves its four-stage vertical composite. -/
theorem generalLiftSourceGeneratorRetainedComparison_tensor
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    F.map₂ (canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star (Type))) ◁
        (canonicalSourceCompositionComparison
          (𝟙 Y) (𝟙 Y) A B).inv) ≫
      F.map₂ (α_ (canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star (Type))))
        (canonicalSourceHom (𝟙 Y) A)
        (canonicalSourceHom (𝟙 Y) B)).inv ≫
      F.map₂ ((canonicalSourceGeneratorRetainedComparison f A).hom ▷
        canonicalSourceHom (𝟙 Y) B) ≫
      F.map₂ (canonicalSourceCompositionComparison f (𝟙 Y) A B).hom =
    F.map₂ (canonicalSourceGeneratorRetainedComparison f (A × B)).hom := by
  simpa only [F.map₂_comp] using congrArg (fun η ↦ F.map₂ η)
    (canonicalSourceGeneratorRetainedComparison_tensor f A B)

/-- Mapping retained/generator multiplicativity through an arbitrary source
pseudofunctor preserves its four-stage vertical composite. -/
theorem generalLiftSourceRetainedGeneratorComparison_tensor
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    F.map₂ ((canonicalSourceCompositionComparison
          (𝟙 X) (𝟙 X) A B).inv ▷
        canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star (Type)))) ≫
      F.map₂ (α_ (canonicalSourceHom (𝟙 X) A)
        (canonicalSourceHom (𝟙 X) B)
        (canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star (Type))))).hom ≫
      F.map₂ (canonicalSourceHom (𝟙 X) A ◁
        (canonicalSourceRetainedGeneratorComparison f B).hom) ≫
      F.map₂ (canonicalSourceCompositionComparison (𝟙 X) f A B).hom =
    F.map₂ (canonicalSourceRetainedGeneratorComparison f (A × B)).hom := by
  simpa only [F.map₂_comp] using congrArg (fun η ↦ F.map₂ η)
    (canonicalSourceRetainedGeneratorComparison_tensor f A B)

/-- Inverse orientation of generator/retained multiplicativity. -/
theorem canonicalSourceGeneratorRetainedComparison_tensor_inv
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (canonicalSourceGeneratorRetainedComparison f (A × B)).inv =
      (canonicalSourceCompositionComparison f (𝟙 Y) A B).inv ≫
      ((canonicalSourceGeneratorRetainedComparison f A).inv ▷
        canonicalSourceHom (𝟙 Y) B) ≫
      (α_ (canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star (Type))))
        (canonicalSourceHom (𝟙 Y) A)
        (canonicalSourceHom (𝟙 Y) B)).hom ≫
      (canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star (Type))) ◁
        (canonicalSourceCompositionComparison
          (𝟙 Y) (𝟙 Y) A B).hom) := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- Inverse orientation of retained/generator multiplicativity. -/
theorem canonicalSourceRetainedGeneratorComparison_tensor_inv
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (canonicalSourceRetainedGeneratorComparison f (A × B)).inv =
      (canonicalSourceCompositionComparison (𝟙 X) f A B).inv ≫
      (canonicalSourceHom (𝟙 X) A ◁
        (canonicalSourceRetainedGeneratorComparison f B).inv) ≫
      (α_ (canonicalSourceHom (𝟙 X) A)
        (canonicalSourceHom (𝟙 X) B)
        (canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star (Type))))).inv ≫
      ((canonicalSourceCompositionComparison
          (𝟙 X) (𝟙 X) A B).hom ▷
        canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star (Type)))) := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- The source pseudofunctor preserves inverse generator/retained
multiplicativity. -/
theorem generalLiftSourceGeneratorRetainedComparison_tensor_inv
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    F.map₂ (canonicalSourceGeneratorRetainedComparison f (A × B)).inv =
      F.map₂ (canonicalSourceCompositionComparison f (𝟙 Y) A B).inv ≫
      F.map₂ ((canonicalSourceGeneratorRetainedComparison f A).inv ▷
        canonicalSourceHom (𝟙 Y) B) ≫
      F.map₂ (α_ (canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star (Type))))
        (canonicalSourceHom (𝟙 Y) A)
        (canonicalSourceHom (𝟙 Y) B)).hom ≫
      F.map₂ (canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star (Type))) ◁
        (canonicalSourceCompositionComparison
          (𝟙 Y) (𝟙 Y) A B).hom) := by
  simpa only [F.map₂_comp] using congrArg (fun η ↦ F.map₂ η)
    (canonicalSourceGeneratorRetainedComparison_tensor_inv f A B)

/-- The source pseudofunctor preserves inverse retained/generator
multiplicativity. -/
theorem generalLiftSourceRetainedGeneratorComparison_tensor_inv
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    F.map₂ (canonicalSourceRetainedGeneratorComparison f (A × B)).inv =
      F.map₂ (canonicalSourceCompositionComparison (𝟙 X) f A B).inv ≫
      F.map₂ (canonicalSourceHom (𝟙 X) A ◁
        (canonicalSourceRetainedGeneratorComparison f B).inv) ≫
      F.map₂ (α_ (canonicalSourceHom (𝟙 X) A)
        (canonicalSourceHom (𝟙 X) B)
        (canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star (Type))))).inv ≫
      F.map₂ ((canonicalSourceCompositionComparison
          (𝟙 X) (𝟙 X) A B).hom ▷
        canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star (Type)))) := by
  simpa only [F.map₂_comp] using congrArg (fun η ↦ F.map₂ η)
    (canonicalSourceRetainedGeneratorComparison_tensor_inv f A B)

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

/-- The retained/retained/inverse target comparisons satisfy their
three-fold associativity square.  The two retained coordinates compose first
on the left, while the right route slides their product across the freely
adjoined inverse. -/
theorem canonicalRetainedInverseCompositionComparison_associativity
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    ((canonicalForwardCompositionComparison
          (𝟙 Y) (𝟙 Y) A B).hom ▷ canonicalInverseHom f C) ≫
        (canonicalRetainedInverseCompositionComparison
          f (A × B) C).hom ≫
        canonicalInverseTwoCell f
          (MonoidalCategory.associator A B C).hom =
      (α_ (canonicalForwardHom (𝟙 Y) A)
          (canonicalForwardHom (𝟙 Y) B)
          (canonicalInverseHom f C)).hom ≫
        (canonicalForwardHom (𝟙 Y) A ◁
          (canonicalRetainedInverseCompositionComparison f B C).hom) ≫
        (canonicalRetainedInverseCompositionComparison
          f A (B × C)).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- Applying the arbitrary target action preserves the
retained/retained/inverse target associativity square. -/
theorem generalLiftRetainedInverseMapCompTarget_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          ((canonicalForwardCompositionComparison
              (𝟙 Y) (𝟙 Y) A B).hom ▷ canonicalInverseHom f C) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalRetainedInverseCompositionComparison
            f (A × B) C).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f
            (MonoidalCategory.associator A B C).hom) =
      (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalForwardHom (𝟙 Y) A)
            (canonicalForwardHom (𝟙 Y) B)
            (canonicalInverseHom f C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardHom (𝟙 Y) A ◁
            (canonicalRetainedInverseCompositionComparison f B C).hom) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalRetainedInverseCompositionComparison
            f A (B × C)).hom := by
  simpa only [(generalLiftPrelaxFunctor F hF).map₂_comp] using
    congrArg (fun η => (generalLiftPrelaxFunctor F hF).map₂ η)
      (canonicalRetainedInverseCompositionComparison_associativity
        f A B C)

/-- Retained/inverse/retained target comparisons satisfy their mixed
three-fold associativity square. -/
theorem canonicalRetainedInverseRetainedComparison_associativity
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    ((canonicalRetainedInverseCompositionComparison f A B).hom ▷
          canonicalForwardHom (𝟙 X) C) ≫
        (canonicalInverseRetainedCompositionComparison
          f (A × B) C).hom ≫
        canonicalInverseTwoCell f
          (MonoidalCategory.associator A B C).hom =
      (α_ (canonicalForwardHom (𝟙 Y) A)
          (canonicalInverseHom f B)
          (canonicalForwardHom (𝟙 X) C)).hom ≫
        (canonicalForwardHom (𝟙 Y) A ◁
          (canonicalInverseRetainedCompositionComparison f B C).hom) ≫
        (canonicalRetainedInverseCompositionComparison
          f A (B × C)).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- Applying the arbitrary target action preserves the mixed
retained/inverse/retained target associativity square. -/
theorem generalLiftRetainedInverseRetainedMapCompTarget_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          ((canonicalRetainedInverseCompositionComparison f A B).hom ▷
            canonicalForwardHom (𝟙 X) C) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseRetainedCompositionComparison
            f (A × B) C).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f
            (MonoidalCategory.associator A B C).hom) =
      (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalForwardHom (𝟙 Y) A)
            (canonicalInverseHom f B)
            (canonicalForwardHom (𝟙 X) C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardHom (𝟙 Y) A ◁
            (canonicalInverseRetainedCompositionComparison f B C).hom) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalRetainedInverseCompositionComparison
            f A (B × C)).hom := by
  simpa only [(generalLiftPrelaxFunctor F hF).map₂_comp] using
    congrArg (fun η => (generalLiftPrelaxFunctor F hF).map₂ η)
      (canonicalRetainedInverseRetainedComparison_associativity
        f A B C)

/-- The retained-then-inverse target comparison is natural in the inverse
factor's retained coordinate. -/
theorem canonicalRetainedInverseCompositionComparison_naturality_right
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) {B C : Type} (η : B ⟶ C) :
    (canonicalForwardHom (𝟙 Y) A ◁
          canonicalInverseTwoCell f η) ≫
        (canonicalRetainedInverseCompositionComparison f A C).hom =
      (canonicalRetainedInverseCompositionComparison f A B).hom ≫
        canonicalInverseTwoCell f
          (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η) := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- The retained-then-inverse target comparison is natural in the retained
factor's coordinate. -/
theorem canonicalRetainedInverseCompositionComparison_naturality_left
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A C : Type} (η : A ⟶ C) (B : Type) :
    (canonicalForwardTwoCell (𝟙 Y) η ▷
          canonicalInverseHom f B) ≫
        (canonicalRetainedInverseCompositionComparison f C B).hom =
      (canonicalRetainedInverseCompositionComparison f A B).hom ≫
        canonicalInverseTwoCell f
          (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B)) := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- Mapping right naturality of the retained-then-inverse target comparison
through the arbitrary lift preserves its vertical composite. -/
theorem generalLiftRetainedInverseMapCompTarget_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) {B C : Type} (η : B ⟶ C) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardHom (𝟙 Y) A ◁
            canonicalInverseTwoCell f η) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalRetainedInverseCompositionComparison f A C).hom =
      (generalLiftPrelaxFunctor F hF).map₂
          (canonicalRetainedInverseCompositionComparison f A B).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f
            (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η)) := by
  rw [← (generalLiftPrelaxFunctor F hF).map₂_comp,
    canonicalRetainedInverseCompositionComparison_naturality_right,
    (generalLiftPrelaxFunctor F hF).map₂_comp]

/-- Mapping left naturality of the retained-then-inverse target comparison
through the arbitrary lift preserves its vertical composite. -/
theorem generalLiftRetainedInverseMapCompTarget_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A C : Type} (η : A ⟶ C) (B : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 Y) η ▷
            canonicalInverseHom f B) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalRetainedInverseCompositionComparison f C B).hom =
      (generalLiftPrelaxFunctor F hF).map₂
          (canonicalRetainedInverseCompositionComparison f A B).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f
            (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B))) := by
  rw [← (generalLiftPrelaxFunctor F hF).map₂_comp,
    canonicalRetainedInverseCompositionComparison_naturality_left,
    (generalLiftPrelaxFunctor F hF).map₂_comp]

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

/-- The source generator-then-retained comparison is natural in its retained
coordinate. -/
theorem canonicalSourceGeneratorRetainedComparison_naturality
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    (canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star (Type))) ◁
        canonicalSourceTwoCell (𝟙 Y) η) ≫
      (canonicalSourceGeneratorRetainedComparison f B).hom =
    (canonicalSourceGeneratorRetainedComparison f A).hom ≫
      canonicalSourceTwoCell f η := by
  apply Prod.ext
  · apply Subsingleton.elim
  · exact leftUnitor_naturality (B := Cell) η

/-- The inverse of the source generator-then-retained comparison is natural
in its retained coordinate. -/
theorem canonicalSourceGeneratorRetainedComparison_naturality_inv
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    canonicalSourceTwoCell f η ≫
        (canonicalSourceGeneratorRetainedComparison f B).inv =
      (canonicalSourceGeneratorRetainedComparison f A).inv ≫
        (canonicalSourceHom f
            (𝟙 (MonoidalSingleObj.star (Type))) ◁
          canonicalSourceTwoCell (𝟙 Y) η) :=
  iso_inv_naturality_of_square
    (canonicalSourceGeneratorRetainedComparison f A)
    (canonicalSourceGeneratorRetainedComparison f B)
    (canonicalSourceGeneratorRetainedComparison_naturality f η)

/-- The source retained-then-generator comparison is natural in its retained
coordinate. -/
theorem canonicalSourceRetainedGeneratorComparison_naturality
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    (canonicalSourceTwoCell (𝟙 X) η ▷
        canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star (Type)))) ≫
      (canonicalSourceRetainedGeneratorComparison f B).hom =
    (canonicalSourceRetainedGeneratorComparison f A).hom ≫
      canonicalSourceTwoCell f η := by
  apply Prod.ext
  · apply Subsingleton.elim
  · exact rightUnitor_naturality (B := Cell) η

/-- The inverse of the source retained-then-generator comparison is natural
in its retained coordinate. -/
theorem canonicalSourceRetainedGeneratorComparison_naturality_inv
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    canonicalSourceTwoCell f η ≫
        (canonicalSourceRetainedGeneratorComparison f B).inv =
      (canonicalSourceRetainedGeneratorComparison f A).inv ≫
        (canonicalSourceTwoCell (𝟙 X) η ▷
          canonicalSourceHom f
            (𝟙 (MonoidalSingleObj.star (Type)))) :=
  iso_inv_naturality_of_square
    (canonicalSourceRetainedGeneratorComparison f A)
    (canonicalSourceRetainedGeneratorComparison f B)
    (canonicalSourceRetainedGeneratorComparison_naturality f η)

/-- Mapping inverse naturality of the source generator-then-retained
comparison preserves its vertical composite. -/
theorem generalLiftSourceGeneratorRetainedComparison_naturality_inv
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    F.map₂ (canonicalSourceTwoCell f η) ≫
        F.map₂ (canonicalSourceGeneratorRetainedComparison f B).inv =
      F.map₂ (canonicalSourceGeneratorRetainedComparison f A).inv ≫
        F.map₂ (canonicalSourceHom f
            (𝟙 (MonoidalSingleObj.star (Type))) ◁
          canonicalSourceTwoCell (𝟙 Y) η) := by
  rw [← F.map₂_comp,
    canonicalSourceGeneratorRetainedComparison_naturality_inv,
    F.map₂_comp]

/-- Mapping inverse naturality of the source retained-then-generator
comparison preserves its vertical composite. -/
theorem generalLiftSourceRetainedGeneratorComparison_naturality_inv
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    F.map₂ (canonicalSourceTwoCell f η) ≫
        F.map₂ (canonicalSourceRetainedGeneratorComparison f B).inv =
      F.map₂ (canonicalSourceRetainedGeneratorComparison f A).inv ≫
        F.map₂ (canonicalSourceTwoCell (𝟙 X) η ▷
          canonicalSourceHom f
            (𝟙 (MonoidalSingleObj.star (Type)))) := by
  rw [← F.map₂_comp,
    canonicalSourceRetainedGeneratorComparison_naturality_inv,
    F.map₂_comp]

/-- The hom of the forward source factorization is its mapped comparison
followed by the source pseudofunctor compositor. -/
theorem generalLiftForwardFactorizationSource_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (generalLiftForwardFactorizationSource F hF f A).hom =
      F.map₂ (canonicalSourceGeneratorRetainedComparison f A).inv ≫
        (F.mapComp
          (canonicalSourceHom f
            (𝟙 (MonoidalSingleObj.star (Type))))
          (canonicalSourceHom (𝟙 Y) A)).hom := by
  rfl

/-- The forward factorization hom is a mapped left-unitor inverse followed by
the ordinary normalized source compositor. -/
theorem generalLiftForwardFactorizationSource_hom_unitor
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (generalLiftForwardFactorizationSource F hF f A).hom =
      F.map₂ (canonicalSourceTwoCell f
        (MonoidalCategory.leftUnitor A).inv) ≫
      (generalLiftForwardMapCompSource F f (𝟙 Y)
        (𝟙 (MonoidalSingleObj.star (Type))) A).hom := by
  rw [generalLiftForwardFactorizationSource_hom,
    generalLiftSourceGeneratorRetainedComparison_factorization_inv]
  rw [Category.assoc]
  congr 1

/-- The forward factorization hom can be written with the explicitly
right-identity-normalized compositor.  The inserted equality transport is
canonical and contracts to the original unitor formula. -/
theorem generalLiftForwardFactorizationSource_hom_normalized
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (generalLiftForwardFactorizationSource F hF f A).hom =
      F.map₂ (canonicalSourceTwoCell f
        (MonoidalCategory.leftUnitor A).inv) ≫
      (generalLiftForwardMapCompSourceRightIdentity F f
        (𝟙 (MonoidalSingleObj.star Type)) A).hom := by
  rw [generalLiftForwardFactorizationSource_hom_unitor,
    generalLiftForwardMapCompSourceRightIdentity_hom]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Forward source factorization is multiplicative in retained data.  The
strictly normalized statement exposes the initial retained compositor, the
factorization of the first factor, target reassociation, and the inverse
retained compositor as one exact square. -/
theorem generalLiftForwardFactorizationSource_tensor
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftForwardFactorizationSource F hF f (A × B)).hom =
      (generalLiftForwardMapCompSourceRightIdentity F f A B).hom ≫
      ((generalLiftForwardFactorizationSource F hF f A).hom ▷
        F.map (canonicalSourceHom (𝟙 Y) B)) ≫
      (α_ (generalLiftSourceEquivalence F hF f).hom
        (F.map (canonicalSourceHom (𝟙 Y) A))
        (F.map (canonicalSourceHom (𝟙 Y) B))).hom ≫
      ((generalLiftSourceEquivalence F hF f).hom ◁
        (generalLiftForwardMapCompSourceRightIdentity F
          (𝟙 Y) A B).inv) := by
  rw [generalLiftForwardFactorizationSource_hom_normalized,
    generalLiftForwardFactorizationSource_hom_normalized,
    generalLiftSourceLeftUnitor_tensor_inv]
  have hnat :=
    generalLiftForwardMapCompSourceRightIdentity_naturality_left F
      f (MonoidalCategory.leftUnitor A).inv B
  have hassoc :=
    generalLiftForwardMapCompSourceRightIdentity_associativity F f A B
  simp only [Bicategory.comp_whiskerRight,
    generalLiftSourceEquivalence_hom, Category.assoc]
  slice_rhs 1 2 => rw [← hnat]
  have hassocInv := congrArg
    (fun k => k ≫
      (F.map (canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star Type))) ◁
        (generalLiftForwardMapCompSourceRightIdentity F
          (𝟙 Y) A B).inv))
    hassoc
  simp only [Category.assoc] at hassocInv
  simp at hassocInv
  have hfinal := congrArg
    (fun k =>
      F.map₂ (canonicalSourceTwoCell f
        (CategoryTheory.MonoidalCategory.tensorHom
          (MonoidalCategory.leftUnitor A).inv (𝟙 B))) ≫ k)
    hassocInv
  simp only [Category.assoc] at hfinal ⊢
  exact eq_of_heq (heq_of_eq hfinal)

set_option backward.isDefEq.respectTransparency false in
/-- Inverse expansion of the normalized forward factorization. -/
theorem generalLiftForwardFactorizationSource_inv_normalized
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (generalLiftForwardFactorizationSource F hF f A).inv =
      (generalLiftForwardMapCompSourceRightIdentity F f
        (𝟙 (MonoidalSingleObj.star Type)) A).inv ≫
      F.map₂ (canonicalSourceTwoCell f
        (MonoidalCategory.leftUnitor A).hom) := by
  let u : canonicalSourceHom f A ≅
      canonicalSourceHom f
        ((𝟙 (MonoidalSingleObj.star Type)) × A) :=
    Iso.prod (Iso.refl _) (MonoidalCategory.leftUnitor A).symm
  let e := F.map₂Iso u ≪≫
    generalLiftForwardMapCompSourceRightIdentity F f
      (𝟙 (MonoidalSingleObj.star Type)) A
  have he : generalLiftForwardFactorizationSource F hF f A = e := by
    apply Iso.ext
    change (generalLiftForwardFactorizationSource F hF f A).hom =
      F.map₂ (canonicalSourceTwoCell f
        (MonoidalCategory.leftUnitor A).inv) ≫
      (generalLiftForwardMapCompSourceRightIdentity F f
        (𝟙 (MonoidalSingleObj.star Type)) A).hom
    exact generalLiftForwardFactorizationSource_hom_normalized F hF f A
  rw [he]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Inverse orientation of forward-factorization multiplicativity. -/
theorem generalLiftForwardFactorizationSource_tensor_inv
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftForwardFactorizationSource F hF f (A × B)).inv =
      ((generalLiftSourceEquivalence F hF f).hom ◁
        (generalLiftForwardMapCompSourceRightIdentity F
          (𝟙 Y) A B).hom) ≫
      (α_ (generalLiftSourceEquivalence F hF f).hom
        (F.map (canonicalSourceHom (𝟙 Y) A))
        (F.map (canonicalSourceHom (𝟙 Y) B))).inv ≫
      ((generalLiftForwardFactorizationSource F hF f A).inv ▷
        F.map (canonicalSourceHom (𝟙 Y) B)) ≫
      (generalLiftForwardMapCompSourceRightIdentity F f A B).inv := by
  let e :=
    generalLiftForwardMapCompSourceRightIdentity F f A B ≪≫
      whiskerRightIso
        (generalLiftForwardFactorizationSource F hF f A)
        (F.map (canonicalSourceHom (𝟙 Y) B)) ≪≫
      (α_ (generalLiftSourceEquivalence F hF f).hom
        (F.map (canonicalSourceHom (𝟙 Y) A))
        (F.map (canonicalSourceHom (𝟙 Y) B))) ≪≫
      whiskerLeftIso (generalLiftSourceEquivalence F hF f).hom
        (generalLiftForwardMapCompSourceRightIdentity F
          (𝟙 Y) A B).symm
  have he : generalLiftForwardFactorizationSource F hF f (A × B) = e := by
    apply Iso.ext
    simpa [e] using
      (generalLiftForwardFactorizationSource_tensor F hF f A B)
  rw [he]
  simp [e]

/-- The hom of the retained-forward source factorization is its mapped
comparison followed by the source pseudofunctor compositor. -/
theorem generalLiftRetainedForwardFactorizationSource_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (generalLiftRetainedForwardFactorizationSource F hF f A).hom =
      F.map₂ (canonicalSourceRetainedGeneratorComparison f A).inv ≫
        (F.mapComp (canonicalSourceHom (𝟙 X) A)
          (canonicalSourceHom f
            (𝟙 (MonoidalSingleObj.star (Type))))).hom := by
  rfl

/-- The retained-forward factorization hom is a mapped right-unitor inverse
followed by the ordinary normalized source compositor. -/
theorem generalLiftRetainedForwardFactorizationSource_hom_unitor
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (generalLiftRetainedForwardFactorizationSource F hF f A).hom =
      F.map₂ (canonicalSourceTwoCell f
        (MonoidalCategory.rightUnitor A).inv) ≫
      (generalLiftForwardMapCompSource F (𝟙 X) f A
        (𝟙 (MonoidalSingleObj.star (Type)))).hom := by
  rw [generalLiftRetainedForwardFactorizationSource_hom,
    generalLiftSourceRetainedGeneratorComparison_factorization_inv]
  rw [Category.assoc]
  congr 1

/-- The retained-forward factorization hom can be written with the explicitly
left-identity-normalized compositor. -/
theorem generalLiftRetainedForwardFactorizationSource_hom_normalized
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (generalLiftRetainedForwardFactorizationSource F hF f A).hom =
      F.map₂ (canonicalSourceTwoCell f
        (MonoidalCategory.rightUnitor A).inv) ≫
      (generalLiftForwardMapCompSourceLeftIdentity F f
        A (𝟙 (MonoidalSingleObj.star Type))).hom := by
  rw [generalLiftRetainedForwardFactorizationSource_hom_unitor,
    generalLiftForwardMapCompSourceLeftIdentity_hom]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Retained-forward source factorization is multiplicative in retained data.
This is the left-identity-normalized mirror of
`generalLiftForwardFactorizationSource_tensor`. -/
theorem generalLiftRetainedForwardFactorizationSource_tensor
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftRetainedForwardFactorizationSource F hF f (A × B)).hom =
      (generalLiftForwardMapCompSourceLeftIdentity F f A B).hom ≫
      (F.map (canonicalSourceHom (𝟙 X) A) ◁
        (generalLiftRetainedForwardFactorizationSource F hF f B).hom) ≫
      (α_ (F.map (canonicalSourceHom (𝟙 X) A))
        (F.map (canonicalSourceHom (𝟙 X) B))
        (generalLiftSourceEquivalence F hF f).hom).inv ≫
      ((generalLiftForwardMapCompSourceLeftIdentity F
          (𝟙 X) A B).inv ▷
        (generalLiftSourceEquivalence F hF f).hom) := by
  rw [generalLiftRetainedForwardFactorizationSource_hom_normalized,
    generalLiftRetainedForwardFactorizationSource_hom_normalized,
    generalLiftSourceRightUnitor_tensor_inv]
  have hnat :=
    generalLiftForwardMapCompSourceLeftIdentity_naturality_right F
      f A (MonoidalCategory.rightUnitor B).inv
  have hassoc :=
    generalLiftForwardMapCompSourceLeftIdentity_associativity F f A B
  simp only [Bicategory.whiskerLeft_comp,
    generalLiftSourceEquivalence_hom, Category.assoc]
  slice_rhs 1 2 => rw [← hnat]
  have hassocInv := congrArg
    (fun k =>
      F.map₂ (canonicalSourceTwoCell f
        (MonoidalCategory.associator A B
          (𝟙 (MonoidalSingleObj.star Type))).inv) ≫ k ≫
      (α_ (F.map (canonicalSourceHom (𝟙 X) A))
        (F.map (canonicalSourceHom (𝟙 X) B))
        (F.map (canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star Type))))).inv ≫
      ((generalLiftForwardMapCompSourceLeftIdentity F
          (𝟙 X) A B).inv ▷
        F.map (canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star Type)))))
    hassoc
  simp only [Category.assoc] at hassocInv
  simp at hassocInv
  have hreverse := hassocInv.symm
  have hcancel :
      F.map₂ (canonicalSourceTwoCell f
          (MonoidalCategory.associator A B
            (𝟙 (MonoidalSingleObj.star Type))).inv) ≫
        F.map₂ (canonicalSourceTwoCell f
          (MonoidalCategory.associator A B
            (𝟙 (MonoidalSingleObj.star Type))).hom) = 𝟙 _ := by
    rw [← F.map₂_comp]
    have hsource :
        canonicalSourceTwoCell f
              (MonoidalCategory.associator A B
                (𝟙 (MonoidalSingleObj.star Type))).inv ≫
            canonicalSourceTwoCell f
              (MonoidalCategory.associator A B
                (𝟙 (MonoidalSingleObj.star Type))).hom =
          𝟙 _ := by
      apply Prod.ext
      · apply Subsingleton.elim
      · exact (MonoidalCategory.associator A B
          (𝟙 (MonoidalSingleObj.star Type))).inv_hom_id
    rw [hsource, F.map₂_id]
  rw [← Category.assoc] at hreverse
  rw [hcancel] at hreverse
  simp at hreverse
  have hfinal := congrArg
    (fun k =>
      F.map₂ (canonicalSourceTwoCell f
        (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A)
          (MonoidalCategory.rightUnitor B).inv)) ≫ k)
    hreverse
  simp only [Category.assoc] at hfinal ⊢
  exact eq_of_heq (heq_of_eq hfinal)

set_option backward.isDefEq.respectTransparency false in
/-- Inverse orientation of retained-forward factorization multiplicativity. -/
theorem generalLiftRetainedForwardFactorizationSource_tensor_inv
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftRetainedForwardFactorizationSource F hF f (A × B)).inv =
      ((generalLiftForwardMapCompSourceLeftIdentity F (𝟙 X) A B).hom ▷
        (generalLiftSourceEquivalence F hF f).hom) ≫
      (α_ (F.map (canonicalSourceHom (𝟙 X) A))
        (F.map (canonicalSourceHom (𝟙 X) B))
        (generalLiftSourceEquivalence F hF f).hom).hom ≫
      (F.map (canonicalSourceHom (𝟙 X) A) ◁
        (generalLiftRetainedForwardFactorizationSource F hF f B).inv) ≫
      (generalLiftForwardMapCompSourceLeftIdentity F f A B).inv := by
  let e :=
    generalLiftForwardMapCompSourceLeftIdentity F f A B ≪≫
      whiskerLeftIso (F.map (canonicalSourceHom (𝟙 X) A))
        (generalLiftRetainedForwardFactorizationSource F hF f B) ≪≫
      (α_ (F.map (canonicalSourceHom (𝟙 X) A))
        (F.map (canonicalSourceHom (𝟙 X) B))
        (generalLiftSourceEquivalence F hF f).hom).symm ≪≫
      whiskerRightIso
        (generalLiftForwardMapCompSourceLeftIdentity F (𝟙 X) A B).symm
        (generalLiftSourceEquivalence F hF f).hom
  have he :
      generalLiftRetainedForwardFactorizationSource F hF f (A × B) = e := by
    apply Iso.ext
    simpa [e] using
      (generalLiftRetainedForwardFactorizationSource_tensor F hF f A B)
  rw [he]
  simp [e]

set_option backward.isDefEq.respectTransparency false in
/-- The two normalized compositor orders are related by the two forward
factorizations.  This interchange square is the middle coherence needed for
forward-sliding multiplicativity. -/
theorem generalLiftForwardFactorizationSource_interchange
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftForwardMapCompSourceRightIdentity F f A B).inv ≫
        (generalLiftForwardMapCompSourceLeftIdentity F f A B).hom =
      ((generalLiftRetainedForwardFactorizationSource F hF f A).hom ▷
        F.map (canonicalSourceHom (𝟙 Y) B)) ≫
      (α_ (F.map (canonicalSourceHom (𝟙 X) A))
        (generalLiftSourceEquivalence F hF f).hom
        (F.map (canonicalSourceHom (𝟙 Y) B))).hom ≫
      (F.map (canonicalSourceHom (𝟙 X) A) ◁
        (generalLiftForwardFactorizationSource F hF f B).inv) := by
  let U : Type := 𝟙 (MonoidalSingleObj.star Type)
  have hmix := generalLiftForwardMapCompSourceMixedIdentity_associativity
    F f A U B
  have hmiddle := congrArg
    (fun k =>
      (generalLiftForwardMapCompSourceRightIdentity F f
        (A × U) B).inv ≫ k ≫
      (F.map (canonicalSourceHom (𝟙 X) A) ◁
        (generalLiftForwardMapCompSourceRightIdentity F f U B).inv))
    hmix
  simp only [Category.assoc] at hmiddle
  simp at hmiddle
  have hmiddle := hmiddle.symm
  have hnatR :=
    generalLiftForwardMapCompSourceRightIdentity_naturality_left F
      f (MonoidalCategory.rightUnitor A).inv B
  have hnatRInv := iso_inv_naturality_of_square
    (generalLiftForwardMapCompSourceRightIdentity F f A B)
    (generalLiftForwardMapCompSourceRightIdentity F f (A × U) B)
    hnatR
  have hnatL :=
    generalLiftForwardMapCompSourceLeftIdentity_naturality_right F
      f A (MonoidalCategory.leftUnitor B).hom
  have hnatL' :
      F.map₂ (canonicalSourceTwoCell f
            (CategoryTheory.MonoidalCategory.tensorHom
              (𝟙 A) (MonoidalCategory.leftUnitor B).hom)) ≫
          (generalLiftForwardMapCompSourceLeftIdentity F f A B).hom =
        (generalLiftForwardMapCompSourceLeftIdentity F f
            A (U × B)).hom ≫
          F.map (canonicalSourceHom (𝟙 X) A) ◁
            F.map₂ (canonicalSourceTwoCell f
              (MonoidalCategory.leftUnitor B).hom) := by
    exact eq_of_heq (heq_of_eq hnatL)
  rw [generalLiftRetainedForwardFactorizationSource_hom_normalized,
    generalLiftForwardFactorizationSource_inv_normalized]
  simp only [Bicategory.comp_whiskerRight,
    Bicategory.whiskerLeft_comp, generalLiftSourceEquivalence_hom,
    Category.assoc]
  slice_rhs 2 4 => rw [hmiddle]
  slice_rhs 1 2 => rw [hnatRInv]
  slice_rhs 4 5 => rw [← hnatL']
  have htriangle :
      F.map₂ (canonicalSourceTwoCell f
          (CategoryTheory.MonoidalCategory.tensorHom
            (MonoidalCategory.rightUnitor A).inv (𝟙 B))) ≫
        F.map₂ (canonicalSourceTwoCell f
          (MonoidalCategory.associator A U B).hom) ≫
        F.map₂ (canonicalSourceTwoCell f
          (CategoryTheory.MonoidalCategory.tensorHom
            (𝟙 A) (MonoidalCategory.leftUnitor B).hom)) = 𝟙 _ := by
    rw [← F.map₂_comp, ← F.map₂_comp]
    have hsource :
        canonicalSourceTwoCell f
              (CategoryTheory.MonoidalCategory.tensorHom
                (MonoidalCategory.rightUnitor A).inv (𝟙 B)) ≫
            canonicalSourceTwoCell f
              (MonoidalCategory.associator A U B).hom ≫
            canonicalSourceTwoCell f
              (CategoryTheory.MonoidalCategory.tensorHom
                (𝟙 A) (MonoidalCategory.leftUnitor B).hom) =
          𝟙 _ := by
      apply Prod.ext
      · apply Subsingleton.elim
      · have htri :
            MonoidalCategoryStruct.whiskerRight
                  (MonoidalCategory.rightUnitor A).inv B ≫
                (MonoidalCategory.associator A
                  (MonoidalCategoryStruct.tensorUnit Type) B).hom ≫
                MonoidalCategoryStruct.whiskerLeft A
                  (MonoidalCategory.leftUnitor B).hom = 𝟙 _ := by
          rw [← Category.assoc,
            MonoidalCategory.triangle_assoc_comp_right_inv]
          simp
        exact eq_of_heq (heq_of_eq htri)
    rw [hsource, F.map₂_id]
  slice_rhs 2 4 => rw [htriangle]
  have htransport : HEq
      ((generalLiftForwardMapCompSourceRightIdentity F f A B).inv ≫
        (𝟙 (F.map (canonicalSourceHom f
          (MonoidalCategoryStruct.tensorObj A B)))) ≫
        (generalLiftForwardMapCompSourceLeftIdentity F f A B).hom)
      ((generalLiftForwardMapCompSourceRightIdentity F f A B).inv ≫
        (𝟙 (F.map (canonicalSourceHom f (A × B)))) ≫
        (generalLiftForwardMapCompSourceLeftIdentity F f A B).hom) := by
    rfl
  have hgood :
      (generalLiftForwardMapCompSourceRightIdentity F f A B).inv ≫
          (𝟙 (F.map (canonicalSourceHom f (A × B)))) ≫
          (generalLiftForwardMapCompSourceLeftIdentity F f A B).hom =
        (generalLiftForwardMapCompSourceRightIdentity F f A B).inv ≫
          (generalLiftForwardMapCompSourceLeftIdentity F f A B).hom := by
    simp
  exact eq_of_heq ((heq_of_eq hgood).symm.trans htransport.symm)

set_option backward.isDefEq.respectTransparency false in
/-- Inverse orientation of the forward-factorization interchange square. -/
theorem generalLiftForwardFactorizationSource_interchange_inv
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftForwardMapCompSourceLeftIdentity F f A B).inv ≫
        (generalLiftForwardMapCompSourceRightIdentity F f A B).hom =
      (F.map (canonicalSourceHom (𝟙 X) A) ◁
        (generalLiftForwardFactorizationSource F hF f B).hom) ≫
      (α_ (F.map (canonicalSourceHom (𝟙 X) A))
        (generalLiftSourceEquivalence F hF f).hom
        (F.map (canonicalSourceHom (𝟙 Y) B))).inv ≫
      ((generalLiftRetainedForwardFactorizationSource F hF f A).inv ▷
        F.map (canonicalSourceHom (𝟙 Y) B)) := by
  let e :=
    (generalLiftForwardMapCompSourceRightIdentity F f A B).symm ≪≫
      generalLiftForwardMapCompSourceLeftIdentity F f A B
  let q :=
    whiskerRightIso
        (generalLiftRetainedForwardFactorizationSource F hF f A)
        (F.map (canonicalSourceHom (𝟙 Y) B)) ≪≫
      (α_ (F.map (canonicalSourceHom (𝟙 X) A))
        (generalLiftSourceEquivalence F hF f).hom
        (F.map (canonicalSourceHom (𝟙 Y) B))) ≪≫
      whiskerLeftIso (F.map (canonicalSourceHom (𝟙 X) A))
        (generalLiftForwardFactorizationSource F hF f B).symm
  have he : e = q := by
    apply Iso.ext
    simpa [e, q] using
      (generalLiftForwardFactorizationSource_interchange F hF f A B)
  have hi := congrArg (fun k => k.inv) he
  simpa [e, q] using hi

/-- The forward source factorization is natural in retained-coordinate
2-cells. -/
theorem generalLiftForwardFactorizationSource_naturality
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    F.map₂ (canonicalSourceTwoCell f η) ≫
        (generalLiftForwardFactorizationSource F hF f B).hom =
      (generalLiftForwardFactorizationSource F hF f A).hom ≫
        ((generalLiftSourceEquivalence F hF f).hom ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 Y) η)) := by
  rw [generalLiftForwardFactorizationSource_hom,
    generalLiftForwardFactorizationSource_hom]
  exact comp_naturality_of_squares
    (generalLiftSourceGeneratorRetainedComparison_naturality_inv F f η)
    (F.toOplax.mapComp_naturality_right
      (canonicalSourceHom f (𝟙 (MonoidalSingleObj.star (Type))))
      (canonicalSourceTwoCell (𝟙 Y) η))

/-- The retained-forward source factorization is natural in
retained-coordinate 2-cells. -/
theorem generalLiftRetainedForwardFactorizationSource_naturality
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    F.map₂ (canonicalSourceTwoCell f η) ≫
        (generalLiftRetainedForwardFactorizationSource F hF f B).hom =
      (generalLiftRetainedForwardFactorizationSource F hF f A).hom ≫
        (F.map₂ (canonicalSourceTwoCell (𝟙 X) η) ▷
          (generalLiftSourceEquivalence F hF f).hom) := by
  rw [generalLiftRetainedForwardFactorizationSource_hom,
    generalLiftRetainedForwardFactorizationSource_hom]
  exact comp_naturality_of_squares
    (generalLiftSourceRetainedGeneratorComparison_naturality_inv F f η)
    (F.toOplax.mapComp_naturality_left
      (canonicalSourceTwoCell (𝟙 X) η)
      (canonicalSourceHom f (𝟙 (MonoidalSingleObj.star (Type)))))

/-- The hom of forward sliding is the comparison between its two canonical
source factorizations. -/
theorem generalLiftForwardSlidingSource_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (generalLiftForwardSlidingSource F hF f A).hom =
      (generalLiftForwardFactorizationSource F hF f A).inv ≫
        (generalLiftRetainedForwardFactorizationSource F hF f A).hom := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Forward sliding is multiplicative in retained data.  The formula slides
the first factor, reassociates, slides the second factor, and reassembles the
retained product through the two normalized identity compositors. -/
theorem generalLiftForwardSlidingSource_tensor
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftForwardSlidingSource F hF f (A × B)).hom =
      ((generalLiftSourceEquivalence F hF f).hom ◁
        (generalLiftForwardMapCompSourceRightIdentity F
          (𝟙 Y) A B).hom) ≫
      (α_ (generalLiftSourceEquivalence F hF f).hom
        (F.map (canonicalSourceHom (𝟙 Y) A))
        (F.map (canonicalSourceHom (𝟙 Y) B))).inv ≫
      ((generalLiftForwardSlidingSource F hF f A).hom ▷
        F.map (canonicalSourceHom (𝟙 Y) B)) ≫
      (α_ (F.map (canonicalSourceHom (𝟙 X) A))
        (generalLiftSourceEquivalence F hF f).hom
        (F.map (canonicalSourceHom (𝟙 Y) B))).hom ≫
      (F.map (canonicalSourceHom (𝟙 X) A) ◁
        (generalLiftForwardSlidingSource F hF f B).hom) ≫
      (α_ (F.map (canonicalSourceHom (𝟙 X) A))
        (F.map (canonicalSourceHom (𝟙 X) B))
        (generalLiftSourceEquivalence F hF f).hom).inv ≫
      ((generalLiftForwardMapCompSourceLeftIdentity F
          (𝟙 X) A B).inv ▷
        (generalLiftSourceEquivalence F hF f).hom) := by
  rw [generalLiftForwardSlidingSource_hom,
    generalLiftForwardFactorizationSource_tensor_inv,
    generalLiftRetainedForwardFactorizationSource_tensor]
  simp only [generalLiftSourceEquivalence_hom, Category.assoc]
  slice_lhs 4 5 =>
    rw [generalLiftForwardFactorizationSource_interchange F hF f A B]
  slice_lhs 3 4 =>
    rw [← Bicategory.comp_whiskerRight,
      ← generalLiftForwardSlidingSource_hom F hF f A]
  slice_lhs 5 6 =>
    rw [← Bicategory.whiskerLeft_comp,
      ← generalLiftForwardSlidingSource_hom F hF f B]
  simp only [generalLiftSourceEquivalence_hom, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Inverse orientation of forward-sliding multiplicativity, packaged as the
vertical composite of its two left-adjoint squares. -/
theorem generalLiftForwardSlidingSource_tensor_inv
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftForwardSlidingSource F hF f (A × B)).inv =
      ((generalLiftForwardMapCompSourceLeftIdentity F
          (𝟙 X) A B).hom ▷
        (generalLiftSourceEquivalence F hF f).hom) ≫
      leftAdjointSquare.vcomp
        (generalLiftForwardSlidingSource F hF f A).inv
        (generalLiftForwardSlidingSource F hF f B).inv ≫
      ((generalLiftSourceEquivalence F hF f).hom ◁
        (generalLiftForwardMapCompSourceRightIdentity F
          (𝟙 Y) A B).inv) := by
  let e :=
    whiskerLeftIso (generalLiftSourceEquivalence F hF f).hom
        (generalLiftForwardMapCompSourceRightIdentity F
          (𝟙 Y) A B) ≪≫
      (α_ (generalLiftSourceEquivalence F hF f).hom
        (F.map (canonicalSourceHom (𝟙 Y) A))
        (F.map (canonicalSourceHom (𝟙 Y) B))).symm ≪≫
      whiskerRightIso (generalLiftForwardSlidingSource F hF f A)
        (F.map (canonicalSourceHom (𝟙 Y) B)) ≪≫
      (α_ (F.map (canonicalSourceHom (𝟙 X) A))
        (generalLiftSourceEquivalence F hF f).hom
        (F.map (canonicalSourceHom (𝟙 Y) B))) ≪≫
      whiskerLeftIso (F.map (canonicalSourceHom (𝟙 X) A))
        (generalLiftForwardSlidingSource F hF f B) ≪≫
      (α_ (F.map (canonicalSourceHom (𝟙 X) A))
        (F.map (canonicalSourceHom (𝟙 X) B))
        (generalLiftSourceEquivalence F hF f).hom).symm ≪≫
      whiskerRightIso
        (generalLiftForwardMapCompSourceLeftIdentity F
          (𝟙 X) A B).symm
        (generalLiftSourceEquivalence F hF f).hom
  have he : generalLiftForwardSlidingSource F hF f (A × B) = e := by
    apply Iso.ext
    simpa [e] using generalLiftForwardSlidingSource_tensor F hF f A B
  rw [he]
  simp [e, leftAdjointSquare.vcomp]

/-- Forward sliding is natural in retained-coordinate 2-cells. -/
theorem generalLiftForwardSlidingSource_naturality
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    ((generalLiftSourceEquivalence F hF f).hom ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 Y) η)) ≫
        (generalLiftForwardSlidingSource F hF f B).hom =
      (generalLiftForwardSlidingSource F hF f A).hom ≫
        (F.map₂ (canonicalSourceTwoCell (𝟙 X) η) ▷
          (generalLiftSourceEquivalence F hF f).hom) := by
  rw [generalLiftForwardSlidingSource_hom,
    generalLiftForwardSlidingSource_hom]
  exact comp_naturality_of_squares
    (iso_inv_naturality_of_square
      (generalLiftForwardFactorizationSource F hF f A)
      (generalLiftForwardFactorizationSource F hF f B)
      (generalLiftForwardFactorizationSource_naturality F hF f η))
    (generalLiftRetainedForwardFactorizationSource_naturality F hF f η)

/-- The hom of inverse sliding is the mate of the inverse forward-sliding
constraint. -/
theorem generalLiftInverseSlidingSource_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (generalLiftInverseSlidingSource F hF f A).hom =
      mateEquiv
        ((Pseudofunctor.id E).mapAdjunction
          (generalLiftSourceEquivalence F hF f).toAdjunction)
        ((Pseudofunctor.id E).mapAdjunction
          (generalLiftSourceEquivalence F hF f).toAdjunction)
        (generalLiftForwardSlidingSource F hF f A).inv := by
  exact Pseudofunctor.StrongTrans.inverseNaturalityIso_hom
    (Pseudofunctor.id E) (Pseudofunctor.id E)
    (generalLiftSourceEquivalence F hF f)
    (F.map (canonicalSourceHom (𝟙 X) A))
    (F.map (canonicalSourceHom (𝟙 Y) A))
    (generalLiftForwardSlidingSource F hF f A)

/-- The inverse-sliding hom can equivalently be read as the direct mate for
the source equivalence, without the identity-pseudofunctor wrapper used by
the generic inverse-naturality construction. -/
theorem generalLiftInverseSlidingSource_hom_directMate
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (generalLiftInverseSlidingSource F hF f A).hom =
      mateEquiv
        (generalLiftSourceEquivalence F hF f).toAdjunction
        (generalLiftSourceEquivalence F hF f).toAdjunction
        (generalLiftForwardSlidingSource F hF f A).inv := by
  rw [generalLiftInverseSlidingSource_hom]
  exact identityPseudofunctor_mateEquiv
    (generalLiftSourceEquivalence F hF f)
    (generalLiftForwardSlidingSource F hF f A).inv

set_option backward.isDefEq.respectTransparency false in
/-- Taking the inverse-sliding constraint back across the reversed source
equivalence recovers the original forward-sliding hom. -/
private theorem generalLiftInverseSlidingSource_reverseMate
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    mateEquiv
        (reverseEquivalenceAdjunction
          (generalLiftSourceEquivalence F hF f))
        (reverseEquivalenceAdjunction
          (generalLiftSourceEquivalence F hF f))
        (generalLiftInverseSlidingSource F hF f A).inv =
      (generalLiftForwardSlidingSource F hF f A).hom := by
  apply reverseMate_inv
    (generalLiftSourceEquivalence F hF f)
    (generalLiftForwardSlidingSource F hF f A)
  exact generalLiftInverseSlidingSource_hom_directMate F hF f A

set_option backward.isDefEq.respectTransparency false in
/-- Counit insertion across a retained source factor agrees with moving that
factor through the inverse-sliding constraint before inserting the counit in
the remaining tail. -/
private theorem generalLiftCounitInsertion_inverseSliding
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type)
    (z : F.obj (canonicalSourceObject Y) ⟶
      F.obj (canonicalSourceObject Y)) :
    (equivalenceCounitInsertion (generalLiftSourceEquivalence F hF f)
        (F.map (canonicalSourceHom (𝟙 Y) A) ≫ z)).hom ≫
      ((generalLiftSourceEquivalence F hF f).inv ◁
        (α_ (generalLiftSourceEquivalence F hF f).hom
          (F.map (canonicalSourceHom (𝟙 Y) A)) z).inv) ≫
      ((generalLiftSourceEquivalence F hF f).inv ◁
        ((generalLiftForwardSlidingSource F hF f A).hom ▷ z)) ≫
      ((generalLiftSourceEquivalence F hF f).inv ◁
        (α_ (F.map (canonicalSourceHom (𝟙 X) A))
          (generalLiftSourceEquivalence F hF f).hom z).hom) =
    (F.map (canonicalSourceHom (𝟙 Y) A) ◁
        (equivalenceCounitInsertion
          (generalLiftSourceEquivalence F hF f) z).hom) ≫
      (α_ (F.map (canonicalSourceHom (𝟙 Y) A))
        (generalLiftSourceEquivalence F hF f).inv
        ((generalLiftSourceEquivalence F hF f).hom ≫ z)).inv ≫
      ((generalLiftInverseSlidingSource F hF f A).inv ▷
        ((generalLiftSourceEquivalence F hF f).hom ≫ z)) ≫
      (α_ (generalLiftSourceEquivalence F hF f).inv
        (F.map (canonicalSourceHom (𝟙 X) A))
        ((generalLiftSourceEquivalence F hF f).hom ≫ z)).hom := by
  rw [← generalLiftInverseSlidingSource_reverseMate F hF f A]
  exact equivalenceCounitInsertion_reverseMate_vcomp
    (generalLiftSourceEquivalence F hF f)
    (generalLiftInverseSlidingSource F hF f A)

set_option backward.isDefEq.respectTransparency false in
/-- Inserting the unit of the chosen source equivalence across a retained
pair agrees with first inserting it in the tail and then passing the first
retained factor through the inverse-sliding mate. -/
theorem generalLiftEquivalenceUnitInsertion_inverseSliding
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (equivalenceUnitInsertion (generalLiftSourceEquivalence F hF f)
          (F.map (canonicalSourceHom (𝟙 X) A) ≫
            F.map (canonicalSourceHom (𝟙 X) B))).hom ≫
        ((generalLiftSourceEquivalence F hF f).hom ◁
          (α_ (generalLiftSourceEquivalence F hF f).inv
            (F.map (canonicalSourceHom (𝟙 X) A))
            (F.map (canonicalSourceHom (𝟙 X) B))).inv) ≫
        ((generalLiftSourceEquivalence F hF f).hom ◁
          ((generalLiftInverseSlidingSource F hF f A).hom ▷
            F.map (canonicalSourceHom (𝟙 X) B))) ≫
        ((generalLiftSourceEquivalence F hF f).hom ◁
          (α_ (F.map (canonicalSourceHom (𝟙 Y) A))
            (generalLiftSourceEquivalence F hF f).inv
            (F.map (canonicalSourceHom (𝟙 X) B))).hom) =
      (F.map (canonicalSourceHom (𝟙 X) A) ◁
          (equivalenceUnitInsertion (generalLiftSourceEquivalence F hF f)
            (F.map (canonicalSourceHom (𝟙 X) B))).hom) ≫
        (α_ (F.map (canonicalSourceHom (𝟙 X) A))
          (generalLiftSourceEquivalence F hF f).hom
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) B))).inv ≫
        ((generalLiftForwardSlidingSource F hF f A).inv ▷
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) B))) ≫
        (α_ (generalLiftSourceEquivalence F hF f).hom
          (F.map (canonicalSourceHom (𝟙 Y) A))
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) B))).hom := by
  rw [generalLiftInverseSlidingSource_hom_directMate]
  exact equivalenceUnitInsertion_mate_vcomp
    (generalLiftSourceEquivalence F hF f)
    (generalLiftForwardSlidingSource F hF f A).inv

set_option backward.isDefEq.respectTransparency false in
/-- Mate transfer of forward-sliding multiplicativity.  Inverse sliding on a
retained product is the vertical composite of the two right-adjoint mate
squares, with normalized retained compositors on the outside. -/
theorem generalLiftInverseSlidingSource_tensor
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftInverseSlidingSource F hF f (A × B)).hom =
      ((generalLiftSourceEquivalence F hF f).inv ◁
        (generalLiftForwardMapCompSourceLeftIdentity F
          (𝟙 X) A B).hom) ≫
      rightAdjointSquare.vcomp
        (generalLiftInverseSlidingSource F hF f A).hom
        (generalLiftInverseSlidingSource F hF f B).hom ≫
      ((generalLiftForwardMapCompSourceRightIdentity F
          (𝟙 Y) A B).inv ▷
        (generalLiftSourceEquivalence F hF f).inv) := by
  let adj := (Pseudofunctor.id E).mapAdjunction
    (generalLiftSourceEquivalence F hF f).toAdjunction
  rw [generalLiftInverseSlidingSource_hom,
    generalLiftForwardSlidingSource_tensor_inv]
  have hpre := Bicategory.mateEquiv_precomp_postcomp adj adj
    (generalLiftForwardMapCompSourceLeftIdentity F (𝟙 X) A B).hom
    (leftAdjointSquare.vcomp
      (generalLiftForwardSlidingSource F hF f A).inv
      (generalLiftForwardSlidingSource F hF f B).inv)
    (generalLiftForwardMapCompSourceRightIdentity F (𝟙 Y) A B).inv
  have hv := Bicategory.mateEquiv_vcomp adj adj adj
    (generalLiftForwardSlidingSource F hF f A).inv
    (generalLiftForwardSlidingSource F hF f B).inv
  have hA :
      mateEquiv adj adj
          (generalLiftForwardSlidingSource F hF f A).inv =
        (generalLiftInverseSlidingSource F hF f A).hom := by
    exact (generalLiftInverseSlidingSource_hom F hF f A).symm
  have hB :
      mateEquiv adj adj
          (generalLiftForwardSlidingSource F hF f B).inv =
        (generalLiftInverseSlidingSource F hF f B).hom := by
    exact (generalLiftInverseSlidingSource_hom F hF f B).symm
  rw [hA, hB] at hv
  rw [hv] at hpre
  have hmapHom :
      (Pseudofunctor.id E).map
          (generalLiftSourceEquivalence F hF f).hom =
        (generalLiftSourceEquivalence F hF f).hom := by
    rfl
  have hmapInv :
      (Pseudofunctor.id E).map
          (generalLiftSourceEquivalence F hF f).inv =
        (generalLiftSourceEquivalence F hF f).inv := by
    rfl
  have hLeft : HEq
      ((mateEquiv adj adj)
        (((generalLiftForwardMapCompSourceLeftIdentity F
              (𝟙 X) A B).hom ▷
            (Pseudofunctor.id E).map
              (generalLiftSourceEquivalence F hF f).hom ≫
          leftAdjointSquare.vcomp
            (generalLiftForwardSlidingSource F hF f A).inv
            (generalLiftForwardSlidingSource F hF f B).inv) ≫
        (Pseudofunctor.id E).map
            (generalLiftSourceEquivalence F hF f).hom ◁
          (generalLiftForwardMapCompSourceRightIdentity F
            (𝟙 Y) A B).inv))
      ((mateEquiv adj adj)
        (((generalLiftForwardMapCompSourceLeftIdentity F
              (𝟙 X) A B).hom ▷
            (generalLiftSourceEquivalence F hF f).hom ≫
          leftAdjointSquare.vcomp
            (generalLiftForwardSlidingSource F hF f A).inv
            (generalLiftForwardSlidingSource F hF f B).inv) ≫
        (generalLiftSourceEquivalence F hF f).hom ◁
          (generalLiftForwardMapCompSourceRightIdentity F
            (𝟙 Y) A B).inv)) := by
    cases hmapHom
    rfl
  have hRight : HEq
      ((Pseudofunctor.id E).map
            (generalLiftSourceEquivalence F hF f).inv ◁
          (generalLiftForwardMapCompSourceLeftIdentity F
            (𝟙 X) A B).hom ≫
        rightAdjointSquare.vcomp
            (generalLiftInverseSlidingSource F hF f A).hom
            (generalLiftInverseSlidingSource F hF f B).hom ≫
        (generalLiftForwardMapCompSourceRightIdentity F
            (𝟙 Y) A B).inv ▷
          (Pseudofunctor.id E).map
            (generalLiftSourceEquivalence F hF f).inv)
      ((generalLiftSourceEquivalence F hF f).inv ◁
          (generalLiftForwardMapCompSourceLeftIdentity F
            (𝟙 X) A B).hom ≫
        rightAdjointSquare.vcomp
            (generalLiftInverseSlidingSource F hF f A).hom
            (generalLiftInverseSlidingSource F hF f B).hom ≫
        (generalLiftForwardMapCompSourceRightIdentity F
            (𝟙 Y) A B).inv ▷
          (generalLiftSourceEquivalence F hF f).inv) := by
    cases hmapInv
    rfl
  have hdirect := eq_of_heq
    (hLeft.symm.trans ((heq_of_eq hpre).trans hRight))
  simpa only [Category.assoc] using hdirect

set_option backward.isDefEq.respectTransparency false in
/-- Inverse orientation of inverse-sliding multiplicativity, stopped after
the first retained factor.  The remaining inverse sliding and normalized
codomain compositor are exposed on the other side. -/
private theorem generalLiftInverseSlidingSource_tensor_inv_prefix
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftInverseSlidingSource F hF f (A × B)).inv ≫
        ((generalLiftSourceEquivalence F hF f).inv ◁
          (generalLiftForwardMapCompSourceLeftIdentity F
            (𝟙 X) A B).hom) ≫
        (α_ (generalLiftSourceEquivalence F hF f).inv
          (F.map (canonicalSourceHom (𝟙 X) A))
          (F.map (canonicalSourceHom (𝟙 X) B))).inv ≫
        ((generalLiftInverseSlidingSource F hF f A).hom ▷
          F.map (canonicalSourceHom (𝟙 X) B)) ≫
        (α_ (F.map (canonicalSourceHom (𝟙 Y) A))
          (generalLiftSourceEquivalence F hF f).inv
          (F.map (canonicalSourceHom (𝟙 X) B))).hom =
      ((generalLiftForwardMapCompSourceRightIdentity F
          (𝟙 Y) A B).hom ▷
        (generalLiftSourceEquivalence F hF f).inv) ≫
        (α_ (F.map (canonicalSourceHom (𝟙 Y) A))
          (F.map (canonicalSourceHom (𝟙 Y) B))
          (generalLiftSourceEquivalence F hF f).inv).hom ≫
        (F.map (canonicalSourceHom (𝟙 Y) A) ◁
          (generalLiftInverseSlidingSource F hF f B).inv) := by
  let suffix :=
    (F.map (canonicalSourceHom (𝟙 Y) A) ◁
      (generalLiftInverseSlidingSource F hF f B).hom) ≫
    (α_ (F.map (canonicalSourceHom (𝟙 Y) A))
      (F.map (canonicalSourceHom (𝟙 Y) B))
      (generalLiftSourceEquivalence F hF f).inv).inv ≫
    ((generalLiftForwardMapCompSourceRightIdentity F
      (𝟙 Y) A B).inv ▷
        (generalLiftSourceEquivalence F hF f).inv)
  rw [← cancel_mono suffix]
  simp only [Category.assoc]
  dsimp [suffix]
  have ht := generalLiftInverseSlidingSource_tensor F hF f A B
  simp only [rightAdjointSquare.vcomp, Category.assoc] at ht
  rw [← ht]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The inverse tensor-sliding prefix is natural in an arbitrary following
2-cell.  This is the exchange form needed when a forward factorization sits
between cancellation and the retained/inverse normalization. -/
private theorem generalLiftInverseSlidingSource_tensor_inv_prefix_naturality
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type)
    {S T : F.obj (canonicalSourceObject X) ⟶
      F.obj (canonicalSourceObject Y)} (q : S ⟶ T) :
    ((generalLiftInverseSlidingSource F hF f (A × B)).inv ▷ S) ≫
        (((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) (A × B))) ◁ q) ≫
        ((((generalLiftSourceEquivalence F hF f).inv ◁
          (generalLiftForwardMapCompSourceLeftIdentity F
            (𝟙 X) A B).hom) ≫
          (α_ (generalLiftSourceEquivalence F hF f).inv
            (F.map (canonicalSourceHom (𝟙 X) A))
            (F.map (canonicalSourceHom (𝟙 X) B))).inv ≫
          ((generalLiftInverseSlidingSource F hF f A).hom ▷
            F.map (canonicalSourceHom (𝟙 X) B)) ≫
          (α_ (F.map (canonicalSourceHom (𝟙 Y) A))
            (generalLiftSourceEquivalence F hF f).inv
            (F.map (canonicalSourceHom (𝟙 X) B))).hom) ▷ T) =
      ((((generalLiftForwardMapCompSourceRightIdentity F
          (𝟙 Y) A B).hom ▷
        (generalLiftSourceEquivalence F hF f).inv) ≫
        (α_ (F.map (canonicalSourceHom (𝟙 Y) A))
          (F.map (canonicalSourceHom (𝟙 Y) B))
          (generalLiftSourceEquivalence F hF f).inv).hom ≫
        (F.map (canonicalSourceHom (𝟙 Y) A) ◁
          (generalLiftInverseSlidingSource F hF f B).inv)) ▷ S) ≫
        ((F.map (canonicalSourceHom (𝟙 Y) A) ≫
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) B))) ◁ q) := by
  let p :=
    ((generalLiftSourceEquivalence F hF f).inv ◁
      (generalLiftForwardMapCompSourceLeftIdentity F
        (𝟙 X) A B).hom) ≫
    (α_ (generalLiftSourceEquivalence F hF f).inv
      (F.map (canonicalSourceHom (𝟙 X) A))
      (F.map (canonicalSourceHom (𝟙 X) B))).inv ≫
    ((generalLiftInverseSlidingSource F hF f A).hom ▷
      F.map (canonicalSourceHom (𝟙 X) B)) ≫
    (α_ (F.map (canonicalSourceHom (𝟙 Y) A))
      (generalLiftSourceEquivalence F hF f).inv
      (F.map (canonicalSourceHom (𝟙 X) B))).hom
  calc
    _ = ((generalLiftInverseSlidingSource F hF f (A × B)).inv ▷ S) ≫
        (p ▷ S) ≫
        ((F.map (canonicalSourceHom (𝟙 Y) A) ≫
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) B))) ◁ q) := by
      dsimp [p]
      rw [whisker_exchange]
    _ = (((generalLiftInverseSlidingSource F hF f (A × B)).inv ≫
          p) ▷ S) ≫
        ((F.map (canonicalSourceHom (𝟙 Y) A) ≫
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) B))) ◁ q) := by
      conv_rhs => rw [Bicategory.comp_whiskerRight]
      simp only [Category.assoc]
    _ = _ := by
      dsimp [p]
      rw [generalLiftInverseSlidingSource_tensor_inv_prefix]

/-- Inverse sliding is natural in retained-coordinate 2-cells. -/
theorem generalLiftInverseSlidingSource_naturality
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A B : Type} (η : A ⟶ B) :
    ((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X) η)) ≫
        (generalLiftInverseSlidingSource F hF f B).hom =
      (generalLiftInverseSlidingSource F hF f A).hom ≫
        (F.map₂ (canonicalSourceTwoCell (𝟙 Y) η) ▷
          (generalLiftSourceEquivalence F hF f).inv) := by
  rw [generalLiftInverseSlidingSource_hom,
    generalLiftInverseSlidingSource_hom]
  apply mate_naturality_of_square
  exact iso_inv_naturality_of_square
    (generalLiftForwardSlidingSource F hF f A)
    (generalLiftForwardSlidingSource F hF f B)
    (generalLiftForwardSlidingSource_naturality F hF f η)

/-- The sliding stage of the retained-then-inverse compositor moves retained
data across the chosen inverse and reassociates the result. -/
noncomputable def generalLiftRetainedInverseMapCompSliding
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) A)) ≫
      F.map (canonicalSourceHom (𝟙 X) B)) ≅
      (F.map (canonicalSourceHom (𝟙 Y) A) ≫
        ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) B))) :=
  whiskerRightIso (generalLiftInverseSlidingSource F hF f A)
      (F.map (canonicalSourceHom (𝟙 X) B)) ≪≫
    α_ (F.map (canonicalSourceHom (𝟙 Y) A))
      (generalLiftSourceEquivalence F hF f).inv
      (F.map (canonicalSourceHom (𝟙 X) B))

/-- The hom of the retained-then-inverse sliding stage is inverse sliding
followed by the associator. -/
theorem generalLiftRetainedInverseMapCompSliding_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftRetainedInverseMapCompSliding F hF f A B).hom =
      ((generalLiftInverseSlidingSource F hF f A).hom ▷
        F.map (canonicalSourceHom (𝟙 X) B)) ≫
      (α_ (F.map (canonicalSourceHom (𝟙 Y) A))
        (generalLiftSourceEquivalence F hF f).inv
        (F.map (canonicalSourceHom (𝟙 X) B))).hom := by
  rfl

/-- The retained-then-inverse sliding stage is natural in the inverse
factor's retained coordinate. -/
theorem generalLiftRetainedInverseMapCompSliding_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) {B C : Type} (η : B ⟶ C) :
    (((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) A)) ◁
        F.map₂ (canonicalSourceTwoCell (𝟙 X) η)) ≫
      (generalLiftRetainedInverseMapCompSliding F hF f A C).hom =
    (generalLiftRetainedInverseMapCompSliding F hF f A B).hom ≫
      (F.map (canonicalSourceHom (𝟙 Y) A) ◁
        ((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X) η))) := by
  rw [generalLiftRetainedInverseMapCompSliding_hom,
    generalLiftRetainedInverseMapCompSliding_hom]
  exact comp_naturality_of_squares
    (whisker_exchange
      (generalLiftInverseSlidingSource F hF f A).hom
      (F.map₂ (canonicalSourceTwoCell (𝟙 X) η)))
    (associator_naturality_right
      (F.map (canonicalSourceHom (𝟙 Y) A))
      (generalLiftSourceEquivalence F hF f).inv
      (F.map₂ (canonicalSourceTwoCell (𝟙 X) η)))

/-- The retained-then-inverse sliding stage is natural in the retained
factor's coordinate. -/
theorem generalLiftRetainedInverseMapCompSliding_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A C : Type} (η : A ⟶ C) (B : Type) :
    (((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X) η)) ▷
        F.map (canonicalSourceHom (𝟙 X) B)) ≫
      (generalLiftRetainedInverseMapCompSliding F hF f C B).hom =
    (generalLiftRetainedInverseMapCompSliding F hF f A B).hom ≫
      (F.map₂ (canonicalSourceTwoCell (𝟙 Y) η) ▷
        ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) B))) := by
  rw [generalLiftRetainedInverseMapCompSliding_hom,
    generalLiftRetainedInverseMapCompSliding_hom]
  exact comp_naturality_of_squares
    (whiskerRight_naturality_of_square
      (F.map (canonicalSourceHom (𝟙 X) B))
      (generalLiftInverseSlidingSource_naturality F hF f η))
    (associator_naturality_left
      (F.map₂ (canonicalSourceTwoCell (𝟙 Y) η))
      (generalLiftSourceEquivalence F hF f).inv
      (F.map (canonicalSourceHom (𝟙 X) B)))

/-- Source-normalized retained-then-inverse compositor, before endpoint
equality transports return to the arbitrary target action. -/
noncomputable def generalLiftRetainedInverseMapCompSource
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) (A × B)) ≅
      F.map (canonicalSourceHom (𝟙 Y) A) ≫
        ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) B)) :=
  whiskerLeftIso (generalLiftSourceEquivalence F hF f).inv
      (generalLiftForwardMapCompSource F (𝟙 X) (𝟙 X) A B) ≪≫
    (α_ (generalLiftSourceEquivalence F hF f).inv
      (F.map (canonicalSourceHom (𝟙 X) A))
      (F.map (canonicalSourceHom (𝟙 X) B))).symm ≪≫
    generalLiftRetainedInverseMapCompSliding F hF f A B

/-- Hom expansion of the source-normalized retained/inverse compositor. -/
theorem generalLiftRetainedInverseMapCompSource_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftRetainedInverseMapCompSource F hF f A B).hom =
      ((generalLiftSourceEquivalence F hF f).inv ◁
          (generalLiftForwardMapCompSource F
            (𝟙 X) (𝟙 X) A B).hom) ≫
        (α_ (generalLiftSourceEquivalence F hF f).inv
          (F.map (canonicalSourceHom (𝟙 X) A))
          (F.map (canonicalSourceHom (𝟙 X) B))).inv ≫
        (generalLiftRetainedInverseMapCompSliding F hF f A B).hom := by
  rfl

/-- Endpoint-strict source-normalized retained/inverse compositor.  This
version uses the right-identity-normalized retained compositor explicitly,
so its source is definitionally the chosen walking-identity representative. -/
noncomputable def generalLiftRetainedInverseMapCompSourceNormalized
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) (A × B)) ≅
      F.map (canonicalSourceHom (𝟙 Y) A) ≫
        ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) B)) :=
  whiskerLeftIso (generalLiftSourceEquivalence F hF f).inv
      (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X) A B) ≪≫
    (α_ (generalLiftSourceEquivalence F hF f).inv
      (F.map (canonicalSourceHom (𝟙 X) A))
      (F.map (canonicalSourceHom (𝟙 X) B))).symm ≪≫
    generalLiftRetainedInverseMapCompSliding F hF f A B

/-- Hom expansion of the endpoint-strict retained/inverse compositor. -/
theorem generalLiftRetainedInverseMapCompSourceNormalized_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftRetainedInverseMapCompSourceNormalized F hF f A B).hom =
      ((generalLiftSourceEquivalence F hF f).inv ◁
          (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X) A B).hom) ≫
        (α_ (generalLiftSourceEquivalence F hF f).inv
          (F.map (canonicalSourceHom (𝟙 X) A))
          (F.map (canonicalSourceHom (𝟙 X) B))).inv ≫
        (generalLiftRetainedInverseMapCompSliding F hF f A B).hom := by
  rfl

/-- Exchange inverse sliding with a compositor on the retained tail, keeping
all associator transports explicit. -/
private theorem retainedInverse_whiskerExchange
    {a b : E} {r : b ⟶ a}
    {xA xB xC xBC : a ⟶ a} {yA yB : b ⟶ b}
    (sA : r ≫ xA ⟶ yA ≫ r)
    (sB : r ≫ xB ⟶ yB ≫ r)
    (cBC : xBC ⟶ xB ≫ xC) :
    (α_ r xA xBC).inv ≫
        (sA ▷ xBC) ≫
        (α_ yA r xBC).hom ≫
        (yA ◁ (r ◁ cBC)) ≫
        (yA ◁ (α_ r xB xC).inv) ≫
        (yA ◁ (sB ▷ xC)) ≫
        (yA ◁ (α_ yB r xC).hom) =
      (r ◁ (xA ◁ cBC)) ≫
        (r ◁ (α_ xA xB xC).inv) ≫
        (α_ r (xA ≫ xB) xC).inv ≫
        (rightAdjointSquare.vcomp sA sB ▷ xC) ≫
        (α_ (yA ≫ yB) r xC).hom ≫
        (α_ yA yB (r ≫ xC)).hom := by
  let post :=
    (α_ yA r (xB ≫ xC)).hom ≫
      (yA ◁ (α_ r xB xC).inv) ≫
      (yA ◁ (sB ▷ xC)) ≫
      (yA ◁ (α_ yB r xC).hom)
  have hex := congrArg
    (fun k => (α_ r xA xBC).inv ≫ k ≫ post)
    (whisker_exchange sA cBC).symm
  dsimp [post] at hex
  convert hex using 1
  · bicategory
  · simp only [rightAdjointSquare.vcomp]
    bicategory

set_option backward.isDefEq.respectTransparency false in
/-- The endpoint-strict retained/retained/inverse source compositor satisfies
its full three-fold associativity law. -/
theorem generalLiftRetainedInverseMapCompSourceNormalized_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    ((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X)
            (MonoidalCategory.associator A B C).hom)) ≫
        (generalLiftRetainedInverseMapCompSourceNormalized F hF f
          A (B × C)).hom ≫
        F.map (canonicalSourceHom (𝟙 Y) A) ◁
          (generalLiftRetainedInverseMapCompSourceNormalized F hF f
            B C).hom =
      (generalLiftRetainedInverseMapCompSourceNormalized F hF f
          (A × B) C).hom ≫
        ((generalLiftForwardMapCompSourceRightIdentity F (𝟙 Y) A B).hom ▷
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) C))) ≫
        (α_ (F.map (canonicalSourceHom (𝟙 Y) A))
          (F.map (canonicalSourceHom (𝟙 Y) B))
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) C))).hom := by
  rw [generalLiftRetainedInverseMapCompSourceNormalized_hom,
    generalLiftRetainedInverseMapCompSourceNormalized_hom,
    generalLiftRetainedInverseMapCompSourceNormalized_hom]
  rw [generalLiftRetainedInverseMapCompSliding_hom,
    generalLiftRetainedInverseMapCompSliding_hom,
    generalLiftRetainedInverseMapCompSliding_hom]
  rw [generalLiftInverseSlidingSource_tensor F hF f A B]
  rw [generalLiftForwardMapCompSource_identityNormalizations_eq F X A B]
  simp only [Bicategory.whiskerLeft_comp,
    Bicategory.comp_whiskerRight, Category.assoc]
  slice_lhs 3 9 =>
    rw [retainedInverse_whiskerExchange
      (generalLiftInverseSlidingSource F hF f A).hom
      (generalLiftInverseSlidingSource F hF f B).hom
      (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X) B C).hom]
  have hsource :=
    generalLiftForwardMapCompSourceIdentity_associativity F X A B C
  have hsourceW := congrArg
    (fun k => (generalLiftSourceEquivalence F hF f).inv ◁ k)
    hsource
  simp only [Bicategory.whiskerLeft_comp] at hsourceW
  slice_lhs 1 3 => rw [hsourceW]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The historical source-normalized retained/inverse compositor is exactly
the endpoint-strict normalized compositor. -/
theorem generalLiftRetainedInverseMapCompSource_eq_normalized
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    generalLiftRetainedInverseMapCompSource F hF f A B =
      generalLiftRetainedInverseMapCompSourceNormalized F hF f A B := by
  apply Iso.ext
  rw [generalLiftRetainedInverseMapCompSource_hom,
    generalLiftRetainedInverseMapCompSourceNormalized_hom,
    generalLiftForwardMapCompSourceRightIdentity_hom]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The existing source-normalized retained/retained/inverse compositor
satisfies the endpoint-strict three-fold associativity law. -/
theorem generalLiftRetainedInverseMapCompSource_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    ((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X)
            (MonoidalCategory.associator A B C).hom)) ≫
        (generalLiftRetainedInverseMapCompSource F hF f
          A (B × C)).hom ≫
        F.map (canonicalSourceHom (𝟙 Y) A) ◁
          (generalLiftRetainedInverseMapCompSource F hF f B C).hom =
      (generalLiftRetainedInverseMapCompSource F hF f
          (A × B) C).hom ≫
        ((generalLiftForwardMapCompSourceRightIdentity F (𝟙 Y) A B).hom ▷
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) C))) ≫
        (α_ (F.map (canonicalSourceHom (𝟙 Y) A))
          (F.map (canonicalSourceHom (𝟙 Y) B))
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) C))).hom := by
  rw [generalLiftRetainedInverseMapCompSource_eq_normalized,
    generalLiftRetainedInverseMapCompSource_eq_normalized,
    generalLiftRetainedInverseMapCompSource_eq_normalized]
  exact generalLiftRetainedInverseMapCompSourceNormalized_associativity
    F hF f A B C

/-- Endpoint-strict inverse/retained source compositor used by mixed
retained/inverse/retained associativity. -/
noncomputable def generalLiftInverseRetainedMapCompSourceNormalized
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) (A × B)) ≅
      ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) A)) ≫
          F.map (canonicalSourceHom (𝟙 X) B) :=
  whiskerLeftIso (generalLiftSourceEquivalence F hF f).inv
      (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X) A B) ≪≫
    (α_ (generalLiftSourceEquivalence F hF f).inv
      (F.map (canonicalSourceHom (𝟙 X) A))
      (F.map (canonicalSourceHom (𝟙 X) B))).symm

/-- Hom expansion of the endpoint-strict inverse/retained source compositor. -/
theorem generalLiftInverseRetainedMapCompSourceNormalized_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftInverseRetainedMapCompSourceNormalized F hF f A B).hom =
      ((generalLiftSourceEquivalence F hF f).inv ◁
        (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X) A B).hom) ≫
      (α_ (generalLiftSourceEquivalence F hF f).inv
        (F.map (canonicalSourceHom (𝟙 X) A))
        (F.map (canonicalSourceHom (𝟙 X) B))).inv := by
  rfl

/-- Exchange one inverse-sliding square with a compositor on its retained
tail, with the necessary associators made explicit. -/
private theorem retainedInverse_singleWhiskerExchange
    {a b : E} {r : b ⟶ a}
    {xA xB xC xBC : a ⟶ a} {yA : b ⟶ b}
    (sA : r ≫ xA ⟶ yA ≫ r)
    (cBC : xBC ⟶ xB ≫ xC) :
    (α_ r xA xBC).inv ≫
        (sA ▷ xBC) ≫
        (α_ yA r xBC).hom ≫
        (yA ◁ (r ◁ cBC)) ≫
        (yA ◁ (α_ r xB xC).inv) =
      (r ◁ (xA ◁ cBC)) ≫
        (r ◁ (α_ xA xB xC).inv) ≫
        (α_ r (xA ≫ xB) xC).inv ≫
        (((α_ r xA xB).inv ≫
          (sA ▷ xB) ≫
          (α_ yA r xB).hom) ▷ xC) ≫
        (α_ yA (r ≫ xB) xC).hom := by
  let post :=
    (α_ yA r (xB ≫ xC)).hom ≫
      (yA ◁ (α_ r xB xC).inv)
  have hex := congrArg
    (fun k => (α_ r xA xBC).inv ≫ k ≫ post)
    (whisker_exchange sA cBC).symm
  dsimp [post] at hex
  convert hex using 1
  · bicategory
  · bicategory

set_option backward.isDefEq.respectTransparency false in
/-- The normalized retained/inverse/retained source compositors satisfy their
mixed three-fold associativity law. -/
theorem generalLiftRetainedInverseRetainedMapCompSource_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    ((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X)
            (MonoidalCategory.associator A B C).hom)) ≫
        (generalLiftRetainedInverseMapCompSourceNormalized F hF f
          A (B × C)).hom ≫
        F.map (canonicalSourceHom (𝟙 Y) A) ◁
          (generalLiftInverseRetainedMapCompSourceNormalized F hF f B C).hom =
      (generalLiftInverseRetainedMapCompSourceNormalized F hF f
          (A × B) C).hom ≫
        ((generalLiftRetainedInverseMapCompSourceNormalized F hF f A B).hom ▷
          F.map (canonicalSourceHom (𝟙 X) C)) ≫
        (α_ (F.map (canonicalSourceHom (𝟙 Y) A))
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) B))
          (F.map (canonicalSourceHom (𝟙 X) C))).hom := by
  rw [generalLiftRetainedInverseMapCompSourceNormalized_hom,
    generalLiftInverseRetainedMapCompSourceNormalized_hom,
    generalLiftInverseRetainedMapCompSourceNormalized_hom,
    generalLiftRetainedInverseMapCompSourceNormalized_hom]
  rw [generalLiftRetainedInverseMapCompSliding_hom,
    generalLiftRetainedInverseMapCompSliding_hom]
  simp only [Bicategory.whiskerLeft_comp,
    Bicategory.comp_whiskerRight, Category.assoc]
  slice_lhs 3 7 =>
    rw [retainedInverse_singleWhiskerExchange
      (generalLiftInverseSlidingSource F hF f A).hom
      (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X) B C).hom]
  have hsource :=
    generalLiftForwardMapCompSourceIdentity_associativity F X A B C
  let tail :=
    ((generalLiftSourceEquivalence F hF f).inv ◁
      (α_ (F.map (canonicalSourceHom (𝟙 X) A))
        (F.map (canonicalSourceHom (𝟙 X) B))
        (F.map (canonicalSourceHom (𝟙 X) C))).inv) ≫
    (α_ (generalLiftSourceEquivalence F hF f).inv
      (F.map (canonicalSourceHom (𝟙 X) A) ≫
        F.map (canonicalSourceHom (𝟙 X) B))
      (F.map (canonicalSourceHom (𝟙 X) C))).inv ≫
    (((α_ (generalLiftSourceEquivalence F hF f).inv
          (F.map (canonicalSourceHom (𝟙 X) A))
          (F.map (canonicalSourceHom (𝟙 X) B))).inv ≫
      ((generalLiftInverseSlidingSource F hF f A).hom ▷
        F.map (canonicalSourceHom (𝟙 X) B)) ≫
      (α_ (F.map (canonicalSourceHom (𝟙 Y) A))
        (generalLiftSourceEquivalence F hF f).inv
        (F.map (canonicalSourceHom (𝟙 X) B))).hom) ▷
      F.map (canonicalSourceHom (𝟙 X) C)) ≫
    (α_ (F.map (canonicalSourceHom (𝟙 Y) A))
      ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) B))
      (F.map (canonicalSourceHom (𝟙 X) C))).hom
  calc
    _ = ((generalLiftSourceEquivalence F hF f).inv ◁
          (F.map₂ (canonicalSourceTwoCell (𝟙 X)
              (MonoidalCategory.associator A B C).hom) ≫
            (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X)
              A (B × C)).hom ≫
            F.map (canonicalSourceHom (𝟙 X) A) ◁
              (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X) B C).hom)) ≫
          tail := by
      dsimp [tail]
      bicategory
    _ = ((generalLiftSourceEquivalence F hF f).inv ◁
          ((generalLiftForwardMapCompSourceRightIdentity F (𝟙 X)
              (A × B) C).hom ≫
            ((generalLiftForwardMapCompSourceRightIdentity F (𝟙 X) A B).hom ▷
              F.map (canonicalSourceHom (𝟙 X) C)) ≫
            (α_ (F.map (canonicalSourceHom (𝟙 X) A))
              (F.map (canonicalSourceHom (𝟙 X) B))
              (F.map (canonicalSourceHom (𝟙 X) C))).hom)) ≫
          tail := by
      rw [hsource]
    _ = _ := by
      dsimp [tail]
      bicategory

/-- Source-normalized retained/inverse composition is natural in the inverse
factor's retained coordinate. -/
theorem generalLiftRetainedInverseMapCompSource_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) {B C : Type} (η : B ⟶ C) :
    ((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X)
            (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η))) ≫
        (generalLiftRetainedInverseMapCompSource F hF f A C).hom =
      (generalLiftRetainedInverseMapCompSource F hF f A B).hom ≫
        (F.map (canonicalSourceHom (𝟙 Y) A) ◁
          ((generalLiftSourceEquivalence F hF f).inv ◁
            F.map₂ (canonicalSourceTwoCell (𝟙 X) η))) := by
  have hsource := generalLiftForwardMapCompSource_naturality_right F
    (𝟙 X) (𝟙 X) A η
  have hid : (𝟙 X ≫ 𝟙 X) = 𝟙 X := Subsingleton.elim _ _
  rw [hid] at hsource
  rw [generalLiftRetainedInverseMapCompSource_hom,
    generalLiftRetainedInverseMapCompSource_hom]
  exact comp_naturality_of_squares
    (whiskerLeft_naturality_of_square
      (generalLiftSourceEquivalence F hF f).inv hsource)
    (comp_naturality_of_squares
      (associator_inv_naturality_right
        (generalLiftSourceEquivalence F hF f).inv
        (F.map (canonicalSourceHom (𝟙 X) A))
        (F.map₂ (canonicalSourceTwoCell (𝟙 X) η)))
      (generalLiftRetainedInverseMapCompSliding_naturality_right
        F hF f A η))

/-- Source-normalized retained/inverse composition is natural in the first
retained coordinate. -/
theorem generalLiftRetainedInverseMapCompSource_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A C : Type} (η : A ⟶ C) (B : Type) :
    ((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X)
            (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B)))) ≫
        (generalLiftRetainedInverseMapCompSource F hF f C B).hom =
      (generalLiftRetainedInverseMapCompSource F hF f A B).hom ≫
        (F.map₂ (canonicalSourceTwoCell (𝟙 Y) η) ▷
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) B))) := by
  have hsource := generalLiftForwardMapCompSource_naturality_left F
    (𝟙 X) (𝟙 X) η B
  have hid : (𝟙 X ≫ 𝟙 X) = 𝟙 X := Subsingleton.elim _ _
  rw [hid] at hsource
  rw [generalLiftRetainedInverseMapCompSource_hom,
    generalLiftRetainedInverseMapCompSource_hom]
  exact comp_naturality_of_squares
    (whiskerLeft_naturality_of_square
      (generalLiftSourceEquivalence F hF f).inv hsource)
    (comp_naturality_of_squares
      (associator_inv_naturality_middle
        (generalLiftSourceEquivalence F hF f).inv
        (F.map₂ (canonicalSourceTwoCell (𝟙 X) η))
        (F.map (canonicalSourceHom (𝟙 X) B)))
      (generalLiftRetainedInverseMapCompSliding_naturality_left
        F hF f η B))

/-- The factor-transport stage of the retained-then-inverse compositor
returns from source endpoints to the arbitrary lift. -/
noncomputable def generalLiftRetainedInverseMapCompFactors
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (F.map (canonicalSourceHom (𝟙 Y) A) ≫
        ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) B))) ≅
      ((generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom (𝟙 Y) A) ≫
        (generalLiftPrelaxFunctor F hF).map
          (canonicalInverseHom f B)) :=
  whiskerRightIso
      (eqToIso
        (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y) A)).symm
      ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) B)) ≪≫
    whiskerLeftIso
      ((generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom (𝟙 Y) A))
      (eqToIso
        (generalLiftPrelaxFunctor_map_inverse F hF f hf B)).symm

/-- The hom of retained-then-inverse factor transport is the pair of endpoint
equality transports. -/
theorem generalLiftRetainedInverseMapCompFactors_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftRetainedInverseMapCompFactors F hF f hf A B).hom =
      (eqToHom
          (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y) A).symm ▷
        ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) B))) ≫
      ((generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom (𝟙 Y) A) ◁
        eqToHom
          (generalLiftPrelaxFunctor_map_inverse F hF f hf B).symm) := by
  rfl

/-- Factor transport in the retained-then-inverse compositor is natural in
the inverse factor's retained coordinate. -/
theorem generalLiftRetainedInverseMapCompFactors_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    (F.map (canonicalSourceHom (𝟙 Y) A) ◁
        ((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X) η))) ≫
      (generalLiftRetainedInverseMapCompFactors F hF f hf A C).hom =
    (generalLiftRetainedInverseMapCompFactors F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom (𝟙 Y) A) ◁
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f η)) := by
  rw [generalLiftRetainedInverseMapCompFactors_hom,
    generalLiftRetainedInverseMapCompFactors_hom]
  exact comp_naturality_of_squares
    (whisker_exchange
      (eqToHom
        (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y) A).symm)
      ((generalLiftSourceEquivalence F hF f).inv ◁
        F.map₂ (canonicalSourceTwoCell (𝟙 X) η)))
    (whiskerLeft_naturality_of_square
      ((generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom (𝟙 Y) A))
      (generalLiftMap₂InverseTransportSymm F hF f hf η))

/-- Factor transport in the retained-then-inverse compositor is natural in
the retained factor's coordinate. -/
theorem generalLiftRetainedInverseMapCompFactors_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    (F.map₂ (canonicalSourceTwoCell (𝟙 Y) η) ▷
        ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) B))) ≫
      (generalLiftRetainedInverseMapCompFactors F hF f hf C B).hom =
    (generalLiftRetainedInverseMapCompFactors F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 Y) η) ▷
        (generalLiftPrelaxFunctor F hF).map
          (canonicalInverseHom f B)) := by
  rw [generalLiftRetainedInverseMapCompFactors_hom,
    generalLiftRetainedInverseMapCompFactors_hom]
  exact comp_naturality_of_squares
    (whiskerRight_naturality_of_square
      ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) B))
      (generalLiftMap₂ForwardTransportSymm F hF (𝟙 Y) η))
    (whisker_exchange
      ((generalLiftPrelaxFunctor F hF).map₂
        (canonicalForwardTwoCell (𝟙 Y) η))
      (eqToHom
        (generalLiftPrelaxFunctor_map_inverse F hF f hf B).symm)).symm

/-- The complete post-comparison transport for the retained-then-inverse
compositor. -/
noncomputable def generalLiftRetainedInverseMapCompTransport
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftPrelaxFunctor F hF).map
        (canonicalInverseHom f (A × B)) ≅
      ((generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom (𝟙 Y) A) ≫
        (generalLiftPrelaxFunctor F hF).map
          (canonicalInverseHom f B)) :=
  generalLiftInverseRetainedMapCompCore F hF f hf A B ≪≫
    (generalLiftRetainedInverseMapCompSliding F hF f A B ≪≫
      generalLiftRetainedInverseMapCompFactors F hF f hf A B)

/-- The hom of the complete retained-then-inverse transport is the composite
of its core, sliding, and factor-transport stages. -/
theorem generalLiftRetainedInverseMapCompTransport_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftRetainedInverseMapCompTransport F hF f hf A B).hom =
      (generalLiftInverseRetainedMapCompCore F hF f hf A B).hom ≫
        ((generalLiftRetainedInverseMapCompSliding F hF f A B).hom ≫
          (generalLiftRetainedInverseMapCompFactors F hF f hf A B).hom) := by
  rfl

/-- The complete retained-then-inverse transport is natural in the inverse
factor's retained coordinate. -/
theorem generalLiftRetainedInverseMapCompTransport_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f
            (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η)) ≫
      (generalLiftRetainedInverseMapCompTransport F hF f hf A C).hom =
    (generalLiftRetainedInverseMapCompTransport F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom (𝟙 Y) A) ◁
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f η)) := by
  rw [generalLiftRetainedInverseMapCompTransport_hom,
    generalLiftRetainedInverseMapCompTransport_hom]
  exact comp_naturality_of_squares
    (generalLiftInverseRetainedMapCompCore_naturality_right
      F hF f hf A η)
    (comp_naturality_of_squares
      (generalLiftRetainedInverseMapCompSliding_naturality_right
        F hF f A η)
      (generalLiftRetainedInverseMapCompFactors_naturality_right
        F hF f hf A η))

/-- The complete retained-then-inverse transport is natural in the retained
factor's coordinate. -/
theorem generalLiftRetainedInverseMapCompTransport_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f
            (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B))) ≫
      (generalLiftRetainedInverseMapCompTransport F hF f hf C B).hom =
    (generalLiftRetainedInverseMapCompTransport F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 Y) η) ▷
        (generalLiftPrelaxFunctor F hF).map
          (canonicalInverseHom f B)) := by
  rw [generalLiftRetainedInverseMapCompTransport_hom,
    generalLiftRetainedInverseMapCompTransport_hom]
  exact comp_naturality_of_squares
    (generalLiftInverseRetainedMapCompCore_naturality_left
      F hF f hf η B)
    (comp_naturality_of_squares
      (generalLiftRetainedInverseMapCompSliding_naturality_left
        F hF f η B)
      (generalLiftRetainedInverseMapCompFactors_naturality_left
        F hF f hf η B))

set_option backward.isDefEq.respectTransparency false in
/-- Endpoint transport preserves the retained/retained/inverse source
associativity law. -/
theorem generalLiftRetainedInverseMapCompTransport_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f
            (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftRetainedInverseMapCompTransport F hF f hf
          A (B × C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 Y) A) ◁
          (generalLiftRetainedInverseMapCompTransport F hF f hf B C).hom =
      (generalLiftRetainedInverseMapCompTransport F hF f hf
          (A × B) C).hom ≫
        ((generalLiftForwardMapCompTransport F hF
            (𝟙 Y) (𝟙 Y) A B).hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f C)) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 Y) A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 Y) B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f C))).hom := by
  simp only [generalLiftRetainedInverseMapCompTransport_hom,
    generalLiftInverseRetainedMapCompCore_hom,
    generalLiftRetainedInverseMapCompSliding_hom,
    generalLiftRetainedInverseMapCompFactors_hom,
    generalLiftForwardMapCompTransport_hom,
    generalLiftForwardMapCompCore_hom,
    generalLiftForwardMapCompFactors_hom, Category.assoc]
  simpa [eqToIso.hom, eqToIso.inv,
    generalLiftRetainedInverseMapCompSource_hom,
    generalLiftRetainedInverseMapCompSliding_hom,
    generalLiftForwardMapCompSourceRightIdentity_hom,
    Category.assoc] using
    transportCompositor_associativity
    (e₀ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y) A))
    (e₁ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y) B))
    (e₂ := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf C))
    (e₀₁ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y) (A × B)))
    (e₁₂ := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf (B × C)))
    (eL := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf ((A × B) × C)))
    (eR := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf (A × (B × C))))
    (c₀₁ := (generalLiftForwardMapCompSourceRightIdentity F
      (𝟙 Y) A B).hom)
    (c₁₂ := (generalLiftRetainedInverseMapCompSource F hF f B C).hom)
    (cL := (generalLiftRetainedInverseMapCompSource F hF f (A × B) C).hom)
    (cR := (generalLiftRetainedInverseMapCompSource F hF f A (B × C)).hom)
    (aP := (generalLiftSourceEquivalence F hF f).inv ◁
      F.map₂ (canonicalSourceTwoCell (𝟙 X)
        (MonoidalCategory.associator A B C).hom))
    (aQ := (generalLiftPrelaxFunctor F hF).map₂
      (canonicalInverseTwoCell f
        (MonoidalCategory.associator A B C).hom))
    (ha := generalLiftMap₂InverseTransport F hF f hf
      (MonoidalCategory.associator A B C).hom)
    (hc := generalLiftRetainedInverseMapCompSource_associativity
      F hF f A B C)

set_option backward.isDefEq.respectTransparency false in
/-- Endpoint transport preserves the mixed retained/inverse/retained source
associativity law. -/
theorem generalLiftRetainedInverseRetainedMapCompTransport_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f
            (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftRetainedInverseMapCompTransport F hF f hf
          A (B × C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 Y) A) ◁
          (generalLiftInverseRetainedMapCompTransport F hF f hf B C).hom =
      (generalLiftInverseRetainedMapCompTransport F hF f hf
          (A × B) C).hom ≫
        ((generalLiftRetainedInverseMapCompTransport F hF f hf A B).hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 X) C)) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 Y) A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 X) C))).hom := by
  simp only [generalLiftRetainedInverseMapCompTransport_hom,
    generalLiftInverseRetainedMapCompCore_hom,
    generalLiftRetainedInverseMapCompSliding_hom,
    generalLiftRetainedInverseMapCompFactors_hom,
    generalLiftInverseRetainedMapCompTransport_hom,
    generalLiftInverseRetainedMapCompFactors_hom, Category.assoc]
  simpa [eqToIso.hom, eqToIso.inv,
    generalLiftRetainedInverseMapCompSourceNormalized_hom,
    generalLiftRetainedInverseMapCompSliding_hom,
    generalLiftInverseRetainedMapCompSourceNormalized_hom,
    generalLiftForwardMapCompSourceRightIdentity_hom,
    Category.assoc] using
    transportCompositor_associativity
    (e₀ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y) A))
    (e₁ := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf B))
    (e₂ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X) C))
    (e₀₁ := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf (A × B)))
    (e₁₂ := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf (B × C)))
    (eL := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf ((A × B) × C)))
    (eR := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf (A × (B × C))))
    (c₀₁ :=
      (generalLiftRetainedInverseMapCompSourceNormalized F hF f A B).hom)
    (c₁₂ :=
      (generalLiftInverseRetainedMapCompSourceNormalized F hF f B C).hom)
    (cL :=
      (generalLiftInverseRetainedMapCompSourceNormalized F hF f (A × B) C).hom)
    (cR :=
      (generalLiftRetainedInverseMapCompSourceNormalized F hF f A (B × C)).hom)
    (aP := (generalLiftSourceEquivalence F hF f).inv ◁
      F.map₂ (canonicalSourceTwoCell (𝟙 X)
        (MonoidalCategory.associator A B C).hom))
    (aQ := (generalLiftPrelaxFunctor F hF).map₂
      (canonicalInverseTwoCell f
        (MonoidalCategory.associator A B C).hom))
    (ha := generalLiftMap₂InverseTransport F hF f hf
      (MonoidalCategory.associator A B C).hom)
    (hc := generalLiftRetainedInverseRetainedMapCompSource_associativity
      F hF f A B C)

/-- Composition comparison for a retained-coordinate endomorphism followed
by a genuine inverse arrow. -/
noncomputable def generalLiftMapCompRetainedInverse
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom (𝟙 Y) A ≫ canonicalInverseHom f B) ≅
      ((generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom (𝟙 Y) A) ≫
        (generalLiftPrelaxFunctor F hF).map
          (canonicalInverseHom f B)) :=
  (generalLiftPrelaxFunctor F hF).map₂Iso
      (canonicalRetainedInverseCompositionComparison f A B) ≪≫
    generalLiftRetainedInverseMapCompTransport F hF f hf A B

/-- The hom of the complete retained-then-inverse compositor is its mapped
target comparison followed by the named transport. -/
theorem generalLiftMapCompRetainedInverse_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftMapCompRetainedInverse F hF f hf A B).hom =
      (generalLiftPrelaxFunctor F hF).map₂
          (canonicalRetainedInverseCompositionComparison f A B).hom ≫
        (generalLiftRetainedInverseMapCompTransport F hF f hf A B).hom := by
  rfl

/-- The complete retained-then-inverse composition comparison is natural in
retained-coordinate 2-cells on its inverse factor. -/
theorem generalLiftMapCompRetainedInverse_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardHom (𝟙 Y) A ◁
            canonicalInverseTwoCell f η) ≫
      (generalLiftMapCompRetainedInverse F hF f hf A C).hom =
    (generalLiftMapCompRetainedInverse F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom (𝟙 Y) A) ◁
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f η)) := by
  rw [generalLiftMapCompRetainedInverse_hom,
    generalLiftMapCompRetainedInverse_hom]
  exact comp_naturality_of_squares
    (generalLiftRetainedInverseMapCompTarget_naturality_right F hF f A η)
    (generalLiftRetainedInverseMapCompTransport_naturality_right
      F hF f hf A η)

/-- The complete retained-then-inverse composition comparison is natural in
retained-coordinate 2-cells on its retained factor. -/
theorem generalLiftMapCompRetainedInverse_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 Y) η ▷
            canonicalInverseHom f B) ≫
      (generalLiftMapCompRetainedInverse F hF f hf C B).hom =
    (generalLiftMapCompRetainedInverse F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 Y) η) ▷
        (generalLiftPrelaxFunctor F hF).map
          (canonicalInverseHom f B)) := by
  rw [generalLiftMapCompRetainedInverse_hom,
    generalLiftMapCompRetainedInverse_hom]
  exact comp_naturality_of_squares
    (generalLiftRetainedInverseMapCompTarget_naturality_left F hF f η B)
    (generalLiftRetainedInverseMapCompTransport_naturality_left
      F hF f hf η B)

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

/-- Forward/retained/inverse target comparisons satisfy the cancellation
three-fold associativity square. -/
theorem canonicalForwardRetainedInverseComparison_associativity
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    ((canonicalForwardCompositionComparison f (𝟙 Y) A B).hom ▷
          canonicalInverseHom f C) ≫
        (canonicalForwardInverseCompositionComparison
          f (A × B) C).hom ≫
        canonicalForwardTwoCell (𝟙 X)
          (MonoidalCategory.associator A B C).hom =
      (α_ (canonicalForwardHom f A)
          (canonicalForwardHom (𝟙 Y) B)
          (canonicalInverseHom f C)).hom ≫
        (canonicalForwardHom f A ◁
          (canonicalRetainedInverseCompositionComparison f B C).hom) ≫
        (canonicalForwardInverseCompositionComparison
          f A (B × C)).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- Applying the arbitrary target action preserves the
forward/retained/inverse target associativity square. -/
theorem generalLiftForwardRetainedInverseMapCompTarget_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          ((canonicalForwardCompositionComparison f (𝟙 Y) A B).hom ▷
            canonicalInverseHom f C) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardInverseCompositionComparison
            f (A × B) C).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 X)
            (MonoidalCategory.associator A B C).hom) =
      (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalForwardHom f A)
            (canonicalForwardHom (𝟙 Y) B)
            (canonicalInverseHom f C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardHom f A ◁
            (canonicalRetainedInverseCompositionComparison f B C).hom) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardInverseCompositionComparison
            f A (B × C)).hom := by
  simpa only [(generalLiftPrelaxFunctor F hF).map₂_comp] using
    congrArg (fun η => (generalLiftPrelaxFunctor F hF).map₂ η)
      (canonicalForwardRetainedInverseComparison_associativity
        f A B C)

/-- Retained/forward/inverse target comparisons satisfy the cancellation
three-fold associativity square. -/
theorem canonicalRetainedForwardInverseComparison_associativity
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    ((canonicalForwardCompositionComparison (𝟙 X) f A B).hom ▷
          canonicalInverseHom f C) ≫
        (canonicalForwardInverseCompositionComparison
          f (A × B) C).hom ≫
        canonicalForwardTwoCell (𝟙 X)
          (MonoidalCategory.associator A B C).hom =
      (α_ (canonicalForwardHom (𝟙 X) A)
          (canonicalForwardHom f B)
          (canonicalInverseHom f C)).hom ≫
        (canonicalForwardHom (𝟙 X) A ◁
          (canonicalForwardInverseCompositionComparison f B C).hom) ≫
        (canonicalForwardCompositionComparison
          (𝟙 X) (𝟙 X) A (B × C)).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- Applying the arbitrary target action preserves the
retained/forward/inverse target associativity square. -/
theorem generalLiftRetainedForwardInverseMapCompTarget_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          ((canonicalForwardCompositionComparison (𝟙 X) f A B).hom ▷
            canonicalInverseHom f C) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardInverseCompositionComparison
            f (A × B) C).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 X)
            (MonoidalCategory.associator A B C).hom) =
      (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalForwardHom (𝟙 X) A)
            (canonicalForwardHom f B)
            (canonicalInverseHom f C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardHom (𝟙 X) A ◁
            (canonicalForwardInverseCompositionComparison f B C).hom) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardCompositionComparison
            (𝟙 X) (𝟙 X) A (B × C)).hom := by
  simpa only [(generalLiftPrelaxFunctor F hF).map₂_comp] using
    congrArg (fun η => (generalLiftPrelaxFunctor F hF).map₂ η)
      (canonicalRetainedForwardInverseComparison_associativity
        f A B C)

/-- Forward/inverse/retained target comparisons satisfy the cancellation
three-fold associativity square. -/
theorem canonicalForwardInverseRetainedComparison_associativity
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    ((canonicalForwardInverseCompositionComparison f A B).hom ▷
          canonicalForwardHom (𝟙 X) C) ≫
        (canonicalForwardCompositionComparison
          (𝟙 X) (𝟙 X) (A × B) C).hom ≫
        canonicalForwardTwoCell (𝟙 X)
          (MonoidalCategory.associator A B C).hom =
      (α_ (canonicalForwardHom f A)
          (canonicalInverseHom f B)
          (canonicalForwardHom (𝟙 X) C)).hom ≫
        (canonicalForwardHom f A ◁
          (canonicalInverseRetainedCompositionComparison f B C).hom) ≫
        (canonicalForwardInverseCompositionComparison
          f A (B × C)).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- Applying the arbitrary target action preserves the
forward/inverse/retained target associativity square. -/
theorem generalLiftForwardInverseRetainedMapCompTarget_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          ((canonicalForwardInverseCompositionComparison f A B).hom ▷
            canonicalForwardHom (𝟙 X) C) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardCompositionComparison
            (𝟙 X) (𝟙 X) (A × B) C).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 X)
            (MonoidalCategory.associator A B C).hom) =
      (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalForwardHom f A)
            (canonicalInverseHom f B)
            (canonicalForwardHom (𝟙 X) C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardHom f A ◁
            (canonicalInverseRetainedCompositionComparison f B C).hom) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardInverseCompositionComparison
            f A (B × C)).hom := by
  simpa only [(generalLiftPrelaxFunctor F hF).map₂_comp] using
    congrArg (fun η => (generalLiftPrelaxFunctor F hF).map₂ η)
      (canonicalForwardInverseRetainedComparison_associativity
        f A B C)

/-- Inverse/forward/retained target comparisons satisfy the cancellation
three-fold associativity square. -/
theorem canonicalInverseForwardRetainedComparison_associativity
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    ((canonicalInverseForwardCompositionComparison f A B).hom ▷
          canonicalForwardHom (𝟙 Y) C) ≫
        (canonicalForwardCompositionComparison
          (𝟙 Y) (𝟙 Y) (A × B) C).hom ≫
        canonicalForwardTwoCell (𝟙 Y)
          (MonoidalCategory.associator A B C).hom =
      (α_ (canonicalInverseHom f A)
          (canonicalForwardHom f B)
          (canonicalForwardHom (𝟙 Y) C)).hom ≫
        (canonicalInverseHom f A ◁
          (canonicalForwardCompositionComparison f (𝟙 Y) B C).hom) ≫
        (canonicalInverseForwardCompositionComparison
          f A (B × C)).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- Applying the arbitrary target action preserves the
inverse/forward/retained target associativity square. -/
theorem generalLiftInverseForwardRetainedMapCompTarget_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          ((canonicalInverseForwardCompositionComparison f A B).hom ▷
            canonicalForwardHom (𝟙 Y) C) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardCompositionComparison
            (𝟙 Y) (𝟙 Y) (A × B) C).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 Y)
            (MonoidalCategory.associator A B C).hom) =
      (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalInverseHom f A)
            (canonicalForwardHom f B)
            (canonicalForwardHom (𝟙 Y) C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseHom f A ◁
            (canonicalForwardCompositionComparison f (𝟙 Y) B C).hom) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseForwardCompositionComparison
            f A (B × C)).hom := by
  simpa only [(generalLiftPrelaxFunctor F hF).map₂_comp] using
    congrArg (fun η => (generalLiftPrelaxFunctor F hF).map₂ η)
      (canonicalInverseForwardRetainedComparison_associativity
        f A B C)

/-- Inverse/retained/forward target comparisons satisfy the cancellation
three-fold associativity square. -/
theorem canonicalInverseRetainedForwardComparison_associativity
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    ((canonicalInverseRetainedCompositionComparison f A B).hom ▷
          canonicalForwardHom f C) ≫
        (canonicalInverseForwardCompositionComparison
          f (A × B) C).hom ≫
        canonicalForwardTwoCell (𝟙 Y)
          (MonoidalCategory.associator A B C).hom =
      (α_ (canonicalInverseHom f A)
          (canonicalForwardHom (𝟙 X) B)
          (canonicalForwardHom f C)).hom ≫
        (canonicalInverseHom f A ◁
          (canonicalForwardCompositionComparison (𝟙 X) f B C).hom) ≫
        (canonicalInverseForwardCompositionComparison
          f A (B × C)).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- Applying the arbitrary target action preserves the
inverse/retained/forward target associativity square. -/
theorem generalLiftInverseRetainedForwardMapCompTarget_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          ((canonicalInverseRetainedCompositionComparison f A B).hom ▷
            canonicalForwardHom f C) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseForwardCompositionComparison
            f (A × B) C).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 Y)
            (MonoidalCategory.associator A B C).hom) =
      (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalInverseHom f A)
            (canonicalForwardHom (𝟙 X) B)
            (canonicalForwardHom f C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseHom f A ◁
            (canonicalForwardCompositionComparison (𝟙 X) f B C).hom) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseForwardCompositionComparison
            f A (B × C)).hom := by
  simpa only [(generalLiftPrelaxFunctor F hF).map₂_comp] using
    congrArg (fun η => (generalLiftPrelaxFunctor F hF).map₂ η)
      (canonicalInverseRetainedForwardComparison_associativity
        f A B C)

/-- Retained/inverse/forward target comparisons satisfy the cancellation
three-fold associativity square. -/
theorem canonicalRetainedInverseForwardComparison_associativity
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    ((canonicalRetainedInverseCompositionComparison f A B).hom ▷
          canonicalForwardHom f C) ≫
        (canonicalInverseForwardCompositionComparison
          f (A × B) C).hom ≫
        canonicalForwardTwoCell (𝟙 Y)
          (MonoidalCategory.associator A B C).hom =
      (α_ (canonicalForwardHom (𝟙 Y) A)
          (canonicalInverseHom f B)
          (canonicalForwardHom f C)).hom ≫
        (canonicalForwardHom (𝟙 Y) A ◁
          (canonicalInverseForwardCompositionComparison f B C).hom) ≫
        (canonicalForwardCompositionComparison
          (𝟙 Y) (𝟙 Y) A (B × C)).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- Applying the arbitrary target action preserves the
retained/inverse/forward target associativity square. -/
theorem generalLiftRetainedInverseForwardMapCompTarget_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          ((canonicalRetainedInverseCompositionComparison f A B).hom ▷
            canonicalForwardHom f C) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseForwardCompositionComparison
            f (A × B) C).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 Y)
            (MonoidalCategory.associator A B C).hom) =
      (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalForwardHom (𝟙 Y) A)
            (canonicalInverseHom f B)
            (canonicalForwardHom f C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardHom (𝟙 Y) A ◁
            (canonicalInverseForwardCompositionComparison f B C).hom) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardCompositionComparison
            (𝟙 Y) (𝟙 Y) A (B × C)).hom := by
  simpa only [(generalLiftPrelaxFunctor F hF).map₂_comp] using
    congrArg (fun η => (generalLiftPrelaxFunctor F hF).map₂ η)
      (canonicalRetainedInverseForwardComparison_associativity
        f A B C)

/-- Forward/inverse/forward target comparisons satisfy the alternating
cancellation three-fold associativity square. -/
theorem canonicalForwardInverseForwardComparison_associativity
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    ((canonicalForwardInverseCompositionComparison f A B).hom ▷
          canonicalForwardHom f C) ≫
        (canonicalForwardCompositionComparison
          (𝟙 X) f (A × B) C).hom ≫
        canonicalForwardTwoCell f
          (MonoidalCategory.associator A B C).hom =
      (α_ (canonicalForwardHom f A)
          (canonicalInverseHom f B)
          (canonicalForwardHom f C)).hom ≫
        (canonicalForwardHom f A ◁
          (canonicalInverseForwardCompositionComparison f B C).hom) ≫
        (canonicalForwardCompositionComparison
          f (𝟙 Y) A (B × C)).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- Applying the arbitrary target action preserves the alternating
forward/inverse/forward target associativity square. -/
theorem generalLiftForwardInverseForwardMapCompTarget_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          ((canonicalForwardInverseCompositionComparison f A B).hom ▷
            canonicalForwardHom f C) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardCompositionComparison
            (𝟙 X) f (A × B) C).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell f
            (MonoidalCategory.associator A B C).hom) =
      (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalForwardHom f A)
            (canonicalInverseHom f B)
            (canonicalForwardHom f C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardHom f A ◁
            (canonicalInverseForwardCompositionComparison f B C).hom) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardCompositionComparison
            f (𝟙 Y) A (B × C)).hom := by
  simpa only [(generalLiftPrelaxFunctor F hF).map₂_comp] using
    congrArg (fun η => (generalLiftPrelaxFunctor F hF).map₂ η)
      (canonicalForwardInverseForwardComparison_associativity
        f A B C)

/-- Inverse/forward/inverse target comparisons satisfy the dual alternating
cancellation three-fold associativity square. -/
theorem canonicalInverseForwardInverseComparison_associativity
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    ((canonicalInverseForwardCompositionComparison f A B).hom ▷
          canonicalInverseHom f C) ≫
        (canonicalRetainedInverseCompositionComparison
          f (A × B) C).hom ≫
        canonicalInverseTwoCell f
          (MonoidalCategory.associator A B C).hom =
      (α_ (canonicalInverseHom f A)
          (canonicalForwardHom f B)
          (canonicalInverseHom f C)).hom ≫
        (canonicalInverseHom f A ◁
          (canonicalForwardInverseCompositionComparison f B C).hom) ≫
        (canonicalInverseRetainedCompositionComparison
          f A (B × C)).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- Applying the arbitrary target action preserves the dual alternating
inverse/forward/inverse target associativity square. -/
theorem generalLiftInverseForwardInverseMapCompTarget_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          ((canonicalInverseForwardCompositionComparison f A B).hom ▷
            canonicalInverseHom f C) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalRetainedInverseCompositionComparison
            f (A × B) C).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f
            (MonoidalCategory.associator A B C).hom) =
      (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalInverseHom f A)
            (canonicalForwardHom f B)
            (canonicalInverseHom f C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseHom f A ◁
            (canonicalForwardInverseCompositionComparison f B C).hom) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseRetainedCompositionComparison
            f A (B × C)).hom := by
  simpa only [(generalLiftPrelaxFunctor F hF).map₂_comp] using
    congrArg (fun η => (generalLiftPrelaxFunctor F hF).map₂ η)
      (canonicalInverseForwardInverseComparison_associativity
        f A B C)

/-- Inverse/forward cancellation is natural in the forward factor's retained
coordinate. -/
theorem canonicalInverseForwardCompositionComparison_naturality_right
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) {B C : Type} (η : B ⟶ C) :
    (canonicalInverseHom f A ◁ canonicalForwardTwoCell f η) ≫
        (canonicalInverseForwardCompositionComparison f A C).hom =
      (canonicalInverseForwardCompositionComparison f A B).hom ≫
        canonicalForwardTwoCell (𝟙 Y)
          (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η) := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- Inverse/forward cancellation is natural in the inverse factor's retained
coordinate. -/
theorem canonicalInverseForwardCompositionComparison_naturality_left
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A C : Type} (η : A ⟶ C) (B : Type) :
    (canonicalInverseTwoCell f η ▷ canonicalForwardHom f B) ≫
        (canonicalInverseForwardCompositionComparison f C B).hom =
      (canonicalInverseForwardCompositionComparison f A B).hom ≫
        canonicalForwardTwoCell (𝟙 Y)
          (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B)) := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- Mapping right naturality of inverse/forward cancellation through the lift
preserves the vertical composite. -/
theorem generalLiftInverseForwardMapCompTarget_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) {B C : Type} (η : B ⟶ C) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseHom f A ◁ canonicalForwardTwoCell f η) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseForwardCompositionComparison f A C).hom =
      (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseForwardCompositionComparison f A B).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 Y)
            (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η)) := by
  rw [← (generalLiftPrelaxFunctor F hF).map₂_comp,
    canonicalInverseForwardCompositionComparison_naturality_right,
    (generalLiftPrelaxFunctor F hF).map₂_comp]

/-- Mapping left naturality of inverse/forward cancellation through the lift
preserves the vertical composite. -/
theorem generalLiftInverseForwardMapCompTarget_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A C : Type} (η : A ⟶ C) (B : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f η ▷ canonicalForwardHom f B) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseForwardCompositionComparison f C B).hom =
      (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseForwardCompositionComparison f A B).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 Y)
            (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B))) := by
  rw [← (generalLiftPrelaxFunctor F hF).map₂_comp,
    canonicalInverseForwardCompositionComparison_naturality_left,
    (generalLiftPrelaxFunctor F hF).map₂_comp]

/-- The inner sliding stage moves the chosen forward equivalence past the
left retained coordinate. -/
noncomputable def generalLiftInverseForwardMapCompSlidingInner
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftSourceEquivalence F hF f).hom ≫
        (F.map (canonicalSourceHom (𝟙 Y) A) ≫
          F.map (canonicalSourceHom (𝟙 Y) B)) ≅
      F.map (canonicalSourceHom (𝟙 X) A) ≫
        ((generalLiftSourceEquivalence F hF f).hom ≫
          F.map (canonicalSourceHom (𝟙 Y) B)) :=
  (α_ (generalLiftSourceEquivalence F hF f).hom
      (F.map (canonicalSourceHom (𝟙 Y) A))
      (F.map (canonicalSourceHom (𝟙 Y) B))).symm ≪≫
    whiskerRightIso (generalLiftForwardSlidingSource F hF f A)
      (F.map (canonicalSourceHom (𝟙 Y) B)) ≪≫
    α_ (F.map (canonicalSourceHom (𝟙 X) A))
      (generalLiftSourceEquivalence F hF f).hom
      (F.map (canonicalSourceHom (𝟙 Y) B))

/-- The hom of the inverse/forward inner sliding stage is its three explicit
coherence factors. -/
theorem generalLiftInverseForwardMapCompSlidingInner_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftInverseForwardMapCompSlidingInner F hF f A B).hom =
      (α_ (generalLiftSourceEquivalence F hF f).hom
        (F.map (canonicalSourceHom (𝟙 Y) A))
        (F.map (canonicalSourceHom (𝟙 Y) B))).inv ≫
      ((generalLiftForwardSlidingSource F hF f A).hom ▷
        F.map (canonicalSourceHom (𝟙 Y) B)) ≫
      (α_ (F.map (canonicalSourceHom (𝟙 X) A))
        (generalLiftSourceEquivalence F hF f).hom
        (F.map (canonicalSourceHom (𝟙 Y) B))).hom := by
  rfl

/-- Inner sliding is natural in the forward factor's retained coordinate. -/
theorem generalLiftInverseForwardMapCompSlidingInner_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) {B C : Type} (η : B ⟶ C) :
    ((generalLiftSourceEquivalence F hF f).hom ◁
        (F.map (canonicalSourceHom (𝟙 Y) A) ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 Y) η))) ≫
      (generalLiftInverseForwardMapCompSlidingInner F hF f A C).hom =
    (generalLiftInverseForwardMapCompSlidingInner F hF f A B).hom ≫
      (F.map (canonicalSourceHom (𝟙 X) A) ◁
        ((generalLiftSourceEquivalence F hF f).hom ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 Y) η))) := by
  rw [generalLiftInverseForwardMapCompSlidingInner_hom,
    generalLiftInverseForwardMapCompSlidingInner_hom]
  exact comp_naturality_of_squares
    (associator_inv_naturality_right
      (generalLiftSourceEquivalence F hF f).hom
      (F.map (canonicalSourceHom (𝟙 Y) A))
      (F.map₂ (canonicalSourceTwoCell (𝟙 Y) η)))
    (comp_naturality_of_squares
      (whisker_exchange
        (generalLiftForwardSlidingSource F hF f A).hom
        (F.map₂ (canonicalSourceTwoCell (𝟙 Y) η)))
      (associator_naturality_right
        (F.map (canonicalSourceHom (𝟙 X) A))
        (generalLiftSourceEquivalence F hF f).hom
        (F.map₂ (canonicalSourceTwoCell (𝟙 Y) η))))

/-- Inner sliding is natural in the inverse factor's retained coordinate. -/
theorem generalLiftInverseForwardMapCompSlidingInner_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A C : Type} (η : A ⟶ C) (B : Type) :
    ((generalLiftSourceEquivalence F hF f).hom ◁
        (F.map₂ (canonicalSourceTwoCell (𝟙 Y) η) ▷
          F.map (canonicalSourceHom (𝟙 Y) B))) ≫
      (generalLiftInverseForwardMapCompSlidingInner F hF f C B).hom =
    (generalLiftInverseForwardMapCompSlidingInner F hF f A B).hom ≫
      (F.map₂ (canonicalSourceTwoCell (𝟙 X) η) ▷
        ((generalLiftSourceEquivalence F hF f).hom ≫
          F.map (canonicalSourceHom (𝟙 Y) B))) := by
  rw [generalLiftInverseForwardMapCompSlidingInner_hom,
    generalLiftInverseForwardMapCompSlidingInner_hom]
  exact comp_naturality_of_squares
    (associator_inv_naturality_middle
      (generalLiftSourceEquivalence F hF f).hom
      (F.map₂ (canonicalSourceTwoCell (𝟙 Y) η))
      (F.map (canonicalSourceHom (𝟙 Y) B)))
    (comp_naturality_of_squares
      (whiskerRight_naturality_of_square
        (F.map (canonicalSourceHom (𝟙 Y) B))
        (generalLiftForwardSlidingSource_naturality F hF f η))
      (associator_naturality_left
        (F.map₂ (canonicalSourceTwoCell (𝟙 X) η))
        (generalLiftSourceEquivalence F hF f).hom
        (F.map (canonicalSourceHom (𝟙 Y) B))))

/-- The outer sliding stage whisks the inner move by the chosen inverse and
restores the cancellation-factor association. -/
noncomputable def generalLiftInverseForwardMapCompSliding
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftSourceEquivalence F hF f).inv ≫
        ((generalLiftSourceEquivalence F hF f).hom ≫
          (F.map (canonicalSourceHom (𝟙 Y) A) ≫
            F.map (canonicalSourceHom (𝟙 Y) B))) ≅
      ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) A)) ≫
        ((generalLiftSourceEquivalence F hF f).hom ≫
          F.map (canonicalSourceHom (𝟙 Y) B)) :=
  whiskerLeftIso (generalLiftSourceEquivalence F hF f).inv
      (generalLiftInverseForwardMapCompSlidingInner F hF f A B) ≪≫
    (α_ (generalLiftSourceEquivalence F hF f).inv
      (F.map (canonicalSourceHom (𝟙 X) A))
      ((generalLiftSourceEquivalence F hF f).hom ≫
        F.map (canonicalSourceHom (𝟙 Y) B))).symm

/-- The hom of the outer sliding stage is the whiskered inner move followed by
inverse associator transport. -/
theorem generalLiftInverseForwardMapCompSliding_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftInverseForwardMapCompSliding F hF f A B).hom =
      ((generalLiftSourceEquivalence F hF f).inv ◁
        (generalLiftInverseForwardMapCompSlidingInner F hF f A B).hom) ≫
      (α_ (generalLiftSourceEquivalence F hF f).inv
        (F.map (canonicalSourceHom (𝟙 X) A))
        ((generalLiftSourceEquivalence F hF f).hom ≫
          F.map (canonicalSourceHom (𝟙 Y) B))).inv := by
  rfl

/-- Outer sliding is natural in the forward factor's retained coordinate. -/
theorem generalLiftInverseForwardMapCompSliding_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) {B C : Type} (η : B ⟶ C) :
    ((generalLiftSourceEquivalence F hF f).inv ◁
      ((generalLiftSourceEquivalence F hF f).hom ◁
        (F.map (canonicalSourceHom (𝟙 Y) A) ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 Y) η)))) ≫
      (generalLiftInverseForwardMapCompSliding F hF f A C).hom =
    (generalLiftInverseForwardMapCompSliding F hF f A B).hom ≫
      (((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) A)) ◁
        ((generalLiftSourceEquivalence F hF f).hom ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 Y) η))) := by
  rw [generalLiftInverseForwardMapCompSliding_hom,
    generalLiftInverseForwardMapCompSliding_hom]
  exact comp_naturality_of_squares
    (whiskerLeft_naturality_of_square
      (generalLiftSourceEquivalence F hF f).inv
      (generalLiftInverseForwardMapCompSlidingInner_naturality_right
        F hF f A η))
    (associator_inv_naturality_right
      (generalLiftSourceEquivalence F hF f).inv
      (F.map (canonicalSourceHom (𝟙 X) A))
      ((generalLiftSourceEquivalence F hF f).hom ◁
        F.map₂ (canonicalSourceTwoCell (𝟙 Y) η)))

/-- Outer sliding is natural in the inverse factor's retained coordinate. -/
theorem generalLiftInverseForwardMapCompSliding_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A C : Type} (η : A ⟶ C) (B : Type) :
    ((generalLiftSourceEquivalence F hF f).inv ◁
      ((generalLiftSourceEquivalence F hF f).hom ◁
        (F.map₂ (canonicalSourceTwoCell (𝟙 Y) η) ▷
          F.map (canonicalSourceHom (𝟙 Y) B)))) ≫
      (generalLiftInverseForwardMapCompSliding F hF f C B).hom =
    (generalLiftInverseForwardMapCompSliding F hF f A B).hom ≫
      (((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X) η)) ▷
        ((generalLiftSourceEquivalence F hF f).hom ≫
          F.map (canonicalSourceHom (𝟙 Y) B))) := by
  rw [generalLiftInverseForwardMapCompSliding_hom,
    generalLiftInverseForwardMapCompSliding_hom]
  exact comp_naturality_of_squares
    (whiskerLeft_naturality_of_square
      (generalLiftSourceEquivalence F hF f).inv
      (generalLiftInverseForwardMapCompSlidingInner_naturality_left
        F hF f η B))
    (associator_inv_naturality_middle
      (generalLiftSourceEquivalence F hF f).inv
      (F.map₂ (canonicalSourceTwoCell (𝟙 X) η))
      ((generalLiftSourceEquivalence F hF f).hom ≫
        F.map (canonicalSourceHom (𝟙 Y) B)))

/-- The factorization stage replaces the remaining forward equivalence/source
pair by the source image of the forward factor. -/
noncomputable def generalLiftInverseForwardMapCompFactorization
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) A)) ≫
        ((generalLiftSourceEquivalence F hF f).hom ≫
          F.map (canonicalSourceHom (𝟙 Y) B)) ≅
      ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) A)) ≫
        F.map (canonicalSourceHom f B) :=
  whiskerLeftIso
    ((generalLiftSourceEquivalence F hF f).inv ≫
      F.map (canonicalSourceHom (𝟙 X) A))
    (generalLiftForwardFactorizationSource F hF f B).symm

/-- The factorization hom is the inverse forward factorization whiskered by
the fixed inverse factor. -/
theorem generalLiftInverseForwardMapCompFactorization_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftInverseForwardMapCompFactorization F hF f A B).hom =
      ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) A)) ◁
      (generalLiftForwardFactorizationSource F hF f B).inv := by
  rfl

/-- Factorization is natural in the forward factor's retained coordinate. -/
theorem generalLiftInverseForwardMapCompFactorization_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) {B C : Type} (η : B ⟶ C) :
    (((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) A)) ◁
        ((generalLiftSourceEquivalence F hF f).hom ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 Y) η))) ≫
      (generalLiftInverseForwardMapCompFactorization F hF f A C).hom =
    (generalLiftInverseForwardMapCompFactorization F hF f A B).hom ≫
      (((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) A)) ◁
        F.map₂ (canonicalSourceTwoCell f η)) := by
  rw [generalLiftInverseForwardMapCompFactorization_hom,
    generalLiftInverseForwardMapCompFactorization_hom]
  exact whiskerLeft_naturality_of_square
    ((generalLiftSourceEquivalence F hF f).inv ≫
      F.map (canonicalSourceHom (𝟙 X) A))
    (iso_inv_naturality_of_square
      (generalLiftForwardFactorizationSource F hF f B)
      (generalLiftForwardFactorizationSource F hF f C)
      (generalLiftForwardFactorizationSource_naturality F hF f η))

/-- Factorization is natural in the inverse factor's retained coordinate. -/
theorem generalLiftInverseForwardMapCompFactorization_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A C : Type} (η : A ⟶ C) (B : Type) :
    (((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X) η)) ▷
        ((generalLiftSourceEquivalence F hF f).hom ≫
          F.map (canonicalSourceHom (𝟙 Y) B))) ≫
      (generalLiftInverseForwardMapCompFactorization F hF f C B).hom =
    (generalLiftInverseForwardMapCompFactorization F hF f A B).hom ≫
      (((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X) η)) ▷
        F.map (canonicalSourceHom f B)) := by
  rw [generalLiftInverseForwardMapCompFactorization_hom,
    generalLiftInverseForwardMapCompFactorization_hom]
  exact (whisker_exchange
    ((generalLiftSourceEquivalence F hF f).inv ◁
      F.map₂ (canonicalSourceTwoCell (𝟙 X) η))
    (generalLiftForwardFactorizationSource F hF f B).inv).symm

/-- The endpoint-factor stage transports the chosen inverse and source
forward factor back to the arbitrary lift's mapped factors. -/
noncomputable def generalLiftInverseForwardMapCompFactors
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) A)) ≫
          F.map (canonicalSourceHom f B) ≅
      (generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A) ≫
        (generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom f B) :=
  whiskerRightIso
      (eqToIso
        (generalLiftPrelaxFunctor_map_inverse F hF f hf A)).symm
      (F.map (canonicalSourceHom f B)) ≪≫
    whiskerLeftIso
      ((generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A))
      (eqToIso
        (generalLiftPrelaxFunctor_map_forward F hF f B)).symm

/-- The hom of inverse/forward endpoint-factor transport is its pair of
endpoint equality transports. -/
theorem generalLiftInverseForwardMapCompFactors_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftInverseForwardMapCompFactors F hF f hf A B).hom =
      (eqToHom
          (generalLiftPrelaxFunctor_map_inverse F hF f hf A).symm ▷
        F.map (canonicalSourceHom f B)) ≫
      ((generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A) ◁
        eqToHom
          (generalLiftPrelaxFunctor_map_forward F hF f B).symm) := by
  rfl

/-- Endpoint-factor transport is natural in the forward factor's retained
coordinate. -/
theorem generalLiftInverseForwardMapCompFactors_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    (((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) A)) ◁
        F.map₂ (canonicalSourceTwoCell f η)) ≫
      (generalLiftInverseForwardMapCompFactors F hF f hf A C).hom =
    (generalLiftInverseForwardMapCompFactors F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A) ◁
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell f η)) := by
  rw [generalLiftInverseForwardMapCompFactors_hom,
    generalLiftInverseForwardMapCompFactors_hom]
  exact comp_naturality_of_squares
    (whisker_exchange
      (eqToHom
        (generalLiftPrelaxFunctor_map_inverse F hF f hf A).symm)
      (F.map₂ (canonicalSourceTwoCell f η)))
    (whiskerLeft_naturality_of_square
      ((generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A))
      (generalLiftMap₂ForwardTransportSymm F hF f η))

/-- Endpoint-factor transport is natural in the inverse factor's retained
coordinate. -/
theorem generalLiftInverseForwardMapCompFactors_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    (((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X) η)) ▷
        F.map (canonicalSourceHom f B)) ≫
      (generalLiftInverseForwardMapCompFactors F hF f hf C B).hom =
    (generalLiftInverseForwardMapCompFactors F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f η) ▷
        (generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom f B)) := by
  rw [generalLiftInverseForwardMapCompFactors_hom,
    generalLiftInverseForwardMapCompFactors_hom]
  exact comp_naturality_of_squares
    (whiskerRight_naturality_of_square
      (F.map (canonicalSourceHom f B))
      (generalLiftMap₂InverseTransportSymm F hF f hf η))
    (whisker_exchange
      ((generalLiftPrelaxFunctor F hF).map₂
        (canonicalInverseTwoCell f η))
      (eqToHom
        (generalLiftPrelaxFunctor_map_forward F hF f B).symm)).symm

/-- Cancellation, sliding, and factorization transport the two codomain
source factors to the inverse/forward source normal form. -/
noncomputable def generalLiftInverseForwardMapCompSourceTransport
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    F.map (canonicalSourceHom (𝟙 Y) A) ≫
        F.map (canonicalSourceHom (𝟙 Y) B) ≅
      ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) A)) ≫
        F.map (canonicalSourceHom f B) :=
  equivalenceCounitInsertion (generalLiftSourceEquivalence F hF f)
      (F.map (canonicalSourceHom (𝟙 Y) A) ≫
        F.map (canonicalSourceHom (𝟙 Y) B)) ≪≫
    generalLiftInverseForwardMapCompSliding F hF f A B ≪≫
    generalLiftInverseForwardMapCompFactorization F hF f A B

/-- The source transport hom is the counit insertion, sliding, and
factorization composite. -/
theorem generalLiftInverseForwardMapCompSourceTransport_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftInverseForwardMapCompSourceTransport F hF f A B).hom =
      (equivalenceCounitInsertion (generalLiftSourceEquivalence F hF f)
        (F.map (canonicalSourceHom (𝟙 Y) A) ≫
          F.map (canonicalSourceHom (𝟙 Y) B))).hom ≫
      (generalLiftInverseForwardMapCompSliding F hF f A B).hom ≫
      (generalLiftInverseForwardMapCompFactorization F hF f A B).hom := by
  rfl

/-- Endpoint-strict inverse/forward cancellation source compositor.  It
starts at the chosen retained codomain representative and exposes the source
normal form needed by the remaining inverse/forward associativity branches. -/
noncomputable def generalLiftInverseForwardMapCompSourceNormalized
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    F.map (canonicalSourceHom (𝟙 Y) (A × B)) ≅
      ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) A)) ≫
        F.map (canonicalSourceHom f B) :=
  generalLiftForwardMapCompSourceRightIdentity F (𝟙 Y) A B ≪≫
    generalLiftInverseForwardMapCompSourceTransport F hF f A B

/-- Hom expansion of the endpoint-strict inverse/forward cancellation source
compositor. -/
theorem generalLiftInverseForwardMapCompSourceNormalized_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftInverseForwardMapCompSourceNormalized F hF f A B).hom =
      (generalLiftForwardMapCompSourceRightIdentity F (𝟙 Y) A B).hom ≫
      (generalLiftInverseForwardMapCompSourceTransport F hF f A B).hom := by
  rfl

/-- Source transport is natural in the forward factor's retained
coordinate. -/
theorem generalLiftInverseForwardMapCompSourceTransport_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) {B C : Type} (η : B ⟶ C) :
    (F.map (canonicalSourceHom (𝟙 Y) A) ◁
        F.map₂ (canonicalSourceTwoCell (𝟙 Y) η)) ≫
      (generalLiftInverseForwardMapCompSourceTransport F hF f A C).hom =
    (generalLiftInverseForwardMapCompSourceTransport F hF f A B).hom ≫
      (((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) A)) ◁
        F.map₂ (canonicalSourceTwoCell f η)) := by
  rw [generalLiftInverseForwardMapCompSourceTransport_hom,
    generalLiftInverseForwardMapCompSourceTransport_hom]
  exact comp_naturality_of_squares
    (equivalenceCounitInsertion_naturality
      (generalLiftSourceEquivalence F hF f)
      (F.map (canonicalSourceHom (𝟙 Y) A) ◁
        F.map₂ (canonicalSourceTwoCell (𝟙 Y) η)))
    (comp_naturality_of_squares
      (generalLiftInverseForwardMapCompSliding_naturality_right
        F hF f A η)
      (generalLiftInverseForwardMapCompFactorization_naturality_right
        F hF f A η))

/-- Source transport is natural in the inverse factor's retained
coordinate. -/
theorem generalLiftInverseForwardMapCompSourceTransport_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A C : Type} (η : A ⟶ C) (B : Type) :
    (F.map₂ (canonicalSourceTwoCell (𝟙 Y) η) ▷
        F.map (canonicalSourceHom (𝟙 Y) B)) ≫
      (generalLiftInverseForwardMapCompSourceTransport F hF f C B).hom =
    (generalLiftInverseForwardMapCompSourceTransport F hF f A B).hom ≫
      (((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X) η)) ▷
        F.map (canonicalSourceHom f B)) := by
  rw [generalLiftInverseForwardMapCompSourceTransport_hom,
    generalLiftInverseForwardMapCompSourceTransport_hom]
  exact comp_naturality_of_squares
    (equivalenceCounitInsertion_naturality
      (generalLiftSourceEquivalence F hF f)
      (F.map₂ (canonicalSourceTwoCell (𝟙 Y) η) ▷
        F.map (canonicalSourceHom (𝟙 Y) B)))
    (comp_naturality_of_squares
      (generalLiftInverseForwardMapCompSliding_naturality_left
        F hF f η B)
      (generalLiftInverseForwardMapCompFactorization_naturality_left
        F hF f η B))

/-- The complete post-comparison transport for inverse/forward cancellation,
from the retained codomain composite to the arbitrary lift's two factors. -/
noncomputable def generalLiftInverseForwardMapCompTransport
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom (𝟙 Y) (A × B)) ≅
      (generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A) ≫
        (generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom f B) :=
  generalLiftForwardMapCompCore F hF (𝟙 Y) (𝟙 Y) A B ≪≫
    generalLiftInverseForwardMapCompSourceTransport F hF f A B ≪≫
    generalLiftInverseForwardMapCompFactors F hF f hf A B

/-- The post-comparison transport hom is its forward core, cancellation source
transport, and endpoint-factor transport. -/
theorem generalLiftInverseForwardMapCompTransport_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftInverseForwardMapCompTransport F hF f hf A B).hom =
      (generalLiftForwardMapCompCore F hF (𝟙 Y) (𝟙 Y) A B).hom ≫
      (generalLiftInverseForwardMapCompSourceTransport F hF f A B).hom ≫
      (generalLiftInverseForwardMapCompFactors F hF f hf A B).hom := by
  rfl

/-- The complete inverse/forward transport is natural in the forward factor's
retained coordinate. -/
theorem generalLiftInverseForwardMapCompTransport_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 Y)
            (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η)) ≫
      (generalLiftInverseForwardMapCompTransport F hF f hf A C).hom =
    (generalLiftInverseForwardMapCompTransport F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A) ◁
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell f η)) := by
  rw [generalLiftInverseForwardMapCompTransport_hom,
    generalLiftInverseForwardMapCompTransport_hom]
  exact comp_naturality_of_squares
    (generalLiftForwardMapCompCore_naturality_right
      F hF (𝟙 Y) (𝟙 Y) A η)
    (comp_naturality_of_squares
      (generalLiftInverseForwardMapCompSourceTransport_naturality_right
        F hF f A η)
      (generalLiftInverseForwardMapCompFactors_naturality_right
        F hF f hf A η))

/-- The complete inverse/forward transport is natural in the inverse factor's
retained coordinate. -/
theorem generalLiftInverseForwardMapCompTransport_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 Y)
            (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B))) ≫
      (generalLiftInverseForwardMapCompTransport F hF f hf C B).hom =
    (generalLiftInverseForwardMapCompTransport F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f η) ▷
        (generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom f B)) := by
  rw [generalLiftInverseForwardMapCompTransport_hom,
    generalLiftInverseForwardMapCompTransport_hom]
  exact comp_naturality_of_squares
    (generalLiftForwardMapCompCore_naturality_left
      F hF (𝟙 Y) (𝟙 Y) η B)
    (comp_naturality_of_squares
      (generalLiftInverseForwardMapCompSourceTransport_naturality_left
        F hF f η B)
      (generalLiftInverseForwardMapCompFactors_naturality_left
        F hF f hf η B))

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
    generalLiftInverseForwardMapCompTransport F hF f hf A B

/-- The hom of the complete inverse/forward compositor is its mapped target
comparison followed by the named transport. -/
theorem generalLiftMapCompInverseForward_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftMapCompInverseForward F hF f hf A B).hom =
      (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseForwardCompositionComparison f A B).hom ≫
        (generalLiftInverseForwardMapCompTransport F hF f hf A B).hom := by
  rfl

/-- The complete inverse/forward cancellation compositor is natural in the
forward factor's retained coordinate. -/
theorem generalLiftMapCompInverseForward_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseHom f A ◁ canonicalForwardTwoCell f η) ≫
      (generalLiftMapCompInverseForward F hF f hf A C).hom =
    (generalLiftMapCompInverseForward F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map (canonicalInverseHom f A) ◁
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell f η)) := by
  rw [generalLiftMapCompInverseForward_hom,
    generalLiftMapCompInverseForward_hom]
  exact comp_naturality_of_squares
    (generalLiftInverseForwardMapCompTarget_naturality_right F hF f A η)
    (generalLiftInverseForwardMapCompTransport_naturality_right
      F hF f hf A η)

/-- The complete inverse/forward cancellation compositor is natural in the
inverse factor's retained coordinate. -/
theorem generalLiftMapCompInverseForward_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f η ▷ canonicalForwardHom f B) ≫
      (generalLiftMapCompInverseForward F hF f hf C B).hom =
    (generalLiftMapCompInverseForward F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f η) ▷
        (generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom f B)) := by
  rw [generalLiftMapCompInverseForward_hom,
    generalLiftMapCompInverseForward_hom]
  exact comp_naturality_of_squares
    (generalLiftInverseForwardMapCompTarget_naturality_left F hF f η B)
    (generalLiftInverseForwardMapCompTransport_naturality_left
      F hF f hf η B)

/-- Forward/inverse cancellation is natural in the inverse factor's retained
coordinate. -/
theorem canonicalForwardInverseCompositionComparison_naturality_right
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) {B C : Type} (η : B ⟶ C) :
    (canonicalForwardHom f A ◁ canonicalInverseTwoCell f η) ≫
        (canonicalForwardInverseCompositionComparison f A C).hom =
      (canonicalForwardInverseCompositionComparison f A B).hom ≫
        canonicalForwardTwoCell (𝟙 X)
          (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η) := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- Forward/inverse cancellation is natural in the forward factor's retained
coordinate. -/
theorem canonicalForwardInverseCompositionComparison_naturality_left
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A C : Type} (η : A ⟶ C) (B : Type) :
    (canonicalForwardTwoCell f η ▷ canonicalInverseHom f B) ≫
        (canonicalForwardInverseCompositionComparison f C B).hom =
      (canonicalForwardInverseCompositionComparison f A B).hom ≫
        canonicalForwardTwoCell (𝟙 X)
          (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B)) := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- Mapping right naturality of forward/inverse cancellation through the lift
preserves the vertical composite. -/
theorem generalLiftForwardInverseMapCompTarget_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) {B C : Type} (η : B ⟶ C) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardHom f A ◁ canonicalInverseTwoCell f η) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardInverseCompositionComparison f A C).hom =
      (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardInverseCompositionComparison f A B).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 X)
            (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η)) := by
  rw [← (generalLiftPrelaxFunctor F hF).map₂_comp,
    canonicalForwardInverseCompositionComparison_naturality_right,
    (generalLiftPrelaxFunctor F hF).map₂_comp]

/-- Mapping left naturality of forward/inverse cancellation through the lift
preserves the vertical composite. -/
theorem generalLiftForwardInverseMapCompTarget_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A C : Type} (η : A ⟶ C) (B : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell f η ▷ canonicalInverseHom f B) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardInverseCompositionComparison f C B).hom =
      (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardInverseCompositionComparison f A B).hom ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 X)
            (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B))) := by
  rw [← (generalLiftPrelaxFunctor F hF).map₂_comp,
    canonicalForwardInverseCompositionComparison_naturality_left,
    (generalLiftPrelaxFunctor F hF).map₂_comp]

/-- The forward/inverse unit stage inserts the chosen equivalence and inverse
inside the right factor. -/
noncomputable def generalLiftForwardInverseMapCompUnit
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    F.map (canonicalSourceHom (𝟙 X) A) ≫
        F.map (canonicalSourceHom (𝟙 X) B) ≅
      F.map (canonicalSourceHom (𝟙 X) A) ≫
        ((generalLiftSourceEquivalence F hF f).hom ≫
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) B))) :=
  whiskerLeftIso (F.map (canonicalSourceHom (𝟙 X) A))
    (equivalenceUnitInsertion (generalLiftSourceEquivalence F hF f)
      (F.map (canonicalSourceHom (𝟙 X) B)))

/-- The unit-stage hom is the equivalence unit insertion whiskered by the
fixed left source factor. -/
theorem generalLiftForwardInverseMapCompUnit_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftForwardInverseMapCompUnit F hF f A B).hom =
      F.map (canonicalSourceHom (𝟙 X) A) ◁
        (equivalenceUnitInsertion (generalLiftSourceEquivalence F hF f)
          (F.map (canonicalSourceHom (𝟙 X) B))).hom := by
  rfl

/-- The unit stage is natural in the inverse factor's retained coordinate. -/
theorem generalLiftForwardInverseMapCompUnit_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) {B C : Type} (η : B ⟶ C) :
    (F.map (canonicalSourceHom (𝟙 X) A) ◁
        F.map₂ (canonicalSourceTwoCell (𝟙 X) η)) ≫
      (generalLiftForwardInverseMapCompUnit F hF f A C).hom =
    (generalLiftForwardInverseMapCompUnit F hF f A B).hom ≫
      (F.map (canonicalSourceHom (𝟙 X) A) ◁
        ((generalLiftSourceEquivalence F hF f).hom ◁
          ((generalLiftSourceEquivalence F hF f).inv ◁
            F.map₂ (canonicalSourceTwoCell (𝟙 X) η)))) := by
  rw [generalLiftForwardInverseMapCompUnit_hom,
    generalLiftForwardInverseMapCompUnit_hom]
  exact whiskerLeft_naturality_of_square
    (F.map (canonicalSourceHom (𝟙 X) A))
    (equivalenceUnitInsertion_naturality
      (generalLiftSourceEquivalence F hF f)
      (F.map₂ (canonicalSourceTwoCell (𝟙 X) η)))

/-- The unit stage is natural in the forward factor's retained coordinate. -/
theorem generalLiftForwardInverseMapCompUnit_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A C : Type} (η : A ⟶ C) (B : Type) :
    (F.map₂ (canonicalSourceTwoCell (𝟙 X) η) ▷
        F.map (canonicalSourceHom (𝟙 X) B)) ≫
      (generalLiftForwardInverseMapCompUnit F hF f C B).hom =
    (generalLiftForwardInverseMapCompUnit F hF f A B).hom ≫
      (F.map₂ (canonicalSourceTwoCell (𝟙 X) η) ▷
        ((generalLiftSourceEquivalence F hF f).hom ≫
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) B)))) := by
  rw [generalLiftForwardInverseMapCompUnit_hom,
    generalLiftForwardInverseMapCompUnit_hom]
  exact (whisker_exchange
    (F.map₂ (canonicalSourceTwoCell (𝟙 X) η))
    (equivalenceUnitInsertion (generalLiftSourceEquivalence F hF f)
      (F.map (canonicalSourceHom (𝟙 X) B))).hom).symm

/-- The forward/inverse factorization stage reassociates and collapses the
retained-factor/forward-equivalence pair to the source forward arrow. -/
noncomputable def generalLiftForwardInverseMapCompFactorization
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    F.map (canonicalSourceHom (𝟙 X) A) ≫
        ((generalLiftSourceEquivalence F hF f).hom ≫
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) B))) ≅
      F.map (canonicalSourceHom f A) ≫
        ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) B)) :=
  (α_ (F.map (canonicalSourceHom (𝟙 X) A))
      (generalLiftSourceEquivalence F hF f).hom
      ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) B))).symm ≪≫
    whiskerRightIso
      (generalLiftRetainedForwardFactorizationSource F hF f A).symm
      ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) B))

/-- The factorization hom is inverse association followed by the inverse
retained-forward factorization. -/
theorem generalLiftForwardInverseMapCompFactorization_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftForwardInverseMapCompFactorization F hF f A B).hom =
      (α_ (F.map (canonicalSourceHom (𝟙 X) A))
        (generalLiftSourceEquivalence F hF f).hom
        ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) B))).inv ≫
      ((generalLiftRetainedForwardFactorizationSource F hF f A).inv ▷
        ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) B))) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The retained compositor may be moved through the unit-insertion and
fixed forward-factorization stages of forward/inverse cancellation. -/
theorem generalLiftForwardInverseUnitFactorization_compositor
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    (F.map (canonicalSourceHom (𝟙 X) A) ◁
          (generalLiftForwardMapCompSourceRightIdentity F
            (𝟙 X) B C).hom) ≫
        (F.map (canonicalSourceHom (𝟙 X) A) ◁
          (equivalenceUnitInsertion (generalLiftSourceEquivalence F hF f)
            (F.map (canonicalSourceHom (𝟙 X) B) ≫
              F.map (canonicalSourceHom (𝟙 X) C))).hom) ≫
        (α_ (F.map (canonicalSourceHom (𝟙 X) A))
          (generalLiftSourceEquivalence F hF f).hom
          ((generalLiftSourceEquivalence F hF f).inv ≫
            (F.map (canonicalSourceHom (𝟙 X) B) ≫
              F.map (canonicalSourceHom (𝟙 X) C)))).inv ≫
        ((generalLiftRetainedForwardFactorizationSource F hF f A).inv ▷
          ((generalLiftSourceEquivalence F hF f).inv ≫
            (F.map (canonicalSourceHom (𝟙 X) B) ≫
              F.map (canonicalSourceHom (𝟙 X) C)))) =
      (F.map (canonicalSourceHom (𝟙 X) A) ◁
          (equivalenceUnitInsertion (generalLiftSourceEquivalence F hF f)
            (F.map (canonicalSourceHom (𝟙 X) (B × C)))).hom) ≫
        (α_ (F.map (canonicalSourceHom (𝟙 X) A))
          (generalLiftSourceEquivalence F hF f).hom
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) (B × C)))).inv ≫
        ((generalLiftRetainedForwardFactorizationSource F hF f A).inv ▷
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) (B × C)))) ≫
        (F.map (canonicalSourceHom f A) ◁
          ((generalLiftSourceEquivalence F hF f).inv ◁
            (generalLiftForwardMapCompSourceRightIdentity F
              (𝟙 X) B C).hom)) := by
  exact equivalenceUnitInsertion_whisker_naturality
    (generalLiftSourceEquivalence F hF f)
    (generalLiftRetainedForwardFactorizationSource F hF f A).inv
    (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X) B C).hom

/-- Factorization is natural in the inverse factor's retained coordinate. -/
theorem generalLiftForwardInverseMapCompFactorization_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) {B C : Type} (η : B ⟶ C) :
    (F.map (canonicalSourceHom (𝟙 X) A) ◁
        ((generalLiftSourceEquivalence F hF f).hom ◁
          ((generalLiftSourceEquivalence F hF f).inv ◁
            F.map₂ (canonicalSourceTwoCell (𝟙 X) η)))) ≫
      (generalLiftForwardInverseMapCompFactorization F hF f A C).hom =
    (generalLiftForwardInverseMapCompFactorization F hF f A B).hom ≫
      (F.map (canonicalSourceHom f A) ◁
        ((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X) η))) := by
  rw [generalLiftForwardInverseMapCompFactorization_hom,
    generalLiftForwardInverseMapCompFactorization_hom]
  exact comp_naturality_of_squares
    (associator_inv_naturality_right
      (F.map (canonicalSourceHom (𝟙 X) A))
      (generalLiftSourceEquivalence F hF f).hom
      ((generalLiftSourceEquivalence F hF f).inv ◁
        F.map₂ (canonicalSourceTwoCell (𝟙 X) η)))
    (whisker_exchange
      (generalLiftRetainedForwardFactorizationSource F hF f A).inv
      ((generalLiftSourceEquivalence F hF f).inv ◁
        F.map₂ (canonicalSourceTwoCell (𝟙 X) η)))

/-- Factorization is natural in the forward factor's retained coordinate. -/
theorem generalLiftForwardInverseMapCompFactorization_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A C : Type} (η : A ⟶ C) (B : Type) :
    (F.map₂ (canonicalSourceTwoCell (𝟙 X) η) ▷
        ((generalLiftSourceEquivalence F hF f).hom ≫
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) B)))) ≫
      (generalLiftForwardInverseMapCompFactorization F hF f C B).hom =
    (generalLiftForwardInverseMapCompFactorization F hF f A B).hom ≫
      (F.map₂ (canonicalSourceTwoCell f η) ▷
        ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) B))) := by
  rw [generalLiftForwardInverseMapCompFactorization_hom,
    generalLiftForwardInverseMapCompFactorization_hom]
  exact comp_naturality_of_squares
    (associator_inv_naturality_left
      (F.map₂ (canonicalSourceTwoCell (𝟙 X) η))
      (generalLiftSourceEquivalence F hF f).hom
      ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) B)))
    (whiskerRight_naturality_of_square
      ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) B))
      (iso_inv_naturality_of_square
        (generalLiftRetainedForwardFactorizationSource F hF f A)
        (generalLiftRetainedForwardFactorizationSource F hF f C)
        (generalLiftRetainedForwardFactorizationSource_naturality
          F hF f η)))

/-- The forward/inverse endpoint-factor stage transports the source forward
factor and chosen inverse back to the arbitrary lift's mapped factors. -/
noncomputable def generalLiftForwardInverseMapCompFactors
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    F.map (canonicalSourceHom f A) ≫
        ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) B)) ≅
      (generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A) ≫
        (generalLiftPrelaxFunctor F hF).map
          (canonicalInverseHom f B) :=
  whiskerRightIso
      (eqToIso
        (generalLiftPrelaxFunctor_map_forward F hF f A)).symm
      ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) B)) ≪≫
    whiskerLeftIso
      ((generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A))
      (eqToIso
        (generalLiftPrelaxFunctor_map_inverse F hF f hf B)).symm

/-- The hom of forward/inverse endpoint-factor transport is its pair of
endpoint equality transports. -/
theorem generalLiftForwardInverseMapCompFactors_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftForwardInverseMapCompFactors F hF f hf A B).hom =
      (eqToHom
          (generalLiftPrelaxFunctor_map_forward F hF f A).symm ▷
        ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) B))) ≫
      ((generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A) ◁
        eqToHom
          (generalLiftPrelaxFunctor_map_inverse F hF f hf B).symm) := by
  rfl

/-- Endpoint-factor transport is natural in the inverse factor's retained
coordinate. -/
theorem generalLiftForwardInverseMapCompFactors_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    (F.map (canonicalSourceHom f A) ◁
        ((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X) η))) ≫
      (generalLiftForwardInverseMapCompFactors F hF f hf A C).hom =
    (generalLiftForwardInverseMapCompFactors F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A) ◁
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f η)) := by
  rw [generalLiftForwardInverseMapCompFactors_hom,
    generalLiftForwardInverseMapCompFactors_hom]
  exact comp_naturality_of_squares
    (whisker_exchange
      (eqToHom
        (generalLiftPrelaxFunctor_map_forward F hF f A).symm)
      ((generalLiftSourceEquivalence F hF f).inv ◁
        F.map₂ (canonicalSourceTwoCell (𝟙 X) η)))
    (whiskerLeft_naturality_of_square
      ((generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A))
      (generalLiftMap₂InverseTransportSymm F hF f hf η))

/-- Endpoint-factor transport is natural in the forward factor's retained
coordinate. -/
theorem generalLiftForwardInverseMapCompFactors_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    (F.map₂ (canonicalSourceTwoCell f η) ▷
        ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) B))) ≫
      (generalLiftForwardInverseMapCompFactors F hF f hf C B).hom =
    (generalLiftForwardInverseMapCompFactors F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell f η) ▷
        (generalLiftPrelaxFunctor F hF).map
          (canonicalInverseHom f B)) := by
  rw [generalLiftForwardInverseMapCompFactors_hom,
    generalLiftForwardInverseMapCompFactors_hom]
  exact comp_naturality_of_squares
    (whiskerRight_naturality_of_square
      ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) B))
      (generalLiftMap₂ForwardTransportSymm F hF f η))
    (whisker_exchange
      ((generalLiftPrelaxFunctor F hF).map₂
        (canonicalForwardTwoCell f η))
      (eqToHom
        (generalLiftPrelaxFunctor_map_inverse F hF f hf B).symm)).symm

/-- The forward core, unit insertion, and retained-forward factorization form
the source-level transport for forward/inverse cancellation. -/
noncomputable def generalLiftForwardInverseMapCompSourceTransport
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom (𝟙 X) (A × B)) ≅
      F.map (canonicalSourceHom f A) ≫
        ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) B)) :=
  generalLiftForwardMapCompCore F hF (𝟙 X) (𝟙 X) A B ≪≫
    generalLiftForwardInverseMapCompUnit F hF f A B ≪≫
    generalLiftForwardInverseMapCompFactorization F hF f A B

/-- The source transport hom is the forward core, unit insertion, and
factorization composite. -/
theorem generalLiftForwardInverseMapCompSourceTransport_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftForwardInverseMapCompSourceTransport F hF f A B).hom =
      (generalLiftForwardMapCompCore F hF (𝟙 X) (𝟙 X) A B).hom ≫
      (generalLiftForwardInverseMapCompUnit F hF f A B).hom ≫
      (generalLiftForwardInverseMapCompFactorization F hF f A B).hom := by
  rfl

/-- Endpoint-strict source compositor for forward/inverse cancellation.  It
starts at the chosen source representative rather than at the arbitrary
target action, so it can participate directly in source associativity. -/
noncomputable def generalLiftForwardInverseMapCompSourceNormalized
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    F.map (canonicalSourceHom (𝟙 X) (A × B)) ≅
      F.map (canonicalSourceHom f A) ≫
        ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) B)) :=
  generalLiftForwardMapCompSourceRightIdentity F (𝟙 X) A B ≪≫
    generalLiftForwardInverseMapCompUnit F hF f A B ≪≫
    generalLiftForwardInverseMapCompFactorization F hF f A B

/-- Hom expansion of the endpoint-strict forward/inverse source
compositor. -/
theorem generalLiftForwardInverseMapCompSourceNormalized_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B : Type) :
    (generalLiftForwardInverseMapCompSourceNormalized F hF f A B).hom =
      (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X) A B).hom ≫
      (generalLiftForwardInverseMapCompUnit F hF f A B).hom ≫
      (generalLiftForwardInverseMapCompFactorization F hF f A B).hom := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- After the retained identity compositor has been exposed, counit
insertion and inverse sliding identify the two source pastings for a
retained arrow, the matching inverse, and the matching forward arrow. -/
private theorem retainedInverseForward_afterIdentity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    ((generalLiftForwardMapCompSourceRightIdentity F (𝟙 Y) A B).hom ▷
        F.map (canonicalSourceHom (𝟙 Y) C)) ≫
      (α_ (F.map (canonicalSourceHom (𝟙 Y) A))
        (F.map (canonicalSourceHom (𝟙 Y) B))
        (F.map (canonicalSourceHom (𝟙 Y) C))).hom ≫
      (F.map (canonicalSourceHom (𝟙 Y) A) ◁
        (generalLiftInverseForwardMapCompSourceTransport F hF f
          B C).hom) =
    (generalLiftInverseForwardMapCompSourceTransport F hF f
        (A × B) C).hom ≫
      ((generalLiftRetainedInverseMapCompSourceNormalized F hF f A B).hom ▷
        F.map (canonicalSourceHom f C)) ≫
      (α_ (F.map (canonicalSourceHom (𝟙 Y) A))
        ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) B))
        (F.map (canonicalSourceHom f C))).hom := by
  rw [generalLiftInverseForwardMapCompSourceTransport_hom,
    generalLiftInverseForwardMapCompSourceTransport_hom,
    generalLiftRetainedInverseMapCompSourceNormalized_hom]
  rw [generalLiftInverseForwardMapCompSliding_hom,
    generalLiftInverseForwardMapCompSliding_hom]
  rw [generalLiftInverseForwardMapCompSlidingInner_hom,
    generalLiftInverseForwardMapCompSlidingInner_hom]
  rw [generalLiftInverseForwardMapCompFactorization_hom,
    generalLiftInverseForwardMapCompFactorization_hom]
  rw [generalLiftRetainedInverseMapCompSliding_hom]
  simp only [Bicategory.whiskerLeft_comp,
    Bicategory.comp_whiskerRight, Category.assoc]
  slice_lhs 3 6 =>
    rw [← Bicategory.whiskerLeft_comp,
      ← Bicategory.whiskerLeft_comp,
      ← Bicategory.whiskerLeft_comp]
    change F.map (canonicalSourceHom (𝟙 Y) A) ◁
      ((equivalenceCounitInsertion
        (generalLiftSourceEquivalence F hF f)
        (F.map (canonicalSourceHom (𝟙 Y) B) ≫
          F.map (canonicalSourceHom (𝟙 Y) C))).hom ≫
      ((generalLiftSourceEquivalence F hF f).inv ◁
        (α_ (generalLiftSourceEquivalence F hF f).hom
          (F.map (canonicalSourceHom (𝟙 Y) B))
          (F.map (canonicalSourceHom (𝟙 Y) C))).inv) ≫
      ((generalLiftSourceEquivalence F hF f).inv ◁
        ((generalLiftForwardSlidingSource F hF f B).hom ▷
          F.map (canonicalSourceHom (𝟙 Y) C))) ≫
      ((generalLiftSourceEquivalence F hF f).inv ◁
        (α_ (F.map (canonicalSourceHom (𝟙 X) B))
          (generalLiftSourceEquivalence F hF f).hom
          (F.map (canonicalSourceHom (𝟙 Y) C))).hom))
    rw [generalLiftCounitInsertion_inverseSliding F hF f B
      (F.map (canonicalSourceHom (𝟙 Y) C))]
  slice_rhs 1 4 =>
    rw [generalLiftCounitInsertion_inverseSliding F hF f (A × B)
      (F.map (canonicalSourceHom (𝟙 Y) C))]
  simp only [Category.assoc]
  slice_rhs 4 5 => simp
  simp only [generalLiftSourceEquivalence_hom]
  have hprefix :=
    generalLiftInverseSlidingSource_tensor_inv_prefix_naturality
      F hF f A B
      (generalLiftForwardFactorizationSource F hF f C).inv
  simp only [generalLiftForwardMapCompSource_identityNormalizations_eq,
    generalLiftSourceEquivalence_hom] at hprefix
  slice_rhs 3 9 =>
    rw [Category.id_comp]
    rw [← Bicategory.comp_whiskerRight,
      ← Bicategory.comp_whiskerRight,
      ← Bicategory.comp_whiskerRight]
    rw [hprefix]
  simp only [Bicategory.whiskerLeft_comp,
    Bicategory.comp_whiskerRight, Category.assoc]
  have hsplit := equivalenceCounitInsertion_splitLeft_naturality
    (generalLiftSourceEquivalence F hF f)
    (generalLiftForwardMapCompSourceRightIdentity F (𝟙 Y) A B).hom
    (F.map (canonicalSourceHom (𝟙 Y) C))
  simp only [generalLiftSourceEquivalence_hom] at hsplit
  slice_lhs 1 4 => rw [hsplit]
  bicategory

set_option backward.isDefEq.respectTransparency false in
/-- The endpoint-strict retained/inverse/forward source compositors satisfy
the cancellation three-fold associativity law. -/
theorem generalLiftRetainedInverseForwardMapCompSource_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    F.map₂ (canonicalSourceTwoCell (𝟙 Y)
          (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftForwardMapCompSourceRightIdentity F (𝟙 Y)
          A (B × C)).hom ≫
        (F.map (canonicalSourceHom (𝟙 Y) A) ◁
          (generalLiftInverseForwardMapCompSourceNormalized F hF f
            B C).hom) =
      (generalLiftInverseForwardMapCompSourceNormalized F hF f
          (A × B) C).hom ≫
        ((generalLiftRetainedInverseMapCompSourceNormalized F hF f A B).hom ▷
          F.map (canonicalSourceHom f C)) ≫
        (α_ (F.map (canonicalSourceHom (𝟙 Y) A))
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) B))
          (F.map (canonicalSourceHom f C))).hom := by
  rw [generalLiftInverseForwardMapCompSourceNormalized_hom,
    generalLiftInverseForwardMapCompSourceNormalized_hom]
  simp only [Bicategory.whiskerLeft_comp, Category.assoc]
  slice_lhs 1 3 =>
    rw [generalLiftForwardMapCompSourceIdentity_associativity
      F Y A B C]
  simp only [Category.assoc]
  rw [cancel_epi
    (generalLiftForwardMapCompSourceRightIdentity F (𝟙 Y)
      (A × B) C).hom]
  exact retainedInverseForward_afterIdentity F hF f A B C

set_option backward.isDefEq.respectTransparency false in
/-- The endpoint-strict forward/inverse/forward source compositors satisfy
the alternating cancellation three-fold associativity law. -/
theorem generalLiftForwardInverseForwardMapCompSource_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    F.map₂ (canonicalSourceTwoCell f
          (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftForwardMapCompSourceRightIdentity F f
          A (B × C)).hom ≫
        (F.map (canonicalSourceHom f A) ◁
          (generalLiftInverseForwardMapCompSourceNormalized F hF f
            B C).hom) =
      (generalLiftForwardMapCompSourceLeftIdentity F f
          (A × B) C).hom ≫
        ((generalLiftForwardInverseMapCompSourceNormalized F hF f A B).hom ▷
          F.map (canonicalSourceHom f C)) ≫
        (α_ (F.map (canonicalSourceHom f A))
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) B))
          (F.map (canonicalSourceHom f C))).hom := by
  rw [generalLiftInverseForwardMapCompSourceNormalized_hom,
    generalLiftForwardInverseMapCompSourceNormalized_hom]
  rw [generalLiftInverseForwardMapCompSourceTransport_hom]
  rw [generalLiftInverseForwardMapCompSliding_hom]
  rw [generalLiftInverseForwardMapCompSlidingInner_hom]
  rw [generalLiftInverseForwardMapCompFactorization_hom]
  rw [generalLiftForwardInverseMapCompUnit_hom,
    generalLiftForwardInverseMapCompFactorization_hom]
  simp only [Bicategory.whiskerLeft_comp,
    Bicategory.comp_whiskerRight, Category.assoc]
  slice_lhs 1 3 =>
    rw [generalLiftForwardMapCompSourceRightIdentity3_associativity
      F f A B C]
  simp only [Category.assoc]
  rw [← cancel_epi
    (generalLiftForwardMapCompSourceRightIdentity F f (A × B) C).inv]
  slice_rhs 1 2 =>
    rw [generalLiftForwardFactorizationSource_interchange
      F hF f (A × B) C]
  simp only [Category.assoc]
  slice_lhs 1 2 => simp
  rw [generalLiftRetainedForwardFactorizationSource_tensor F hF f A B]
  simp only [Bicategory.comp_whiskerRight, Category.assoc,
    Category.id_comp]
  rw [← cancel_epi
    ((generalLiftForwardMapCompSourceRightIdentity F f A B).inv ▷
      F.map (canonicalSourceHom (𝟙 Y) C))]
  slice_lhs 1 2 =>
    rw [← Bicategory.comp_whiskerRight, Iso.inv_hom_id]
    simp
  slice_rhs 1 2 =>
    rw [← Bicategory.comp_whiskerRight,
      generalLiftForwardFactorizationSource_interchange F hF f A B]
  simp only [Bicategory.comp_whiskerRight, Category.assoc]
  rw [← cancel_epi
    (((generalLiftRetainedForwardFactorizationSource F hF f A).inv ▷
      F.map (canonicalSourceHom (𝟙 Y) B)) ▷
      F.map (canonicalSourceHom (𝟙 Y) C))]
  slice_rhs 1 2 =>
    rw [← Bicategory.comp_whiskerRight,
      ← Bicategory.comp_whiskerRight, Iso.inv_hom_id]
    simp
  slice_rhs 3 4 =>
    rw [← Bicategory.comp_whiskerRight,
      ← Bicategory.whiskerLeft_comp,
      ← generalLiftForwardSlidingSource_hom F hF f B]
  rw [generalLiftForwardMapCompSource_identityNormalizations_eq
    F X A B]
  slice_rhs 4 8 =>
    rw [iso_conjugation_bicategorical_inner
      (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X) A B)
      (generalLiftForwardFactorizationSource F hF f C).inv]
  have hcore := equivalenceUnitCounit_alternating
    (generalLiftSourceEquivalence F hF f)
    (generalLiftForwardSlidingSource F hF f B)
    (generalLiftForwardFactorizationSource F hF f C).symm
  let kR :=
    (α_ (generalLiftSourceEquivalence F hF f).hom
      (F.map (canonicalSourceHom (𝟙 Y) B))
      (F.map (canonicalSourceHom (𝟙 Y) C))).inv ≫
    ((generalLiftForwardSlidingSource F hF f B).hom ▷
      F.map (canonicalSourceHom (𝟙 Y) C)) ≫
    (α_ (F.map (canonicalSourceHom (𝟙 X) B))
      (generalLiftSourceEquivalence F hF f).hom
      (F.map (canonicalSourceHom (𝟙 Y) C))).hom ≫
    (F.map (canonicalSourceHom (𝟙 X) B) ◁
      (generalLiftForwardFactorizationSource F hF f C).inv) ≫
    ((equivalenceUnitInsertion (generalLiftSourceEquivalence F hF f)
      (F.map (canonicalSourceHom (𝟙 X) B))).hom ▷
        F.map (canonicalSourceHom f C)) ≫
    (α_ (generalLiftSourceEquivalence F hF f).hom
      ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) B))
      (F.map (canonicalSourceHom f C))).hom
  have hgroup :
      (generalLiftSourceEquivalence F hF f).hom ◁
          (generalLiftInverseForwardMapCompSourceTransport F hF f B C).hom =
        kR := by
    rw [generalLiftInverseForwardMapCompSourceTransport_hom,
      generalLiftInverseForwardMapCompSliding_hom,
      generalLiftInverseForwardMapCompSlidingInner_hom,
      generalLiftInverseForwardMapCompFactorization_hom]
    simp only [Bicategory.whiskerLeft_comp]
    simpa only [Category.assoc, Iso.symm_hom] using hcore
  have houter := iso_whisker_transport_of_whiskered_eq
    (xA := F.map (canonicalSourceHom (𝟙 X) A))
    (x := (generalLiftSourceEquivalence F hF f).hom)
    (U := F.map (canonicalSourceHom (𝟙 Y) B) ≫
      F.map (canonicalSourceHom (𝟙 Y) C))
    (V := ((generalLiftSourceEquivalence F hF f).inv ≫
      F.map (canonicalSourceHom (𝟙 X) B)) ≫
      F.map (canonicalSourceHom f C))
    (generalLiftRetainedForwardFactorizationSource F hF f A) hgroup
  dsimp [kR] at houter
  simp only [generalLiftSourceEquivalence_hom] at houter ⊢
  have houterAssoc := congrArg
    (fun u => (α_
      (F.map (canonicalSourceHom (𝟙 X) A) ≫
        F.map (canonicalSourceHom f
          (𝟙 (MonoidalSingleObj.star Type))))
      (F.map (canonicalSourceHom (𝟙 Y) B))
      (F.map (canonicalSourceHom (𝟙 Y) C))).hom ≫ u) houter
  convert houterAssoc using 1
  · rw [generalLiftInverseForwardMapCompSourceTransport_hom,
      generalLiftInverseForwardMapCompSliding_hom,
      generalLiftInverseForwardMapCompSlidingInner_hom,
      generalLiftInverseForwardMapCompFactorization_hom]
    simp only [Bicategory.whiskerLeft_comp]
    bicategory
  · bicategory

set_option backward.isDefEq.respectTransparency false in
/-- The endpoint-strict inverse/forward/inverse source compositors satisfy
the dual alternating cancellation three-fold associativity law. -/
theorem generalLiftInverseForwardInverseMapCompSource_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    ((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X)
            (MonoidalCategory.associator A B C).hom)) ≫
        (generalLiftInverseRetainedMapCompSourceNormalized F hF f
          A (B × C)).hom ≫
        (((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) A)) ◁
          (generalLiftForwardInverseMapCompSourceNormalized F hF f
            B C).hom) =
      (generalLiftRetainedInverseMapCompSourceNormalized F hF f
          (A × B) C).hom ≫
        ((generalLiftInverseForwardMapCompSourceNormalized F hF f A B).hom ▷
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) C))) ≫
        (α_ ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) A))
          (F.map (canonicalSourceHom f B))
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) C))).hom := by
  rw [generalLiftInverseRetainedMapCompSourceNormalized_hom,
    generalLiftRetainedInverseMapCompSourceNormalized_hom,
    generalLiftInverseForwardMapCompSourceNormalized_hom,
    generalLiftForwardInverseMapCompSourceNormalized_hom]
  rw [generalLiftRetainedInverseMapCompSliding_hom]
  rw [generalLiftInverseForwardMapCompSourceTransport_hom]
  rw [generalLiftInverseForwardMapCompSliding_hom]
  rw [generalLiftInverseForwardMapCompSlidingInner_hom]
  rw [generalLiftInverseForwardMapCompFactorization_hom]
  rw [generalLiftForwardInverseMapCompUnit_hom,
    generalLiftForwardInverseMapCompFactorization_hom]
  rw [generalLiftInverseSlidingSource_tensor F hF f A B]
  rw [generalLiftForwardMapCompSource_identityNormalizations_eq F X A B]
  simp only [Bicategory.whiskerLeft_comp,
    Bicategory.comp_whiskerRight, Category.assoc]
  have hsource :=
    generalLiftForwardMapCompSourceIdentity_associativity F X A B C
  have hsourceW := congrArg
    (fun k => (generalLiftSourceEquivalence F hF f).inv ◁ k)
    hsource
  simp only [Bicategory.whiskerLeft_comp] at hsourceW
  have hprefix :
      ((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X)
            (MonoidalCategory.associator A B C).hom)) ≫
        ((generalLiftSourceEquivalence F hF f).inv ◁
          (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X)
            A (B × C)).hom) ≫
        (α_ (generalLiftSourceEquivalence F hF f).inv
          (F.map (canonicalSourceHom (𝟙 X) A))
          (F.map (canonicalSourceHom (𝟙 X) (B × C)))).inv ≫
        (((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) A)) ◁
          (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X)
            B C).hom) =
      ((generalLiftSourceEquivalence F hF f).inv ◁
          (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X)
            (A × B) C).hom) ≫
        (α_ (generalLiftSourceEquivalence F hF f).inv
          (F.map (canonicalSourceHom (𝟙 X) (A × B)))
          (F.map (canonicalSourceHom (𝟙 X) C))).inv ≫
        (((generalLiftSourceEquivalence F hF f).inv ◁
          (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X)
            A B).hom) ▷
          F.map (canonicalSourceHom (𝟙 X) C)) ≫
        ((α_ (generalLiftSourceEquivalence F hF f).inv
          (F.map (canonicalSourceHom (𝟙 X) A))
          (F.map (canonicalSourceHom (𝟙 X) B))).inv ▷
          F.map (canonicalSourceHom (𝟙 X) C)) ≫
        (α_ ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) A))
          (F.map (canonicalSourceHom (𝟙 X) B))
          (F.map (canonicalSourceHom (𝟙 X) C))).hom := by
    have hsourceWpost := congrArg
      (fun k => k ≫
        (α_ (generalLiftSourceEquivalence F hF f).inv
          (F.map (canonicalSourceHom (𝟙 X) A))
          (F.map (canonicalSourceHom (𝟙 X) B) ≫
            F.map (canonicalSourceHom (𝟙 X) C))).inv)
      hsourceW
    convert hsourceWpost using 1 <;> bicategory
  slice_lhs 1 4 => rw [hprefix]
  simp only [Category.assoc]
  rw [cancel_epi
    ((generalLiftSourceEquivalence F hF f).inv ◁
      (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X)
        (A × B) C).hom)]
  rw [cancel_epi
    (α_ (generalLiftSourceEquivalence F hF f).inv
      (F.map (canonicalSourceHom (𝟙 X) (A × B)))
      (F.map (canonicalSourceHom (𝟙 X) C))).inv]
  rw [cancel_epi
    (((generalLiftSourceEquivalence F hF f).inv ◁
      (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X)
        A B).hom) ▷
      F.map (canonicalSourceHom (𝟙 X) C))]
  have hcore := equivalenceUnitCounit_alternating_dual
    (generalLiftSourceEquivalence F hF f)
    (z := F.map (canonicalSourceHom (𝟙 X) C))
    (generalLiftInverseSlidingSource F hF f B)
  rw [← cancel_mono
    (((generalLiftSourceEquivalence F hF f).inv ≫
      F.map (canonicalSourceHom (𝟙 X) A)) ◁
      (((generalLiftForwardFactorizationSource F hF f B).hom ▷
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) C))) ≫
        (α_ (generalLiftSourceEquivalence F hF f).hom
          (F.map (canonicalSourceHom (𝟙 Y) B))
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) C))).hom))]
  simp only [Bicategory.whiskerLeft_comp, Category.assoc]
  have hslideB :
      (generalLiftForwardSlidingSource F hF f B).inv =
        (generalLiftRetainedForwardFactorizationSource F hF f B).inv ≫
          (generalLiftForwardFactorizationSource F hF f B).hom := by
    rfl
  slice_lhs 5 6 =>
    rw [← Bicategory.whiskerLeft_comp,
      ← Bicategory.comp_whiskerRight, ← hslideB]
  have hunit := generalLiftEquivalenceUnitInsertion_inverseSliding
    F hF f B C
  have hunitW := congrArg
    (fun k => ((generalLiftSourceEquivalence F hF f).inv ≫
      F.map (canonicalSourceHom (𝟙 X) A)) ◁ k) hunit
  simp only [Bicategory.whiskerLeft_comp] at hunitW
  slice_lhs 3 6 => rw [← hunitW]
  have hcounitA := generalLiftCounitInsertion_inverseSliding
    F hF f A (F.map (canonicalSourceHom (𝟙 Y) B))
  have hcounitAW := congrArg
    (fun k => k ▷ ((generalLiftSourceEquivalence F hF f).inv ≫
      F.map (canonicalSourceHom (𝟙 X) C))) hcounitA
  simp only [Bicategory.comp_whiskerRight] at hcounitAW
  slice_rhs 5 8 => rw [hcounitAW]
  simp only [rightAdjointSquare.vcomp,
    Bicategory.comp_whiskerRight, Category.assoc]
  have hη := iso_conjugation_bicategorical_inner
    (generalLiftForwardMapCompSourceRightIdentity F (𝟙 Y) A B)
    (𝟙 (((generalLiftSourceEquivalence F hF f).inv ≫
      F.map (canonicalSourceHom (𝟙 X) C))))
  simp only [Bicategory.whiskerLeft_id,
    Category.id_comp] at hη
  slice_rhs 5 8 => rw [hη]
  rw [← cancel_mono
    (((generalLiftSourceEquivalence F hF f).inv ≫
      F.map (canonicalSourceHom (𝟙 X) A)) ◁
      (α_ (generalLiftSourceEquivalence F hF f).hom
        (F.map (canonicalSourceHom (𝟙 Y) B))
        ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) C))).inv)]
  have hcoreGroup := hcore
  rw [← Bicategory.whiskerLeft_comp,
    ← Bicategory.whiskerLeft_comp,
    ← Bicategory.whiskerLeft_comp,
    ← Bicategory.whiskerLeft_comp] at hcoreGroup
  have houter := iso_whisker_transport_of_whiskered_eq
    (xA := F.map (canonicalSourceHom (𝟙 Y) A))
    (x := (generalLiftSourceEquivalence F hF f).inv)
    (generalLiftInverseSlidingSource F hF f A) hcoreGroup
  simp only [Category.assoc]
  rw [cancel_epi
    ((α_ (generalLiftSourceEquivalence F hF f).inv
      (F.map (canonicalSourceHom (𝟙 X) A))
      (F.map (canonicalSourceHom (𝟙 X) B))).inv ▷
      F.map (canonicalSourceHom (𝟙 X) C))]
  rw [← cancel_epi
    (((generalLiftInverseSlidingSource F hF f A).inv ▷
      F.map (canonicalSourceHom (𝟙 X) B)) ▷
      F.map (canonicalSourceHom (𝟙 X) C))]
  have houterPre := congrArg
    (fun k =>
      (α_ (F.map (canonicalSourceHom (𝟙 Y) A) ≫
        (generalLiftSourceEquivalence F hF f).inv)
        (F.map (canonicalSourceHom (𝟙 X) B))
        (F.map (canonicalSourceHom (𝟙 X) C))).hom ≫ k)
    houter
  convert houterPre using 1
  all_goals simp

set_option backward.isDefEq.respectTransparency false in
/-- The endpoint-strict forward/retained/inverse source compositors satisfy
the cancellation three-fold associativity law. -/
theorem generalLiftForwardRetainedInverseMapCompSource_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    F.map₂ (canonicalSourceTwoCell (𝟙 X)
          (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftForwardInverseMapCompSourceNormalized F hF f
          A (B × C)).hom ≫
        (F.map (canonicalSourceHom f A) ◁
          (generalLiftRetainedInverseMapCompSourceNormalized F hF f
            B C).hom) =
      (generalLiftForwardInverseMapCompSourceNormalized F hF f
          (A × B) C).hom ≫
        ((generalLiftForwardMapCompSourceRightIdentity F f A B).hom ▷
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) C))) ≫
        (α_ (F.map (canonicalSourceHom f A))
          (F.map (canonicalSourceHom (𝟙 Y) B))
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) C))).hom := by
  rw [generalLiftForwardInverseMapCompSourceNormalized_hom,
    generalLiftForwardInverseMapCompSourceNormalized_hom,
    generalLiftRetainedInverseMapCompSourceNormalized_hom]
  rw [generalLiftForwardInverseMapCompUnit_hom,
    generalLiftForwardInverseMapCompUnit_hom,
    generalLiftForwardInverseMapCompFactorization_hom,
    generalLiftForwardInverseMapCompFactorization_hom]
  rw [generalLiftRetainedInverseMapCompSliding_hom]
  rw [generalLiftRetainedForwardFactorizationSource_tensor_inv
    F hF f A B]
  simp only [Bicategory.whiskerLeft_comp,
    Bicategory.comp_whiskerRight, Category.assoc]
  slice_rhs 7 8 =>
    rw [← Bicategory.comp_whiskerRight,
      generalLiftForwardFactorizationSource_interchange_inv F hF f A B]
  simp only [Bicategory.comp_whiskerRight, Category.assoc]
  have hslideB :
      (generalLiftForwardSlidingSource F hF f B).inv =
        (generalLiftRetainedForwardFactorizationSource F hF f B).inv ≫
          (generalLiftForwardFactorizationSource F hF f B).hom := by
    rfl
  slice_rhs 6 7 =>
    rw [← Bicategory.comp_whiskerRight,
      ← Bicategory.whiskerLeft_comp, ← hslideB]
  slice_lhs 3 6 =>
    rw [← generalLiftForwardInverseUnitFactorization_compositor
      F hF f A B C]
  slice_lhs 1 3 =>
    rw [generalLiftForwardMapCompSourceIdentity_associativity F X A B C]
  simp only [Category.assoc]
  rw [cancel_epi
    (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X)
      (A × B) C).hom]
  have hunit := generalLiftEquivalenceUnitInsertion_inverseSliding
    F hF f B C
  have hunitContext := congrArg
    (fun k =>
      ((generalLiftForwardMapCompSourceRightIdentity F
          (𝟙 X) A B).hom ▷
        F.map (canonicalSourceHom (𝟙 X) C)) ≫
      (α_ (F.map (canonicalSourceHom (𝟙 X) A))
        (F.map (canonicalSourceHom (𝟙 X) B))
        (F.map (canonicalSourceHom (𝟙 X) C))).hom ≫
      (F.map (canonicalSourceHom (𝟙 X) A) ◁ k) ≫
      (α_ (F.map (canonicalSourceHom (𝟙 X) A))
        (generalLiftSourceEquivalence F hF f).hom
        (F.map (canonicalSourceHom (𝟙 Y) B) ≫
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) C)))).inv ≫
      ((generalLiftRetainedForwardFactorizationSource F hF f A).inv ▷
        (F.map (canonicalSourceHom (𝟙 Y) B) ≫
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) C)))))
    hunit
  let kLeft :=
    (α_ (generalLiftSourceEquivalence F hF f).inv
      (F.map (canonicalSourceHom (𝟙 X) B))
      (F.map (canonicalSourceHom (𝟙 X) C))).inv ≫
    ((generalLiftInverseSlidingSource F hF f B).hom ▷
      F.map (canonicalSourceHom (𝟙 X) C)) ≫
    (α_ (F.map (canonicalSourceHom (𝟙 Y) B))
      (generalLiftSourceEquivalence F hF f).inv
      (F.map (canonicalSourceHom (𝟙 X) C))).hom
  slice_lhs 6 8 =>
    rw [← Bicategory.whiskerLeft_comp,
      ← Bicategory.whiskerLeft_comp]
  slice_lhs 4 7 =>
    change
      (α_ (F.map (canonicalSourceHom (𝟙 X) A))
        (generalLiftSourceEquivalence F hF f).hom
        ((generalLiftSourceEquivalence F hF f).inv ≫
          (F.map (canonicalSourceHom (𝟙 X) B) ≫
            F.map (canonicalSourceHom (𝟙 X) C)))).inv ≫
      ((generalLiftRetainedForwardFactorizationSource F hF f A).inv ▷
        ((generalLiftSourceEquivalence F hF f).inv ≫
          (F.map (canonicalSourceHom (𝟙 X) B) ≫
            F.map (canonicalSourceHom (𝟙 X) C)))) ≫
      (F.map (canonicalSourceHom f A) ◁ kLeft)
    rw [forwardCancellation_tail
      (generalLiftRetainedForwardFactorizationSource F hF f A).inv
      kLeft]
  rw [generalLiftForwardMapCompSource_identityNormalizations_eq
    F X A B]
  slice_rhs 1 4 =>
    rw [forwardCancellation_prefix
      (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X) A B).hom]
  slice_rhs 5 9 =>
    rw [← forwardCancellation_suffix
      (generalLiftForwardSlidingSource F hF f B).inv
      (generalLiftRetainedForwardFactorizationSource F hF f A).inv
      ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) C))]
  simpa only [kLeft, Bicategory.whiskerLeft_comp,
    Category.assoc] using hunitContext

set_option backward.isDefEq.respectTransparency false in
/-- The endpoint-strict retained/forward/inverse source compositors satisfy
the cancellation three-fold associativity law. -/
theorem generalLiftRetainedForwardInverseMapCompSource_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    F.map₂ (canonicalSourceTwoCell (𝟙 X)
          (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X)
          A (B × C)).hom ≫
        (F.map (canonicalSourceHom (𝟙 X) A) ◁
          (generalLiftForwardInverseMapCompSourceNormalized F hF f
            B C).hom) =
      (generalLiftForwardInverseMapCompSourceNormalized F hF f
          (A × B) C).hom ≫
        ((generalLiftForwardMapCompSourceLeftIdentity F f A B).hom ▷
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) C))) ≫
        (α_ (F.map (canonicalSourceHom (𝟙 X) A))
          (F.map (canonicalSourceHom f B))
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) C))).hom := by
  rw [generalLiftForwardInverseMapCompSourceNormalized_hom,
    generalLiftForwardInverseMapCompSourceNormalized_hom]
  rw [generalLiftForwardInverseMapCompUnit_hom,
    generalLiftForwardInverseMapCompUnit_hom,
    generalLiftForwardInverseMapCompFactorization_hom,
    generalLiftForwardInverseMapCompFactorization_hom]
  rw [generalLiftRetainedForwardFactorizationSource_tensor_inv
    F hF f A B]
  simp only [Bicategory.whiskerLeft_comp,
    Bicategory.comp_whiskerRight, Category.assoc]
  slice_rhs 7 8 =>
    rw [← Bicategory.comp_whiskerRight, Iso.inv_hom_id]
    simp
  simp only [Category.id_comp]
  slice_lhs 1 3 =>
    rw [generalLiftForwardMapCompSourceIdentity_associativity F X A B C]
  simp only [Category.assoc]
  rw [cancel_epi
    (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X)
      (A × B) C).hom]
  rw [generalLiftForwardMapCompSource_identityNormalizations_eq
    F X A B]
  slice_rhs 1 4 =>
    rw [forwardCancellation_prefix
      (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X) A B).hom]
  slice_rhs 5 7 =>
    rw [← forwardCancellation_factorizationSuffix
      (generalLiftRetainedForwardFactorizationSource F hF f B).inv
      ((generalLiftSourceEquivalence F hF f).inv ≫
        F.map (canonicalSourceHom (𝟙 X) C))]

set_option backward.isDefEq.respectTransparency false in
/-- The endpoint-strict forward/inverse/retained source compositors satisfy
the cancellation three-fold associativity law. -/
theorem generalLiftForwardInverseRetainedMapCompSource_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    F.map₂ (canonicalSourceTwoCell (𝟙 X)
          (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftForwardInverseMapCompSourceNormalized F hF f
          A (B × C)).hom ≫
        (F.map (canonicalSourceHom f A) ◁
          (generalLiftInverseRetainedMapCompSourceNormalized F hF f
            B C).hom) =
      (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X)
          (A × B) C).hom ≫
        ((generalLiftForwardInverseMapCompSourceNormalized F hF f A B).hom ▷
          F.map (canonicalSourceHom (𝟙 X) C)) ≫
        (α_ (F.map (canonicalSourceHom f A))
          ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) B))
          (F.map (canonicalSourceHom (𝟙 X) C))).hom := by
  rw [generalLiftForwardInverseMapCompSourceNormalized_hom,
    generalLiftForwardInverseMapCompSourceNormalized_hom,
    generalLiftInverseRetainedMapCompSourceNormalized_hom]
  rw [generalLiftForwardInverseMapCompUnit_hom,
    generalLiftForwardInverseMapCompUnit_hom,
    generalLiftForwardInverseMapCompFactorization_hom,
    generalLiftForwardInverseMapCompFactorization_hom]
  simp only [Bicategory.whiskerLeft_comp,
    Bicategory.comp_whiskerRight, Category.assoc]
  slice_lhs 3 6 =>
    rw [← generalLiftForwardInverseUnitFactorization_compositor
      F hF f A B C]
  slice_lhs 1 3 =>
    rw [generalLiftForwardMapCompSourceIdentity_associativity F X A B C]
  simp only [Category.assoc]
  rw [cancel_epi
    (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X)
      (A × B) C).hom]
  rw [cancel_epi
    ((generalLiftForwardMapCompSourceRightIdentity F (𝟙 X) A B).hom ▷
      F.map (canonicalSourceHom (𝟙 X) C))]
  rw [equivalenceUnitInsertion_hom,
    equivalenceUnitInsertion_hom]
  bicategory

set_option backward.isDefEq.respectTransparency false in
/-- The endpoint-strict inverse/forward/retained source compositors satisfy
the cancellation three-fold associativity law. -/
theorem generalLiftInverseForwardRetainedMapCompSource_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    F.map₂ (canonicalSourceTwoCell (𝟙 Y)
          (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftInverseForwardMapCompSourceNormalized F hF f
          A (B × C)).hom ≫
        (((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) A)) ◁
          (generalLiftForwardMapCompSourceRightIdentity F f B C).hom) =
      (generalLiftForwardMapCompSourceRightIdentity F (𝟙 Y)
          (A × B) C).hom ≫
        ((generalLiftInverseForwardMapCompSourceNormalized F hF f A B).hom ▷
          F.map (canonicalSourceHom (𝟙 Y) C)) ≫
        (α_ ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) A))
          (F.map (canonicalSourceHom f B))
          (F.map (canonicalSourceHom (𝟙 Y) C))).hom := by
  rw [generalLiftInverseForwardMapCompSourceNormalized_hom,
    generalLiftInverseForwardMapCompSourceNormalized_hom]
  rw [generalLiftInverseForwardMapCompSourceTransport_hom,
    generalLiftInverseForwardMapCompSourceTransport_hom]
  rw [generalLiftInverseForwardMapCompSliding_hom,
    generalLiftInverseForwardMapCompSliding_hom]
  rw [generalLiftInverseForwardMapCompSlidingInner_hom,
    generalLiftInverseForwardMapCompSlidingInner_hom]
  rw [generalLiftInverseForwardMapCompFactorization_hom,
    generalLiftInverseForwardMapCompFactorization_hom]
  rw [generalLiftForwardFactorizationSource_tensor_inv F hF f B C]
  simp only [Bicategory.whiskerLeft_comp,
    Bicategory.comp_whiskerRight, Category.assoc]
  slice_lhs 11 12 =>
    rw [← Bicategory.whiskerLeft_comp, Iso.inv_hom_id]
    simp
  slice_lhs 3 10 =>
    rw [inverseForward_rightWhisker
      (generalLiftSourceEquivalence F hF f)
      (generalLiftForwardSlidingSource F hF f A).hom
      (generalLiftForwardFactorizationSource F hF f B).inv
      (generalLiftForwardMapCompSourceRightIdentity F (𝟙 Y) B C).hom]
  slice_lhs 1 3 =>
    rw [generalLiftForwardMapCompSourceIdentity_associativity F Y A B C]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The endpoint-strict inverse/retained/forward source compositors satisfy
the cancellation three-fold associativity law. -/
theorem generalLiftInverseRetainedForwardMapCompSource_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A B C : Type) :
    F.map₂ (canonicalSourceTwoCell (𝟙 Y)
          (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftInverseForwardMapCompSourceNormalized F hF f
          A (B × C)).hom ≫
        (((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) A)) ◁
          (generalLiftForwardMapCompSourceLeftIdentity F f B C).hom) =
      (generalLiftInverseForwardMapCompSourceNormalized F hF f
          (A × B) C).hom ≫
        ((generalLiftInverseRetainedMapCompSourceNormalized F hF f A B).hom ▷
          F.map (canonicalSourceHom f C)) ≫
        (α_ ((generalLiftSourceEquivalence F hF f).inv ≫
            F.map (canonicalSourceHom (𝟙 X) A))
          (F.map (canonicalSourceHom (𝟙 X) B))
          (F.map (canonicalSourceHom f C))).hom := by
  rw [generalLiftInverseForwardMapCompSourceNormalized_hom,
    generalLiftInverseForwardMapCompSourceNormalized_hom,
    generalLiftInverseRetainedMapCompSourceNormalized_hom]
  rw [generalLiftInverseForwardMapCompSourceTransport_hom,
    generalLiftInverseForwardMapCompSourceTransport_hom]
  rw [generalLiftInverseForwardMapCompSliding_hom,
    generalLiftInverseForwardMapCompSliding_hom]
  rw [generalLiftInverseForwardMapCompSlidingInner_hom,
    generalLiftInverseForwardMapCompSlidingInner_hom]
  rw [generalLiftInverseForwardMapCompFactorization_hom,
    generalLiftInverseForwardMapCompFactorization_hom]
  rw [generalLiftForwardFactorizationSource_tensor_inv F hF f B C]
  rw [generalLiftForwardSlidingSource_tensor F hF f A B]
  rw [generalLiftForwardMapCompSource_identityNormalizations_eq F X A B]
  simp only [Bicategory.whiskerLeft_comp,
    Bicategory.comp_whiskerRight, Category.assoc]
  slice_lhs 11 12 =>
    rw [← Bicategory.whiskerLeft_comp,
      generalLiftForwardFactorizationSource_interchange F hF f B C]
  simp only [Bicategory.whiskerLeft_comp]
  slice_lhs 10 11 =>
    rw [← Bicategory.whiskerLeft_comp,
      ← Bicategory.comp_whiskerRight,
      ← generalLiftForwardSlidingSource_hom F hF f B]
  slice_lhs 3 12 =>
    rw [inverseForward_rightWhisker_factorization
      (generalLiftSourceEquivalence F hF f)
      (generalLiftForwardSlidingSource F hF f A).hom
      (generalLiftForwardSlidingSource F hF f B).hom
      (generalLiftForwardFactorizationSource F hF f C).inv
      (generalLiftForwardMapCompSourceRightIdentity F (𝟙 Y) B C).hom]
  slice_lhs 1 3 =>
    rw [generalLiftForwardMapCompSourceIdentity_associativity F Y A B C]
  simp
  let η :=
    (generalLiftForwardMapCompSourceRightIdentity F (𝟙 Y) A B).hom ▷
      F.map (canonicalSourceHom (𝟙 Y) C)
  let post :=
    ((generalLiftSourceEquivalence F hF f).inv ◁
      (α_ (generalLiftSourceEquivalence F hF f).hom
        (F.map (canonicalSourceHom (𝟙 Y) A) ≫
          F.map (canonicalSourceHom (𝟙 Y) B))
        (F.map (canonicalSourceHom (𝟙 Y) C))).inv) ≫
    (α_ (generalLiftSourceEquivalence F hF f).inv
        ((generalLiftSourceEquivalence F hF f).hom ≫
          F.map (canonicalSourceHom (𝟙 Y) A) ≫
            F.map (canonicalSourceHom (𝟙 Y) B))
        (F.map (canonicalSourceHom (𝟙 Y) C))).inv ≫
      (((generalLiftSourceEquivalence F hF f).inv ◁
        (α_ (generalLiftSourceEquivalence F hF f).hom
          (F.map (canonicalSourceHom (𝟙 Y) A))
          (F.map (canonicalSourceHom (𝟙 Y) B))).inv) ▷
        F.map (canonicalSourceHom (𝟙 Y) C)) ≫
      (((generalLiftSourceEquivalence F hF f).inv ◁
        ((generalLiftForwardSlidingSource F hF f A).hom ▷
          F.map (canonicalSourceHom (𝟙 Y) B))) ▷
        F.map (canonicalSourceHom (𝟙 Y) C)) ≫
      (((generalLiftSourceEquivalence F hF f).inv ◁
        (α_ (F.map (canonicalSourceHom (𝟙 X) A))
          (generalLiftSourceEquivalence F hF f).hom
          (F.map (canonicalSourceHom (𝟙 Y) B))).hom) ▷
        F.map (canonicalSourceHom (𝟙 Y) C)) ≫
      (α_ (generalLiftSourceEquivalence F hF f).inv
        (F.map (canonicalSourceHom (𝟙 X) A) ≫
          ((generalLiftSourceEquivalence F hF f).hom ≫
            F.map (canonicalSourceHom (𝟙 Y) B)))
        (F.map (canonicalSourceHom (𝟙 Y) C))).hom ≫
      ((generalLiftSourceEquivalence F hF f).inv ◁
        (α_ (F.map (canonicalSourceHom (𝟙 X) A))
          ((generalLiftSourceEquivalence F hF f).hom ≫
            F.map (canonicalSourceHom (𝟙 Y) B))
          (F.map (canonicalSourceHom (𝟙 Y) C))).hom) ≫
      ((generalLiftSourceEquivalence F hF f).inv ◁
        (F.map (canonicalSourceHom (𝟙 X) A) ◁
          ((generalLiftForwardSlidingSource F hF f B).hom ▷
            F.map (canonicalSourceHom (𝟙 Y) C)))) ≫
      ((generalLiftSourceEquivalence F hF f).inv ◁
        (F.map (canonicalSourceHom (𝟙 X) A) ◁
          (α_ (F.map (canonicalSourceHom (𝟙 X) B))
            (generalLiftSourceEquivalence F hF f).hom
            (F.map (canonicalSourceHom (𝟙 Y) C))).hom)) ≫
      ((generalLiftSourceEquivalence F hF f).inv ◁
        (F.map (canonicalSourceHom (𝟙 X) A) ◁
          (F.map (canonicalSourceHom (𝟙 X) B) ◁
            (generalLiftForwardFactorizationSource F hF f C).inv))) ≫
      (α_ (generalLiftSourceEquivalence F hF f).inv
        (F.map (canonicalSourceHom (𝟙 X) A))
        (F.map (canonicalSourceHom (𝟙 X) B) ≫
          F.map (canonicalSourceHom f C))).inv
  have hnat := equivalenceCounitInsertion_naturality
    (generalLiftSourceEquivalence F hF f) η
  have hnatPost := congrArg (fun u => u ≫ post) hnat
  dsimp [η, post] at hnatPost
  convert hnatPost using 1
  · bicategory_nf
    simp
    rw [← equivalenceCounitInsertion_rightWhisker_assoc
      (generalLiftSourceEquivalence F hF f)
      (F.map (canonicalSourceHom (𝟙 Y) A) ≫
        F.map (canonicalSourceHom (𝟙 Y) B))
      (F.map (canonicalSourceHom (𝟙 Y) C))]
    bicategory
  · bicategory_nf
    simp
    have hconj := whiskerLeft_iso_conjugation_bicategorical
      (generalLiftSourceEquivalence F hF f).inv
      (generalLiftForwardMapCompSourceRightIdentity F (𝟙 X) A B)
      (generalLiftForwardFactorizationSource F hF f C).inv
    simp only [generalLiftSourceEquivalence_hom] at hconj
    rw [hconj]

/-- Source transport is natural in the inverse factor's retained
coordinate. -/
theorem generalLiftForwardInverseMapCompSourceTransport_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) {B C : Type} (η : B ⟶ C) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 X)
            (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η)) ≫
      (generalLiftForwardInverseMapCompSourceTransport F hF f A C).hom =
    (generalLiftForwardInverseMapCompSourceTransport F hF f A B).hom ≫
      (F.map (canonicalSourceHom f A) ◁
        ((generalLiftSourceEquivalence F hF f).inv ◁
          F.map₂ (canonicalSourceTwoCell (𝟙 X) η))) := by
  rw [generalLiftForwardInverseMapCompSourceTransport_hom,
    generalLiftForwardInverseMapCompSourceTransport_hom]
  exact comp_naturality_of_squares
    (generalLiftForwardMapCompCore_naturality_right
      F hF (𝟙 X) (𝟙 X) A η)
    (comp_naturality_of_squares
      (generalLiftForwardInverseMapCompUnit_naturality_right F hF f A η)
      (generalLiftForwardInverseMapCompFactorization_naturality_right
        F hF f A η))

/-- Source transport is natural in the forward factor's retained
coordinate. -/
theorem generalLiftForwardInverseMapCompSourceTransport_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) {A C : Type} (η : A ⟶ C) (B : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 X)
            (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B))) ≫
      (generalLiftForwardInverseMapCompSourceTransport F hF f C B).hom =
    (generalLiftForwardInverseMapCompSourceTransport F hF f A B).hom ≫
      (F.map₂ (canonicalSourceTwoCell f η) ▷
        ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) B))) := by
  rw [generalLiftForwardInverseMapCompSourceTransport_hom,
    generalLiftForwardInverseMapCompSourceTransport_hom]
  exact comp_naturality_of_squares
    (generalLiftForwardMapCompCore_naturality_left
      F hF (𝟙 X) (𝟙 X) η B)
    (comp_naturality_of_squares
      (generalLiftForwardInverseMapCompUnit_naturality_left F hF f η B)
      (generalLiftForwardInverseMapCompFactorization_naturality_left
        F hF f η B))

/-- The complete post-comparison transport for forward/inverse cancellation,
including source normalization and endpoint equality transport. -/
noncomputable def generalLiftForwardInverseMapCompTransport
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom (𝟙 X) (A × B)) ≅
      (generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A) ≫
        (generalLiftPrelaxFunctor F hF).map
          (canonicalInverseHom f B) :=
  generalLiftForwardInverseMapCompSourceTransport F hF f A B ≪≫
    generalLiftForwardInverseMapCompFactors F hF f hf A B

/-- The post-comparison transport hom is its source-normalization and
endpoint-factor composite. -/
theorem generalLiftForwardInverseMapCompTransport_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftForwardInverseMapCompTransport F hF f hf A B).hom =
      (generalLiftForwardInverseMapCompSourceTransport F hF f A B).hom ≫
      (generalLiftForwardInverseMapCompFactors F hF f hf A B).hom := by
  rfl

/-- The complete forward/inverse transport is natural in the inverse factor's
retained coordinate. -/
theorem generalLiftForwardInverseMapCompTransport_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 X)
            (CategoryTheory.MonoidalCategory.tensorHom (𝟙 A) η)) ≫
      (generalLiftForwardInverseMapCompTransport F hF f hf A C).hom =
    (generalLiftForwardInverseMapCompTransport F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A) ◁
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f η)) := by
  rw [generalLiftForwardInverseMapCompTransport_hom,
    generalLiftForwardInverseMapCompTransport_hom]
  exact comp_naturality_of_squares
    (generalLiftForwardInverseMapCompSourceTransport_naturality_right
      F hF f A η)
    (generalLiftForwardInverseMapCompFactors_naturality_right
      F hF f hf A η)

/-- The complete forward/inverse transport is natural in the forward factor's
retained coordinate. -/
theorem generalLiftForwardInverseMapCompTransport_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 X)
            (CategoryTheory.MonoidalCategory.tensorHom η (𝟙 B))) ≫
      (generalLiftForwardInverseMapCompTransport F hF f hf C B).hom =
    (generalLiftForwardInverseMapCompTransport F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell f η) ▷
        (generalLiftPrelaxFunctor F hF).map
          (canonicalInverseHom f B)) := by
  rw [generalLiftForwardInverseMapCompTransport_hom,
    generalLiftForwardInverseMapCompTransport_hom]
  exact comp_naturality_of_squares
    (generalLiftForwardInverseMapCompSourceTransport_naturality_left
      F hF f η B)
    (generalLiftForwardInverseMapCompFactors_naturality_left
      F hF f hf η B)

set_option backward.isDefEq.respectTransparency false in
/-- Endpoint transport preserves the forward/retained/inverse cancellation
source associativity law. -/
theorem generalLiftForwardRetainedInverseMapCompTransport_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 X)
            (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftForwardInverseMapCompTransport F hF f hf
          A (B × C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A) ◁
          (generalLiftRetainedInverseMapCompTransport F hF f hf B C).hom =
      (generalLiftForwardInverseMapCompTransport F hF f hf
          (A × B) C).hom ≫
        ((generalLiftForwardMapCompTransport F hF f (𝟙 Y) A B).hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f C)) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 Y) B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f C))).hom := by
  simp only [generalLiftForwardInverseMapCompTransport_hom,
    generalLiftForwardInverseMapCompSourceTransport_hom,
    generalLiftForwardInverseMapCompFactors_hom,
    generalLiftRetainedInverseMapCompTransport_hom,
    generalLiftInverseRetainedMapCompCore_hom,
    generalLiftRetainedInverseMapCompSliding_hom,
    generalLiftRetainedInverseMapCompFactors_hom,
    generalLiftForwardMapCompTransport_hom,
    generalLiftForwardMapCompCore_hom,
    generalLiftForwardMapCompFactors_hom, Category.assoc]
  simpa [eqToIso.hom, eqToIso.inv,
    generalLiftForwardInverseMapCompSourceNormalized_hom,
    generalLiftForwardInverseMapCompUnit_hom,
    generalLiftForwardInverseMapCompFactorization_hom,
    generalLiftRetainedInverseMapCompSourceNormalized_hom,
    generalLiftRetainedInverseMapCompSliding_hom,
    generalLiftForwardMapCompSourceRightIdentity_hom,
    Category.assoc] using
    transportCompositor_associativity
    (e₀ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF f A))
    (e₁ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y) B))
    (e₂ := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf C))
    (e₀₁ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF f (A × B)))
    (e₁₂ := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf (B × C)))
    (eL := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X)
        ((A × B) × C)))
    (eR := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X)
        (A × (B × C))))
    (c₀₁ := (generalLiftForwardMapCompSourceRightIdentity F
      f A B).hom)
    (c₁₂ :=
      (generalLiftRetainedInverseMapCompSourceNormalized F hF f B C).hom)
    (cL :=
      (generalLiftForwardInverseMapCompSourceNormalized F hF f
        (A × B) C).hom)
    (cR :=
      (generalLiftForwardInverseMapCompSourceNormalized F hF f
        A (B × C)).hom)
    (aP := F.map₂ (canonicalSourceTwoCell (𝟙 X)
      (MonoidalCategory.associator A B C).hom))
    (aQ := (generalLiftPrelaxFunctor F hF).map₂
      (canonicalForwardTwoCell (𝟙 X)
        (MonoidalCategory.associator A B C).hom))
    (ha := generalLiftMap₂ForwardTransport F hF (𝟙 X)
      (MonoidalCategory.associator A B C).hom)
    (hc := generalLiftForwardRetainedInverseMapCompSource_associativity
      F hF f A B C)

set_option backward.isDefEq.respectTransparency false in
/-- Endpoint transport preserves the retained/forward/inverse cancellation
source associativity law. -/
theorem generalLiftRetainedForwardInverseMapCompTransport_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 X)
            (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftForwardMapCompTransport F hF (𝟙 X) (𝟙 X)
          A (B × C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 X) A) ◁
          (generalLiftForwardInverseMapCompTransport F hF f hf B C).hom =
      (generalLiftForwardInverseMapCompTransport F hF f hf
          (A × B) C).hom ≫
        ((generalLiftForwardMapCompTransport F hF (𝟙 X) f A B).hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f C)) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 X) A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f C))).hom := by
  simp only [generalLiftForwardMapCompTransport_hom,
    generalLiftForwardMapCompCore_hom,
    generalLiftForwardMapCompFactors_hom,
    generalLiftForwardInverseMapCompTransport_hom,
    generalLiftForwardInverseMapCompSourceTransport_hom,
    generalLiftForwardInverseMapCompFactors_hom, Category.assoc]
  simpa [eqToIso.hom, eqToIso.inv,
    generalLiftForwardMapCompSourceRightIdentity_hom,
    generalLiftForwardMapCompSourceLeftIdentity_hom,
    generalLiftForwardInverseMapCompSourceNormalized_hom,
    generalLiftForwardInverseMapCompUnit_hom,
    generalLiftForwardInverseMapCompFactorization_hom,
    Category.assoc] using
    transportCompositor_associativity
    (e₀ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X) A))
    (e₁ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF f B))
    (e₂ := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf C))
    (e₀₁ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF f (A × B)))
    (e₁₂ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X) (B × C)))
    (eL := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X)
        ((A × B) × C)))
    (eR := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X)
        (A × (B × C))))
    (c₀₁ := (generalLiftForwardMapCompSourceLeftIdentity F
      f A B).hom)
    (c₁₂ :=
      (generalLiftForwardInverseMapCompSourceNormalized F hF f B C).hom)
    (cL :=
      (generalLiftForwardInverseMapCompSourceNormalized F hF f
        (A × B) C).hom)
    (cR := (generalLiftForwardMapCompSourceRightIdentity F
      (𝟙 X) A (B × C)).hom)
    (aP := F.map₂ (canonicalSourceTwoCell (𝟙 X)
      (MonoidalCategory.associator A B C).hom))
    (aQ := (generalLiftPrelaxFunctor F hF).map₂
      (canonicalForwardTwoCell (𝟙 X)
        (MonoidalCategory.associator A B C).hom))
    (ha := generalLiftMap₂ForwardTransport F hF (𝟙 X)
      (MonoidalCategory.associator A B C).hom)
    (hc := generalLiftRetainedForwardInverseMapCompSource_associativity
      F hF f A B C)

set_option backward.isDefEq.respectTransparency false in
/-- Endpoint transport preserves the forward/inverse/retained cancellation
source associativity law. -/
theorem generalLiftForwardInverseRetainedMapCompTransport_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 X)
            (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftForwardInverseMapCompTransport F hF f hf
          A (B × C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A) ◁
          (generalLiftInverseRetainedMapCompTransport F hF f hf B C).hom =
      (generalLiftForwardMapCompTransport F hF (𝟙 X) (𝟙 X)
          (A × B) C).hom ≫
        ((generalLiftForwardInverseMapCompTransport F hF f hf A B).hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 X) C)) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 X) C))).hom := by
  simp only [generalLiftForwardInverseMapCompTransport_hom,
    generalLiftForwardInverseMapCompSourceTransport_hom,
    generalLiftForwardInverseMapCompFactors_hom,
    generalLiftInverseRetainedMapCompTransport_hom,
    generalLiftInverseRetainedMapCompCore_hom,
    generalLiftInverseRetainedMapCompFactors_hom,
    generalLiftForwardMapCompTransport_hom,
    generalLiftForwardMapCompCore_hom,
    generalLiftForwardMapCompFactors_hom, Category.assoc]
  simpa [eqToIso.hom, eqToIso.inv,
    generalLiftForwardInverseMapCompSourceNormalized_hom,
    generalLiftForwardInverseMapCompUnit_hom,
    generalLiftForwardInverseMapCompFactorization_hom,
    generalLiftInverseRetainedMapCompSourceNormalized_hom,
    generalLiftForwardMapCompSourceRightIdentity_hom,
    Category.assoc] using
    transportCompositor_associativity
    (e₀ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF f A))
    (e₁ := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf B))
    (e₂ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X) C))
    (e₀₁ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X) (A × B)))
    (e₁₂ := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf (B × C)))
    (eL := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X)
        ((A × B) × C)))
    (eR := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X)
        (A × (B × C))))
    (c₀₁ :=
      (generalLiftForwardInverseMapCompSourceNormalized F hF f A B).hom)
    (c₁₂ :=
      (generalLiftInverseRetainedMapCompSourceNormalized F hF f B C).hom)
    (cL := (generalLiftForwardMapCompSourceRightIdentity F
      (𝟙 X) (A × B) C).hom)
    (cR :=
      (generalLiftForwardInverseMapCompSourceNormalized F hF f
        A (B × C)).hom)
    (aP := F.map₂ (canonicalSourceTwoCell (𝟙 X)
      (MonoidalCategory.associator A B C).hom))
    (aQ := (generalLiftPrelaxFunctor F hF).map₂
      (canonicalForwardTwoCell (𝟙 X)
        (MonoidalCategory.associator A B C).hom))
    (ha := generalLiftMap₂ForwardTransport F hF (𝟙 X)
      (MonoidalCategory.associator A B C).hom)
    (hc := generalLiftForwardInverseRetainedMapCompSource_associativity
      F hF f A B C)

set_option backward.isDefEq.respectTransparency false in
/-- Endpoint transport preserves the inverse/forward/retained cancellation
source associativity law. -/
theorem generalLiftInverseForwardRetainedMapCompTransport_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 Y)
            (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftInverseForwardMapCompTransport F hF f hf
          A (B × C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A) ◁
          (generalLiftForwardMapCompTransport F hF f (𝟙 Y) B C).hom =
      (generalLiftForwardMapCompTransport F hF (𝟙 Y) (𝟙 Y)
          (A × B) C).hom ≫
        ((generalLiftInverseForwardMapCompTransport F hF f hf A B).hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 Y) C)) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 Y) C))).hom := by
  simp only [generalLiftInverseForwardMapCompTransport_hom,
    generalLiftInverseForwardMapCompFactors_hom,
    generalLiftForwardMapCompTransport_hom,
    generalLiftForwardMapCompCore_hom,
    generalLiftForwardMapCompFactors_hom, Category.assoc]
  simpa [eqToIso.hom, eqToIso.inv,
    generalLiftInverseForwardMapCompSourceNormalized_hom,
    generalLiftForwardMapCompSourceRightIdentity_hom,
    Category.assoc] using
    transportCompositor_associativity
    (e₀ := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf A))
    (e₁ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF f B))
    (e₂ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y) C))
    (e₀₁ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y) (A × B)))
    (e₁₂ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF f (B × C)))
    (eL := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y)
        ((A × B) × C)))
    (eR := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y)
        (A × (B × C))))
    (c₀₁ :=
      (generalLiftInverseForwardMapCompSourceNormalized F hF f A B).hom)
    (c₁₂ := (generalLiftForwardMapCompSourceRightIdentity F
      f B C).hom)
    (cL := (generalLiftForwardMapCompSourceRightIdentity F
      (𝟙 Y) (A × B) C).hom)
    (cR :=
      (generalLiftInverseForwardMapCompSourceNormalized F hF f
        A (B × C)).hom)
    (aP := F.map₂ (canonicalSourceTwoCell (𝟙 Y)
      (MonoidalCategory.associator A B C).hom))
    (aQ := (generalLiftPrelaxFunctor F hF).map₂
      (canonicalForwardTwoCell (𝟙 Y)
        (MonoidalCategory.associator A B C).hom))
    (ha := generalLiftMap₂ForwardTransport F hF (𝟙 Y)
      (MonoidalCategory.associator A B C).hom)
    (hc := generalLiftInverseForwardRetainedMapCompSource_associativity
      F hF f A B C)

set_option backward.isDefEq.respectTransparency false in
/-- Endpoint transport preserves the inverse/retained/forward cancellation
source associativity law. -/
theorem generalLiftInverseRetainedForwardMapCompTransport_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 Y)
            (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftInverseForwardMapCompTransport F hF f hf
          A (B × C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A) ◁
          (generalLiftForwardMapCompTransport F hF (𝟙 X) f B C).hom =
      (generalLiftInverseForwardMapCompTransport F hF f hf
          (A × B) C).hom ≫
        ((generalLiftInverseRetainedMapCompTransport F hF f hf A B).hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f C)) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 X) B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f C))).hom := by
  simp only [generalLiftInverseForwardMapCompTransport_hom,
    generalLiftInverseForwardMapCompFactors_hom,
    generalLiftInverseRetainedMapCompTransport_hom,
    generalLiftInverseRetainedMapCompCore_hom,
    generalLiftInverseRetainedMapCompFactors_hom,
    generalLiftForwardMapCompTransport_hom,
    generalLiftForwardMapCompCore_hom,
    generalLiftForwardMapCompFactors_hom, Category.assoc]
  simpa [eqToIso.hom, eqToIso.inv,
    generalLiftInverseForwardMapCompSourceNormalized_hom,
    generalLiftInverseRetainedMapCompSourceNormalized_hom,
    generalLiftForwardMapCompSourceRightIdentity_hom,
    generalLiftForwardMapCompSourceLeftIdentity_hom,
    Category.assoc] using
    transportCompositor_associativity
    (e₀ := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf A))
    (e₁ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X) B))
    (e₂ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF f C))
    (e₀₁ := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf (A × B)))
    (e₁₂ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF f (B × C)))
    (eL := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y)
        ((A × B) × C)))
    (eR := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y)
        (A × (B × C))))
    (c₀₁ :=
      (generalLiftInverseRetainedMapCompSourceNormalized F hF f A B).hom)
    (c₁₂ := (generalLiftForwardMapCompSourceLeftIdentity F
      f B C).hom)
    (cL :=
      (generalLiftInverseForwardMapCompSourceNormalized F hF f
        (A × B) C).hom)
    (cR :=
      (generalLiftInverseForwardMapCompSourceNormalized F hF f
        A (B × C)).hom)
    (aP := F.map₂ (canonicalSourceTwoCell (𝟙 Y)
      (MonoidalCategory.associator A B C).hom))
    (aQ := (generalLiftPrelaxFunctor F hF).map₂
      (canonicalForwardTwoCell (𝟙 Y)
        (MonoidalCategory.associator A B C).hom))
    (ha := generalLiftMap₂ForwardTransport F hF (𝟙 Y)
      (MonoidalCategory.associator A B C).hom)
    (hc := generalLiftInverseRetainedForwardMapCompSource_associativity
      F hF f A B C)

set_option backward.isDefEq.respectTransparency false in
/-- Endpoint transport preserves the retained/inverse/forward cancellation
source associativity law. -/
theorem generalLiftRetainedInverseForwardMapCompTransport_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell (𝟙 Y)
            (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftForwardMapCompTransport F hF (𝟙 Y) (𝟙 Y)
          A (B × C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 Y) A) ◁
          (generalLiftInverseForwardMapCompTransport F hF f hf B C).hom =
      (generalLiftInverseForwardMapCompTransport F hF f hf
          (A × B) C).hom ≫
        ((generalLiftRetainedInverseMapCompTransport F hF f hf A B).hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f C)) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 Y) A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f C))).hom := by
  simp only [generalLiftForwardMapCompTransport_hom,
    generalLiftForwardMapCompCore_hom,
    generalLiftForwardMapCompFactors_hom,
    generalLiftInverseForwardMapCompTransport_hom,
    generalLiftInverseForwardMapCompFactors_hom,
    generalLiftRetainedInverseMapCompTransport_hom,
    generalLiftInverseRetainedMapCompCore_hom,
    generalLiftRetainedInverseMapCompSliding_hom,
    generalLiftRetainedInverseMapCompFactors_hom, Category.assoc]
  simpa [eqToIso.hom, eqToIso.inv,
    generalLiftForwardMapCompSourceRightIdentity_hom,
    generalLiftInverseForwardMapCompSourceNormalized_hom,
    generalLiftRetainedInverseMapCompSourceNormalized_hom,
    generalLiftRetainedInverseMapCompSliding_hom,
    Category.assoc] using
    transportCompositor_associativity
    (e₀ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y) A))
    (e₁ := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf B))
    (e₂ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF f C))
    (e₀₁ := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf (A × B)))
    (e₁₂ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y) (B × C)))
    (eL := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y)
        ((A × B) × C)))
    (eR := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y)
        (A × (B × C))))
    (c₀₁ :=
      (generalLiftRetainedInverseMapCompSourceNormalized F hF f A B).hom)
    (c₁₂ :=
      (generalLiftInverseForwardMapCompSourceNormalized F hF f B C).hom)
    (cL :=
      (generalLiftInverseForwardMapCompSourceNormalized F hF f
        (A × B) C).hom)
    (cR := (generalLiftForwardMapCompSourceRightIdentity F
      (𝟙 Y) A (B × C)).hom)
    (aP := F.map₂ (canonicalSourceTwoCell (𝟙 Y)
      (MonoidalCategory.associator A B C).hom))
    (aQ := (generalLiftPrelaxFunctor F hF).map₂
      (canonicalForwardTwoCell (𝟙 Y)
        (MonoidalCategory.associator A B C).hom))
    (ha := generalLiftMap₂ForwardTransport F hF (𝟙 Y)
      (MonoidalCategory.associator A B C).hom)
    (hc := generalLiftRetainedInverseForwardMapCompSource_associativity
      F hF f A B C)

set_option backward.isDefEq.respectTransparency false in
/-- Endpoint transport preserves the alternating forward/inverse/forward
source associativity law. -/
theorem generalLiftForwardInverseForwardMapCompTransport_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell f
            (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftForwardMapCompTransport F hF f (𝟙 Y)
          A (B × C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A) ◁
          (generalLiftInverseForwardMapCompTransport F hF f hf B C).hom =
      (generalLiftForwardMapCompTransport F hF (𝟙 X) f
          (A × B) C).hom ≫
        ((generalLiftForwardInverseMapCompTransport F hF f hf A B).hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f C)) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f C))).hom := by
  simp only [generalLiftForwardMapCompTransport_hom,
    generalLiftForwardMapCompCore_hom,
    generalLiftForwardMapCompFactors_hom,
    generalLiftInverseForwardMapCompTransport_hom,
    generalLiftInverseForwardMapCompFactors_hom,
    generalLiftForwardInverseMapCompTransport_hom,
    generalLiftForwardInverseMapCompSourceTransport_hom,
    generalLiftForwardInverseMapCompFactors_hom, Category.assoc]
  simpa [eqToIso.hom, eqToIso.inv,
    generalLiftForwardMapCompSourceRightIdentity_hom,
    generalLiftForwardMapCompSourceLeftIdentity_hom,
    generalLiftInverseForwardMapCompSourceNormalized_hom,
    generalLiftForwardInverseMapCompSourceNormalized_hom,
    generalLiftForwardInverseMapCompUnit_hom,
    generalLiftForwardInverseMapCompFactorization_hom,
    Category.assoc] using
    transportCompositor_associativity
    (e₀ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF f A))
    (e₁ := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf B))
    (e₂ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF f C))
    (e₀₁ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X) (A × B)))
    (e₁₂ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y) (B × C)))
    (eL := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF f
        ((A × B) × C)))
    (eR := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF f
        (A × (B × C))))
    (c₀₁ :=
      (generalLiftForwardInverseMapCompSourceNormalized F hF f A B).hom)
    (c₁₂ :=
      (generalLiftInverseForwardMapCompSourceNormalized F hF f B C).hom)
    (cL := (generalLiftForwardMapCompSourceLeftIdentity F
      f (A × B) C).hom)
    (cR := (generalLiftForwardMapCompSourceRightIdentity F
      f A (B × C)).hom)
    (aP := F.map₂ (canonicalSourceTwoCell f
      (MonoidalCategory.associator A B C).hom))
    (aQ := (generalLiftPrelaxFunctor F hF).map₂
      (canonicalForwardTwoCell f
        (MonoidalCategory.associator A B C).hom))
    (ha := generalLiftMap₂ForwardTransport F hF f
      (MonoidalCategory.associator A B C).hom)
    (hc := generalLiftForwardInverseForwardMapCompSource_associativity
      F hF f A B C)

set_option backward.isDefEq.respectTransparency false in
/-- Endpoint transport preserves the dual alternating
inverse/forward/inverse source associativity law. -/
theorem generalLiftInverseForwardInverseMapCompTransport_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f
            (MonoidalCategory.associator A B C).hom) ≫
        (generalLiftInverseRetainedMapCompTransport F hF f hf
          A (B × C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A) ◁
          (generalLiftForwardInverseMapCompTransport F hF f hf B C).hom =
      (generalLiftRetainedInverseMapCompTransport F hF f hf
          (A × B) C).hom ≫
        ((generalLiftInverseForwardMapCompTransport F hF f hf A B).hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f C)) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f C))).hom := by
  simp only [generalLiftInverseRetainedMapCompTransport_hom,
    generalLiftInverseRetainedMapCompCore_hom,
    generalLiftInverseRetainedMapCompFactors_hom,
    generalLiftForwardInverseMapCompTransport_hom,
    generalLiftForwardInverseMapCompSourceTransport_hom,
    generalLiftForwardMapCompCore_hom,
    generalLiftForwardInverseMapCompFactors_hom,
    generalLiftRetainedInverseMapCompTransport_hom,
    generalLiftRetainedInverseMapCompSliding_hom,
    generalLiftRetainedInverseMapCompFactors_hom,
    generalLiftInverseForwardMapCompTransport_hom,
    generalLiftInverseForwardMapCompSourceTransport_hom,
    generalLiftInverseForwardMapCompFactors_hom, Category.assoc]
  simpa [eqToIso.hom, eqToIso.inv,
    generalLiftInverseRetainedMapCompSourceNormalized_hom,
    generalLiftForwardInverseMapCompSourceNormalized_hom,
    generalLiftForwardInverseMapCompUnit_hom,
    generalLiftForwardInverseMapCompFactorization_hom,
    generalLiftRetainedInverseMapCompSourceNormalized_hom,
    generalLiftRetainedInverseMapCompSliding_hom,
    generalLiftInverseForwardMapCompSourceNormalized_hom,
    generalLiftInverseForwardMapCompSourceTransport_hom,
    generalLiftForwardMapCompSourceRightIdentity_hom,
    Category.assoc] using
    transportCompositor_associativity
    (e₀ := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf A))
    (e₁ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF f B))
    (e₂ := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf C))
    (e₀₁ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y) (A × B)))
    (e₁₂ := eqToIso
      (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X) (B × C)))
    (eL := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf
        ((A × B) × C)))
    (eR := eqToIso
      (generalLiftPrelaxFunctor_map_inverse F hF f hf
        (A × (B × C))))
    (c₀₁ :=
      (generalLiftInverseForwardMapCompSourceNormalized F hF f A B).hom)
    (c₁₂ :=
      (generalLiftForwardInverseMapCompSourceNormalized F hF f B C).hom)
    (cL :=
      (generalLiftRetainedInverseMapCompSourceNormalized F hF f
        (A × B) C).hom)
    (cR :=
      (generalLiftInverseRetainedMapCompSourceNormalized F hF f
        A (B × C)).hom)
    (aP := (generalLiftSourceEquivalence F hF f).inv ◁
      F.map₂ (canonicalSourceTwoCell (𝟙 X)
        (MonoidalCategory.associator A B C).hom))
    (aQ := (generalLiftPrelaxFunctor F hF).map₂
      (canonicalInverseTwoCell f
        (MonoidalCategory.associator A B C).hom))
    (ha := generalLiftMap₂InverseTransport F hF f hf
      (MonoidalCategory.associator A B C).hom)
    (hc := generalLiftInverseForwardInverseMapCompSource_associativity
      F hF f A B C)

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
    generalLiftForwardInverseMapCompTransport F hF f hf A B

/-- The hom of the complete forward/inverse compositor is its mapped target
comparison followed by the named transport. -/
theorem generalLiftMapCompForwardInverse_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    (generalLiftMapCompForwardInverse F hF f hf A B).hom =
      (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardInverseCompositionComparison f A B).hom ≫
        (generalLiftForwardInverseMapCompTransport F hF f hf A B).hom := by
  rfl

/-- The complete forward/inverse cancellation compositor is natural in the
inverse factor's retained coordinate. -/
theorem generalLiftMapCompForwardInverse_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardHom f A ◁ canonicalInverseTwoCell f η) ≫
      (generalLiftMapCompForwardInverse F hF f hf A C).hom =
    (generalLiftMapCompForwardInverse F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A) ◁
        (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f η)) := by
  rw [generalLiftMapCompForwardInverse_hom,
    generalLiftMapCompForwardInverse_hom]
  exact comp_naturality_of_squares
    (generalLiftForwardInverseMapCompTarget_naturality_right F hF f A η)
    (generalLiftForwardInverseMapCompTransport_naturality_right
      F hF f hf A η)

/-- The complete forward/inverse cancellation compositor is natural in the
forward factor's retained coordinate. -/
theorem generalLiftMapCompForwardInverse_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell f η ▷ canonicalInverseHom f B) ≫
      (generalLiftMapCompForwardInverse F hF f hf C B).hom =
    (generalLiftMapCompForwardInverse F hF f hf A B).hom ≫
      ((generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell f η) ▷
        (generalLiftPrelaxFunctor F hF).map
          (canonicalInverseHom f B)) := by
  rw [generalLiftMapCompForwardInverse_hom,
    generalLiftMapCompForwardInverse_hom]
  exact comp_naturality_of_squares
    (generalLiftForwardInverseMapCompTarget_naturality_left F hF f η B)
    (generalLiftForwardInverseMapCompTransport_naturality_left
      F hF f hf η B)

/-- A target arrow in the unique normal form determined by its two walking
endpoints and its retained-coordinate type. -/
noncomputable def canonicalEndpointHom
    (X Y : Ript.Examples.WalkingLocalization.Arrow) (A : Type) :
    canonicalTargetObject X ⟶ canonicalTargetObject Y :=
  (canonicalCompletionHom X Y).toLoc ×ₘ A

/-- A retained-coordinate 2-morphism between endpoint-normal target arrows.
Unlike the forward-only helper, this definition also covers the formally
adjoined reverse endpoint. -/
noncomputable def canonicalEndpointTwoCell
    (X Y : Ript.Examples.WalkingLocalization.Arrow)
    {A B : Type} (η : A ⟶ B) :
    canonicalEndpointHom X Y A ⟶ canonicalEndpointHom X Y B :=
  (𝟙 _, η)

/-- A canonical endpoint arrow in an ordered walking direction is exactly
the corresponding forward arrow.  The statement is independent of the
chosen proof that the walking endpoints are ordered. -/
theorem canonicalEndpointHom_eq_forward
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    canonicalEndpointHom X Y A = canonicalForwardHom f A := by
  apply Prod.ext
  · change (canonicalCompletionHom X Y).toLoc =
      (CategoryTheory.FreeGroupoid.homMk f).toLoc
    rw [homMk_eq_canonicalCompletionHom]
  · rfl

/-- Reversing an ordered walking direction identifies the canonical endpoint
arrow with the corresponding freely adjoined inverse arrow. -/
theorem canonicalEndpointHom_eq_inverse
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    canonicalEndpointHom Y X A = canonicalInverseHom f A := by
  apply Prod.ext
  · change (canonicalCompletionHom Y X).toLoc =
      (inv (CategoryTheory.FreeGroupoid.homMk f)).toLoc
    rw [inv_homMk_eq_canonicalCompletionHom]
  · rfl

private theorem walkingArrow_eq_zero_or_one
    (X : Ript.Examples.WalkingLocalization.Arrow) : X = 0 ∨ X = 1 := by
  fin_cases X <;> simp

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

/-- The endpoint-normal composition comparison is natural in every
retained-coordinate 2-morphism on its right factor.  The proof covers all
eight walking-endpoint triples and transports each one to its compiled
forward, mixed, or cancellation compositor. -/
theorem generalLiftEndpointMapComp_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    (X Y Z : Ript.Examples.WalkingLocalization.Arrow) (A : Type)
    {B C : Type} (η : B ⟶ C) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalEndpointHom X Y A ◁
            canonicalEndpointTwoCell Y Z η) ≫
        (generalLiftEndpointMapComp F hF X Y Z A C).hom =
      (generalLiftEndpointMapComp F hF X Y Z A B).hom ≫
        ((generalLiftPrelaxFunctor F hF).map
            (canonicalEndpointHom X Y A) ◁
          (generalLiftPrelaxFunctor F hF).map₂
            (canonicalEndpointTwoCell Y Z η)) := by
  rcases walkingArrow_eq_zero_or_one X with rfl | rfl <;>
    rcases walkingArrow_eq_zero_or_one Y with rfl | rfl <;>
      rcases walkingArrow_eq_zero_or_one Z with rfl | rfl
  · rw [generalLiftEndpointMapComp_zero_zero_zero,
      generalLiftEndpointMapComp_zero_zero_zero]
    cases canonicalEndpointHom_eq_forward
      (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) A
    cases canonicalEndpointHom_eq_forward
      (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) B
    cases canonicalEndpointHom_eq_forward
      (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) C
    exact generalLiftMapCompForward_naturality_right F hF (𝟙 0) (𝟙 0) A η
  · rw [generalLiftEndpointMapComp_zero_zero_one,
      generalLiftEndpointMapComp_zero_zero_one]
    cases canonicalEndpointHom_eq_forward
      (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) A
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow B
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow C
    exact generalLiftMapCompForward_naturality_right F hF
      (𝟙 0) Ript.Examples.WalkingLocalization.arrow A η
  · rw [generalLiftEndpointMapComp_zero_one_zero,
      generalLiftEndpointMapComp_zero_one_zero]
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow A
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow B
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow C
    exact generalLiftMapCompForwardInverse_naturality_right F hF
      Ript.Examples.WalkingLocalization.arrow (by decide) A η
  · rw [generalLiftEndpointMapComp_zero_one_one,
      generalLiftEndpointMapComp_zero_one_one]
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow A
    cases canonicalEndpointHom_eq_forward
      (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) B
    cases canonicalEndpointHom_eq_forward
      (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) C
    exact generalLiftMapCompForward_naturality_right F hF
      Ript.Examples.WalkingLocalization.arrow (𝟙 1) A η
  · rw [generalLiftEndpointMapComp_one_zero_zero,
      generalLiftEndpointMapComp_one_zero_zero]
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow A
    cases canonicalEndpointHom_eq_forward
      (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) B
    cases canonicalEndpointHom_eq_forward
      (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) C
    exact generalLiftMapCompInverseRetained_naturality_right F hF
      Ript.Examples.WalkingLocalization.arrow (by decide) A η
  · rw [generalLiftEndpointMapComp_one_zero_one,
      generalLiftEndpointMapComp_one_zero_one]
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow A
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow B
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow C
    exact generalLiftMapCompInverseForward_naturality_right F hF
      Ript.Examples.WalkingLocalization.arrow (by decide) A η
  · rw [generalLiftEndpointMapComp_one_one_zero,
      generalLiftEndpointMapComp_one_one_zero]
    cases canonicalEndpointHom_eq_forward
      (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) A
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow B
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow C
    exact generalLiftMapCompRetainedInverse_naturality_right F hF
      Ript.Examples.WalkingLocalization.arrow (by decide) A η
  · rw [generalLiftEndpointMapComp_one_one_one,
      generalLiftEndpointMapComp_one_one_one]
    cases canonicalEndpointHom_eq_forward
      (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) A
    cases canonicalEndpointHom_eq_forward
      (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) B
    cases canonicalEndpointHom_eq_forward
      (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) C
    exact generalLiftMapCompForward_naturality_right F hF (𝟙 1) (𝟙 1) A η

/-- The endpoint-normal composition comparison is natural in every
retained-coordinate 2-morphism on its left factor, uniformly across all eight
walking-endpoint triples. -/
theorem generalLiftEndpointMapComp_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    (X Y Z : Ript.Examples.WalkingLocalization.Arrow) {A C : Type}
    (η : A ⟶ C) (B : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalEndpointTwoCell X Y η ▷
            canonicalEndpointHom Y Z B) ≫
        (generalLiftEndpointMapComp F hF X Y Z C B).hom =
      (generalLiftEndpointMapComp F hF X Y Z A B).hom ≫
        ((generalLiftPrelaxFunctor F hF).map₂
            (canonicalEndpointTwoCell X Y η) ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalEndpointHom Y Z B)) := by
  rcases walkingArrow_eq_zero_or_one X with rfl | rfl <;>
    rcases walkingArrow_eq_zero_or_one Y with rfl | rfl <;>
      rcases walkingArrow_eq_zero_or_one Z with rfl | rfl
  · rw [generalLiftEndpointMapComp_zero_zero_zero,
      generalLiftEndpointMapComp_zero_zero_zero]
    cases canonicalEndpointHom_eq_forward
      (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) A
    cases canonicalEndpointHom_eq_forward
      (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) C
    cases canonicalEndpointHom_eq_forward
      (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) B
    exact generalLiftMapCompForward_naturality_left F hF (𝟙 0) (𝟙 0) η B
  · rw [generalLiftEndpointMapComp_zero_zero_one,
      generalLiftEndpointMapComp_zero_zero_one]
    cases canonicalEndpointHom_eq_forward
      (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) A
    cases canonicalEndpointHom_eq_forward
      (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) C
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow B
    exact generalLiftMapCompForward_naturality_left F hF
      (𝟙 0) Ript.Examples.WalkingLocalization.arrow η B
  · rw [generalLiftEndpointMapComp_zero_one_zero,
      generalLiftEndpointMapComp_zero_one_zero]
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow A
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow C
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow B
    exact generalLiftMapCompForwardInverse_naturality_left F hF
      Ript.Examples.WalkingLocalization.arrow (by decide) η B
  · rw [generalLiftEndpointMapComp_zero_one_one,
      generalLiftEndpointMapComp_zero_one_one]
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow A
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow C
    cases canonicalEndpointHom_eq_forward
      (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) B
    exact generalLiftMapCompForward_naturality_left F hF
      Ript.Examples.WalkingLocalization.arrow (𝟙 1) η B
  · rw [generalLiftEndpointMapComp_one_zero_zero,
      generalLiftEndpointMapComp_one_zero_zero]
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow A
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow C
    cases canonicalEndpointHom_eq_forward
      (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) B
    exact generalLiftMapCompInverseRetained_naturality_left F hF
      Ript.Examples.WalkingLocalization.arrow (by decide) η B
  · rw [generalLiftEndpointMapComp_one_zero_one,
      generalLiftEndpointMapComp_one_zero_one]
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow A
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow C
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow B
    exact generalLiftMapCompInverseForward_naturality_left F hF
      Ript.Examples.WalkingLocalization.arrow (by decide) η B
  · rw [generalLiftEndpointMapComp_one_one_zero,
      generalLiftEndpointMapComp_one_one_zero]
    cases canonicalEndpointHom_eq_forward
      (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) A
    cases canonicalEndpointHom_eq_forward
      (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) C
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow B
    exact generalLiftMapCompRetainedInverse_naturality_left F hF
      Ript.Examples.WalkingLocalization.arrow (by decide) η B
  · rw [generalLiftEndpointMapComp_one_one_one,
      generalLiftEndpointMapComp_one_one_one]
    cases canonicalEndpointHom_eq_forward
      (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) A
    cases canonicalEndpointHom_eq_forward
      (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) C
    cases canonicalEndpointHom_eq_forward
      (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) B
    exact generalLiftMapCompForward_naturality_left F hF (𝟙 1) (𝟙 1) η B

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

private theorem generalLiftMapComp_naturality_right_canonicalObjects
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : canonicalTargetObject X ⟶ canonicalTargetObject Y)
    {g h : canonicalTargetObject Y ⟶ canonicalTargetObject Z}
    (η : g ⟶ h) :
    (generalLiftPrelaxFunctor F hF).map₂ (f ◁ η) ≫
        (generalLiftMapComp F hF f h).hom =
      (generalLiftMapComp F hF f g).hom ≫
        ((generalLiftPrelaxFunctor F hF).map f ◁
          (generalLiftPrelaxFunctor F hF).map₂ η) := by
  rcases f with ⟨⟨f⟩, A⟩
  rcases g with ⟨⟨g⟩, B⟩
  rcases h with ⟨⟨h⟩, C⟩
  rcases η with ⟨η, ηret⟩
  have hf : f = canonicalCompletionHom X Y :=
    completion_hom_eq_canonical f
  have hg : g = canonicalCompletionHom Y Z :=
    completion_hom_eq_canonical g
  have hh : h = canonicalCompletionHom Y Z :=
    completion_hom_eq_canonical h
  cases hf
  cases hg
  cases hh
  have hη : η = 𝟙 _ := Subsingleton.elim _ _
  cases hη
  change
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalEndpointHom X Y A ◁
            canonicalEndpointTwoCell Y Z ηret) ≫
        (generalLiftEndpointMapComp F hF X Y Z A C).hom =
      (generalLiftEndpointMapComp F hF X Y Z A B).hom ≫
        ((generalLiftPrelaxFunctor F hF).map
            (canonicalEndpointHom X Y A) ◁
          (generalLiftPrelaxFunctor F hF).map₂
            (canonicalEndpointTwoCell Y Z ηret))
  exact generalLiftEndpointMapComp_naturality_right F hF X Y Z A ηret

private theorem generalLiftMapComp_naturality_left_canonicalObjects
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    {f h : canonicalTargetObject X ⟶ canonicalTargetObject Y}
    (η : f ⟶ h) (g : canonicalTargetObject Y ⟶ canonicalTargetObject Z) :
    (generalLiftPrelaxFunctor F hF).map₂ (η ▷ g) ≫
        (generalLiftMapComp F hF h g).hom =
      (generalLiftMapComp F hF f g).hom ≫
        ((generalLiftPrelaxFunctor F hF).map₂ η ▷
          (generalLiftPrelaxFunctor F hF).map g) := by
  rcases f with ⟨⟨f⟩, A⟩
  rcases h with ⟨⟨h⟩, C⟩
  rcases g with ⟨⟨g⟩, B⟩
  rcases η with ⟨η, ηret⟩
  have hf : f = canonicalCompletionHom X Y :=
    completion_hom_eq_canonical f
  have hh : h = canonicalCompletionHom X Y :=
    completion_hom_eq_canonical h
  have hg : g = canonicalCompletionHom Y Z :=
    completion_hom_eq_canonical g
  cases hf
  cases hh
  cases hg
  have hη : η = 𝟙 _ := Subsingleton.elim _ _
  cases hη
  change
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalEndpointTwoCell X Y ηret ▷
            canonicalEndpointHom Y Z B) ≫
        (generalLiftEndpointMapComp F hF X Y Z C B).hom =
      (generalLiftEndpointMapComp F hF X Y Z A B).hom ≫
        ((generalLiftPrelaxFunctor F hF).map₂
            (canonicalEndpointTwoCell X Y ηret) ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalEndpointHom Y Z B))
  exact generalLiftEndpointMapComp_naturality_left F hF X Y Z ηret B

/-- The all-arrow composition comparison is natural in every target 2-cell
on its right factor.  Free-groupoid thinness normalizes both walking
representatives, and local discreteness removes the unique walking 2-cell,
leaving the endpoint-normal naturality theorem. -/
theorem generalLiftMapComp_naturality_right
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Target} (f : X ⟶ Y) {g h : Y ⟶ Z} (η : g ⟶ h) :
    (generalLiftPrelaxFunctor F hF).map₂ (f ◁ η) ≫
        (generalLiftMapComp F hF f h).hom =
      (generalLiftMapComp F hF f g).hom ≫
        ((generalLiftPrelaxFunctor F hF).map f ◁
          (generalLiftPrelaxFunctor F hF).map₂ η) := by
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
  exact generalLiftMapComp_naturality_right_canonicalObjects F hF f η

/-- The all-arrow composition comparison is natural in every target 2-cell
on its left factor, after the same endpoint and locally-discrete
normalization used by the right naturality theorem. -/
theorem generalLiftMapComp_naturality_left
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Target} {f h : X ⟶ Y} (η : f ⟶ h) (g : Y ⟶ Z) :
    (generalLiftPrelaxFunctor F hF).map₂ (η ▷ g) ≫
        (generalLiftMapComp F hF h g).hom =
      (generalLiftMapComp F hF f g).hom ≫
        ((generalLiftPrelaxFunctor F hF).map₂ η ▷
          (generalLiftPrelaxFunctor F hF).map g) := by
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
  exact generalLiftMapComp_naturality_left_canonicalObjects F hF η g

/-- The all-arrow compositor can be recovered from its value after replacing
the right factor by an isomorphic arrow.  The final inverse image cancels the
change in the compositor's right output factor. -/
theorem generalLiftMapComp_iso_right_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Target} (f : X ⟶ Y) {g g' : Y ⟶ Z}
    (e : g ≅ g') :
    (generalLiftMapComp F hF f g).hom =
      (generalLiftPrelaxFunctor F hF).map₂ (f ◁ e.hom) ≫
        (generalLiftMapComp F hF f g').hom ≫
        ((generalLiftPrelaxFunctor F hF).map f ◁
          (generalLiftPrelaxFunctor F hF).map₂ e.inv) := by
  rw [← cancel_mono
    ((generalLiftPrelaxFunctor F hF).map f ◁
      (generalLiftPrelaxFunctor F hF).map₂ e.hom)]
  simp only [Category.assoc]
  slice_rhs 3 4 =>
    rw [← Bicategory.whiskerLeft_comp,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp]
    simp
  rw [(generalLiftPrelaxFunctor F hF).map₂_id]
  simp
  exact (generalLiftMapComp_naturality_right F hF f e.hom).symm

/-- The corresponding reconstruction when the left factor is replaced by an
isomorphic arrow.  Its final inverse image cancels the change in the left
output factor. -/
theorem generalLiftMapComp_iso_left_hom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Target} {f f' : X ⟶ Y} (e : f ≅ f')
    (g : Y ⟶ Z) :
    (generalLiftMapComp F hF f g).hom =
      (generalLiftPrelaxFunctor F hF).map₂ (e.hom ▷ g) ≫
        (generalLiftMapComp F hF f' g).hom ≫
        ((generalLiftPrelaxFunctor F hF).map₂ e.inv ▷
          (generalLiftPrelaxFunctor F hF).map g) := by
  rw [← cancel_mono
    ((generalLiftPrelaxFunctor F hF).map₂ e.hom ▷
      (generalLiftPrelaxFunctor F hF).map g)]
  simp only [Category.assoc]
  slice_rhs 3 4 =>
    rw [← Bicategory.comp_whiskerRight,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp]
    simp
  rw [(generalLiftPrelaxFunctor F hF).map₂_id]
  simp
  exact (generalLiftMapComp_naturality_left F hF e.hom g).symm

/-- On any two canonical forward arrows, the all-arrow compositor selects
the explicit forward/forward comparison. -/
theorem generalLiftMapComp_forward
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A B : Type) :
    generalLiftMapComp F hF
        (canonicalForwardHom f A) (canonicalForwardHom g B) =
      generalLiftMapCompForward F hF f g A B := by
  rcases (by fin_cases X <;> simp : X = 0 ∨ X = 1) with rfl | rfl <;>
    rcases (by fin_cases Y <;> simp : Y = 0 ∨ Y = 1) with rfl | rfl <;>
      rcases (by fin_cases Z <;> simp : Z = 0 ∨ Z = 1) with rfl | rfl
  · have hf : f = 𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow) :=
      Subsingleton.elim _ _
    have hg : g = 𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow) :=
      Subsingleton.elim _ _
    subst f
    subst g
    cases canonicalEndpointHom_eq_forward
      (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) A
    cases canonicalEndpointHom_eq_forward
      (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) B
    exact (generalLiftMapComp_endpoint F hF 0 0 0 A B).trans
      (generalLiftEndpointMapComp_zero_zero_zero F hF A B)
  · have hf : f = 𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow) :=
      Subsingleton.elim _ _
    have hg : g = Ript.Examples.WalkingLocalization.arrow :=
      Subsingleton.elim _ _
    subst f
    subst g
    cases canonicalEndpointHom_eq_forward
      (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) A
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow B
    exact (generalLiftMapComp_endpoint F hF 0 0 1 A B).trans
      (generalLiftEndpointMapComp_zero_zero_one F hF A B)
  · exact False.elim ((by omega : ¬ (1 : Fin 2) ≤ 0) g.le)
  · have hf : f = Ript.Examples.WalkingLocalization.arrow :=
      Subsingleton.elim _ _
    have hg : g = 𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow) :=
      Subsingleton.elim _ _
    subst f
    subst g
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow A
    cases canonicalEndpointHom_eq_forward
      (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) B
    exact (generalLiftMapComp_endpoint F hF 0 1 1 A B).trans
      (generalLiftEndpointMapComp_zero_one_one F hF A B)
  · exact False.elim ((by omega : ¬ (1 : Fin 2) ≤ 0) f.le)
  · exact False.elim ((by omega : ¬ (1 : Fin 2) ≤ 0) f.le)
  · exact False.elim ((by omega : ¬ (1 : Fin 2) ≤ 0) g.le)
  · have hf : f = 𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow) :=
      Subsingleton.elim _ _
    have hg : g = 𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow) :=
      Subsingleton.elim _ _
    subst f
    subst g
    cases canonicalEndpointHom_eq_forward
      (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) A
    cases canonicalEndpointHom_eq_forward
      (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) B
    exact (generalLiftMapComp_endpoint F hF 1 1 1 A B).trans
      (generalLiftEndpointMapComp_one_one_one F hF A B)

/-- On a genuine forward arrow followed by its matching inverse, the
all-arrow compositor selects the explicit forward/inverse cancellation
comparison. -/
theorem generalLiftMapComp_forwardInverse
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    generalLiftMapComp F hF
        (canonicalForwardHom f A)
        (canonicalInverseHom f B) =
      generalLiftMapCompForwardInverse F hF f hf A B := by
  fin_cases X <;> fin_cases Y
  · exact False.elim (hf (by decide))
  · have hf' : f = Ript.Examples.WalkingLocalization.arrow :=
      Subsingleton.elim _ _
    subst f
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow A
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow B
    exact (generalLiftMapComp_endpoint F hF 0 1 0 A B).trans
      (generalLiftEndpointMapComp_zero_one_zero F hF A B)
  · exact False.elim ((by omega : ¬ (1 : Fin 2) ≤ 0) f.le)
  · exact False.elim (hf (by decide))

/-- On a genuine inverse arrow followed by its matching forward arrow, the
all-arrow compositor selects the explicit inverse/forward cancellation
comparison. -/
theorem generalLiftMapComp_inverseForward
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    generalLiftMapComp F hF
        (canonicalInverseHom f A)
        (canonicalForwardHom f B) =
      generalLiftMapCompInverseForward F hF f hf A B := by
  fin_cases X <;> fin_cases Y
  · exact False.elim (hf (by decide))
  · have hf' : f = Ript.Examples.WalkingLocalization.arrow :=
      Subsingleton.elim _ _
    subst f
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow A
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow B
    exact (generalLiftMapComp_endpoint F hF 1 0 1 A B).trans
      (generalLiftEndpointMapComp_one_zero_one F hF A B)
  · exact False.elim ((by omega : ¬ (1 : Fin 2) ≤ 0) f.le)
  · exact False.elim (hf (by decide))

/-- On a genuine inverse arrow followed by a retained endomorphism, the
all-arrow compositor selects the explicit inverse/retained comparison. -/
theorem generalLiftMapComp_inverseRetained
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    generalLiftMapComp F hF
        (canonicalInverseHom f A)
        (canonicalForwardHom (𝟙 X) B) =
      generalLiftMapCompInverseRetained F hF f hf A B := by
  fin_cases X <;> fin_cases Y
  · exact False.elim (hf (by decide))
  · have hf' : f = Ript.Examples.WalkingLocalization.arrow :=
      Subsingleton.elim _ _
    subst f
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow A
    cases canonicalEndpointHom_eq_forward
      (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) B
    exact (generalLiftMapComp_endpoint F hF 1 0 0 A B).trans
      (generalLiftEndpointMapComp_one_zero_zero F hF A B)
  · exact False.elim ((by omega : ¬ (1 : Fin 2) ≤ 0) f.le)
  · exact False.elim (hf (by decide))

/-- On a retained endomorphism followed by a genuine inverse arrow, the
all-arrow compositor selects the explicit retained/inverse comparison. -/
theorem generalLiftMapComp_retainedInverse
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B : Type) :
    generalLiftMapComp F hF
        (canonicalForwardHom (𝟙 Y) A)
        (canonicalInverseHom f B) =
      generalLiftMapCompRetainedInverse F hF f hf A B := by
  fin_cases X <;> fin_cases Y
  · exact False.elim (hf (by decide))
  · have hf' : f = Ript.Examples.WalkingLocalization.arrow :=
      Subsingleton.elim _ _
    subst f
    cases canonicalEndpointHom_eq_forward
      (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) A
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow B
    exact (generalLiftMapComp_endpoint F hF 1 1 0 A B).trans
      (generalLiftEndpointMapComp_one_one_zero F hF A B)
  · exact False.elim ((by omega : ¬ (1 : Fin 2) ≤ 0) f.le)
  · exact False.elim (hf (by decide))

set_option backward.isDefEq.respectTransparency false in
/-- The all-arrow compositor satisfies the full oplax associativity law on
three canonical forward arrows.  Naturality first replaces each raw binary
composite by its canonical target normal form; the target comparison square
and the seven-endpoint transport law then identify the two routes. -/
theorem generalLiftMapComp_forward_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y Z W : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalForwardHom f A) (canonicalForwardHom g B)
            (canonicalForwardHom h C)).hom ≫
        (generalLiftMapComp F hF (canonicalForwardHom f A)
          (canonicalForwardHom g B ≫ canonicalForwardHom h C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map (canonicalForwardHom f A) ◁
          (generalLiftMapComp F hF (canonicalForwardHom g B)
            (canonicalForwardHom h C)).hom =
      (generalLiftMapComp F hF
          (canonicalForwardHom f A ≫ canonicalForwardHom g B)
          (canonicalForwardHom h C)).hom ≫
        (generalLiftMapComp F hF (canonicalForwardHom f A)
          (canonicalForwardHom g B)).hom ▷
            (generalLiftPrelaxFunctor F hF).map
              (canonicalForwardHom h C) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom g B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom h C))).hom := by
  rw [generalLiftMapComp_iso_right_hom F hF (canonicalForwardHom f A)
    (canonicalForwardCompositionComparison g h B C)]
  rw [generalLiftMapComp_forward F hF f (g ≫ h) A (B × C)]
  rw [generalLiftMapComp_forward F hF g h B C]
  rw [generalLiftMapComp_iso_left_hom F hF
    (canonicalForwardCompositionComparison f g A B)
    (canonicalForwardHom h C)]
  rw [generalLiftMapComp_forward F hF (f ≫ g) h (A × B) C]
  rw [generalLiftMapComp_forward F hF f g A B]
  simp only [generalLiftMapCompForward_hom,
    Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight,
    Category.assoc]
  slice_lhs 5 6 =>
    rw [← Bicategory.whiskerLeft_comp,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  slice_rhs 4 5 =>
    rw [← Bicategory.comp_whiskerRight,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  simp only [Category.id_comp]
  slice_lhs 1 4 =>
    rw [← generalLiftForwardMapCompTarget_associativity F hF f g h A B C]
  have hwalking : (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
    Category.assoc f g h
  have htransport :=
    generalLiftForwardMapCompTransport_associativity F hF f g h A B C
  rw [hwalking] at htransport
  slice_lhs 3 6 =>
    rw [htransport]

set_option backward.isDefEq.respectTransparency false in
/-- The all-arrow compositor satisfies the full oplax associativity law for a
genuine inverse arrow followed by two retained-coordinate endomorphisms.
Target normalization and inverse endpoint transport expose the already
compiled source associativity law. -/
theorem generalLiftMapComp_inverseRetained_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalInverseHom f A)
            (canonicalForwardHom (𝟙 X) B)
            (canonicalForwardHom (𝟙 X) C)).hom ≫
        (generalLiftMapComp F hF (canonicalInverseHom f A)
          (canonicalForwardHom (𝟙 X) B ≫
            canonicalForwardHom (𝟙 X) C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A) ◁
          (generalLiftMapComp F hF
            (canonicalForwardHom (𝟙 X) B)
            (canonicalForwardHom (𝟙 X) C)).hom =
      (generalLiftMapComp F hF
          (canonicalInverseHom f A ≫
            canonicalForwardHom (𝟙 X) B)
          (canonicalForwardHom (𝟙 X) C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalInverseHom f A)
          (canonicalForwardHom (𝟙 X) B)).hom ▷
            (generalLiftPrelaxFunctor F hF).map
              (canonicalForwardHom (𝟙 X) C) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 X) B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 X) C))).hom := by
  rw [generalLiftMapComp_iso_right_hom F hF (canonicalInverseHom f A)
    (canonicalForwardCompositionComparison (𝟙 X) (𝟙 X) B C)]
  have hid : (𝟙 X ≫ 𝟙 X) = 𝟙 X :=
    Subsingleton.elim _ _
  rw [hid]
  rw [generalLiftMapComp_inverseRetained F hF
    f hf A (B × C)]
  rw [generalLiftMapComp_forward F hF
    (𝟙 X) (𝟙 X) B C]
  rw [generalLiftMapComp_iso_left_hom F hF
    (canonicalInverseRetainedCompositionComparison f A B)
    (canonicalForwardHom (𝟙 X) C)]
  rw [generalLiftMapComp_inverseRetained F hF
    f hf (A × B) C]
  rw [generalLiftMapComp_inverseRetained F hF
    f hf A B]
  simp only [generalLiftMapCompInverseRetained_hom,
    generalLiftMapCompForward_hom,
    Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight,
    Category.assoc]
  slice_lhs 5 6 =>
    rw [← Bicategory.whiskerLeft_comp,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  slice_rhs 4 5 =>
    rw [← Bicategory.comp_whiskerRight,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  simp only [Category.id_comp]
  slice_lhs 1 3 =>
    rw [← generalLiftInverseRetainedMapCompTarget_associativity
      F hF f A B C]
  slice_lhs 3 6 =>
    rw [generalLiftInverseRetainedMapCompTransport_associativity
      F hF f hf A B C]

set_option backward.isDefEq.respectTransparency false in
/-- The all-arrow compositor satisfies the full oplax associativity law for
two retained-coordinate endomorphisms followed by a genuine inverse arrow. -/
theorem generalLiftMapComp_retainedRetainedInverse_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalForwardHom (𝟙 Y) A)
            (canonicalForwardHom (𝟙 Y) B)
            (canonicalInverseHom f C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalForwardHom (𝟙 Y) A)
          (canonicalForwardHom (𝟙 Y) B ≫
            canonicalInverseHom f C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 Y) A) ◁
          (generalLiftMapComp F hF
            (canonicalForwardHom (𝟙 Y) B)
            (canonicalInverseHom f C)).hom =
      (generalLiftMapComp F hF
          (canonicalForwardHom (𝟙 Y) A ≫
            canonicalForwardHom (𝟙 Y) B)
          (canonicalInverseHom f C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalForwardHom (𝟙 Y) A)
          (canonicalForwardHom (𝟙 Y) B)).hom ▷
            (generalLiftPrelaxFunctor F hF).map
              (canonicalInverseHom f C) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 Y) A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 Y) B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f C))).hom := by
  rw [generalLiftMapComp_iso_right_hom F hF
    (canonicalForwardHom (𝟙 Y) A)
    (canonicalRetainedInverseCompositionComparison f B C)]
  rw [generalLiftMapComp_retainedInverse F hF f hf A (B × C)]
  rw [generalLiftMapComp_retainedInverse F hF f hf B C]
  rw [generalLiftMapComp_iso_left_hom F hF
    (canonicalForwardCompositionComparison (𝟙 Y) (𝟙 Y) A B)
    (canonicalInverseHom f C)]
  have hid : (𝟙 Y ≫ 𝟙 Y) = 𝟙 Y :=
    Subsingleton.elim _ _
  rw [hid]
  rw [generalLiftMapComp_retainedInverse F hF f hf (A × B) C]
  rw [generalLiftMapComp_forward F hF (𝟙 Y) (𝟙 Y) A B]
  simp only [generalLiftMapCompRetainedInverse_hom,
    generalLiftMapCompForward_hom,
    Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight,
    Category.assoc]
  slice_lhs 5 6 =>
    rw [← Bicategory.whiskerLeft_comp,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  slice_rhs 4 5 =>
    rw [← Bicategory.comp_whiskerRight,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  simp only [Category.id_comp]
  slice_lhs 1 3 =>
    rw [← generalLiftRetainedInverseMapCompTarget_associativity
      F hF f A B C]
  slice_lhs 3 6 =>
    rw [generalLiftRetainedInverseMapCompTransport_associativity
      F hF f hf A B C]

set_option backward.isDefEq.respectTransparency false in
/-- The all-arrow compositor satisfies the full oplax associativity law for a
retained endomorphism, a genuine inverse arrow, and a retained endomorphism. -/
theorem generalLiftMapComp_retainedInverseRetained_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalForwardHom (𝟙 Y) A)
            (canonicalInverseHom f B)
            (canonicalForwardHom (𝟙 X) C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalForwardHom (𝟙 Y) A)
          (canonicalInverseHom f B ≫
            canonicalForwardHom (𝟙 X) C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 Y) A) ◁
          (generalLiftMapComp F hF
            (canonicalInverseHom f B)
            (canonicalForwardHom (𝟙 X) C)).hom =
      (generalLiftMapComp F hF
          (canonicalForwardHom (𝟙 Y) A ≫
            canonicalInverseHom f B)
          (canonicalForwardHom (𝟙 X) C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalForwardHom (𝟙 Y) A)
          (canonicalInverseHom f B)).hom ▷
            (generalLiftPrelaxFunctor F hF).map
              (canonicalForwardHom (𝟙 X) C) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 Y) A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 X) C))).hom := by
  rw [generalLiftMapComp_iso_right_hom F hF
    (canonicalForwardHom (𝟙 Y) A)
    (canonicalInverseRetainedCompositionComparison f B C)]
  rw [generalLiftMapComp_retainedInverse F hF f hf A (B × C)]
  rw [generalLiftMapComp_inverseRetained F hF f hf B C]
  rw [generalLiftMapComp_iso_left_hom F hF
    (canonicalRetainedInverseCompositionComparison f A B)
    (canonicalForwardHom (𝟙 X) C)]
  rw [generalLiftMapComp_inverseRetained F hF f hf (A × B) C]
  rw [generalLiftMapComp_retainedInverse F hF f hf A B]
  simp only [generalLiftMapCompRetainedInverse_hom,
    generalLiftMapCompInverseRetained_hom,
    Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight,
    Category.assoc]
  slice_lhs 5 6 =>
    rw [← Bicategory.whiskerLeft_comp,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  slice_rhs 4 5 =>
    rw [← Bicategory.comp_whiskerRight,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  simp only [Category.id_comp]
  slice_lhs 1 3 =>
    rw [← generalLiftRetainedInverseRetainedMapCompTarget_associativity
      F hF f A B C]
  slice_lhs 3 6 =>
    rw [generalLiftRetainedInverseRetainedMapCompTransport_associativity
      F hF f hf A B C]

set_option backward.isDefEq.respectTransparency false in
/-- The all-arrow compositor satisfies the full oplax associativity law for
a genuine forward arrow, a retained endomorphism, and the matching inverse
arrow. -/
theorem generalLiftMapComp_forwardRetainedInverse_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalForwardHom f A)
            (canonicalForwardHom (𝟙 Y) B)
            (canonicalInverseHom f C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalForwardHom f A)
          (canonicalForwardHom (𝟙 Y) B ≫
            canonicalInverseHom f C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A) ◁
          (generalLiftMapComp F hF
            (canonicalForwardHom (𝟙 Y) B)
            (canonicalInverseHom f C)).hom =
      (generalLiftMapComp F hF
          (canonicalForwardHom f A ≫
            canonicalForwardHom (𝟙 Y) B)
          (canonicalInverseHom f C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalForwardHom f A)
          (canonicalForwardHom (𝟙 Y) B)).hom ▷
            (generalLiftPrelaxFunctor F hF).map
              (canonicalInverseHom f C) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 Y) B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f C))).hom := by
  rw [generalLiftMapComp_iso_right_hom F hF
    (canonicalForwardHom f A)
    (canonicalRetainedInverseCompositionComparison f B C)]
  rw [generalLiftMapComp_forwardInverse F hF f hf A (B × C)]
  rw [generalLiftMapComp_retainedInverse F hF f hf B C]
  rw [generalLiftMapComp_iso_left_hom F hF
    (canonicalForwardCompositionComparison f (𝟙 Y) A B)
    (canonicalInverseHom f C)]
  have hid : (f ≫ 𝟙 Y) = f := Subsingleton.elim _ _
  rw [hid]
  rw [generalLiftMapComp_forwardInverse F hF f hf (A × B) C]
  rw [generalLiftMapComp_forward F hF f (𝟙 Y) A B]
  simp only [generalLiftMapCompForwardInverse_hom,
    generalLiftMapCompRetainedInverse_hom,
    generalLiftMapCompForward_hom,
    Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight,
    Category.assoc]
  slice_lhs 5 6 =>
    rw [← Bicategory.whiskerLeft_comp,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  slice_rhs 4 5 =>
    rw [← Bicategory.comp_whiskerRight,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  simp only [Category.id_comp]
  slice_lhs 1 3 =>
    rw [← generalLiftForwardRetainedInverseMapCompTarget_associativity
      F hF f A B C]
  slice_lhs 3 6 =>
    rw [generalLiftForwardRetainedInverseMapCompTransport_associativity
      F hF f hf A B C]

set_option backward.isDefEq.respectTransparency false in
/-- The all-arrow compositor satisfies the full oplax associativity law for a
retained endomorphism, a genuine forward arrow, and the matching inverse. -/
theorem generalLiftMapComp_retainedForwardInverse_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalForwardHom (𝟙 X) A)
            (canonicalForwardHom f B)
            (canonicalInverseHom f C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalForwardHom (𝟙 X) A)
          (canonicalForwardHom f B ≫
            canonicalInverseHom f C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 X) A) ◁
          (generalLiftMapComp F hF
            (canonicalForwardHom f B)
            (canonicalInverseHom f C)).hom =
      (generalLiftMapComp F hF
          (canonicalForwardHom (𝟙 X) A ≫
            canonicalForwardHom f B)
          (canonicalInverseHom f C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalForwardHom (𝟙 X) A)
          (canonicalForwardHom f B)).hom ▷
            (generalLiftPrelaxFunctor F hF).map
              (canonicalInverseHom f C) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 X) A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f C))).hom := by
  rw [generalLiftMapComp_iso_right_hom F hF
    (canonicalForwardHom (𝟙 X) A)
    (canonicalForwardInverseCompositionComparison f B C)]
  rw [generalLiftMapComp_forward F hF (𝟙 X) (𝟙 X) A (B × C)]
  rw [generalLiftMapComp_forwardInverse F hF f hf B C]
  rw [generalLiftMapComp_iso_left_hom F hF
    (canonicalForwardCompositionComparison (𝟙 X) f A B)
    (canonicalInverseHom f C)]
  have hid : (𝟙 X ≫ f) = f := Subsingleton.elim _ _
  rw [hid]
  rw [generalLiftMapComp_forwardInverse F hF f hf (A × B) C]
  rw [generalLiftMapComp_forward F hF (𝟙 X) f A B]
  simp only [generalLiftMapCompForwardInverse_hom,
    generalLiftMapCompForward_hom,
    Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight,
    Category.assoc]
  slice_lhs 5 6 =>
    rw [← Bicategory.whiskerLeft_comp,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  slice_rhs 4 5 =>
    rw [← Bicategory.comp_whiskerRight,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  simp only [Category.id_comp]
  slice_lhs 1 3 =>
    rw [← generalLiftRetainedForwardInverseMapCompTarget_associativity
      F hF f A B C]
  slice_lhs 3 6 =>
    rw [generalLiftRetainedForwardInverseMapCompTransport_associativity
      F hF f hf A B C]

set_option backward.isDefEq.respectTransparency false in
/-- The all-arrow compositor satisfies the full oplax associativity law for a
genuine forward arrow, its matching inverse, and a retained endomorphism. -/
theorem generalLiftMapComp_forwardInverseRetained_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalForwardHom f A)
            (canonicalInverseHom f B)
            (canonicalForwardHom (𝟙 X) C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalForwardHom f A)
          (canonicalInverseHom f B ≫
            canonicalForwardHom (𝟙 X) C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A) ◁
          (generalLiftMapComp F hF
            (canonicalInverseHom f B)
            (canonicalForwardHom (𝟙 X) C)).hom =
      (generalLiftMapComp F hF
          (canonicalForwardHom f A ≫
            canonicalInverseHom f B)
          (canonicalForwardHom (𝟙 X) C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalForwardHom f A)
          (canonicalInverseHom f B)).hom ▷
            (generalLiftPrelaxFunctor F hF).map
              (canonicalForwardHom (𝟙 X) C) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 X) C))).hom := by
  rw [generalLiftMapComp_iso_right_hom F hF
    (canonicalForwardHom f A)
    (canonicalInverseRetainedCompositionComparison f B C)]
  rw [generalLiftMapComp_forwardInverse F hF f hf A (B × C)]
  rw [generalLiftMapComp_inverseRetained F hF f hf B C]
  rw [generalLiftMapComp_iso_left_hom F hF
    (canonicalForwardInverseCompositionComparison f A B)
    (canonicalForwardHom (𝟙 X) C)]
  rw [generalLiftMapComp_forward F hF (𝟙 X) (𝟙 X) (A × B) C]
  rw [generalLiftMapComp_forwardInverse F hF f hf A B]
  simp only [generalLiftMapCompForwardInverse_hom,
    generalLiftMapCompInverseRetained_hom,
    generalLiftMapCompForward_hom,
    Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight,
    Category.assoc]
  slice_lhs 5 6 =>
    rw [← Bicategory.whiskerLeft_comp,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  slice_rhs 4 5 =>
    rw [← Bicategory.comp_whiskerRight,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  simp only [Category.id_comp]
  slice_lhs 1 3 =>
    rw [← generalLiftForwardInverseRetainedMapCompTarget_associativity
      F hF f A B C]
  slice_lhs 3 6 =>
    rw [generalLiftForwardInverseRetainedMapCompTransport_associativity
      F hF f hf A B C]

set_option backward.isDefEq.respectTransparency false in
/-- The all-arrow compositor satisfies the full oplax associativity law for a
genuine inverse arrow, its matching forward arrow, and a retained
endomorphism. -/
theorem generalLiftMapComp_inverseForwardRetained_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalInverseHom f A)
            (canonicalForwardHom f B)
            (canonicalForwardHom (𝟙 Y) C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalInverseHom f A)
          (canonicalForwardHom f B ≫
            canonicalForwardHom (𝟙 Y) C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A) ◁
          (generalLiftMapComp F hF
            (canonicalForwardHom f B)
            (canonicalForwardHom (𝟙 Y) C)).hom =
      (generalLiftMapComp F hF
          (canonicalInverseHom f A ≫
            canonicalForwardHom f B)
          (canonicalForwardHom (𝟙 Y) C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalInverseHom f A)
          (canonicalForwardHom f B)).hom ▷
            (generalLiftPrelaxFunctor F hF).map
              (canonicalForwardHom (𝟙 Y) C) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 Y) C))).hom := by
  rw [generalLiftMapComp_iso_right_hom F hF
    (canonicalInverseHom f A)
    (canonicalForwardCompositionComparison f (𝟙 Y) B C)]
  have hid : (f ≫ 𝟙 Y) = f := Subsingleton.elim _ _
  rw [hid]
  rw [generalLiftMapComp_inverseForward F hF f hf A (B × C)]
  rw [generalLiftMapComp_forward F hF f (𝟙 Y) B C]
  rw [generalLiftMapComp_iso_left_hom F hF
    (canonicalInverseForwardCompositionComparison f A B)
    (canonicalForwardHom (𝟙 Y) C)]
  rw [generalLiftMapComp_forward F hF (𝟙 Y) (𝟙 Y) (A × B) C]
  rw [generalLiftMapComp_inverseForward F hF f hf A B]
  simp only [generalLiftMapCompInverseForward_hom,
    generalLiftMapCompForward_hom,
    Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight,
    Category.assoc]
  slice_lhs 5 6 =>
    rw [← Bicategory.whiskerLeft_comp,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  slice_rhs 4 5 =>
    rw [← Bicategory.comp_whiskerRight,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  simp only [Category.id_comp]
  slice_lhs 1 3 =>
    rw [← generalLiftInverseForwardRetainedMapCompTarget_associativity
      F hF f A B C]
  slice_lhs 3 6 =>
    rw [generalLiftInverseForwardRetainedMapCompTransport_associativity
      F hF f hf A B C]

set_option backward.isDefEq.respectTransparency false in
/-- The all-arrow compositor satisfies the full oplax associativity law for a
genuine inverse arrow, a retained endomorphism, and the matching forward
arrow. -/
theorem generalLiftMapComp_inverseRetainedForward_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalInverseHom f A)
            (canonicalForwardHom (𝟙 X) B)
            (canonicalForwardHom f C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalInverseHom f A)
          (canonicalForwardHom (𝟙 X) B ≫
            canonicalForwardHom f C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A) ◁
          (generalLiftMapComp F hF
            (canonicalForwardHom (𝟙 X) B)
            (canonicalForwardHom f C)).hom =
      (generalLiftMapComp F hF
          (canonicalInverseHom f A ≫
            canonicalForwardHom (𝟙 X) B)
          (canonicalForwardHom f C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalInverseHom f A)
          (canonicalForwardHom (𝟙 X) B)).hom ▷
            (generalLiftPrelaxFunctor F hF).map
              (canonicalForwardHom f C) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 X) B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f C))).hom := by
  rw [generalLiftMapComp_iso_right_hom F hF
    (canonicalInverseHom f A)
    (canonicalForwardCompositionComparison (𝟙 X) f B C)]
  have hid : (𝟙 X ≫ f) = f := Subsingleton.elim _ _
  rw [hid]
  rw [generalLiftMapComp_inverseForward F hF f hf A (B × C)]
  rw [generalLiftMapComp_forward F hF (𝟙 X) f B C]
  rw [generalLiftMapComp_iso_left_hom F hF
    (canonicalInverseRetainedCompositionComparison f A B)
    (canonicalForwardHom f C)]
  rw [generalLiftMapComp_inverseForward F hF f hf (A × B) C]
  rw [generalLiftMapComp_inverseRetained F hF f hf A B]
  simp only [generalLiftMapCompInverseForward_hom,
    generalLiftMapCompInverseRetained_hom,
    generalLiftMapCompForward_hom,
    Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight,
    Category.assoc]
  slice_lhs 5 6 =>
    rw [← Bicategory.whiskerLeft_comp,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  slice_rhs 4 5 =>
    rw [← Bicategory.comp_whiskerRight,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  simp only [Category.id_comp]
  slice_lhs 1 3 =>
    rw [← generalLiftInverseRetainedForwardMapCompTarget_associativity
      F hF f A B C]
  slice_lhs 3 6 =>
    rw [generalLiftInverseRetainedForwardMapCompTransport_associativity
      F hF f hf A B C]

set_option backward.isDefEq.respectTransparency false in
/-- The all-arrow compositor satisfies the full oplax associativity law for a
retained endomorphism, the matching inverse, and the matching forward arrow. -/
theorem generalLiftMapComp_retainedInverseForward_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalForwardHom (𝟙 Y) A)
            (canonicalInverseHom f B)
            (canonicalForwardHom f C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalForwardHom (𝟙 Y) A)
          (canonicalInverseHom f B ≫
            canonicalForwardHom f C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 Y) A) ◁
          (generalLiftMapComp F hF
            (canonicalInverseHom f B)
            (canonicalForwardHom f C)).hom =
      (generalLiftMapComp F hF
          (canonicalForwardHom (𝟙 Y) A ≫
            canonicalInverseHom f B)
          (canonicalForwardHom f C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalForwardHom (𝟙 Y) A)
          (canonicalInverseHom f B)).hom ▷
            (generalLiftPrelaxFunctor F hF).map
              (canonicalForwardHom f C) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 Y) A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f C))).hom := by
  rw [generalLiftMapComp_iso_right_hom F hF
    (canonicalForwardHom (𝟙 Y) A)
    (canonicalInverseForwardCompositionComparison f B C)]
  rw [generalLiftMapComp_forward F hF (𝟙 Y) (𝟙 Y)
    A (B × C)]
  rw [generalLiftMapComp_inverseForward F hF f hf B C]
  rw [generalLiftMapComp_iso_left_hom F hF
    (canonicalRetainedInverseCompositionComparison f A B)
    (canonicalForwardHom f C)]
  rw [generalLiftMapComp_inverseForward F hF f hf (A × B) C]
  rw [generalLiftMapComp_retainedInverse F hF f hf A B]
  simp only [generalLiftMapCompInverseForward_hom,
    generalLiftMapCompRetainedInverse_hom,
    generalLiftMapCompForward_hom,
    Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight,
    Category.assoc]
  slice_lhs 5 6 =>
    rw [← Bicategory.whiskerLeft_comp,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  slice_rhs 4 5 =>
    rw [← Bicategory.comp_whiskerRight,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  simp only [Category.id_comp]
  slice_lhs 1 3 =>
    rw [← generalLiftRetainedInverseForwardMapCompTarget_associativity
      F hF f A B C]
  slice_lhs 3 6 =>
    rw [generalLiftRetainedInverseForwardMapCompTransport_associativity
      F hF f hf A B C]

set_option backward.isDefEq.respectTransparency false in
/-- The all-arrow compositor satisfies the full oplax associativity law for a
forward arrow, its matching inverse, and the forward arrow again. -/
theorem generalLiftMapComp_forwardInverseForward_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalForwardHom f A)
            (canonicalInverseHom f B)
            (canonicalForwardHom f C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalForwardHom f A)
          (canonicalInverseHom f B ≫
            canonicalForwardHom f C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A) ◁
          (generalLiftMapComp F hF
            (canonicalInverseHom f B)
            (canonicalForwardHom f C)).hom =
      (generalLiftMapComp F hF
          (canonicalForwardHom f A ≫
            canonicalInverseHom f B)
          (canonicalForwardHom f C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalForwardHom f A)
          (canonicalInverseHom f B)).hom ▷
            (generalLiftPrelaxFunctor F hF).map
              (canonicalForwardHom f C) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f C))).hom := by
  rw [generalLiftMapComp_iso_right_hom F hF
    (canonicalForwardHom f A)
    (canonicalInverseForwardCompositionComparison f B C)]
  rw [generalLiftMapComp_forward F hF f (𝟙 Y) A (B × C)]
  rw [generalLiftMapComp_inverseForward F hF f hf B C]
  rw [generalLiftMapComp_iso_left_hom F hF
    (canonicalForwardInverseCompositionComparison f A B)
    (canonicalForwardHom f C)]
  rw [generalLiftMapComp_forward F hF (𝟙 X) f (A × B) C]
  rw [generalLiftMapComp_forwardInverse F hF f hf A B]
  simp only [generalLiftMapCompForwardInverse_hom,
    generalLiftMapCompInverseForward_hom,
    generalLiftMapCompForward_hom,
    Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight,
    Category.assoc]
  slice_lhs 5 6 =>
    rw [← Bicategory.whiskerLeft_comp,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  slice_rhs 4 5 =>
    rw [← Bicategory.comp_whiskerRight,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  simp only [Category.id_comp]
  slice_lhs 1 3 =>
    rw [← generalLiftForwardInverseForwardMapCompTarget_associativity
      F hF f A B C]
  slice_lhs 3 6 =>
    rw [generalLiftForwardInverseForwardMapCompTransport_associativity
      F hF f hf A B C]

set_option backward.isDefEq.respectTransparency false in
/-- The all-arrow compositor satisfies the full oplax associativity law for
an inverse arrow, its matching forward arrow, and the inverse arrow again. -/
theorem generalLiftMapComp_inverseForwardInverse_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalInverseHom f A)
            (canonicalForwardHom f B)
            (canonicalInverseHom f C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalInverseHom f A)
          (canonicalForwardHom f B ≫
            canonicalInverseHom f C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A) ◁
          (generalLiftMapComp F hF
            (canonicalForwardHom f B)
            (canonicalInverseHom f C)).hom =
      (generalLiftMapComp F hF
          (canonicalInverseHom f A ≫
            canonicalForwardHom f B)
          (canonicalInverseHom f C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalInverseHom f A)
          (canonicalForwardHom f B)).hom ▷
            (generalLiftPrelaxFunctor F hF).map
              (canonicalInverseHom f C) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f C))).hom := by
  rw [generalLiftMapComp_iso_right_hom F hF
    (canonicalInverseHom f A)
    (canonicalForwardInverseCompositionComparison f B C)]
  rw [generalLiftMapComp_inverseRetained F hF f hf A (B × C)]
  rw [generalLiftMapComp_forwardInverse F hF f hf B C]
  rw [generalLiftMapComp_iso_left_hom F hF
    (canonicalInverseForwardCompositionComparison f A B)
    (canonicalInverseHom f C)]
  rw [generalLiftMapComp_retainedInverse F hF f hf (A × B) C]
  rw [generalLiftMapComp_inverseForward F hF f hf A B]
  simp only [generalLiftMapCompInverseRetained_hom,
    generalLiftMapCompForwardInverse_hom,
    generalLiftMapCompRetainedInverse_hom,
    generalLiftMapCompInverseForward_hom,
    Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight,
    Category.assoc]
  slice_lhs 5 6 =>
    rw [← Bicategory.whiskerLeft_comp,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  slice_rhs 4 5 =>
    rw [← Bicategory.comp_whiskerRight,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp,
      Iso.inv_hom_id,
      (generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  simp only [Category.id_comp]
  slice_lhs 1 3 =>
    rw [← generalLiftInverseForwardInverseMapCompTarget_associativity
      F hF f A B C]
  slice_lhs 3 6 =>
    rw [generalLiftInverseForwardInverseMapCompTransport_associativity
      F hF f hf A B C]

/-! ## The forward left-unit coherence frontier -/

/-- Canonical source composition with the retained left unitor factors
through the canonical source identity comparison. -/
theorem canonicalSourceLeftUnitorFactorization
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (canonicalSourceCompositionComparison
        (𝟙 X) f (𝟙 (MonoidalSingleObj.star (Type))) A).hom ≫
        canonicalSourceTwoCell f (MonoidalCategory.leftUnitor A).hom =
      ((canonicalSourceIdentityComparison X).hom ▷
          canonicalSourceHom f A) ≫
        (λ_ (canonicalSourceHom f A)).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- The target analogue of `canonicalSourceLeftUnitorFactorization`. -/
theorem canonicalForwardLeftUnitorFactorization
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (canonicalForwardCompositionComparison
        (𝟙 X) f (𝟙 (MonoidalSingleObj.star (Type))) A).hom ≫
        canonicalForwardTwoCell f (MonoidalCategory.leftUnitor A).hom =
      ((canonicalForwardIdentityComparison X).hom ▷
          canonicalForwardHom f A) ≫
        (λ_ (canonicalForwardHom f A)).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- A retained identity followed by a canonical inverse arrow factors through
the canonical target identity comparison and left unitor. -/
theorem canonicalInverseLeftUnitorFactorization
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (canonicalRetainedInverseCompositionComparison f
        (𝟙 (MonoidalSingleObj.star (Type))) A).hom ≫
        canonicalInverseTwoCell f (MonoidalCategory.leftUnitor A).hom =
      ((canonicalForwardIdentityComparison Y).hom ▷
          canonicalInverseHom f A) ≫
        (λ_ (canonicalInverseHom f A)).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- Canonical source composition with the retained right unitor factors
through the canonical source identity comparison. -/
theorem canonicalSourceRightUnitorFactorization
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (canonicalSourceCompositionComparison
        f (𝟙 Y) A (𝟙 (MonoidalSingleObj.star (Type)))).hom ≫
        canonicalSourceTwoCell f (MonoidalCategory.rightUnitor A).hom =
      (canonicalSourceHom f A ◁
          (canonicalSourceIdentityComparison Y).hom) ≫
        (ρ_ (canonicalSourceHom f A)).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- The target analogue of `canonicalSourceRightUnitorFactorization`. -/
theorem canonicalForwardRightUnitorFactorization
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (canonicalForwardCompositionComparison
        f (𝟙 Y) A (𝟙 (MonoidalSingleObj.star (Type)))).hom ≫
        canonicalForwardTwoCell f (MonoidalCategory.rightUnitor A).hom =
      (canonicalForwardHom f A ◁
          (canonicalForwardIdentityComparison Y).hom) ≫
        (ρ_ (canonicalForwardHom f A)).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- A canonical inverse arrow followed by the retained identity factors
through the canonical target identity comparison and right unitor. -/
theorem canonicalInverseRightUnitorFactorization
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (canonicalInverseRetainedCompositionComparison f A
        (𝟙 (MonoidalSingleObj.star (Type)))).hom ≫
        canonicalInverseTwoCell f (MonoidalCategory.rightUnitor A).hom =
      (canonicalInverseHom f A ◁
          (canonicalForwardIdentityComparison X).hom) ≫
        (ρ_ (canonicalInverseHom f A)).hom := by
  apply Prod.ext
  · apply Subsingleton.elim
  · rfl

/-- The last three stages of the canonical unit comparison, starting at the
mapped canonical forward identity rather than the mapped strict identity. -/
noncomputable def generalLiftForwardMapIdTail
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    (X : Ript.Examples.WalkingLocalization.Arrow) :
    (generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom (𝟙 X)
          (𝟙 (MonoidalSingleObj.star (Type)))) ≅
      𝟙 ((generalLiftPrelaxFunctor F hF).obj
        (canonicalTargetObject X)) :=
  eqToIso (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X)
      (𝟙 (MonoidalSingleObj.star (Type)))) ≪≫
    F.map₂Iso (canonicalSourceIdentityComparison X) ≪≫
    F.mapId (canonicalSourceObject X)

/-- The source pseudofunctor's left-unit law, expressed through the
canonical source identity and composition comparisons. -/
theorem generalLiftSourceLeftUnitor
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    F.map₂
        ((canonicalSourceCompositionComparison
            (𝟙 X) f (𝟙 (MonoidalSingleObj.star (Type))) A).hom ≫
          canonicalSourceTwoCell f
            (MonoidalCategory.leftUnitor A).hom) =
      (F.mapComp
          (canonicalSourceHom (𝟙 X)
            (𝟙 (MonoidalSingleObj.star (Type))))
          (canonicalSourceHom f A)).hom ≫
        (F.map₂ (canonicalSourceIdentityComparison X).hom ≫
          (F.mapId (canonicalSourceObject X)).hom) ▷
            F.map (canonicalSourceHom f A) ≫
        (λ_ (F.map (canonicalSourceHom f A))).hom := by
  rw [canonicalSourceLeftUnitorFactorization]
  have hnat :
      F.map₂ ((canonicalSourceIdentityComparison X).hom ▷
            canonicalSourceHom f A) ≫
          (F.mapComp (𝟙 (canonicalSourceObject X))
            (canonicalSourceHom f A)).hom =
        (F.mapComp
            (canonicalSourceHom (𝟙 X)
              (𝟙 (MonoidalSingleObj.star (Type))))
            (canonicalSourceHom f A)).hom ≫
          F.map₂ (canonicalSourceIdentityComparison X).hom ▷
            F.map (canonicalSourceHom f A) :=
    F.toOplax.mapComp_naturality_left
      (canonicalSourceIdentityComparison X).hom
      (canonicalSourceHom f A)
  rw [F.map₂_comp, F.map₂_left_unitor,
    ← Category.assoc, hnat]
  simp only [comp_whiskerRight, Category.assoc]

/-- After entering the source through the inverse composition comparison,
the canonical source left-unit chain contracts to the mapped retained
left unitor. -/
theorem generalLiftSourceLeftUnitor_afterCompositionComparison
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    F.map₂ (canonicalSourceCompositionComparison
          (𝟙 X) f (𝟙 (MonoidalSingleObj.star (Type))) A).symm.hom ≫
        (F.mapComp
          (canonicalSourceHom (𝟙 X)
            (𝟙 (MonoidalSingleObj.star (Type))))
          (canonicalSourceHom f A)).hom ≫
        (F.map₂ (canonicalSourceIdentityComparison X).hom ≫
          (F.mapId (canonicalSourceObject X)).hom) ▷
            F.map (canonicalSourceHom f A) ≫
        (λ_ (F.map (canonicalSourceHom f A))).hom =
      F.map₂ (canonicalSourceTwoCell f
        (MonoidalCategory.leftUnitor A).hom) := by
  rw [← generalLiftSourceLeftUnitor (F := F) (f := f) (A := A)]
  rw [← F.map₂_comp]
  congr 1

/-- The source pseudofunctor's right-unit law, expressed through the
canonical source identity and composition comparisons. -/
theorem generalLiftSourceRightUnitor
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    F.map₂
        ((canonicalSourceCompositionComparison
            f (𝟙 Y) A (𝟙 (MonoidalSingleObj.star (Type)))).hom ≫
          canonicalSourceTwoCell f
            (MonoidalCategory.rightUnitor A).hom) =
      (F.mapComp
          (canonicalSourceHom f A)
          (canonicalSourceHom (𝟙 Y)
            (𝟙 (MonoidalSingleObj.star (Type))))).hom ≫
        F.map (canonicalSourceHom f A) ◁
          (F.map₂ (canonicalSourceIdentityComparison Y).hom ≫
            (F.mapId (canonicalSourceObject Y)).hom) ≫
        (ρ_ (F.map (canonicalSourceHom f A))).hom := by
  rw [canonicalSourceRightUnitorFactorization]
  have hnat :
      F.map₂ (canonicalSourceHom f A ◁
            (canonicalSourceIdentityComparison Y).hom) ≫
          (F.mapComp (canonicalSourceHom f A)
            (𝟙 (canonicalSourceObject Y))).hom =
        (F.mapComp
            (canonicalSourceHom f A)
            (canonicalSourceHom (𝟙 Y)
              (𝟙 (MonoidalSingleObj.star (Type))))).hom ≫
          F.map (canonicalSourceHom f A) ◁
            F.map₂ (canonicalSourceIdentityComparison Y).hom :=
    F.toOplax.mapComp_naturality_right
      (canonicalSourceHom f A)
      (canonicalSourceIdentityComparison Y).hom
  rw [F.map₂_comp, F.map₂_right_unitor,
    ← Category.assoc, hnat]
  simp only [whiskerLeft_comp, Category.assoc]

/-- After entering the source through the inverse composition comparison,
the canonical source right-unit chain contracts to the mapped retained
right unitor. -/
theorem generalLiftSourceRightUnitor_afterCompositionComparison
    (F : Source ⥤ᵖ E)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    F.map₂ (canonicalSourceCompositionComparison
          f (𝟙 Y) A (𝟙 (MonoidalSingleObj.star (Type)))).symm.hom ≫
        (F.mapComp
          (canonicalSourceHom f A)
          (canonicalSourceHom (𝟙 Y)
            (𝟙 (MonoidalSingleObj.star (Type))))).hom ≫
        F.map (canonicalSourceHom f A) ◁
          (F.map₂ (canonicalSourceIdentityComparison Y).hom ≫
            (F.mapId (canonicalSourceObject Y)).hom) ≫
        (ρ_ (F.map (canonicalSourceHom f A))).hom =
      F.map₂ (canonicalSourceTwoCell f
        (MonoidalCategory.rightUnitor A).hom) := by
  rw [← generalLiftSourceRightUnitor (F := F) (f := f) (A := A)]
  rw [← F.map₂_comp]
  congr 1

/-- Transporting both factors of a left-unit chain through isomorphisms and
then transporting the result is the same as applying the transported unit
2-cell directly. -/
private theorem transportLeftUnitorThroughIsos
    {a b : E} {i i' : a ⟶ a} {f f' : a ⟶ b}
    (ei : i ≅ i') (ef : f ≅ f') (α : i' ⟶ 𝟙 a) :
    (ei.inv ▷ f') ≫ (i ◁ ef.inv) ≫
        ((ei.hom ≫ α) ▷ f) ≫ (λ_ f).hom ≫ ef.hom =
      (α ▷ f') ≫ (λ_ f').hom := by
  simp only [comp_whiskerRight, Category.assoc]
  rw [← whisker_exchange_assoc ei.inv ef.inv]
  slice_lhs 2 3 => simp
  simp only [Category.id_comp, Category.assoc]
  rw [whisker_exchange_assoc α ef.inv]
  rw [leftUnitor_naturality_assoc]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Forward sliding at the retained identity intertwines the source identity
tails at the two endpoints. -/
theorem generalLiftForwardSlidingSource_unit
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) :
    (generalLiftForwardSlidingSource F hF f
        (𝟙 (MonoidalSingleObj.star (Type)))).hom ≫
        ((F.map₂ (canonicalSourceIdentityComparison X).hom ≫
          (F.mapId (canonicalSourceObject X)).hom) ▷
            (generalLiftSourceEquivalence F hF f).hom) ≫
        (λ_ (generalLiftSourceEquivalence F hF f).hom).hom =
      ((generalLiftSourceEquivalence F hF f).hom ◁
          (F.map₂ (canonicalSourceIdentityComparison Y).hom ≫
            (F.mapId (canonicalSourceObject Y)).hom)) ≫
        (ρ_ (generalLiftSourceEquivalence F hF f).hom).hom := by
  change
    ((generalLiftForwardFactorizationSource F hF f
          (𝟙 (MonoidalSingleObj.star (Type)))).inv ≫
        (generalLiftRetainedForwardFactorizationSource F hF f
          (𝟙 (MonoidalSingleObj.star (Type)))).hom) ≫
      ((F.map₂ (canonicalSourceIdentityComparison X).hom ≫
        (F.mapId (canonicalSourceObject X)).hom) ▷
          F.map (canonicalSourceHom f
            (𝟙 (MonoidalSingleObj.star (Type))))) ≫
      (λ_ (F.map (canonicalSourceHom f
        (𝟙 (MonoidalSingleObj.star (Type)))))).hom =
    (F.map (canonicalSourceHom f
        (𝟙 (MonoidalSingleObj.star (Type)))) ◁
      (F.map₂ (canonicalSourceIdentityComparison Y).hom ≫
        (F.mapId (canonicalSourceObject Y)).hom)) ≫
      (ρ_ (F.map (canonicalSourceHom f
        (𝟙 (MonoidalSingleObj.star (Type)))))).hom
  simp only [generalLiftForwardFactorizationSource,
    generalLiftRetainedForwardFactorizationSource,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    PrelaxFunctor.map₂Iso_hom, PrelaxFunctor.map₂Iso_inv]
  simp only [Category.assoc]
  rw [← generalLiftSourceLeftUnitor
    (F := F) (f := f)
    (A := 𝟙 (MonoidalSingleObj.star (Type)))]
  rw [← canonicalSourceRetainedGeneratorComparison_unit f]
  slice_lhs 3 4 =>
    rw [← F.map₂_comp]
    simp
  rw [canonicalSourceGeneratorRetainedComparison_unit f]
  rw [generalLiftSourceRightUnitor
    (F := F) (f := f)
    (A := 𝟙 (MonoidalSingleObj.star (Type)))]
  rw [F.map₂_id]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The mate-derived inverse sliding constraint satisfies the corresponding
identity-tail law. -/
theorem generalLiftInverseSlidingSource_unit
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) :
    (generalLiftInverseSlidingSource F hF f
        (𝟙 (MonoidalSingleObj.star (Type)))).hom ≫
        ((F.map₂ (canonicalSourceIdentityComparison Y).hom ≫
          (F.mapId (canonicalSourceObject Y)).hom) ▷
            (generalLiftSourceEquivalence F hF f).inv) ≫
        (λ_ (generalLiftSourceEquivalence F hF f).inv).hom =
      ((generalLiftSourceEquivalence F hF f).inv ◁
          (F.map₂ (canonicalSourceIdentityComparison X).hom ≫
            (F.mapId (canonicalSourceObject X)).hom)) ≫
        (ρ_ (generalLiftSourceEquivalence F hF f).inv).hom := by
  let l := (generalLiftSourceEquivalence F hF f).hom
  let r := (generalLiftSourceEquivalence F hF f).inv
  let p := F.map₂ (canonicalSourceIdentityComparison X).hom ≫
    (F.mapId (canonicalSourceObject X)).hom
  let q := F.map₂ (canonicalSourceIdentityComparison Y).hom ≫
    (F.mapId (canonicalSourceObject Y)).hom
  let s := generalLiftForwardSlidingSource F hF f
    (𝟙 (MonoidalSingleObj.star (Type)))
  let adj := ((Pseudofunctor.id E).mapAdjunction
    (generalLiftSourceEquivalence F hF f).toAdjunction)
  have hforward :
      s.hom ≫ (p ▷ l) ≫ (λ_ l).hom =
        (l ◁ q) ≫ (ρ_ l).hom := by
    exact generalLiftForwardSlidingSource_unit F hF f
  have hsquare :
      (p ▷ l) ≫ ((λ_ l).hom ≫ (ρ_ l).inv) =
        s.inv ≫ (l ◁ q) := by
    rw [← cancel_epi s.hom]
    slice_lhs 1 3 => rw [hforward]
    simp
  have hmate := Bicategory.mateEquiv_sliding adj adj
    p ((λ_ l).hom ≫ (ρ_ l).inv) s.inv q hsquare
  have hmate' :
      (r ◁ p) ≫ mateEquiv adj adj
          ((λ_ l).hom ≫ (ρ_ l).inv) =
        mateEquiv adj adj s.inv ≫ (q ▷ r) := by
    exact hmate
  have hunit :
      mateEquiv adj adj ((λ_ l).hom ≫ (ρ_ l).inv) =
        (ρ_ r).hom ≫ (λ_ r).inv := by
    exact Bicategory.mateEquiv_leftUnitor_hom_rightUnitor_inv adj
  rw [generalLiftInverseSlidingSource_hom F hF f]
  change mateEquiv adj adj s.inv ≫ (q ▷ r) ≫ (λ_ r).hom =
    (r ◁ p) ≫ (ρ_ r).hom
  slice_lhs 1 2 => rw [← hmate']
  rw [hunit]
  simp

/-- Whiskering an inverse-sliding left-unit chain on the right and
reassociating gives the left-unit chain for the composite. -/
private theorem inverseSliding_leftUnitChain
    {a b : E} {i : a ⟶ a} {j : b ⟶ b}
    (r : b ⟶ a) (s : r ≫ i ⟶ j ≫ r)
    (p : i ⟶ 𝟙 a) (q : j ⟶ 𝟙 b)
    (h : s ≫ (q ▷ r) ≫ (λ_ r).hom =
      (r ◁ p) ≫ (ρ_ r).hom)
    (t : a ⟶ a) :
    (α_ r i t).inv ≫ (s ▷ t) ≫
        (α_ j r t).hom ≫ (q ▷ (r ≫ t)) ≫
        (λ_ (r ≫ t)).hom =
      (r ◁ (p ▷ t)) ≫ (r ◁ (λ_ t).hom) := by
  have h' := congrArg (fun η => η ▷ t) h
  simp only [comp_whiskerRight] at h'
  calc
    _ = (α_ r i t).inv ≫
        ((s ▷ t) ≫ ((q ▷ r) ▷ t) ≫
          ((λ_ r).hom ▷ t)) := by bicategory
    _ = (α_ r i t).inv ≫
        (((r ◁ p) ▷ t) ≫ ((ρ_ r).hom ▷ t)) := by
      rw [h']
    _ = _ := by bicategory

set_option backward.isDefEq.respectTransparency false in
/-- The retained/inverse compositor and canonical unit tail satisfy the
left-unit law before the target identity is normalized to a strict one. -/
theorem generalLiftMapCompRetainedInverse_leftUnitor
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
        ((canonicalRetainedInverseCompositionComparison f
            (𝟙 (MonoidalSingleObj.star (Type))) A).hom ≫
          canonicalInverseTwoCell f
            (MonoidalCategory.leftUnitor A).hom) =
      (generalLiftMapCompRetainedInverse F hF f hf
          (𝟙 (MonoidalSingleObj.star (Type))) A).hom ≫
        (generalLiftForwardMapIdTail F hF Y).hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A) ≫
        (λ_ ((generalLiftPrelaxFunctor F hF).map
          (canonicalInverseHom f A))).hom := by
  rw [generalLiftMapCompRetainedInverse_hom F hF f hf]
  rw [(generalLiftPrelaxFunctor F hF).map₂_comp]
  rw [Category.assoc]
  rw [cancel_epi ((generalLiftPrelaxFunctor F hF).map₂
    (canonicalRetainedInverseCompositionComparison f
      (𝟙 (MonoidalSingleObj.star (Type))) A).hom)]
  rw [generalLiftRetainedInverseMapCompTransport_hom F hF f hf,
    generalLiftInverseRetainedMapCompCore_hom F hF f hf,
    generalLiftRetainedInverseMapCompSliding_hom,
    generalLiftRetainedInverseMapCompFactors_hom F hF f hf]
  simp only [generalLiftForwardMapCompSource,
    generalLiftForwardMapIdTail, Iso.trans_hom,
    PrelaxFunctor.map₂Iso_hom]
  let e := eqToIso
    (generalLiftPrelaxFunctor_map_inverse F hF f hf A)
  have : IsIso e.hom := e.isIso_hom
  have : Mono e.hom := IsIso.mono_of_iso e.hom
  rw [← cancel_mono e.hom]
  change
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f
            (MonoidalCategory.leftUnitor A).hom) ≫
        eqToHom (generalLiftPrelaxFunctor_map_inverse F hF f hf A) = _
  rw [generalLiftMap₂InverseTransport F hF f hf]
  simp only [Category.assoc, comp_whiskerRight]
  let ei := eqToIso
    (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y)
      (𝟙 (MonoidalSingleObj.star (Type))))
  let ec := eqToIso
    (generalLiftPrelaxFunctor_map_inverse F hF f hf
      ((𝟙 (MonoidalSingleObj.star (Type))) × A))
  have : IsIso ec.hom := ec.isIso_hom
  have : Epi ec.hom := IsIso.epi_of_iso ec.hom
  change ec.hom ≫ _ = ec.hom ≫ _
  rw [cancel_epi ec.hom]
  change
    (generalLiftSourceEquivalence F hF f).inv ◁
        F.map₂ (canonicalSourceTwoCell (𝟙 X)
          (MonoidalCategory.leftUnitor A).hom) =
      ((generalLiftSourceEquivalence F hF f).inv ◁
          (F.map₂ (canonicalSourceCompositionComparison
              (𝟙 X) (𝟙 X)
              (𝟙 (MonoidalSingleObj.star (Type))) A).symm.hom ≫
            (F.mapComp
              (canonicalSourceHom (𝟙 X)
                (𝟙 (MonoidalSingleObj.star (Type))))
              (canonicalSourceHom (𝟙 X) A)).hom)) ≫
        (α_ (generalLiftSourceEquivalence F hF f).inv
          (F.map (canonicalSourceHom (𝟙 X)
            (𝟙 (MonoidalSingleObj.star (Type)))))
          (F.map (canonicalSourceHom (𝟙 X) A))).inv ≫
        ((generalLiftInverseSlidingSource F hF f
            (𝟙 (MonoidalSingleObj.star (Type)))).hom ▷
          F.map (canonicalSourceHom (𝟙 X) A)) ≫
        (α_ (F.map (canonicalSourceHom (𝟙 Y)
            (𝟙 (MonoidalSingleObj.star (Type)))))
          (generalLiftSourceEquivalence F hF f).inv
          (F.map (canonicalSourceHom (𝟙 X) A))).hom ≫
        (ei.inv ▷ ((generalLiftSourceEquivalence F hF f).inv ≫
          F.map (canonicalSourceHom (𝟙 X) A))) ≫
        ((generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom (𝟙 Y)
              (𝟙 (MonoidalSingleObj.star (Type)))) ◁ e.inv) ≫
        (ei.hom ▷ (generalLiftPrelaxFunctor F hF).map
          (canonicalInverseHom f A)) ≫
        (F.map₂ (canonicalSourceIdentityComparison Y).hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A)) ≫
        ((F.mapId (canonicalSourceObject Y)).hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A)) ≫
        (λ_ ((generalLiftPrelaxFunctor F hF).map
          (canonicalInverseHom f A))).hom ≫ e.hom
  rw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
  rw [Category.assoc]
  rw [transportLeftUnitorThroughIsos
    ei e
    (F.map₂ (canonicalSourceIdentityComparison Y).hom ≫
      (F.mapId (canonicalSourceObject Y)).hom)]
  rw [inverseSliding_leftUnitChain
    (generalLiftSourceEquivalence F hF f).inv
    (generalLiftInverseSlidingSource F hF f
      (𝟙 (MonoidalSingleObj.star (Type)))).hom
    (F.map₂ (canonicalSourceIdentityComparison X).hom ≫
      (F.mapId (canonicalSourceObject X)).hom)
    (F.map₂ (canonicalSourceIdentityComparison Y).hom ≫
      (F.mapId (canonicalSourceObject Y)).hom)
    (generalLiftInverseSlidingSource_unit F hF f)
    (F.map (canonicalSourceHom (𝟙 X) A))]
  rw [← whiskerLeft_comp, ← whiskerLeft_comp]
  simp only [Category.assoc]
  rw [generalLiftSourceLeftUnitor_afterCompositionComparison
    (F := F) (f := 𝟙 X) (A := A)]

set_option backward.isDefEq.respectTransparency false in
/-- The explicit forward compositor and the canonical unit tail satisfy the
left-unit law before the canonical forward identity is normalized to the
strict target identity. -/
theorem generalLiftMapCompForward_leftUnitor
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
        ((canonicalForwardCompositionComparison
            (𝟙 X) f (𝟙 (MonoidalSingleObj.star (Type))) A).hom ≫
          canonicalForwardTwoCell f
            (MonoidalCategory.leftUnitor A).hom) =
      (generalLiftMapCompForward F hF
          (𝟙 X) f (𝟙 (MonoidalSingleObj.star (Type))) A).hom ≫
        (generalLiftForwardMapIdTail F hF X).hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A) ≫
        (λ_ ((generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom f A))).hom := by
  rw [generalLiftMapCompForward_hom]
  rw [(generalLiftPrelaxFunctor F hF).map₂_comp]
  rw [Category.assoc]
  rw [cancel_epi ((generalLiftPrelaxFunctor F hF).map₂
    (canonicalForwardCompositionComparison
      (𝟙 X) f (𝟙 (MonoidalSingleObj.star (Type))) A).hom)]
  rw [generalLiftForwardMapCompTransport_hom,
    generalLiftForwardMapCompCore_hom,
    generalLiftForwardMapCompFactors_hom]
  simp only [generalLiftForwardMapCompSource,
    generalLiftForwardMapIdTail, Iso.trans_hom,
    PrelaxFunctor.map₂Iso_hom]
  let e := eqToIso
    (generalLiftPrelaxFunctor_map_forward F hF f A)
  have : IsIso e.hom := e.isIso_hom
  have : Mono e.hom := IsIso.mono_of_iso e.hom
  rw [← cancel_mono e.hom]
  change
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell f
            (MonoidalCategory.leftUnitor A).hom) ≫
        eqToHom (generalLiftPrelaxFunctor_map_forward F hF f A) = _
  rw [generalLiftMap₂ForwardTransport]
  simp only [Category.assoc, comp_whiskerRight]
  let ei := eqToIso
    (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X)
      (𝟙 (MonoidalSingleObj.star (Type))))
  change _ =
    eqToHom (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X ≫ f)
          ((𝟙 (MonoidalSingleObj.star (Type))) × A)) ≫
      F.map₂ (canonicalSourceCompositionComparison
        (𝟙 X) f (𝟙 (MonoidalSingleObj.star (Type))) A).symm.hom ≫
      (F.mapComp
        (canonicalSourceHom (𝟙 X)
          (𝟙 (MonoidalSingleObj.star (Type))))
        (canonicalSourceHom f A)).hom ≫
      (ei.inv ▷ F.map (canonicalSourceHom f A)) ≫
      ((generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom (𝟙 X)
          (𝟙 (MonoidalSingleObj.star (Type)))) ◁ e.inv) ≫
      (ei.hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A)) ≫
      (F.map₂ (canonicalSourceIdentityComparison X).hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A)) ≫
      ((F.mapId (canonicalSourceObject X)).hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A)) ≫
      (λ_ ((generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom f A))).hom ≫ e.hom
  rw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
  rw [Category.assoc]
  slice_rhs 4 9 =>
    rw [transportLeftUnitorThroughIsos
      ei e
      (F.map₂ (canonicalSourceIdentityComparison X).hom ≫
        (F.mapId (canonicalSourceObject X)).hom)]
  let ec := eqToIso
    (generalLiftPrelaxFunctor_map_forward F hF f
      ((𝟙 (MonoidalSingleObj.star (Type))) × A))
  have : IsIso ec.hom := ec.isIso_hom
  have : Epi ec.hom := IsIso.epi_of_iso ec.hom
  change ec.hom ≫ _ = ec.hom ≫ _
  rw [cancel_epi ec.hom]
  exact (generalLiftSourceLeftUnitor_afterCompositionComparison
    (F := F) (f := f) (A := A)).symm

/-- Transporting both factors of a right-unit chain through isomorphisms and
then transporting the result is the same as applying the transported unit
2-cell directly. -/
private theorem transportRightUnitorThroughIsos
    {a b : E} {f f' : a ⟶ b} {i i' : b ⟶ b}
    (ef : f ≅ f') (ei : i ≅ i') (α : i' ⟶ 𝟙 b) :
    (ef.inv ▷ i') ≫ (f ◁ ei.inv) ≫
        (f ◁ (ei.hom ≫ α)) ≫ (ρ_ f).hom ≫ ef.hom =
      (f' ◁ α) ≫ (ρ_ f').hom := by
  simp only [whiskerLeft_comp, Category.assoc]
  slice_lhs 2 3 => simp
  simp only [Category.id_comp, Category.assoc]
  rw [← whisker_exchange_assoc ef.inv α]
  rw [rightUnitor_naturality_assoc]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The explicit forward compositor and the canonical unit tail satisfy the
right-unit law before the canonical forward identity is normalized to the
strict target identity. -/
theorem generalLiftMapCompForward_rightUnitor
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
        ((canonicalForwardCompositionComparison
            f (𝟙 Y) A (𝟙 (MonoidalSingleObj.star (Type)))).hom ≫
          canonicalForwardTwoCell f
            (MonoidalCategory.rightUnitor A).hom) =
      (generalLiftMapCompForward F hF
          f (𝟙 Y) A (𝟙 (MonoidalSingleObj.star (Type)))).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A) ◁
          (generalLiftForwardMapIdTail F hF Y).hom ≫
        (ρ_ ((generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom f A))).hom := by
  rw [generalLiftMapCompForward_hom]
  rw [(generalLiftPrelaxFunctor F hF).map₂_comp]
  rw [Category.assoc]
  rw [cancel_epi ((generalLiftPrelaxFunctor F hF).map₂
    (canonicalForwardCompositionComparison
      f (𝟙 Y) A (𝟙 (MonoidalSingleObj.star (Type)))).hom)]
  rw [generalLiftForwardMapCompTransport_hom,
    generalLiftForwardMapCompCore_hom,
    generalLiftForwardMapCompFactors_hom]
  simp only [generalLiftForwardMapCompSource,
    generalLiftForwardMapIdTail, Iso.trans_hom,
    PrelaxFunctor.map₂Iso_hom]
  let e := eqToIso
    (generalLiftPrelaxFunctor_map_forward F hF f A)
  have : IsIso e.hom := e.isIso_hom
  have : Mono e.hom := IsIso.mono_of_iso e.hom
  rw [← cancel_mono e.hom]
  change
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardTwoCell f
            (MonoidalCategory.rightUnitor A).hom) ≫
        eqToHom (generalLiftPrelaxFunctor_map_forward F hF f A) = _
  rw [generalLiftMap₂ForwardTransport]
  simp only [Category.assoc, whiskerLeft_comp]
  let ei := eqToIso
    (generalLiftPrelaxFunctor_map_forward F hF (𝟙 Y)
      (𝟙 (MonoidalSingleObj.star (Type))))
  change _ =
    eqToHom (generalLiftPrelaxFunctor_map_forward F hF (f ≫ 𝟙 Y)
          (A × (𝟙 (MonoidalSingleObj.star (Type))))) ≫
      F.map₂ (canonicalSourceCompositionComparison
        f (𝟙 Y) A (𝟙 (MonoidalSingleObj.star (Type)))).symm.hom ≫
      (F.mapComp
        (canonicalSourceHom f A)
        (canonicalSourceHom (𝟙 Y)
          (𝟙 (MonoidalSingleObj.star (Type))))).hom ≫
      (e.inv ▷ F.map (canonicalSourceHom (𝟙 Y)
        (𝟙 (MonoidalSingleObj.star (Type))))) ≫
      ((generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom f A) ◁ ei.inv) ≫
      ((generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom f A) ◁ ei.hom) ≫
      ((generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom f A) ◁
          F.map₂ (canonicalSourceIdentityComparison Y).hom) ≫
      ((generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom f A) ◁
          (F.mapId (canonicalSourceObject Y)).hom) ≫
      (ρ_ ((generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom f A))).hom ≫ e.hom
  slice_rhs 6 8 =>
    rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp]
  rw [Category.assoc]
  slice_rhs 4 9 =>
    rw [transportRightUnitorThroughIsos
      e ei
      (F.map₂ (canonicalSourceIdentityComparison Y).hom ≫
        (F.mapId (canonicalSourceObject Y)).hom)]
  let ec := eqToIso
    (generalLiftPrelaxFunctor_map_forward F hF (f ≫ 𝟙 Y)
      (A × (𝟙 (MonoidalSingleObj.star (Type)))))
  have : IsIso ec.hom := ec.isIso_hom
  have : Epi ec.hom := IsIso.epi_of_iso ec.hom
  change ec.hom ≫ _ = ec.hom ≫ _
  rw [cancel_epi ec.hom]
  exact (generalLiftSourceRightUnitor_afterCompositionComparison
    (F := F) (f := f) (A := A)).symm

/-- On a canonical forward identity followed by a canonical forward arrow,
the all-arrow compositor selects the explicit forward/forward branch. -/
theorem generalLiftMapComp_forwardIdentity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    generalLiftMapComp F hF
        (canonicalForwardHom (𝟙 X)
          (𝟙 (MonoidalSingleObj.star (Type))))
        (canonicalForwardHom f A) =
      generalLiftMapCompForward F hF
        (𝟙 X) f (𝟙 (MonoidalSingleObj.star (Type))) A := by
  have hX : X = 0 ∨ X = 1 := by fin_cases X <;> simp
  have hY : Y = 0 ∨ Y = 1 := by fin_cases Y <;> simp
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
  · have hf : f = 𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow) :=
      Subsingleton.elim _ _
    subst f
    have he := generalLiftMapComp_endpoint F hF 0 0 0
      (𝟙 (MonoidalSingleObj.star (Type))) A
    exact he.trans
      (generalLiftEndpointMapComp_zero_zero_zero F hF _ _)
  · have hf : f = Ript.Examples.WalkingLocalization.arrow :=
      Subsingleton.elim _ _
    subst f
    have he := generalLiftMapComp_endpoint F hF 0 0 1
      (𝟙 (MonoidalSingleObj.star (Type))) A
    exact he.trans
      (generalLiftEndpointMapComp_zero_zero_one F hF _ _)
  · exact False.elim ((by omega : ¬ (1 : Fin 2) ≤ 0) f.le)
  · have hf : f = 𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow) :=
      Subsingleton.elim _ _
    subst f
    have he := generalLiftMapComp_endpoint F hF 1 1 1
      (𝟙 (MonoidalSingleObj.star (Type))) A
    exact he.trans
      (generalLiftEndpointMapComp_one_one_one F hF _ _)

/-- On a canonical forward identity followed by a genuine canonical inverse,
the all-arrow compositor selects the retained/inverse branch. -/
theorem generalLiftMapComp_inverseLeftIdentity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type) :
    generalLiftMapComp F hF
        (canonicalForwardHom (𝟙 Y)
          (𝟙 (MonoidalSingleObj.star (Type))))
        (canonicalInverseHom f A) =
      generalLiftMapCompRetainedInverse F hF f hf
        (𝟙 (MonoidalSingleObj.star (Type))) A := by
  have hX : X = 0 ∨ X = 1 := by fin_cases X <;> simp
  have hY : Y = 0 ∨ Y = 1 := by fin_cases Y <;> simp
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
  · exact False.elim (hf le_rfl)
  · have hf' : f = Ript.Examples.WalkingLocalization.arrow :=
      Subsingleton.elim _ _
    subst f
    cases canonicalEndpointHom_eq_forward
      (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow))
      (𝟙 (MonoidalSingleObj.star (Type)))
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow A
    have he := generalLiftMapComp_endpoint F hF 1 1 0
      (𝟙 (MonoidalSingleObj.star (Type))) A
    exact he.trans
      (generalLiftEndpointMapComp_one_one_zero F hF _ _)
  · exact False.elim ((by omega : ¬ (1 : Fin 2) ≤ 0) f.le)
  · exact False.elim (hf le_rfl)

/-- On a canonical forward arrow followed by its canonical forward identity,
the all-arrow compositor selects the explicit forward/forward branch. -/
theorem generalLiftMapComp_rightIdentity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    generalLiftMapComp F hF
        (canonicalForwardHom f A)
        (canonicalForwardHom (𝟙 Y)
          (𝟙 (MonoidalSingleObj.star (Type)))) =
      generalLiftMapCompForward F hF
        f (𝟙 Y) A (𝟙 (MonoidalSingleObj.star (Type))) := by
  have hX : X = 0 ∨ X = 1 := by fin_cases X <;> simp
  have hY : Y = 0 ∨ Y = 1 := by fin_cases Y <;> simp
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
  · have hf : f = 𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow) :=
      Subsingleton.elim _ _
    subst f
    have he := generalLiftMapComp_endpoint F hF 0 0 0
      A (𝟙 (MonoidalSingleObj.star (Type)))
    exact he.trans
      (generalLiftEndpointMapComp_zero_zero_zero F hF _ _)
  · have hf : f = Ript.Examples.WalkingLocalization.arrow :=
      Subsingleton.elim _ _
    subst f
    have he := generalLiftMapComp_endpoint F hF 0 1 1
      A (𝟙 (MonoidalSingleObj.star (Type)))
    exact he.trans
      (generalLiftEndpointMapComp_zero_one_one F hF _ _)
  · exact False.elim ((by omega : ¬ (1 : Fin 2) ≤ 0) f.le)
  · have hf : f = 𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow) :=
      Subsingleton.elim _ _
    subst f
    have he := generalLiftMapComp_endpoint F hF 1 1 1
      A (𝟙 (MonoidalSingleObj.star (Type)))
    exact he.trans
      (generalLiftEndpointMapComp_one_one_one F hF _ _)

set_option backward.isDefEq.respectTransparency false in
private theorem generalLiftLeftUnitor_forward_of_mapCompForward
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type)
    (hcomp :
      generalLiftMapComp F hF
          (canonicalForwardHom (𝟙 X)
            (𝟙 (MonoidalSingleObj.star (Type))))
          (canonicalForwardHom f A) =
        generalLiftMapCompForward F hF
          (𝟙 X) f (𝟙 (MonoidalSingleObj.star (Type))) A) :
    (generalLiftPrelaxFunctor F hF).map₂
        (λ_ (canonicalForwardHom f A)).hom =
      (generalLiftMapComp F hF (𝟙 (canonicalTargetObject X))
          (canonicalForwardHom f A)).hom ≫
        (generalLiftMapId F hF (canonicalTargetObject X)).hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A) ≫
        (λ_ ((generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom f A))).hom := by
  let e := (generalLiftPrelaxFunctor F hF).map₂Iso
    (whiskerRightIso (canonicalForwardIdentityComparison X)
      (canonicalForwardHom f A))
  have : IsIso e.hom := e.isIso_hom
  have : Epi e.hom := IsIso.epi_of_iso e.hom
  rw [← cancel_epi e.hom]
  change
    (generalLiftPrelaxFunctor F hF).map₂
          ((canonicalForwardIdentityComparison X).hom ▷
            canonicalForwardHom f A) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (λ_ (canonicalForwardHom f A)).hom =
      (generalLiftPrelaxFunctor F hF).map₂
          ((canonicalForwardIdentityComparison X).hom ▷
            canonicalForwardHom f A) ≫ _
  rw [← (generalLiftPrelaxFunctor F hF).map₂_comp]
  rw [← canonicalForwardLeftUnitorFactorization]
  rw [generalLiftMapCompForward_leftUnitor F hF f A]
  slice_rhs 1 2 =>
    rw [generalLiftMapComp_naturality_left F hF
      (canonicalForwardIdentityComparison X).hom
      (canonicalForwardHom f A)]
  rw [generalLiftMapId_canonical]
  simp only [generalLiftCanonicalMapId, Iso.trans_hom,
    PrelaxFunctor.map₂Iso_hom, comp_whiskerRight]
  slice_rhs 2 3 =>
    rw [← comp_whiskerRight,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp]
    simp only [Iso.symm_hom, Iso.hom_inv_id]
    rw [(generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  simp only [Category.id_comp]
  slice_rhs 2 4 =>
    rw [← comp_whiskerRight, ← comp_whiskerRight]
  change _ =
    (generalLiftMapComp F hF
        (canonicalForwardHom (𝟙 X)
          (𝟙 (MonoidalSingleObj.star (Type))))
        (canonicalForwardHom f A)).hom ≫
      (generalLiftForwardMapIdTail F hF X).hom ▷
        (generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom f A) ≫
      (λ_ ((generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom f A))).hom
  rw [hcomp]

/-- The arbitrary lift satisfies oplax left-unit coherence on every
canonical forward target arrow. -/
theorem generalLiftLeftUnitor_forward
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
        (λ_ (canonicalForwardHom f A)).hom =
      (generalLiftMapComp F hF (𝟙 (canonicalTargetObject X))
          (canonicalForwardHom f A)).hom ≫
        (generalLiftMapId F hF (canonicalTargetObject X)).hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A) ≫
        (λ_ ((generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom f A))).hom :=
  generalLiftLeftUnitor_forward_of_mapCompForward F hF f A
    (generalLiftMapComp_forwardIdentity F hF f A)

set_option backward.isDefEq.respectTransparency false in
private theorem generalLiftLeftUnitor_inverse_of_mapCompRetainedInverse
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type)
    (hcomp :
      generalLiftMapComp F hF
          (canonicalForwardHom (𝟙 Y)
            (𝟙 (MonoidalSingleObj.star (Type))))
          (canonicalInverseHom f A) =
        generalLiftMapCompRetainedInverse F hF f hf
          (𝟙 (MonoidalSingleObj.star (Type))) A) :
    (generalLiftPrelaxFunctor F hF).map₂
        (λ_ (canonicalInverseHom f A)).hom =
      (generalLiftMapComp F hF (𝟙 (canonicalTargetObject Y))
          (canonicalInverseHom f A)).hom ≫
        (generalLiftMapId F hF (canonicalTargetObject Y)).hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A) ≫
        (λ_ ((generalLiftPrelaxFunctor F hF).map
          (canonicalInverseHom f A))).hom := by
  let e := (generalLiftPrelaxFunctor F hF).map₂Iso
    (whiskerRightIso (canonicalForwardIdentityComparison Y)
      (canonicalInverseHom f A))
  have : IsIso e.hom := e.isIso_hom
  have : Epi e.hom := IsIso.epi_of_iso e.hom
  rw [← cancel_epi e.hom]
  change
    (generalLiftPrelaxFunctor F hF).map₂
          ((canonicalForwardIdentityComparison Y).hom ▷
            canonicalInverseHom f A) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (λ_ (canonicalInverseHom f A)).hom =
      (generalLiftPrelaxFunctor F hF).map₂
          ((canonicalForwardIdentityComparison Y).hom ▷
            canonicalInverseHom f A) ≫ _
  rw [← (generalLiftPrelaxFunctor F hF).map₂_comp]
  rw [← canonicalInverseLeftUnitorFactorization]
  rw [generalLiftMapCompRetainedInverse_leftUnitor F hF f hf A]
  slice_rhs 1 2 =>
    rw [generalLiftMapComp_naturality_left F hF
      (canonicalForwardIdentityComparison Y).hom
      (canonicalInverseHom f A)]
  rw [generalLiftMapId_canonical]
  simp only [generalLiftCanonicalMapId, Iso.trans_hom,
    PrelaxFunctor.map₂Iso_hom, comp_whiskerRight]
  slice_rhs 2 3 =>
    rw [← comp_whiskerRight,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp]
    simp only [Iso.symm_hom, Iso.hom_inv_id]
    rw [(generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  simp only [Category.id_comp]
  slice_rhs 2 4 =>
    rw [← comp_whiskerRight, ← comp_whiskerRight]
  change _ =
    (generalLiftMapComp F hF
        (canonicalForwardHom (𝟙 Y)
          (𝟙 (MonoidalSingleObj.star (Type))))
        (canonicalInverseHom f A)).hom ≫
      (generalLiftForwardMapIdTail F hF Y).hom ▷
        (generalLiftPrelaxFunctor F hF).map
          (canonicalInverseHom f A) ≫
      (λ_ ((generalLiftPrelaxFunctor F hF).map
        (canonicalInverseHom f A))).hom
  rw [hcomp]

/-- The arbitrary lift satisfies oplax left-unit coherence on every genuine
canonical inverse target arrow. -/
theorem generalLiftLeftUnitor_inverse
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
        (λ_ (canonicalInverseHom f A)).hom =
      (generalLiftMapComp F hF (𝟙 (canonicalTargetObject Y))
          (canonicalInverseHom f A)).hom ≫
        (generalLiftMapId F hF (canonicalTargetObject Y)).hom ▷
          (generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A) ≫
        (λ_ ((generalLiftPrelaxFunctor F hF).map
          (canonicalInverseHom f A))).hom :=
  generalLiftLeftUnitor_inverse_of_mapCompRetainedInverse
    F hF f hf A
      (generalLiftMapComp_inverseLeftIdentity F hF f hf A)

private theorem generalLiftLeftUnitor_canonicalObjects
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : canonicalTargetObject X ⟶ canonicalTargetObject Y) :
    (generalLiftPrelaxFunctor F hF).map₂ (λ_ f).hom =
      (generalLiftMapComp F hF (𝟙 (canonicalTargetObject X)) f).hom ≫
        (generalLiftMapId F hF (canonicalTargetObject X)).hom ▷
          (generalLiftPrelaxFunctor F hF).map f ≫
        (λ_ ((generalLiftPrelaxFunctor F hF).map f)).hom := by
  rcases f with ⟨⟨f⟩, A⟩
  have hf : f = canonicalCompletionHom X Y :=
    completion_hom_eq_canonical f
  cases hf
  rcases (by fin_cases X <;> simp : X = 0 ∨ X = 1) with rfl | rfl <;>
    rcases (by fin_cases Y <;> simp : Y = 0 ∨ Y = 1) with rfl | rfl
  · cases canonicalEndpointHom_eq_forward
      (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) A
    exact generalLiftLeftUnitor_forward F hF (𝟙 0) A
  · cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow A
    exact generalLiftLeftUnitor_forward F hF
      Ript.Examples.WalkingLocalization.arrow A
  · cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow A
    exact generalLiftLeftUnitor_inverse F hF
      Ript.Examples.WalkingLocalization.arrow (by decide) A
  · cases canonicalEndpointHom_eq_forward
      (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) A
    exact generalLiftLeftUnitor_forward F hF (𝟙 1) A

/-- The arbitrary lift satisfies the oplax left-unit law for every target
1-morphism. -/
theorem generalLiftLeftUnitor
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Target} (f : X ⟶ Y) :
    (generalLiftPrelaxFunctor F hF).map₂ (λ_ f).hom =
      (generalLiftMapComp F hF (𝟙 X) f).hom ≫
        (generalLiftMapId F hF X).hom ▷
          (generalLiftPrelaxFunctor F hF).map f ≫
        (λ_ ((generalLiftPrelaxFunctor F hF).map f)).hom := by
  rcases X with ⟨⟨X⟩, X'⟩
  rcases Y with ⟨⟨Y⟩, Y'⟩
  cases X'
  cases Y'
  exact generalLiftLeftUnitor_canonicalObjects F hF f

set_option backward.isDefEq.respectTransparency false in
private theorem generalLiftRightUnitor_forward_of_mapCompForward
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type)
    (hcomp :
      generalLiftMapComp F hF
          (canonicalForwardHom f A)
          (canonicalForwardHom (𝟙 Y)
            (𝟙 (MonoidalSingleObj.star (Type)))) =
        generalLiftMapCompForward F hF
          f (𝟙 Y) A (𝟙 (MonoidalSingleObj.star (Type)))) :
    (generalLiftPrelaxFunctor F hF).map₂
        (ρ_ (canonicalForwardHom f A)).hom =
      (generalLiftMapComp F hF (canonicalForwardHom f A)
          (𝟙 (canonicalTargetObject Y))).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A) ◁
          (generalLiftMapId F hF (canonicalTargetObject Y)).hom ≫
        (ρ_ ((generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom f A))).hom := by
  let e := (generalLiftPrelaxFunctor F hF).map₂Iso
    (whiskerLeftIso (canonicalForwardHom f A)
      (canonicalForwardIdentityComparison Y))
  have : IsIso e.hom := e.isIso_hom
  have : Epi e.hom := IsIso.epi_of_iso e.hom
  rw [← cancel_epi e.hom]
  change
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardHom f A ◁
            (canonicalForwardIdentityComparison Y).hom) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (ρ_ (canonicalForwardHom f A)).hom =
      (generalLiftPrelaxFunctor F hF).map₂
          (canonicalForwardHom f A ◁
            (canonicalForwardIdentityComparison Y).hom) ≫ _
  rw [← (generalLiftPrelaxFunctor F hF).map₂_comp]
  rw [← canonicalForwardRightUnitorFactorization]
  rw [generalLiftMapCompForward_rightUnitor F hF f A]
  slice_rhs 1 2 =>
    rw [generalLiftMapComp_naturality_right F hF
      (canonicalForwardHom f A)
      (canonicalForwardIdentityComparison Y).hom]
  rw [generalLiftMapId_canonical]
  simp only [generalLiftCanonicalMapId, Iso.trans_hom,
    PrelaxFunctor.map₂Iso_hom, whiskerLeft_comp]
  slice_rhs 2 3 =>
    rw [← whiskerLeft_comp,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp]
    simp only [Iso.symm_hom, Iso.hom_inv_id]
    rw [(generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  simp only [Category.id_comp]
  slice_rhs 2 4 =>
    rw [← whiskerLeft_comp, ← whiskerLeft_comp]
  change _ =
    (generalLiftMapComp F hF
        (canonicalForwardHom f A)
        (canonicalForwardHom (𝟙 Y)
          (𝟙 (MonoidalSingleObj.star (Type))))).hom ≫
      (generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom f A) ◁
        (generalLiftForwardMapIdTail F hF Y).hom ≫
      (ρ_ ((generalLiftPrelaxFunctor F hF).map
        (canonicalForwardHom f A))).hom
  rw [hcomp]

/-- The arbitrary lift satisfies oplax right-unit coherence on every
canonical forward target arrow. -/
theorem generalLiftRightUnitor_forward
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (A : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
        (ρ_ (canonicalForwardHom f A)).hom =
      (generalLiftMapComp F hF (canonicalForwardHom f A)
          (𝟙 (canonicalTargetObject Y))).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalForwardHom f A) ◁
          (generalLiftMapId F hF (canonicalTargetObject Y)).hom ≫
        (ρ_ ((generalLiftPrelaxFunctor F hF).map
          (canonicalForwardHom f A))).hom :=
  generalLiftRightUnitor_forward_of_mapCompForward F hF f A
    (generalLiftMapComp_rightIdentity F hF f A)

/-- Whiskering a source right-unit chain on the left and reassociating gives
the right-unit chain for the composite. -/
private theorem whiskerLeft_rightUnitChain
    {a b : E} (r : b ⟶ a) {q₀ q i : a ⟶ a}
    (μ : q₀ ⟶ q ≫ i) (α : i ⟶ 𝟙 a) (η : q₀ ⟶ q)
    (h : μ ≫ (q ◁ α) ≫ (ρ_ q).hom = η) :
    (r ◁ μ) ≫ (α_ r q i).inv ≫
        ((r ≫ q) ◁ α) ≫ (ρ_ (r ≫ q)).hom =
      r ◁ η := by
  rw [← h]
  simp only [whiskerLeft_comp]
  rw [whiskerLeft_rightUnitor]
  bicategory

set_option backward.isDefEq.respectTransparency false in
/-- The inverse/retained compositor and the canonical unit tail satisfy the
right-unit law before the target identity is normalized to a strict one. -/
theorem generalLiftMapCompInverseRetained_rightUnitor
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
        ((canonicalInverseRetainedCompositionComparison f A
            (𝟙 (MonoidalSingleObj.star (Type)))).hom ≫
          canonicalInverseTwoCell f
            (MonoidalCategory.rightUnitor A).hom) =
      (generalLiftMapCompInverseRetained F hF f hf A
          (𝟙 (MonoidalSingleObj.star (Type)))).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A) ◁
          (generalLiftForwardMapIdTail F hF X).hom ≫
        (ρ_ ((generalLiftPrelaxFunctor F hF).map
          (canonicalInverseHom f A))).hom := by
  rw [generalLiftMapCompInverseRetained_hom F hF f hf]
  rw [(generalLiftPrelaxFunctor F hF).map₂_comp]
  rw [Category.assoc]
  rw [cancel_epi ((generalLiftPrelaxFunctor F hF).map₂
    (canonicalInverseRetainedCompositionComparison f A
      (𝟙 (MonoidalSingleObj.star (Type)))).hom)]
  rw [generalLiftInverseRetainedMapCompTransport_hom F hF f hf,
    generalLiftInverseRetainedMapCompCore_hom F hF f hf,
    generalLiftInverseRetainedMapCompFactors_hom F hF f hf]
  simp only [generalLiftForwardMapCompSource,
    generalLiftForwardMapIdTail, Iso.trans_hom,
    PrelaxFunctor.map₂Iso_hom]
  let e := eqToIso
    (generalLiftPrelaxFunctor_map_inverse F hF f hf A)
  have : IsIso e.hom := e.isIso_hom
  have : Mono e.hom := IsIso.mono_of_iso e.hom
  rw [← cancel_mono e.hom]
  change
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseTwoCell f
            (MonoidalCategory.rightUnitor A).hom) ≫
        eqToHom (generalLiftPrelaxFunctor_map_inverse F hF f hf A) = _
  rw [generalLiftMap₂InverseTransport F hF f hf]
  simp only [Category.assoc, whiskerLeft_comp]
  let ei := eqToIso
    (generalLiftPrelaxFunctor_map_forward F hF (𝟙 X)
      (𝟙 (MonoidalSingleObj.star (Type))))
  change _ =
    eqToHom (generalLiftPrelaxFunctor_map_inverse F hF f hf
          (A × (𝟙 (MonoidalSingleObj.star (Type))))) ≫
      ((generalLiftSourceEquivalence F hF f).inv ◁
        F.map₂ (canonicalSourceCompositionComparison
          (𝟙 X) (𝟙 X) A
          (𝟙 (MonoidalSingleObj.star (Type)))).symm.hom) ≫
      ((generalLiftSourceEquivalence F hF f).inv ◁
        (F.mapComp
          (canonicalSourceHom (𝟙 X) A)
          (canonicalSourceHom (𝟙 X)
            (𝟙 (MonoidalSingleObj.star (Type))))).hom) ≫
      (α_ (generalLiftSourceEquivalence F hF f).inv
        (F.map (canonicalSourceHom (𝟙 X) A))
        (F.map (canonicalSourceHom (𝟙 X)
          (𝟙 (MonoidalSingleObj.star (Type)))))).inv ≫
      (e.inv ▷ F.map (canonicalSourceHom (𝟙 X)
        (𝟙 (MonoidalSingleObj.star (Type))))) ≫
      ((generalLiftPrelaxFunctor F hF).map
        (canonicalInverseHom f A) ◁ ei.inv) ≫
      ((generalLiftPrelaxFunctor F hF).map
        (canonicalInverseHom f A) ◁ ei.hom) ≫
      ((generalLiftPrelaxFunctor F hF).map
        (canonicalInverseHom f A) ◁
          F.map₂ (canonicalSourceIdentityComparison X).hom) ≫
      ((generalLiftPrelaxFunctor F hF).map
        (canonicalInverseHom f A) ◁
          (F.mapId (canonicalSourceObject X)).hom) ≫
      (ρ_ ((generalLiftPrelaxFunctor F hF).map
        (canonicalInverseHom f A))).hom ≫ e.hom
  slice_rhs 7 9 =>
    rw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp]
  rw [Category.assoc]
  slice_rhs 5 10 =>
    rw [transportRightUnitorThroughIsos
      e ei
      (F.map₂ (canonicalSourceIdentityComparison X).hom ≫
        (F.mapId (canonicalSourceObject X)).hom)]
  let ec := eqToIso
    (generalLiftPrelaxFunctor_map_inverse F hF f hf
      (A × (𝟙 (MonoidalSingleObj.star (Type)))))
  have : IsIso ec.hom := ec.isIso_hom
  have : Epi ec.hom := IsIso.epi_of_iso ec.hom
  change ec.hom ≫ _ = ec.hom ≫ _
  rw [cancel_epi ec.hom]
  slice_rhs 1 2 =>
    rw [← whiskerLeft_comp]
  symm
  simp only [Category.assoc]
  apply (whiskerLeft_rightUnitChain
    (generalLiftSourceEquivalence F hF f).inv
    (generalLiftForwardMapCompSource F (𝟙 X) (𝟙 X) A
      (𝟙 (MonoidalSingleObj.star (Type)))).hom
    (F.map₂ (canonicalSourceIdentityComparison X).hom ≫
      (F.mapId (canonicalSourceObject X)).hom)
    (F.map₂ (canonicalSourceTwoCell (𝟙 X)
      (MonoidalCategory.rightUnitor A).hom)))
  simpa only [generalLiftForwardMapCompSource, Iso.trans_hom,
    PrelaxFunctor.map₂Iso_hom, Category.assoc] using
      (generalLiftSourceRightUnitor_afterCompositionComparison
        (F := F) (f := 𝟙 X) (A := A))

/-- On a genuine canonical inverse followed by the retained identity, the
all-arrow compositor selects the inverse/retained branch. -/
theorem generalLiftMapComp_inverseRightIdentity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type) :
    generalLiftMapComp F hF
        (canonicalInverseHom f A)
        (canonicalForwardHom (𝟙 X)
          (𝟙 (MonoidalSingleObj.star (Type)))) =
      generalLiftMapCompInverseRetained F hF f hf A
        (𝟙 (MonoidalSingleObj.star (Type))) := by
  have hX : X = 0 ∨ X = 1 := by fin_cases X <;> simp
  have hY : Y = 0 ∨ Y = 1 := by fin_cases Y <;> simp
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
  · exact False.elim (hf le_rfl)
  · have hf' : f = Ript.Examples.WalkingLocalization.arrow :=
      Subsingleton.elim _ _
    subst f
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow A
    cases canonicalEndpointHom_eq_forward
      (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow))
      (𝟙 (MonoidalSingleObj.star (Type)))
    have he := generalLiftMapComp_endpoint F hF 1 0 0
      A (𝟙 (MonoidalSingleObj.star (Type)))
    exact he.trans
      (generalLiftEndpointMapComp_one_zero_zero F hF _ _)
  · exact False.elim ((by omega : ¬ (1 : Fin 2) ≤ 0) f.le)
  · exact False.elim (hf le_rfl)

set_option backward.isDefEq.respectTransparency false in
private theorem generalLiftRightUnitor_inverse_of_mapCompInverseRetained
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type)
    (hcomp :
      generalLiftMapComp F hF
          (canonicalInverseHom f A)
          (canonicalForwardHom (𝟙 X)
            (𝟙 (MonoidalSingleObj.star (Type)))) =
        generalLiftMapCompInverseRetained F hF f hf A
          (𝟙 (MonoidalSingleObj.star (Type)))) :
    (generalLiftPrelaxFunctor F hF).map₂
        (ρ_ (canonicalInverseHom f A)).hom =
      (generalLiftMapComp F hF (canonicalInverseHom f A)
          (𝟙 (canonicalTargetObject X))).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A) ◁
          (generalLiftMapId F hF (canonicalTargetObject X)).hom ≫
        (ρ_ ((generalLiftPrelaxFunctor F hF).map
          (canonicalInverseHom f A))).hom := by
  let e := (generalLiftPrelaxFunctor F hF).map₂Iso
    (whiskerLeftIso (canonicalInverseHom f A)
      (canonicalForwardIdentityComparison X))
  have : IsIso e.hom := e.isIso_hom
  have : Epi e.hom := IsIso.epi_of_iso e.hom
  rw [← cancel_epi e.hom]
  change
    (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseHom f A ◁
            (canonicalForwardIdentityComparison X).hom) ≫
        (generalLiftPrelaxFunctor F hF).map₂
          (ρ_ (canonicalInverseHom f A)).hom =
      (generalLiftPrelaxFunctor F hF).map₂
          (canonicalInverseHom f A ◁
            (canonicalForwardIdentityComparison X).hom) ≫ _
  rw [← (generalLiftPrelaxFunctor F hF).map₂_comp]
  rw [← canonicalInverseRightUnitorFactorization]
  rw [generalLiftMapCompInverseRetained_rightUnitor F hF f hf A]
  slice_rhs 1 2 =>
    rw [generalLiftMapComp_naturality_right F hF
      (canonicalInverseHom f A)
      (canonicalForwardIdentityComparison X).hom]
  rw [generalLiftMapId_canonical]
  simp only [generalLiftCanonicalMapId, Iso.trans_hom,
    PrelaxFunctor.map₂Iso_hom, whiskerLeft_comp]
  slice_rhs 2 3 =>
    rw [← whiskerLeft_comp,
      ← (generalLiftPrelaxFunctor F hF).map₂_comp]
    simp only [Iso.symm_hom, Iso.hom_inv_id]
    rw [(generalLiftPrelaxFunctor F hF).map₂_id]
    simp
  simp only [Category.id_comp]
  slice_rhs 2 4 =>
    rw [← whiskerLeft_comp, ← whiskerLeft_comp]
  change _ =
    (generalLiftMapComp F hF
        (canonicalInverseHom f A)
        (canonicalForwardHom (𝟙 X)
          (𝟙 (MonoidalSingleObj.star (Type))))).hom ≫
      (generalLiftPrelaxFunctor F hF).map
          (canonicalInverseHom f A) ◁
        (generalLiftForwardMapIdTail F hF X).hom ≫
      (ρ_ ((generalLiftPrelaxFunctor F hF).map
        (canonicalInverseHom f A))).hom
  rw [hcomp]

/-- The arbitrary lift satisfies oplax right-unit coherence on every genuine
canonical inverse target arrow. -/
theorem generalLiftRightUnitor_inverse
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : X ⟶ Y) (hf : ¬ Y ≤ X) (A : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
        (ρ_ (canonicalInverseHom f A)).hom =
      (generalLiftMapComp F hF (canonicalInverseHom f A)
          (𝟙 (canonicalTargetObject X))).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalInverseHom f A) ◁
          (generalLiftMapId F hF (canonicalTargetObject X)).hom ≫
        (ρ_ ((generalLiftPrelaxFunctor F hF).map
          (canonicalInverseHom f A))).hom :=
  generalLiftRightUnitor_inverse_of_mapCompInverseRetained
    F hF f hf A
      (generalLiftMapComp_inverseRightIdentity F hF f hf A)

private theorem generalLiftRightUnitor_canonicalObjects
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Ript.Examples.WalkingLocalization.Arrow}
    (f : canonicalTargetObject X ⟶ canonicalTargetObject Y) :
    (generalLiftPrelaxFunctor F hF).map₂ (ρ_ f).hom =
      (generalLiftMapComp F hF f (𝟙 (canonicalTargetObject Y))).hom ≫
        (generalLiftPrelaxFunctor F hF).map f ◁
          (generalLiftMapId F hF (canonicalTargetObject Y)).hom ≫
        (ρ_ ((generalLiftPrelaxFunctor F hF).map f)).hom := by
  rcases f with ⟨⟨f⟩, A⟩
  have hf : f = canonicalCompletionHom X Y :=
    completion_hom_eq_canonical f
  cases hf
  rcases (by fin_cases X <;> simp : X = 0 ∨ X = 1) with rfl | rfl <;>
    rcases (by fin_cases Y <;> simp : Y = 0 ∨ Y = 1) with rfl | rfl
  · cases canonicalEndpointHom_eq_forward
      (𝟙 (0 : Ript.Examples.WalkingLocalization.Arrow)) A
    exact generalLiftRightUnitor_forward F hF (𝟙 0) A
  · cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow A
    exact generalLiftRightUnitor_forward F hF
      Ript.Examples.WalkingLocalization.arrow A
  · cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow A
    exact generalLiftRightUnitor_inverse F hF
      Ript.Examples.WalkingLocalization.arrow (by decide) A
  · cases canonicalEndpointHom_eq_forward
      (𝟙 (1 : Ript.Examples.WalkingLocalization.Arrow)) A
    exact generalLiftRightUnitor_forward F hF (𝟙 1) A

/-- The arbitrary lift satisfies the oplax right-unit law for every target
1-morphism. -/
theorem generalLiftRightUnitor
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Target} (f : X ⟶ Y) :
    (generalLiftPrelaxFunctor F hF).map₂ (ρ_ f).hom =
      (generalLiftMapComp F hF f (𝟙 Y)).hom ≫
        (generalLiftPrelaxFunctor F hF).map f ◁
          (generalLiftMapId F hF Y).hom ≫
        (ρ_ ((generalLiftPrelaxFunctor F hF).map f)).hom := by
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
  cases hX
  cases hY
  exact generalLiftRightUnitor_canonicalObjects F hF f

set_option backward.isDefEq.respectTransparency false in
/-- The all-arrow compositor satisfies oplax associativity on every triple
of endpoint-normal arrows.  The sixteen endpoint sequences reduce to the
twelve compiled forward, retained, inverse, and cancellation laws. -/
theorem generalLiftEndpointMapComp_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    (W X Y Z : Ript.Examples.WalkingLocalization.Arrow)
    (A B C : Type) :
    (generalLiftPrelaxFunctor F hF).map₂
          (α_ (canonicalEndpointHom W X A)
            (canonicalEndpointHom X Y B)
            (canonicalEndpointHom Y Z C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalEndpointHom W X A)
          (canonicalEndpointHom X Y B ≫
            canonicalEndpointHom Y Z C)).hom ≫
        (generalLiftPrelaxFunctor F hF).map
            (canonicalEndpointHom W X A) ◁
          (generalLiftMapComp F hF
            (canonicalEndpointHom X Y B)
            (canonicalEndpointHom Y Z C)).hom =
      (generalLiftMapComp F hF
          (canonicalEndpointHom W X A ≫
            canonicalEndpointHom X Y B)
          (canonicalEndpointHom Y Z C)).hom ≫
        (generalLiftMapComp F hF
          (canonicalEndpointHom W X A)
          (canonicalEndpointHom X Y B)).hom ▷
            (generalLiftPrelaxFunctor F hF).map
              (canonicalEndpointHom Y Z C) ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map
            (canonicalEndpointHom W X A))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalEndpointHom X Y B))
          ((generalLiftPrelaxFunctor F hF).map
            (canonicalEndpointHom Y Z C))).hom := by
  rcases walkingArrow_eq_zero_or_one W with rfl | rfl <;>
    rcases walkingArrow_eq_zero_or_one X with rfl | rfl <;>
      rcases walkingArrow_eq_zero_or_one Y with rfl | rfl <;>
        rcases walkingArrow_eq_zero_or_one Z with rfl | rfl
  · cases canonicalEndpointHom_eq_forward (𝟙 0) A
    cases canonicalEndpointHom_eq_forward (𝟙 0) B
    cases canonicalEndpointHom_eq_forward (𝟙 0) C
    exact generalLiftMapComp_forward_associativity F hF
      (𝟙 0) (𝟙 0) (𝟙 0) A B C
  · cases canonicalEndpointHom_eq_forward (𝟙 0) A
    cases canonicalEndpointHom_eq_forward (𝟙 0) B
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow C
    exact generalLiftMapComp_forward_associativity F hF
      (𝟙 0) (𝟙 0) Ript.Examples.WalkingLocalization.arrow A B C
  · cases canonicalEndpointHom_eq_forward (𝟙 0) A
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow B
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow C
    exact generalLiftMapComp_retainedForwardInverse_associativity F hF
      Ript.Examples.WalkingLocalization.arrow (by decide) A B C
  · cases canonicalEndpointHom_eq_forward (𝟙 0) A
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow B
    cases canonicalEndpointHom_eq_forward (𝟙 1) C
    exact generalLiftMapComp_forward_associativity F hF
      (𝟙 0) Ript.Examples.WalkingLocalization.arrow (𝟙 1) A B C
  · cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow A
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow B
    cases canonicalEndpointHom_eq_forward (𝟙 0) C
    exact generalLiftMapComp_forwardInverseRetained_associativity F hF
      Ript.Examples.WalkingLocalization.arrow (by decide) A B C
  · cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow A
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow B
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow C
    exact generalLiftMapComp_forwardInverseForward_associativity F hF
      Ript.Examples.WalkingLocalization.arrow (by decide) A B C
  · cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow A
    cases canonicalEndpointHom_eq_forward (𝟙 1) B
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow C
    exact generalLiftMapComp_forwardRetainedInverse_associativity F hF
      Ript.Examples.WalkingLocalization.arrow (by decide) A B C
  · cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow A
    cases canonicalEndpointHom_eq_forward (𝟙 1) B
    cases canonicalEndpointHom_eq_forward (𝟙 1) C
    exact generalLiftMapComp_forward_associativity F hF
      Ript.Examples.WalkingLocalization.arrow (𝟙 1) (𝟙 1) A B C
  · cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow A
    cases canonicalEndpointHom_eq_forward (𝟙 0) B
    cases canonicalEndpointHom_eq_forward (𝟙 0) C
    exact generalLiftMapComp_inverseRetained_associativity F hF
      Ript.Examples.WalkingLocalization.arrow (by decide) A B C
  · cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow A
    cases canonicalEndpointHom_eq_forward (𝟙 0) B
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow C
    exact generalLiftMapComp_inverseRetainedForward_associativity F hF
      Ript.Examples.WalkingLocalization.arrow (by decide) A B C
  · cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow A
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow B
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow C
    exact generalLiftMapComp_inverseForwardInverse_associativity F hF
      Ript.Examples.WalkingLocalization.arrow (by decide) A B C
  · cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow A
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow B
    cases canonicalEndpointHom_eq_forward (𝟙 1) C
    exact generalLiftMapComp_inverseForwardRetained_associativity F hF
      Ript.Examples.WalkingLocalization.arrow (by decide) A B C
  · cases canonicalEndpointHom_eq_forward (𝟙 1) A
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow B
    cases canonicalEndpointHom_eq_forward (𝟙 0) C
    exact generalLiftMapComp_retainedInverseRetained_associativity F hF
      Ript.Examples.WalkingLocalization.arrow (by decide) A B C
  · cases canonicalEndpointHom_eq_forward (𝟙 1) A
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow B
    cases canonicalEndpointHom_eq_forward
      Ript.Examples.WalkingLocalization.arrow C
    exact generalLiftMapComp_retainedInverseForward_associativity F hF
      Ript.Examples.WalkingLocalization.arrow (by decide) A B C
  · cases canonicalEndpointHom_eq_forward (𝟙 1) A
    cases canonicalEndpointHom_eq_forward (𝟙 1) B
    cases canonicalEndpointHom_eq_inverse
      Ript.Examples.WalkingLocalization.arrow C
    exact generalLiftMapComp_retainedRetainedInverse_associativity F hF
      Ript.Examples.WalkingLocalization.arrow (by decide) A B C
  · cases canonicalEndpointHom_eq_forward (𝟙 1) A
    cases canonicalEndpointHom_eq_forward (𝟙 1) B
    cases canonicalEndpointHom_eq_forward (𝟙 1) C
    exact generalLiftMapComp_forward_associativity F hF
      (𝟙 1) (𝟙 1) (𝟙 1) A B C

private theorem generalLiftMapComp_associativity_canonicalObjects
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {W X Y Z : Ript.Examples.WalkingLocalization.Arrow}
    (f : canonicalTargetObject W ⟶ canonicalTargetObject X)
    (g : canonicalTargetObject X ⟶ canonicalTargetObject Y)
    (h : canonicalTargetObject Y ⟶ canonicalTargetObject Z) :
    (generalLiftPrelaxFunctor F hF).map₂ (α_ f g h).hom ≫
        (generalLiftMapComp F hF f (g ≫ h)).hom ≫
        (generalLiftPrelaxFunctor F hF).map f ◁
          (generalLiftMapComp F hF g h).hom =
      (generalLiftMapComp F hF (f ≫ g) h).hom ≫
        (generalLiftMapComp F hF f g).hom ▷
          (generalLiftPrelaxFunctor F hF).map h ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map f)
          ((generalLiftPrelaxFunctor F hF).map g)
          ((generalLiftPrelaxFunctor F hF).map h)).hom := by
  rcases f with ⟨⟨f⟩, A⟩
  rcases g with ⟨⟨g⟩, B⟩
  rcases h with ⟨⟨h⟩, C⟩
  have hf : f = canonicalCompletionHom W X :=
    completion_hom_eq_canonical f
  have hg : g = canonicalCompletionHom X Y :=
    completion_hom_eq_canonical g
  have hh : h = canonicalCompletionHom Y Z :=
    completion_hom_eq_canonical h
  cases hf
  cases hg
  cases hh
  exact generalLiftEndpointMapComp_associativity F hF W X Y Z A B C

/-- The all-arrow compositor satisfies the full oplax associativity equation
for every triple of target arrows, without any local-thinness assumption on
the codomain bicategory. -/
theorem generalLiftMapComp_associativity
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {W X Y Z : Target} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (generalLiftPrelaxFunctor F hF).map₂ (α_ f g h).hom ≫
        (generalLiftMapComp F hF f (g ≫ h)).hom ≫
        (generalLiftPrelaxFunctor F hF).map f ◁
          (generalLiftMapComp F hF g h).hom =
      (generalLiftMapComp F hF (f ≫ g) h).hom ≫
        (generalLiftMapComp F hF f g).hom ▷
          (generalLiftPrelaxFunctor F hF).map h ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map f)
          ((generalLiftPrelaxFunctor F hF).map g)
          ((generalLiftPrelaxFunctor F hF).map h)).hom := by
  rcases W with ⟨⟨W⟩, W'⟩
  rcases X with ⟨⟨X⟩, X'⟩
  rcases Y with ⟨⟨Y⟩, Y'⟩
  rcases Z with ⟨⟨Z⟩, Z'⟩
  cases W'
  cases X'
  cases Y'
  cases Z'
  let w : Ript.Examples.WalkingLocalization.Arrow := W.as.as
  let x : Ript.Examples.WalkingLocalization.Arrow := X.as.as
  let y : Ript.Examples.WalkingLocalization.Arrow := Y.as.as
  let z : Ript.Examples.WalkingLocalization.Arrow := Z.as.as
  have hW : W = CategoryTheory.FreeGroupoid.mk w :=
    CategoryTheory.FreeGroupoid.eq_mk W
  have hX : X = CategoryTheory.FreeGroupoid.mk x :=
    CategoryTheory.FreeGroupoid.eq_mk X
  have hY : Y = CategoryTheory.FreeGroupoid.mk y :=
    CategoryTheory.FreeGroupoid.eq_mk Y
  have hZ : Z = CategoryTheory.FreeGroupoid.mk z :=
    CategoryTheory.FreeGroupoid.eq_mk Z
  cases hW
  cases hX
  cases hY
  cases hZ
  exact generalLiftMapComp_associativity_canonicalObjects F hF f g h

/-- An arbitrary source pseudofunctor that inverts the marked walking arrow
extends to a genuine pseudofunctor on the two-dimensional localization. -/
noncomputable def generalLiftPseudofunctor
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) : Target ⥤ᵖ E where
  toPrelaxFunctor := generalLiftPrelaxFunctor F hF
  mapId := generalLiftMapId F hF
  mapComp := generalLiftMapComp F hF
  map₂_whisker_left := by
    intro a b c f g h η
    rw [← cancel_mono (generalLiftMapComp F hF f h).hom]
    simp only [Category.assoc]
    simp
    exact generalLiftMapComp_naturality_right F hF f η
  map₂_whisker_right := by
    intro a b c f g η h
    rw [← cancel_mono (generalLiftMapComp F hF g h).hom]
    simp only [Category.assoc]
    simp
    exact generalLiftMapComp_naturality_left F hF η h
  map₂_associator := by
    intro a b c d f g h
    rw [← cancel_mono
      ((generalLiftMapComp F hF f (g ≫ h)).hom ≫
        ((generalLiftPrelaxFunctor F hF).map f ◁
          (generalLiftMapComp F hF g h).hom))]
    simp only [Category.assoc]
    simp
    exact generalLiftMapComp_associativity F hF f g h
  map₂_left_unitor := by
    intro a b f
    exact generalLiftLeftUnitor F hF f
  map₂_right_unitor := by
    intro a b f
    exact generalLiftRightUnitor F hF f

/-- The genuine arbitrary lift has exactly the previously constructed
prelax action as its underlying object/arrow/2-cell map. -/
theorem generalLiftPseudofunctor_toPrelaxFunctor
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) :
    (generalLiftPseudofunctor F hF).toPrelaxFunctor =
      generalLiftPrelaxFunctor F hF :=
  rfl

/-- The general lift maps every included source arrow exactly as the original
source pseudofunctor. -/
theorem generalLiftPseudofunctor_map_inclusion
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Source} (f : X ⟶ Y) :
    (generalLiftPseudofunctor F hF).map (inclusion.map f) = F.map f := by
  rcases X with ⟨⟨X⟩, X'⟩
  rcases Y with ⟨⟨Y⟩, Y'⟩
  cases X'
  cases Y'
  rcases f with ⟨⟨f⟩, A⟩
  exact generalLiftPrelaxFunctor_map_forward F hF f A

/-- The general lift and the original source pseudofunctor agree on objects
after precomposition with the walking inclusion. -/
theorem generalLiftPseudofunctor_obj_inclusion
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) (X : Source) :
    (inclusion.comp (generalLiftPseudofunctor F hF)).obj X = F.obj X := by
  rcases X with ⟨⟨X⟩, X'⟩
  cases X'
  rfl

/-! ## Arbitrary factorization and the full localization theorem -/

/-- Transport an `HEq` between bicategorical 1-morphisms across object
equalities to the canonical naturality 2-isomorphism. -/
noncomputable def generalLiftFactorizationNaturalityOfHEq
    {C : Type u₂} [Bicategory.{w₂, v₂} C]
    {X Y X' Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) :
    f ≫ eqToHom hY ≅ eqToHom hX ≫ g := by
  subst X'
  subst Y'
  exact (ρ_ f) ≪≫ eqToIso (eq_of_heq h) ≪≫ (λ_ g).symm

/-- The transported `HEq` naturality is compatible with arbitrary
heterogeneously equal 2-morphisms. -/
theorem generalLiftFactorizationNaturalityOfHEq_naturality
    {C : Type u₂} [Bicategory.{w₂, v₂} C]
    {X Y X' Y' : C} (hX : X = X') (hY : Y = Y')
    {f₀ f₁ : X ⟶ Y} {g₀ g₁ : X' ⟶ Y'}
    (hf₀ : HEq f₀ g₀) (hf₁ : HEq f₁ g₁)
    {η : f₀ ⟶ f₁} {θ : g₀ ⟶ g₁} (hη : HEq η θ) :
    (η ▷ eqToHom hY) ≫
        (generalLiftFactorizationNaturalityOfHEq hX hY hf₁).hom =
      (generalLiftFactorizationNaturalityOfHEq hX hY hf₀).hom ≫
        (eqToHom hX ◁ θ) := by
  subst X'
  subst Y'
  have e₀ := eq_of_heq hf₀
  have e₁ := eq_of_heq hf₁
  subst g₀
  subst g₁
  have eη := eq_of_heq hη
  subst θ
  dsimp [generalLiftFactorizationNaturalityOfHEq]
  simp

/-- The restriction of the general lift maps every source arrow
heterogeneously equally to the original pseudofunctor. -/
theorem generalLiftPseudofunctor_map_inclusion_heq
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {a b : Source} (f : a ⟶ b) :
    HEq ((inclusion.comp (generalLiftPseudofunctor F hF)).map f)
      (F.map f) :=
  heq_of_eq (generalLiftPseudofunctor_map_inclusion F hF f)

/-- The restriction of the general lift agrees with the original
pseudofunctor on every source 2-morphism. -/
theorem generalLiftPseudofunctor_map₂_inclusion_heq
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {a b : Source} {f g : a ⟶ b} (η : f ⟶ g) :
    HEq ((inclusion.comp (generalLiftPseudofunctor F hF)).map₂ η)
      (F.map₂ η) := by
  rcases a with ⟨⟨a⟩, a'⟩
  rcases b with ⟨⟨b⟩, b'⟩
  cases a'
  cases b'
  rcases f with ⟨⟨f⟩, A⟩
  rcases g with ⟨⟨g⟩, B⟩
  rcases η with ⟨η, θ⟩
  have hfg : f = g := Subsingleton.elim _ _
  cases hfg
  have hη : η = 𝟙 _ := Subsingleton.elim _ _
  cases hη
  exact generalLiftPrelaxFunctor_map₂_forward F hF f θ

set_option linter.defProp false in
/-- Object equality underlying the restriction comparison.  It is kept
reducible because the comparison components are transported identities. -/
def generalLiftFactorizationObjEq
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) (X : Source) :
    (inclusion.comp (generalLiftPseudofunctor F hF)).obj X = F.obj X := by
  rcases X with ⟨⟨X⟩, X'⟩
  cases X'
  rfl

/-- Identity component of the comparison from the restricted general lift
to the original source pseudofunctor. -/
noncomputable def generalLiftFactorizationApp
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) (X : Source) :
    (inclusion.comp (generalLiftPseudofunctor F hF)).obj X ⟶ F.obj X := by
  rcases X with ⟨⟨X⟩, X'⟩
  cases X'
  exact 𝟙 _

/-- Canonical naturality isomorphism for the forward restriction
comparison. -/
noncomputable def generalLiftFactorizationNaturality
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Source} (f : X ⟶ Y) :
    (inclusion.comp (generalLiftPseudofunctor F hF)).map f ≫
        generalLiftFactorizationApp F hF Y ≅
      generalLiftFactorizationApp F hF X ≫ F.map f :=
by
  rcases X with ⟨⟨X⟩, X'⟩
  rcases Y with ⟨⟨Y⟩, Y'⟩
  cases X'
  cases Y'
  exact generalLiftFactorizationNaturalityOfHEq
    (rfl : (inclusion.comp (generalLiftPseudofunctor F hF)).obj
      ((LocallyDiscrete.mk X, PUnit.unit) : Source) =
        F.obj ((LocallyDiscrete.mk X, PUnit.unit) : Source))
    (rfl : (inclusion.comp (generalLiftPseudofunctor F hF)).obj
      ((LocallyDiscrete.mk Y, PUnit.unit) : Source) =
        F.obj ((LocallyDiscrete.mk Y, PUnit.unit) : Source))
    (generalLiftPseudofunctor_map_inclusion_heq F hF f)

set_option backward.isDefEq.respectTransparency false in
/-- The forward strong transformation from the restricted general lift to
the original source pseudofunctor. -/
noncomputable def generalLiftFactorizationHom
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) :
    inclusion.comp (generalLiftPseudofunctor F hF) ⟶ F where
  app := generalLiftFactorizationApp F hF
  naturality := generalLiftFactorizationNaturality F hF
  naturality_naturality := by
    intro a b f g η
    exact generalLiftFactorizationNaturalityOfHEq_naturality
      (generalLiftFactorizationObjEq F hF a)
      (generalLiftFactorizationObjEq F hF b)
      (generalLiftPseudofunctor_map_inclusion_heq F hF f)
      (generalLiftPseudofunctor_map_inclusion_heq F hF g)
      (generalLiftPseudofunctor_map₂_inclusion_heq F hF η)
  naturality_id := by
    intro a
    rcases a with ⟨⟨a⟩, a'⟩
    cases a'
    have hrestrictionMapIdRaw :
        ((inclusion.comp (generalLiftPseudofunctor F hF)).mapId
          ((LocallyDiscrete.mk a, PUnit.unit) : Source)).hom =
        (generalLiftPseudofunctor F hF).map₂
            (canonicalForwardIdentityComparison a).hom ≫
          (generalLiftPseudofunctor F hF).map₂
            (canonicalForwardIdentityComparison a).inv ≫
          eqToHom (generalLiftPrelaxFunctor_map_forward F hF (𝟙 a)
            (𝟙 (MonoidalSingleObj.star (Type)))) ≫
          F.map₂ (canonicalSourceIdentityComparison a).hom ≫
          (F.mapId ((LocallyDiscrete.mk a, PUnit.unit) : Source)).hom := by
      rfl
    have hrestrictionMapIdSimpleRaw :
        ((inclusion.comp (generalLiftPseudofunctor F hF)).mapId
          ((LocallyDiscrete.mk a, PUnit.unit) : Source)).hom =
        eqToHom (generalLiftPrelaxFunctor_map_forward F hF (𝟙 a)
            (𝟙 (MonoidalSingleObj.star (Type)))) ≫
          F.map₂ (canonicalSourceIdentityComparison a).hom ≫
          (F.mapId ((LocallyDiscrete.mk a, PUnit.unit) : Source)).hom := by
      rw [hrestrictionMapIdRaw]
      have hcancel :
          (generalLiftPseudofunctor F hF).map₂
                (canonicalForwardIdentityComparison a).hom ≫
              (generalLiftPseudofunctor F hF).map₂
                (canonicalForwardIdentityComparison a).inv =
            𝟙 _ := by
        rw [← (generalLiftPseudofunctor F hF).map₂_comp,
          Iso.hom_inv_id,
          (generalLiftPseudofunctor F hF).map₂_id]
      let tail :=
          eqToHom (generalLiftPrelaxFunctor_map_forward F hF (𝟙 a)
            (𝟙 (MonoidalSingleObj.star (Type)))) ≫
          F.map₂ (canonicalSourceIdentityComparison a).hom ≫
          (F.mapId ((LocallyDiscrete.mk a, PUnit.unit) : Source)).hom
      change _ ≫ _ ≫ tail = tail
      calc
        _ = (((generalLiftPseudofunctor F hF).map₂
              (canonicalForwardIdentityComparison a).hom ≫
            (generalLiftPseudofunctor F hF).map₂
              (canonicalForwardIdentityComparison a).inv) ≫ tail) :=
          (Category.assoc _ _ _).symm
        _ = tail := by rw [hcancel]; simp
    have hrestrictionMapIdW := congrArg
      (fun k => k ▷ generalLiftFactorizationApp F hF
        ((LocallyDiscrete.mk a, PUnit.unit) : Source))
      hrestrictionMapIdSimpleRaw
    simp only [Bicategory.comp_whiskerRight] at hrestrictionMapIdW
    rw [hrestrictionMapIdW]
    have hsourceId : (canonicalSourceIdentityComparison a).hom =
        𝟙 (canonicalSourceHom (𝟙 a)
          (𝟙 (MonoidalSingleObj.star (Type)))) := by
      rfl
    rw [hsourceId, F.map₂_id]
    simp [generalLiftFactorizationApp,
      generalLiftFactorizationNaturality,
      generalLiftFactorizationNaturalityOfHEq]
    bicategory
  naturality_comp := by
    intro a b c f g
    rcases a with ⟨⟨a⟩, a'⟩
    rcases b with ⟨⟨b⟩, b'⟩
    rcases c with ⟨⟨c⟩, c'⟩
    cases a'
    cases b'
    cases c'
    rcases f with ⟨⟨f⟩, A⟩
    rcases g with ⟨⟨g⟩, B⟩
    let fRaw :
        ((LocallyDiscrete.mk a, PUnit.unit) : Source) ⟶
          ((LocallyDiscrete.mk b, PUnit.unit) : Source) :=
      (⟨f⟩, A)
    let gRaw :
        ((LocallyDiscrete.mk b, PUnit.unit) : Source) ⟶
          ((LocallyDiscrete.mk c, PUnit.unit) : Source) :=
      (⟨g⟩, B)
    have hmapf : inclusion.map fRaw = canonicalForwardHom f A := rfl
    have hmapg : inclusion.map gRaw = canonicalForwardHom g B := rfl
    have hinclusionMapComp :
        inclusion.mapComp fRaw gRaw =
        (canonicalForwardCompositionComparison f g A B).symm := by
      apply Iso.ext
      apply Prod.ext
      · exact Subsingleton.elim _ _
      · rfl
    have hgeneralLiftMapComp :
        generalLiftMapComp F hF (inclusion.map fRaw)
          (inclusion.map gRaw) =
        generalLiftMapCompForward F hF f g A B := by
      cases hmapf
      cases hmapg
      exact generalLiftMapComp_forward F hF f g A B
    have hrestrictionMapComp :
        ((inclusion.comp (generalLiftPseudofunctor F hF)).mapComp
          fRaw gRaw).hom =
          (generalLiftPseudofunctor F hF).map₂
            (canonicalForwardCompositionComparison f g A B).inv ≫
          (generalLiftMapCompForward F hF f g A B).hom := by
      change
        (((generalLiftPseudofunctor F hF).map₂Iso
            (inclusion.mapComp fRaw gRaw)) ≪≫
          generalLiftMapComp F hF
            (inclusion.map fRaw) (inclusion.map gRaw)).hom = _
      rw [hinclusionMapComp]
      rw [hgeneralLiftMapComp]
      rfl
    have hrestrictionMapCompSimple :
        ((inclusion.comp (generalLiftPseudofunctor F hF)).mapComp
          fRaw gRaw).hom =
        (generalLiftForwardMapCompTransport F hF f g A B).hom := by
      rw [hrestrictionMapComp]
      rw [generalLiftMapCompForward_hom]
      have hcancel :
          (generalLiftPseudofunctor F hF).map₂
                (canonicalForwardCompositionComparison f g A B).inv ≫
              (generalLiftPseudofunctor F hF).map₂
                (canonicalForwardCompositionComparison f g A B).hom =
            𝟙 _ := by
        rw [← (generalLiftPseudofunctor F hF).map₂_comp,
          Iso.inv_hom_id,
          (generalLiftPseudofunctor F hF).map₂_id]
      let tail :=
        (generalLiftForwardMapCompTransport F hF f g A B).hom
      change _ ≫ _ ≫ tail = tail
      calc
        _ = (((generalLiftPseudofunctor F hF).map₂
              (canonicalForwardCompositionComparison f g A B).inv ≫
            (generalLiftPseudofunctor F hF).map₂
              (canonicalForwardCompositionComparison f g A B).hom) ≫
              tail) := (Category.assoc _ _ _).symm
        _ = tail := by rw [hcancel]; simp
    have hrestrictionMapCompW := congrArg
      (fun k => k ▷ generalLiftFactorizationApp F hF
        ((LocallyDiscrete.mk c, PUnit.unit) : Source))
      hrestrictionMapCompSimple
    change
      (generalLiftFactorizationNaturality F hF (fRaw ≫ gRaw)).hom ≫
        generalLiftFactorizationApp F hF
          ((LocallyDiscrete.mk a, PUnit.unit) : Source) ◁
          (F.mapComp fRaw gRaw).hom =
      ((inclusion.comp (generalLiftPseudofunctor F hF)).mapComp
          fRaw gRaw).hom ▷
          generalLiftFactorizationApp F hF
            ((LocallyDiscrete.mk c, PUnit.unit) : Source) ≫
        (α_ ((inclusion.comp (generalLiftPseudofunctor F hF)).map fRaw)
          ((inclusion.comp (generalLiftPseudofunctor F hF)).map gRaw)
          (generalLiftFactorizationApp F hF
            ((LocallyDiscrete.mk c, PUnit.unit) : Source))).hom ≫
        (inclusion.comp (generalLiftPseudofunctor F hF)).map fRaw ◁
          (generalLiftFactorizationNaturality F hF gRaw).hom ≫
        (α_ ((inclusion.comp (generalLiftPseudofunctor F hF)).map fRaw)
          (generalLiftFactorizationApp F hF
            ((LocallyDiscrete.mk b, PUnit.unit) : Source))
          (F.map gRaw)).inv ≫
        (generalLiftFactorizationNaturality F hF fRaw).hom ▷ F.map gRaw ≫
        (α_ (generalLiftFactorizationApp F hF
          ((LocallyDiscrete.mk a, PUnit.unit) : Source))
          (F.map fRaw) (F.map gRaw)).hom
    rw [hrestrictionMapCompW]
    rw [generalLiftForwardMapCompTransport_hom,
      generalLiftForwardMapCompCore_hom,
      generalLiftForwardMapCompFactors_hom]
    simp only [generalLiftForwardMapCompSource, Iso.trans_hom,
      PrelaxFunctor.map₂Iso_hom, Category.assoc]
    simp [generalLiftFactorizationApp,
      generalLiftFactorizationNaturality,
      generalLiftFactorizationNaturalityOfHEq]
    have hsourceComp :
        (canonicalSourceCompositionComparison f g A B).inv =
          𝟙 (canonicalSourceHom (f ≫ g) (A × B)) := by
      rfl
    rw [hsourceComp, F.map₂_id]
    simp
    bicategory
    simp
    bicategory_nf
    simp
    have hfRestr :
        (inclusion.comp (generalLiftPseudofunctor F hF)).map fRaw =
          F.map fRaw := eq_of_heq (generalLiftPseudofunctor_map_inclusion_heq F hF fRaw)
    have hgRestr :
        (inclusion.comp (generalLiftPseudofunctor F hF)).map gRaw =
          F.map gRaw := eq_of_heq (generalLiftPseudofunctor_map_inclusion_heq F hF gRaw)
    have hpair :
        (inclusion.comp (generalLiftPseudofunctor F hF)).map fRaw ≫
            (inclusion.comp (generalLiftPseudofunctor F hF)).map gRaw =
          F.map fRaw ≫ F.map gRaw := by
      rw [hfRestr, hgRestr]
    let ePair := eqToIso hpair
    have hexplicit :
        (λ_ (F.map fRaw ≫ F.map gRaw)).inv =
          ePair.inv ≫
            (ρ_ ((inclusion.comp
              (generalLiftPseudofunctor F hF)).map fRaw ≫
              (inclusion.comp
                (generalLiftPseudofunctor F hF)).map gRaw)).inv ≫
            (α_ ((inclusion.comp
                (generalLiftPseudofunctor F hF)).map fRaw)
              ((inclusion.comp
                (generalLiftPseudofunctor F hF)).map gRaw)
              (𝟙 ((inclusion.comp
                (generalLiftPseudofunctor F hF)).obj
                ((LocallyDiscrete.mk c, PUnit.unit) : Source)))).hom ≫
            (α_ ((inclusion.comp
                (generalLiftPseudofunctor F hF)).map fRaw)
              ((inclusion.comp
                (generalLiftPseudofunctor F hF)).map gRaw)
              (𝟙 (F.obj ((LocallyDiscrete.mk c,
                PUnit.unit) : Source)))).inv ≫
            (ρ_ ((inclusion.comp
              (generalLiftPseudofunctor F hF)).map fRaw ≫
              (inclusion.comp
                (generalLiftPseudofunctor F hF)).map gRaw)).hom ≫
            ePair.hom ≫
            (λ_ (F.map fRaw ≫ F.map gRaw)).inv := by
      have hmiddle :
          ((ρ_ ((inclusion.comp
              (generalLiftPseudofunctor F hF)).map fRaw ≫
              (inclusion.comp
                (generalLiftPseudofunctor F hF)).map gRaw)).inv ≫
            (α_ ((inclusion.comp
                (generalLiftPseudofunctor F hF)).map fRaw)
              ((inclusion.comp
                (generalLiftPseudofunctor F hF)).map gRaw)
              (𝟙 ((inclusion.comp
                (generalLiftPseudofunctor F hF)).obj
                ((LocallyDiscrete.mk c, PUnit.unit) : Source)))).hom ≫
            (α_ ((inclusion.comp
                (generalLiftPseudofunctor F hF)).map fRaw)
              ((inclusion.comp
                (generalLiftPseudofunctor F hF)).map gRaw)
              (𝟙 (F.obj ((LocallyDiscrete.mk c,
                PUnit.unit) : Source)))).inv ≫
            (ρ_ ((inclusion.comp
              (generalLiftPseudofunctor F hF)).map fRaw ≫
              (inclusion.comp
                (generalLiftPseudofunctor F hF)).map gRaw)).hom) =
          𝟙 _ := by
        bicategory
      slice_rhs 2 5 => rw [hmiddle]
      simp [ePair]
    convert hexplicit using 1
    all_goals simp [ePair]

set_option linter.defProp false in
/-- Reverse object equality underlying the inverse restriction comparison.
It remains reducible for the same transport calculation as the forward
comparison. -/
def generalLiftFactorizationObjEqInv
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) (X : Source) :
    F.obj X = (inclusion.comp (generalLiftPseudofunctor F hF)).obj X := by
  rcases X with ⟨⟨X⟩, X'⟩
  cases X'
  rfl

/-- Identity component of the comparison from the source pseudofunctor back
to the restricted general lift. -/
noncomputable def generalLiftFactorizationAppInv
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) (X : Source) :
    F.obj X ⟶ (inclusion.comp (generalLiftPseudofunctor F hF)).obj X := by
  rcases X with ⟨⟨X⟩, X'⟩
  cases X'
  exact 𝟙 _

/-- Canonical naturality isomorphism for the inverse restriction
comparison. -/
noncomputable def generalLiftFactorizationNaturalityInv
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Source} (f : X ⟶ Y) :
    F.map f ≫ generalLiftFactorizationAppInv F hF Y ≅
      generalLiftFactorizationAppInv F hF X ≫
        (inclusion.comp (generalLiftPseudofunctor F hF)).map f := by
  rcases X with ⟨⟨X⟩, X'⟩
  rcases Y with ⟨⟨Y⟩, Y'⟩
  cases X'
  cases Y'
  exact generalLiftFactorizationNaturalityOfHEq
    (rfl : F.obj ((LocallyDiscrete.mk X, PUnit.unit) : Source) =
      (inclusion.comp (generalLiftPseudofunctor F hF)).obj
        ((LocallyDiscrete.mk X, PUnit.unit) : Source))
    (rfl : F.obj ((LocallyDiscrete.mk Y, PUnit.unit) : Source) =
      (inclusion.comp (generalLiftPseudofunctor F hF)).obj
        ((LocallyDiscrete.mk Y, PUnit.unit) : Source))
    (generalLiftPseudofunctor_map_inclusion_heq F hF f).symm

set_option backward.isDefEq.respectTransparency false in
/-- The inverse strong transformation from the original source
pseudofunctor to the restricted general lift. -/
noncomputable def generalLiftFactorizationInverse
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) :
    F ⟶ inclusion.comp (generalLiftPseudofunctor F hF) where
  app := generalLiftFactorizationAppInv F hF
  naturality := generalLiftFactorizationNaturalityInv F hF
  naturality_naturality := by
    intro a b f g η
    exact generalLiftFactorizationNaturalityOfHEq_naturality
      (generalLiftFactorizationObjEqInv F hF a)
      (generalLiftFactorizationObjEqInv F hF b)
      (generalLiftPseudofunctor_map_inclusion_heq F hF f).symm
      (generalLiftPseudofunctor_map_inclusion_heq F hF g).symm
      (generalLiftPseudofunctor_map₂_inclusion_heq F hF η).symm
  naturality_id := by
    intro a
    rcases a with ⟨⟨a⟩, a'⟩
    cases a'
    have h := (generalLiftFactorizationHom F hF).naturality_id
      ((LocallyDiscrete.mk a, PUnit.unit) : Source)
    dsimp [generalLiftFactorizationHom] at h
    simp [generalLiftFactorizationApp,
      generalLiftFactorizationNaturality,
      generalLiftFactorizationAppInv,
      generalLiftFactorizationNaturalityInv,
      generalLiftFactorizationNaturalityOfHEq] at h ⊢
    let iF := 𝟙 (F.obj ((LocallyDiscrete.mk a,
      PUnit.unit) : Source))
    let iR := 𝟙 ((inclusion.comp
      (generalLiftPseudofunctor F hF)).obj
        ((LocallyDiscrete.mk a, PUnit.unit) : Source))
    have hkF : (λ_ iF).inv = (ρ_ iF).inv := by bicategory
    have hkR : (λ_ iR).inv = (ρ_ iR).inv := by bicategory
    rw [hkR, ← hkF]
    rw [← h]
    rw [← Category.assoc, eqToHom_trans]
    simp
    rfl
  naturality_comp := by
    intro a b c f g
    rcases a with ⟨⟨a⟩, a'⟩
    rcases b with ⟨⟨b⟩, b'⟩
    rcases c with ⟨⟨c⟩, c'⟩
    cases a'
    cases b'
    cases c'
    rcases f with ⟨⟨f⟩, A⟩
    rcases g with ⟨⟨g⟩, B⟩
    let fRaw :
        ((LocallyDiscrete.mk a, PUnit.unit) : Source) ⟶
          ((LocallyDiscrete.mk b, PUnit.unit) : Source) :=
      (⟨f⟩, A)
    let gRaw :
        ((LocallyDiscrete.mk b, PUnit.unit) : Source) ⟶
          ((LocallyDiscrete.mk c, PUnit.unit) : Source) :=
      (⟨g⟩, B)
    have h := (generalLiftFactorizationHom F hF).naturality_comp
      fRaw gRaw
    dsimp [generalLiftFactorizationHom] at h
    simp [generalLiftFactorizationApp, generalLiftFactorizationNaturality,
      generalLiftFactorizationAppInv, generalLiftFactorizationNaturalityInv,
      generalLiftFactorizationNaturalityOfHEq] at h ⊢
    have hfRestr :
        (inclusion.comp (generalLiftPseudofunctor F hF)).map fRaw =
          F.map fRaw :=
      eq_of_heq (generalLiftPseudofunctor_map_inclusion_heq F hF fRaw)
    have hgRestr :
        (inclusion.comp (generalLiftPseudofunctor F hF)).map gRaw =
          F.map gRaw :=
      eq_of_heq (generalLiftPseudofunctor_map_inclusion_heq F hF gRaw)
    have hpair :
        (inclusion.comp (generalLiftPseudofunctor F hF)).map fRaw ≫
            (inclusion.comp (generalLiftPseudofunctor F hF)).map gRaw =
          F.map fRaw ≫ F.map gRaw := by
      rw [hfRestr, hgRestr]
    let ePair := eqToIso hpair
    let eComp := eqToIso
      (eq_of_heq (generalLiftPseudofunctor_map_inclusion_heq F hF (fRaw ≫ gRaw)))
    have hmiddleR :
        ((ρ_ ((inclusion.comp
            (generalLiftPseudofunctor F hF)).map fRaw ≫
            (inclusion.comp
              (generalLiftPseudofunctor F hF)).map gRaw)).inv ≫
          (α_ ((inclusion.comp
              (generalLiftPseudofunctor F hF)).map fRaw)
            ((inclusion.comp
              (generalLiftPseudofunctor F hF)).map gRaw)
            (𝟙 ((inclusion.comp
              (generalLiftPseudofunctor F hF)).obj
              ((LocallyDiscrete.mk c, PUnit.unit) : Source)))).hom ≫
          (α_ ((inclusion.comp
              (generalLiftPseudofunctor F hF)).map fRaw)
            ((inclusion.comp
              (generalLiftPseudofunctor F hF)).map gRaw)
            (𝟙 (F.obj ((LocallyDiscrete.mk c,
              PUnit.unit) : Source)))).inv ≫
          (ρ_ ((inclusion.comp
            (generalLiftPseudofunctor F hF)).map fRaw ≫
            (inclusion.comp
              (generalLiftPseudofunctor F hF)).map gRaw)).hom) =
        𝟙 _ := by
      bicategory
    have hmiddleF :
        ((ρ_ (F.map fRaw ≫ F.map gRaw)).inv ≫
          (α_ (F.map fRaw) (F.map gRaw)
            (𝟙 (F.obj ((LocallyDiscrete.mk c,
              PUnit.unit) : Source)))).hom ≫
          (α_ (F.map fRaw) (F.map gRaw)
            (𝟙 ((inclusion.comp
              (generalLiftPseudofunctor F hF)).obj
              ((LocallyDiscrete.mk c, PUnit.unit) : Source)))).inv ≫
          (ρ_ (F.map fRaw ≫ F.map gRaw)).hom) =
        𝟙 _ := by
      bicategory
    change
      eComp.hom ≫ (F.mapComp fRaw gRaw).hom ≫
          (λ_ (F.map fRaw ≫ F.map gRaw)).inv = _ at h
    change eComp.inv ≫ _ = _
    change _ = _ ≫ _ ≫
      (ρ_ ((inclusion.comp
          (generalLiftPseudofunctor F hF)).map fRaw ≫
          (inclusion.comp
            (generalLiftPseudofunctor F hF)).map gRaw)).inv ≫
      (α_ ((inclusion.comp
          (generalLiftPseudofunctor F hF)).map fRaw)
        ((inclusion.comp
          (generalLiftPseudofunctor F hF)).map gRaw)
        (𝟙 ((inclusion.comp
          (generalLiftPseudofunctor F hF)).obj
          ((LocallyDiscrete.mk c, PUnit.unit) : Source)))).hom ≫
      (α_ ((inclusion.comp
          (generalLiftPseudofunctor F hF)).map fRaw)
        ((inclusion.comp
          (generalLiftPseudofunctor F hF)).map gRaw)
        (𝟙 (F.obj ((LocallyDiscrete.mk c,
          PUnit.unit) : Source)))).inv ≫
      (ρ_ ((inclusion.comp
          (generalLiftPseudofunctor F hF)).map fRaw ≫
          (inclusion.comp
            (generalLiftPseudofunctor F hF)).map gRaw)).hom ≫
      ePair.hom ≫
      (λ_ (F.map fRaw ≫ F.map gRaw)).inv at h
    change _ = (F.mapComp fRaw gRaw).hom ≫
      (ρ_ (F.map fRaw ≫ F.map gRaw)).inv ≫
      (α_ (F.map fRaw) (F.map gRaw)
        (𝟙 (F.obj ((LocallyDiscrete.mk c,
          PUnit.unit) : Source)))).hom ≫
      (α_ (F.map fRaw) (F.map gRaw)
        (𝟙 ((inclusion.comp
          (generalLiftPseudofunctor F hF)).obj
          ((LocallyDiscrete.mk c, PUnit.unit) : Source)))).inv ≫
      (ρ_ (F.map fRaw ≫ F.map gRaw)).hom ≫
      ePair.inv ≫
      (λ_ ((inclusion.comp
          (generalLiftPseudofunctor F hF)).map fRaw ≫
          (inclusion.comp
            (generalLiftPseudofunctor F hF)).map gRaw)).inv
    have hmiddleRTail := congrArg
      (fun k => k ≫ ePair.hom ≫
        (λ_ (F.map fRaw ≫ F.map gRaw)).inv)
      hmiddleR
    have hmiddleFTail := congrArg
      (fun k => k ≫ ePair.inv ≫
        (λ_ ((inclusion.comp
          (generalLiftPseudofunctor F hF)).map fRaw ≫
          (inclusion.comp
            (generalLiftPseudofunctor F hF)).map gRaw)).inv)
      hmiddleF
    simp only [Category.assoc, Category.id_comp] at hmiddleRTail hmiddleFTail
    rw [hmiddleRTail] at h
    rw [hmiddleFTail]
    have hAssoc := h
    simp only [← Category.assoc] at hAssoc
    have hcore := (cancel_mono
      (λ_ (F.map fRaw ≫ F.map gRaw)).inv).mp hAssoc
    have hcoreInv := congrArg
      (fun k => eComp.inv ≫ k ≫ ePair.inv) hcore
    simp only [Category.assoc] at hcoreInv
    simp at hcoreInv
    have hfinal := congrArg
      (fun k => k ≫
        (λ_ ((inclusion.comp
          (generalLiftPseudofunctor F hF)).map fRaw ≫
          (inclusion.comp
            (generalLiftPseudofunctor F hF)).map gRaw)).inv)
      hcoreInv.symm
    simp only [Category.assoc] at hfinal
    convert hfinal using 1 <;> simp [fRaw, gRaw]

/-- Every marking-inverting source pseudofunctor is adjoint equivalent to
the restriction of its general lift. -/
noncomputable def generalLiftFactorization
    (F : Pseudofunctor Source E) (hF : marking.IsInvertedBy F) :
    inclusion.comp (generalLiftPseudofunctor F hF) ≌ F :=
  Bicategory.Equivalence.mkOfAdjointifyCounit
    (Pseudofunctor.StrongTrans.isoMk
      (η := 𝟙 (inclusion.comp (generalLiftPseudofunctor F hF)))
      (θ := generalLiftFactorizationHom F hF ≫ generalLiftFactorizationInverse F hF)
      (fun X =>
        (ρ_ (𝟙 ((inclusion.comp
          (generalLiftPseudofunctor F hF)).obj X))).symm)
      (by
        intro a b f
        rcases a with ⟨⟨a⟩, a'⟩
        rcases b with ⟨⟨b⟩, b'⟩
        cases a'
        cases b'
        rcases f with ⟨⟨f⟩, A⟩
        let fRaw :
            ((LocallyDiscrete.mk a, PUnit.unit) : Source) ⟶
              ((LocallyDiscrete.mk b, PUnit.unit) : Source) :=
          (⟨f⟩, A)
        let e := eqToIso
          (eq_of_heq (generalLiftPseudofunctor_map_inclusion_heq F hF fRaw))
        have hforwardNat :
            (generalLiftFactorizationNaturality F hF fRaw).hom =
              (ρ_ ((inclusion.comp
                (generalLiftPseudofunctor F hF)).map fRaw)).hom ≫
              e.hom ≫ (λ_ (F.map fRaw)).inv := by
          dsimp [generalLiftFactorizationNaturality,
            generalLiftFactorizationNaturalityOfHEq, e]
          rfl
        have hinverseNat :
            (generalLiftFactorizationNaturalityInv F hF fRaw).hom =
              (ρ_ (F.map fRaw)).hom ≫ e.inv ≫
              (λ_ ((inclusion.comp
                (generalLiftPseudofunctor F hF)).map fRaw)).inv := by
          dsimp [generalLiftFactorizationNaturalityInv,
            generalLiftFactorizationNaturalityOfHEq, e]
          rfl
        simp only [fRaw] at hforwardNat hinverseNat
        have hcompNat :
            (((generalLiftFactorizationHom F hF ≫
              generalLiftFactorizationInverse F hF).naturality
                ((⟨f⟩, A) :
                  ((LocallyDiscrete.mk a, PUnit.unit) : Source) ⟶
                    ((LocallyDiscrete.mk b,
                      PUnit.unit) : Source))).hom) =
              (α_ ((inclusion.comp
                  (generalLiftPseudofunctor F hF)).map (⟨f⟩, A))
                (generalLiftFactorizationApp F hF
                  ((LocallyDiscrete.mk b, PUnit.unit) : Source))
                (generalLiftFactorizationAppInv F hF
                  ((LocallyDiscrete.mk b, PUnit.unit) : Source))).inv ≫
              (generalLiftFactorizationNaturality F hF (⟨f⟩, A)).hom ▷
                generalLiftFactorizationAppInv F hF
                  ((LocallyDiscrete.mk b, PUnit.unit) : Source) ≫
              (α_ (generalLiftFactorizationApp F hF
                  ((LocallyDiscrete.mk a, PUnit.unit) : Source))
                (F.map (⟨f⟩, A))
                (generalLiftFactorizationAppInv F hF
                  ((LocallyDiscrete.mk b, PUnit.unit) : Source))).hom ≫
              generalLiftFactorizationApp F hF
                  ((LocallyDiscrete.mk a, PUnit.unit) : Source) ◁
                (generalLiftFactorizationNaturalityInv F hF (⟨f⟩, A)).hom ≫
              (α_ (generalLiftFactorizationApp F hF
                  ((LocallyDiscrete.mk a, PUnit.unit) : Source))
                (generalLiftFactorizationAppInv F hF
                  ((LocallyDiscrete.mk a, PUnit.unit) : Source))
                ((inclusion.comp
                  (generalLiftPseudofunctor F hF)).map
                    (⟨f⟩, A))).inv := by
          rfl
        rw [hcompNat, hforwardNat, hinverseNat]
        simp [generalLiftFactorizationApp, generalLiftFactorizationAppInv]
        dsimp [fRaw] at e ⊢
        bicategory
        simp
        let mIso :=
          ((λ_ (F.map (⟨f⟩, A))).symm ≪≫
            (ρ_ (𝟙 (F.obj ((LocallyDiscrete.mk a,
              PUnit.unit) : Source)) ≫
              F.map (⟨f⟩, A))).symm) ≪≫
            α_ (𝟙 ((inclusion.comp
                (generalLiftPseudofunctor F hF)).obj
                ((LocallyDiscrete.mk a, PUnit.unit) : Source)))
              (F.map (⟨f⟩, A))
              (𝟙 (F.obj ((LocallyDiscrete.mk b,
                PUnit.unit) : Source))) ≪≫
            λ_ (F.map (⟨f⟩, A) ≫
              𝟙 (F.obj ((LocallyDiscrete.mk b,
                PUnit.unit) : Source))) ≪≫
            ρ_ (F.map (⟨f⟩, A))
        have hmiddle : mIso.hom = 𝟙 _ := by
          dsimp [mIso, Iso.trans]
          bicategory
        unfold mIso at hmiddle
        slice_lhs 3 3 => erw [hmiddle]
        let sIso :=
          ((λ_ ((inclusion.comp
              (generalLiftPseudofunctor F hF)).map (⟨f⟩, A))).symm ≪≫
            (λ_ (𝟙 ((inclusion.comp
                (generalLiftPseudofunctor F hF)).obj
                ((LocallyDiscrete.mk a, PUnit.unit) : Source)) ≫
              (inclusion.comp
                (generalLiftPseudofunctor F hF)).map (⟨f⟩, A))).symm) ≪≫
            (α_ (𝟙 ((inclusion.comp
                (generalLiftPseudofunctor F hF)).obj
                ((LocallyDiscrete.mk a, PUnit.unit) : Source)))
              (𝟙 (F.obj ((LocallyDiscrete.mk a,
                PUnit.unit) : Source)))
              ((inclusion.comp
                (generalLiftPseudofunctor F hF)).map (⟨f⟩, A))).symm
        have hcancelTail :
            e.hom ≫ 𝟙 _ ≫ e.inv ≫ sIso.hom = sIso.hom := by
          convert e.hom_inv_id_assoc sIso.hom using 1
          exact congrArg (fun k => e.hom ≫ k)
            (Category.id_comp (e.inv ≫ sIso.hom))
        unfold sIso at hcancelTail
        slice_lhs 2 3 => erw [hcancelTail]
        simp
        dsimp [Iso.trans]
        have hpure :
            (((inclusion.comp
                (generalLiftPseudofunctor F hF)).map (⟨f⟩, A) ◁ᵢ
              (ρ_ (𝟙 ((inclusion.comp
                (generalLiftPseudofunctor F hF)).obj
                ((LocallyDiscrete.mk b,
                  PUnit.unit) : Source)))).symm).hom ≫
              (α_ ((inclusion.comp
                  (generalLiftPseudofunctor F hF)).map (⟨f⟩, A))
                (𝟙 ((inclusion.comp
                  (generalLiftPseudofunctor F hF)).obj
                  ((LocallyDiscrete.mk b, PUnit.unit) : Source)))
                (𝟙 ((inclusion.comp
                  (generalLiftPseudofunctor F hF)).obj
                  ((LocallyDiscrete.mk b,
                    PUnit.unit) : Source)))).inv ≫
              (ρ_ ((inclusion.comp
                (generalLiftPseudofunctor F hF)).map (⟨f⟩, A) ≫
                𝟙 ((inclusion.comp
                  (generalLiftPseudofunctor F hF)).obj
                  ((LocallyDiscrete.mk b,
                    PUnit.unit) : Source)))).hom ≫
              (ρ_ ((inclusion.comp
                (generalLiftPseudofunctor F hF)).map (⟨f⟩, A))).hom) ≫
            ((λ_ ((inclusion.comp
                (generalLiftPseudofunctor F hF)).map (⟨f⟩, A))).inv ≫
              (λ_ (𝟙 ((inclusion.comp
                (generalLiftPseudofunctor F hF)).obj
                ((LocallyDiscrete.mk a, PUnit.unit) : Source)) ≫
                (inclusion.comp
                  (generalLiftPseudofunctor F hF)).map (⟨f⟩, A))).inv) ≫
              (α_ (𝟙 ((inclusion.comp
                  (generalLiftPseudofunctor F hF)).obj
                  ((LocallyDiscrete.mk a, PUnit.unit) : Source)))
                (𝟙 ((inclusion.comp
                  (generalLiftPseudofunctor F hF)).obj
                  ((LocallyDiscrete.mk a, PUnit.unit) : Source)))
                ((inclusion.comp
                  (generalLiftPseudofunctor F hF)).map (⟨f⟩, A))).inv =
              (ρ_ ((inclusion.comp
                (generalLiftPseudofunctor F hF)).map (⟨f⟩, A))).hom ≫
              (λ_ ((inclusion.comp
                (generalLiftPseudofunctor F hF)).map (⟨f⟩, A))).inv ≫
              (ρ_ (𝟙 ((inclusion.comp
                (generalLiftPseudofunctor F hF)).obj
                ((LocallyDiscrete.mk a,
                  PUnit.unit) : Source)))).inv ▷
                (inclusion.comp
                  (generalLiftPseudofunctor F hF)).map (⟨f⟩, A) := by
          dsimp [Iso.trans, whiskerLeftIso, whiskerRightIso]
          bicategory
        convert hpure using 1
        all_goals rfl))
    (Pseudofunctor.StrongTrans.isoMk
      (η := generalLiftFactorizationInverse F hF ≫ generalLiftFactorizationHom F hF)
      (θ := 𝟙 F)
      (fun X => ρ_ (𝟙 (F.obj X)))
      (by
        intro a b f
        rcases a with ⟨⟨a⟩, a'⟩
        rcases b with ⟨⟨b⟩, b'⟩
        cases a'
        cases b'
        rcases f with ⟨⟨f⟩, A⟩
        let fRaw :
            ((LocallyDiscrete.mk a, PUnit.unit) : Source) ⟶
              ((LocallyDiscrete.mk b, PUnit.unit) : Source) :=
          (⟨f⟩, A)
        let e := eqToIso
          (eq_of_heq (generalLiftPseudofunctor_map_inclusion_heq F hF fRaw))
        have hforwardNat :
            (generalLiftFactorizationNaturality F hF fRaw).hom =
              (ρ_ ((inclusion.comp
                (generalLiftPseudofunctor F hF)).map fRaw)).hom ≫
              e.hom ≫ (λ_ (F.map fRaw)).inv := by
          dsimp [generalLiftFactorizationNaturality,
            generalLiftFactorizationNaturalityOfHEq, e]
          rfl
        have hinverseNat :
            (generalLiftFactorizationNaturalityInv F hF fRaw).hom =
              (ρ_ (F.map fRaw)).hom ≫ e.inv ≫
              (λ_ ((inclusion.comp
                (generalLiftPseudofunctor F hF)).map fRaw)).inv := by
          dsimp [generalLiftFactorizationNaturalityInv,
            generalLiftFactorizationNaturalityOfHEq, e]
          rfl
        simp only [fRaw] at hforwardNat hinverseNat
        have hcompNat :
            (((generalLiftFactorizationInverse F hF ≫
              generalLiftFactorizationHom F hF).naturality
                ((⟨f⟩, A) :
                  ((LocallyDiscrete.mk a, PUnit.unit) : Source) ⟶
                    ((LocallyDiscrete.mk b,
                      PUnit.unit) : Source))).hom) =
              (α_ (F.map (⟨f⟩, A))
                (generalLiftFactorizationAppInv F hF
                  ((LocallyDiscrete.mk b, PUnit.unit) : Source))
                (generalLiftFactorizationApp F hF
                  ((LocallyDiscrete.mk b, PUnit.unit) : Source))).inv ≫
              (generalLiftFactorizationNaturalityInv F hF (⟨f⟩, A)).hom ▷
                generalLiftFactorizationApp F hF
                  ((LocallyDiscrete.mk b, PUnit.unit) : Source) ≫
              (α_ (generalLiftFactorizationAppInv F hF
                  ((LocallyDiscrete.mk a, PUnit.unit) : Source))
                ((inclusion.comp
                  (generalLiftPseudofunctor F hF)).map (⟨f⟩, A))
                (generalLiftFactorizationApp F hF
                  ((LocallyDiscrete.mk b, PUnit.unit) : Source))).hom ≫
              generalLiftFactorizationAppInv F hF
                  ((LocallyDiscrete.mk a, PUnit.unit) : Source) ◁
                (generalLiftFactorizationNaturality F hF (⟨f⟩, A)).hom ≫
              (α_ (generalLiftFactorizationAppInv F hF
                  ((LocallyDiscrete.mk a, PUnit.unit) : Source))
                (generalLiftFactorizationApp F hF
                  ((LocallyDiscrete.mk a, PUnit.unit) : Source))
                (F.map (⟨f⟩, A))).inv := by
          rfl
        rw [hcompNat, hinverseNat, hforwardNat]
        simp [generalLiftFactorizationApp, generalLiftFactorizationAppInv]
        dsimp [fRaw] at e ⊢
        bicategory
        simp
        let mIso :=
          ((λ_ ((inclusion.comp
              (generalLiftPseudofunctor F hF)).map (⟨f⟩, A))).symm ≪≫
            (ρ_ (𝟙 ((inclusion.comp
                (generalLiftPseudofunctor F hF)).obj
                ((LocallyDiscrete.mk a, PUnit.unit) : Source)) ≫
              (inclusion.comp
                (generalLiftPseudofunctor F hF)).map (⟨f⟩, A))).symm) ≪≫
            α_ (𝟙 (F.obj ((LocallyDiscrete.mk a,
                PUnit.unit) : Source)))
              ((inclusion.comp
                (generalLiftPseudofunctor F hF)).map (⟨f⟩, A))
              (𝟙 ((inclusion.comp
                (generalLiftPseudofunctor F hF)).obj
                ((LocallyDiscrete.mk b, PUnit.unit) : Source))) ≪≫
            λ_ ((inclusion.comp
              (generalLiftPseudofunctor F hF)).map (⟨f⟩, A) ≫
              𝟙 ((inclusion.comp
                (generalLiftPseudofunctor F hF)).obj
                ((LocallyDiscrete.mk b, PUnit.unit) : Source))) ≪≫
            ρ_ ((inclusion.comp
              (generalLiftPseudofunctor F hF)).map (⟨f⟩, A))
        have hmiddle : mIso.hom = 𝟙 _ := by
          dsimp [mIso, Iso.trans]
          bicategory
        unfold mIso at hmiddle
        slice_rhs 3 3 => erw [hmiddle]
        let sIso :=
          (((λ_ (F.map (⟨f⟩, A))).symm ≪≫
            (λ_ (𝟙 (F.obj ((LocallyDiscrete.mk a,
                PUnit.unit) : Source)) ≫
              F.map (⟨f⟩, A))).symm) ≪≫
            (α_ (𝟙 (F.obj ((LocallyDiscrete.mk a,
                PUnit.unit) : Source)))
              (𝟙 ((inclusion.comp
                (generalLiftPseudofunctor F hF)).obj
                ((LocallyDiscrete.mk a, PUnit.unit) : Source)))
              (F.map (⟨f⟩, A))).symm) ≪≫
            (ρ_ (𝟙 (F.obj ((LocallyDiscrete.mk a,
              PUnit.unit) : Source)))) ▷ᵢ F.map (⟨f⟩, A)
        have hcancelTail :
            e.inv ≫ 𝟙 _ ≫ e.hom ≫ sIso.hom = sIso.hom := by
          exact (congrArg (fun k => e.inv ≫ k)
            (Category.id_comp (e.hom ≫ sIso.hom))).trans
              (e.inv_hom_id_assoc sIso.hom)
        unfold sIso at hcancelTail
        slice_rhs 2 3 => erw [hcancelTail]
        simp
        dsimp [Iso.trans, whiskerLeftIso, whiskerRightIso]
        let ff := F.map (⟨f⟩, A)
        let ia := 𝟙 (F.obj ((LocallyDiscrete.mk a,
          PUnit.unit) : Source))
        let ib := 𝟙 (F.obj ((LocallyDiscrete.mk b,
          PUnit.unit) : Source))
        have hpure :
            (α_ ff ib ib).inv ≫ (ρ_ (ff ≫ ib)).hom ≫
                (ρ_ ff).hom ≫ (λ_ ff).inv =
              ((α_ ff ib ib).inv ≫ (ρ_ (ff ≫ ib)).hom ≫
                (ρ_ ff).hom) ≫
              (((λ_ ff).inv ≫ (λ_ (ia ≫ ff)).inv) ≫
                (α_ ia ia ff).inv) ≫
              (ρ_ ia).hom ▷ ff := by
          dsimp [ff, ia, ib]
          bicategory
        convert hpure using 1
        all_goals rfl))

/-- Every pseudofunctor that inverts the walking marking factors through the
completion up to adjoint equivalence. -/
theorem generalLiftFactorsThrough
    (F : Pseudofunctor Source E) (hF : marking.IsInvertedBy F) :
    inclusion.FactorsThrough F :=
  ⟨generalLiftPseudofunctor F hF,
    ⟨generalLiftFactorization F hF⟩⟩

/-- The two-dimensional walking inclusion is a bicategorical localization:
it inverts the marking, admits all marking-inverting lifts, and induces
equivalences on strong transformations and modifications. -/
theorem inclusion_isBicategoricalLocalization :
    marking.IsBicategoricalLocalization inclusion where
  inverts := inclusion_inverts
  lift _E _ F hF := generalLiftFactorsThrough F hF
  local_equivalence _E _ F G :=
    inclusion_localPrecomposition_isEquivalence F G

/-! ## Locally thin target packaging -/

section LocallyThinTarget

variable [∀ (a b : E) (f g : a ⟶ b), Subsingleton (f ⟶ g)]

/-- In a locally thin target bicategory, compositor associativity is also the
unique 2-cell equality; this is retained as the short proof underlying the
historical specialized packaging. -/
theorem generalLiftMapComp_associativity_of_locallyThin
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {W X Y Z : Target} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (generalLiftPrelaxFunctor F hF).map₂ (α_ f g h).hom ≫
        (generalLiftMapComp F hF f (g ≫ h)).hom ≫
        (generalLiftPrelaxFunctor F hF).map f ◁
          (generalLiftMapComp F hF g h).hom =
      (generalLiftMapComp F hF (f ≫ g) h).hom ≫
        (generalLiftMapComp F hF f g).hom ▷
          (generalLiftPrelaxFunctor F hF).map h ≫
        (α_ ((generalLiftPrelaxFunctor F hF).map f)
          ((generalLiftPrelaxFunctor F hF).map g)
          ((generalLiftPrelaxFunctor F hF).map h)).hom := by
  apply Subsingleton.elim

/-- Specialized locally thin packaging of the arbitrary lift.  The general
construction above no longer requires this extra hypothesis. -/
noncomputable def generalLiftLocallyThinPseudofunctor
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) : Target ⥤ᵖ E where
  toPrelaxFunctor := generalLiftPrelaxFunctor F hF
  mapId := generalLiftMapId F hF
  mapComp := generalLiftMapComp F hF
  map₂_whisker_left := by
    intro a b c f g h η
    apply Subsingleton.elim
  map₂_whisker_right := by
    intro a b c f g η h
    apply Subsingleton.elim
  map₂_associator := by
    intro a b c d f g h
    apply Subsingleton.elim
  map₂_left_unitor := by
    intro a b f
    apply Subsingleton.elim
  map₂_right_unitor := by
    intro a b f
    apply Subsingleton.elim

/-- The locally thin pseudofunctor has exactly the already-constructed
arbitrary lift as its underlying prelax action. -/
theorem generalLiftLocallyThinPseudofunctor_toPrelaxFunctor
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) :
    (generalLiftLocallyThinPseudofunctor F hF).toPrelaxFunctor =
      generalLiftPrelaxFunctor F hF :=
  rfl

/-- After precomposition by the walking inclusion, the locally thin lift maps
every source arrow exactly as the original pseudofunctor. -/
theorem generalLiftLocallyThinPseudofunctor_map_inclusion
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F)
    {X Y : Source} (f : X ⟶ Y) :
    (generalLiftLocallyThinPseudofunctor F hF).map (inclusion.map f) =
      F.map f := by
  rcases X with ⟨⟨X⟩, X'⟩
  rcases Y with ⟨⟨Y⟩, Y'⟩
  cases X'
  cases Y'
  rcases f with ⟨⟨f⟩, A⟩
  exact generalLiftPrelaxFunctor_map_forward F hF f A

/-- The locally thin lift and the original source pseudofunctor agree on
objects after precomposition. -/
theorem generalLiftLocallyThinPseudofunctor_obj_inclusion
    (F : Source ⥤ᵖ E) (hF : marking.IsInvertedBy F) (X : Source) :
    (inclusion.comp (generalLiftLocallyThinPseudofunctor F hF)).obj X =
      F.obj X := by
  rcases X with ⟨⟨X⟩, X'⟩
  cases X'
  rfl

end LocallyThinTarget

end ArbitraryLiftPrelaxAction

end Ript.Examples.TwoDimensionalWalkingLocalization
