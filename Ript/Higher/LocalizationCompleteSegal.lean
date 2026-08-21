import Ript.Higher.Localization
import Ript.Higher.TotalModelCompleteSegal

/-!
# Cost-exact localization comparison for Rezk core diagrams

The ordinary cost-exact localization of the model homotopy category induces
a natural map of Rezk core diagrams.  This file balances the source and target
universes with `AsSmall`, constructs that bisimplicial comparison, and proves
that every marked arrow lands in the actual equivalence-arrow subspace of the
localized Rezk diagram.

This comparison is deliberately precise about its scope: the ordinary
localization has already discarded noninvertible bicategorical 2-cells.  Those
remain present in `HigherCompleteSegalCore` through the full local mapping
nerves; the construction here supplies the localization/Rezk outer layer to
which that retained local layer must ultimately be compared.
-/

set_option autoImplicit false
set_option linter.checkUnivs false
set_option linter.style.haveILetI false

namespace Ript.Higher.CostExactRezkComparison

open CategoryTheory

universe u v w

variable {R : Type w} [AddCommMonoid R] [PartialOrder R]

/-- Universe-balanced model homotopy category used as the source Rezk index. -/
abbrev SmallSource :=
  AsSmall.{0} (ModelHomotopyCategory.{u, v, w} R)

/-- Universe-balanced cost-exact localization used as the target Rezk index. -/
abbrev SmallTarget :=
  AsSmall.{0} (CostExactLocalization.{u, v, w} R)

/-- The cost-exact localization functor transported between the balanced
small categories. -/
noncomputable def smallLocalizationFunctor :
    SmallSource.{u, v, w} (R := R) ⥤ SmallTarget.{u, v, w} (R := R) :=
  AsSmall.down ⋙ costExactLocalizationFunctor R ⋙ AsSmall.up

/-- The induced natural comparison of Rezk core diagrams. -/
noncomputable def comparison :
    RezkCore.diagram (SmallSource.{u, v, w} (R := R)) ⟶
      RezkCore.diagram (SmallTarget.{u, v, w} (R := R)) :=
  RezkCore.diagramMap (SmallSource.{u, v, w} (R := R))
    (smallLocalizationFunctor (R := R))

/-- The cost-exact marking transported to the balanced source category. -/
def smallMarking : MorphismProperty
    (SmallSource.{u, v, w} (R := R)) :=
  (costExactMorphisms R).inverseImage AsSmall.down

/-- The balanced localization functor sends every transported marked arrow to
an isomorphism. -/
theorem smallLocalizationInverts :
    (smallMarking (R := R)).IsInvertedBy
      (smallLocalizationFunctor (R := R)) := by
  intro X Y f hf
  change IsIso (AsSmall.up.map
    ((costExactLocalizationFunctor R).map (AsSmall.down.map f)))
  haveI : IsIso ((costExactLocalizationFunctor R).map
      (AsSmall.down.map f)) :=
    costExactLocalizationFunctor_inverts (AsSmall.down.map f) hf
  infer_instance

/-- The target actual-equivalence vertex represented by one marked source
arrow after localization. -/
noncomputable def markedTargetVertex
    {X Y : SmallSource.{u, v, w} (R := R)}
    (f : X ⟶ Y) (hf : smallMarking (R := R) f) :
    (RezkCore.actualEquivalenceSpace
      (SmallTarget.{u, v, w} (R := R))).obj
        (Opposite.op (SimplexCategory.mk 0)) := by
  letI : IsIso ((smallLocalizationFunctor (R := R)).map f) :=
    smallLocalizationInverts (R := R) f hf
  exact RezkCore.actualEquivalenceVertexOfIso
    (SmallTarget.{u, v, w} (R := R))
    ((smallLocalizationFunctor (R := R)).map f)

/-- On a marked arrow, the Rezk localization comparison factors strictly
through the target's actual equivalence-arrow subspace. -/
theorem markedArrowFactorsThroughActualEquivalences
    {X Y : SmallSource.{u, v, w} (R := R)}
    (f : X ⟶ Y) (hf : smallMarking (R := R) f) :
    ((comparison (R := R)).app
        (Opposite.op (SimplexCategory.mk 1))).app
          (Opposite.op (SimplexCategory.mk 0))
          (RezkCore.arrowVertex
            (SmallSource.{u, v, w} (R := R)) f) =
      (RezkCore.actualEquivalenceSpaceInclusion
        (SmallTarget.{u, v, w} (R := R))).app
          (Opposite.op (SimplexCategory.mk 0))
          (markedTargetVertex (R := R) f hf) := by
  letI : IsIso ((smallLocalizationFunctor (R := R)).map f) :=
    smallLocalizationInverts (R := R) f hf
  change (((RezkCore.diagramMap
      (SmallSource.{u, v, w} (R := R))
      (smallLocalizationFunctor (R := R))).app
        (Opposite.op (SimplexCategory.mk 1))).app
          (Opposite.op (SimplexCategory.mk 0))
          (RezkCore.arrowVertex
            (SmallSource.{u, v, w} (R := R)) f)) =
    (RezkCore.actualEquivalenceSpaceInclusion
      (SmallTarget.{u, v, w} (R := R))).app
        (Opposite.op (SimplexCategory.mk 0))
        (RezkCore.actualEquivalenceVertexOfIso
          (SmallTarget.{u, v, w} (R := R))
          ((smallLocalizationFunctor (R := R)).map f))
  rw [RezkCore.diagramMap_arrowVertex]
  rw [RezkCore.actualEquivalenceSpaceInclusion_vertexOfIso]

/-- Machine-facing package for the ordinary cost-exact localization/Rezk
comparison and its marked-arrow inversion law. -/
structure ComparisonCore where
  /-- Natural map of the balanced source and target Rezk diagrams. -/
  map : RezkCore.diagram (SmallSource.{u, v, w} (R := R)) ⟶
    RezkCore.diagram (SmallTarget.{u, v, w} (R := R))
  /-- The map is the canonical functorial Rezk comparison. -/
  map_eq : map = comparison (R := R)
  /-- The balanced localization functor inverts the transported marking. -/
  inverts : (smallMarking.{u, v, w} (R := R)).IsInvertedBy
    (smallLocalizationFunctor.{u, v, w} (R := R))
  /-- Every marked outer one-arrow vertex lands in the target actual
  equivalence-arrow subspace. -/
  markedFactorization : ∀
      {X Y : SmallSource.{u, v, w} (R := R)}
      (f : X ⟶ Y) (hf : smallMarking.{u, v, w} (R := R) f),
    (map.app (Opposite.op (SimplexCategory.mk 1))).app
        (Opposite.op (SimplexCategory.mk 0))
        (RezkCore.arrowVertex
          (SmallSource.{u, v, w} (R := R)) f) =
      (RezkCore.actualEquivalenceSpaceInclusion
        (SmallTarget.{u, v, w} (R := R))).app
        (Opposite.op (SimplexCategory.mk 0))
        (markedTargetVertex.{u, v, w} (R := R) f hf)

attribute [nolint simpNF] ComparisonCore.mk.injEq

/-- Package the canonical cost-exact Rezk comparison. -/
noncomputable def core : ComparisonCore.{u, v, w} (R := R) where
  map := comparison (R := R)
  map_eq := rfl
  inverts := smallLocalizationInverts (R := R)
  markedFactorization := markedArrowFactorsThroughActualEquivalences

end Ript.Higher.CostExactRezkComparison

namespace Ript.Higher.BicategoricalNerveComparison

open CategoryTheory
open CategoryTheory.Bicategory
open Opposite Simplicial

universe u v w

variable {B C : Type u}
  [Bicategory.{w, max v w} B] [Bicategory.{w, max v w} C]

/-- The horizontal-composition functor of an arbitrary locally
universe-balanced bicategory.  Its morphism action is simultaneous
horizontal composition of 2-cells. -/
def horizontalCompositionFunctor (X Y Z : B) :
    ((X ⟶ Y) × (Y ⟶ Z)) ⥤ (X ⟶ Z) where
  obj pair := pair.1 ≫ pair.2
  map := @fun first second transformation =>
    first.1 ◁ transformation.2 ≫ transformation.1 ▷ second.2
  map_id pair := by simp
  map_comp := @fun first second third firstTransformation
      secondTransformation => by
    change
      first.1 ◁ (firstTransformation.2 ≫ secondTransformation.2) ≫
          (firstTransformation.1 ≫ secondTransformation.1) ▷ third.2 =
        (first.1 ◁ firstTransformation.2 ≫
            firstTransformation.1 ▷ second.2) ≫
          (second.1 ◁ secondTransformation.2 ≫
            secondTransformation.1 ▷ third.2)
    symm
    simp only [Category.assoc]
    rw [← whisker_exchange_assoc firstTransformation.1 secondTransformation.2,
      ← whiskerLeft_comp_assoc, ← comp_whiskerRight]

variable (Q : B ⥤ᵖ C)

/-- The full local mapping nerve of an arbitrary bicategory.  Its vertices
are 1-cells and its edges are all 2-cells, without groupoid truncation. -/
abbrev LocalMappingNerve (X Y : B) := CategoryTheory.nerve (X ⟶ Y)

/-- A pseudofunctor induces a simplicial map on every full local mapping
nerve by applying its hom-category functor. -/
def localMap (X Y : B) :
    LocalMappingNerve X Y ⟶ LocalMappingNerve (Q.obj X) (Q.obj Y) :=
  CategoryTheory.nerveMap (Q.mapFunctor X Y)

/-- The local nerve comparison sends a 1-cell vertex to its pseudofunctor
image exactly. -/
@[simp]
theorem localMap_vertex {X Y : B} (f : X ⟶ Y) :
    (localMap Q X Y).app (op ⦋0⦌) (ComposableArrows.mk₀ f) =
      ComposableArrows.mk₀ (Q.map f) :=
  CategoryTheory.nerveMap_app_mk₀ _ _

/-- The local nerve comparison sends an arbitrary, possibly noninvertible,
2-cell edge to its pseudofunctor image exactly. -/
@[simp]
theorem localMap_twoCell {X Y : B} {f g : X ⟶ Y} (α : f ⟶ g) :
    (localMap Q X Y).app (op ⦋1⦌) (ComposableArrows.mk₁ α) =
      ComposableArrows.mk₁ (Q.map₂ α) :=
  CategoryTheory.nerveMap_app_mk₁ _ _

/-- The local nerve comparison sends a vertically composable pair of
2-cells to the canonical 2-simplex of their exact images. -/
@[simp]
theorem localMap_twoSimplex {X Y : B} {f g h : X ⟶ Y}
    (α : f ⟶ g) (β : g ⟶ h) :
    (localMap Q X Y).app (op ⦋2⦌) (ComposableArrows.mk₂ α β) =
      ComposableArrows.mk₂ (Q.map₂ α) (Q.map₂ β) :=
  CategoryTheory.nerveMap_app_mk₂ _ _ _

/-- The constant diagram selecting the image of a source identity. -/
def mappedIdentityFunctor (X : B) :
    (X ⟶ X) ⥤ (Q.obj X ⟶ Q.obj X) :=
  (Functor.const (X ⟶ X)).obj (Q.map (𝟙 X))

/-- The constant diagram selecting the target identity. -/
def targetIdentityFunctor (X : B) :
    (X ⟶ X) ⥤ (Q.obj X ⟶ Q.obj X) :=
  (Functor.const (X ⟶ X)).obj (𝟙 (Q.obj X))

/-- The pseudofunctor unit constraint is a natural isomorphism between the
mapped source-identity diagram and the target-identity diagram. -/
noncomputable def identityComparisonNatIso (X : B) :
    mappedIdentityFunctor Q X ≅ targetIdentityFunctor Q X :=
  (Functor.const (X ⟶ X)).mapIso (Q.mapId X)

/-- The pseudofunctor unit constraint induces a genuine simplicial homotopy
between the two identity-vertex maps in every simplicial degree. -/
noncomputable def identityComparisonNerveHomotopy (X : B) :
    SSet.Homotopy
      (CategoryTheory.nerveMap (mappedIdentityFunctor Q X))
      (CategoryTheory.nerveMap (targetIdentityFunctor Q X)) :=
  CategoryTheory.NerveHomotopy.ofNatTrans
    (identityComparisonNatIso Q X).hom

/-- First compose two source 1-cells and then apply the pseudofunctor. -/
def composeThenMapFunctor (X Y Z : B) :
    ((X ⟶ Y) × (Y ⟶ Z)) ⥤ (Q.obj X ⟶ Q.obj Z) :=
  horizontalCompositionFunctor X Y Z ⋙ Q.mapFunctor X Z

/-- First apply the pseudofunctor to two source 1-cells and then compose in
the target bicategory. -/
def mapThenComposeFunctor (X Y Z : B) :
    ((X ⟶ Y) × (Y ⟶ Z)) ⥤ (Q.obj X ⟶ Q.obj Z) :=
  (Q.mapFunctor X Y).prod (Q.mapFunctor Y Z) ⋙
    horizontalCompositionFunctor (Q.obj X) (Q.obj Y) (Q.obj Z)

/-- The pseudofunctor compositor is natural in both 1-cells and hence gives
a natural isomorphism between compose-then-map and map-then-compose. -/
noncomputable def compositionComparisonNatIso (X Y Z : B) :
    composeThenMapFunctor Q X Y Z ≅ mapThenComposeFunctor Q X Y Z :=
  NatIso.ofComponents
    (fun pair => Q.mapComp pair.1 pair.2)
    (fun {first second} transformation => by
      rcases transformation with ⟨left, right⟩
      change Q.map₂ (first.1 ◁ right ≫ left ▷ second.2) ≫
          (Q.mapComp second.1 second.2).hom =
        (Q.mapComp first.1 first.2).hom ≫
          (Q.map first.1 ◁ Q.map₂ right ≫ Q.map₂ left ▷ Q.map second.2)
      simp only [PrelaxFunctor.map₂_comp, Category.assoc,
        Q.map₂_whisker_left, Q.map₂_whisker_right]
      simp)

/-- The compositor natural isomorphism induces an actual simplicial homotopy
between the two full-local-nerve composition maps. -/
noncomputable def compositionComparisonNerveHomotopy (X Y Z : B) :
    SSet.Homotopy
      (CategoryTheory.nerveMap (composeThenMapFunctor Q X Y Z))
      (CategoryTheory.nerveMap (mapThenComposeFunctor Q X Y Z)) :=
  CategoryTheory.NerveHomotopy.ofNatTrans
    (compositionComparisonNatIso Q X Y Z).hom

/-- Exact associator coherence underlying the compositor nerve homotopies. -/
theorem associatorCompatibility
    {A B₁ C₁ D : B} (f : A ⟶ B₁) (g : B₁ ⟶ C₁)
    (h : C₁ ⟶ D) :
    Q.map₂ (α_ f g h).hom =
      (Q.mapComp (f ≫ g) h).hom ≫
        (Q.mapComp f g).hom ▷ Q.map h ≫
          (α_ (Q.map f) (Q.map g) (Q.map h)).hom ≫
            Q.map f ◁ (Q.mapComp g h).inv ≫
              (Q.mapComp f (g ≫ h)).inv :=
  Q.map₂_associator f g h

/-- Exact left-unitor coherence underlying the unit and compositor nerve
homotopies. -/
theorem leftUnitorCompatibility
    {A B₁ : B} (f : A ⟶ B₁) :
    Q.map₂ (λ_ f).hom =
      (Q.mapComp (𝟙 A) f).hom ≫
        (Q.mapId A).hom ▷ Q.map f ≫ (λ_ (Q.map f)).hom :=
  Q.map₂_left_unitor f

/-- Exact right-unitor coherence underlying the unit and compositor nerve
homotopies. -/
theorem rightUnitorCompatibility
    {A B₁ : B} (f : A ⟶ B₁) :
    Q.map₂ (ρ_ f).hom =
      (Q.mapComp f (𝟙 B₁)).hom ≫
        Q.map f ◁ (Q.mapId B₁).hom ≫ (ρ_ (Q.map f)).hom :=
  Q.map₂_right_unitor f

variable (W : Bicategory.MorphismProperty B)

/-- Universe-explicit bicategorical localization predicate used by the local
nerve comparison.  The destination quantified by the universal property is
kept in the same locally balanced universe. -/
abbrev IsHigherLocalization : Prop :=
  Bicategory.MorphismProperty.IsBicategoricalLocalization.{
    u, max v w, w, u, max v w, w, u, max v w, w} W Q

/-- A marked arrow acquires a chosen adjoint equivalence after any genuine
bicategorical localization.  Choice is confined to the proof-level
equivalence witness. -/
noncomputable def markedEquivalence
    (hQ : IsHigherLocalization Q W)
    {X Y : B} (f : X ⟶ Y) (hf : W f) : Q.obj X ≌ Q.obj Y :=
  (Classical.choice (hQ.inverts f hf)).1

/-- The chosen marked equivalence has exactly the localized arrow as its
forward 1-cell. -/
@[simp]
theorem markedEquivalence_hom
    (hQ : IsHigherLocalization Q W)
    {X Y : B} (f : X ⟶ Y) (hf : W f) :
    (markedEquivalence Q W hQ f hf).hom = Q.map f :=
  (Classical.choice (hQ.inverts f hf)).2

/-- On marked vertices, the full local nerve comparison lands exactly at the
forward 1-cell of the chosen target adjoint equivalence. -/
theorem localMap_markedVertex
    (hQ : IsHigherLocalization Q W)
    {X Y : B} (f : X ⟶ Y) (hf : W f) :
    (localMap Q X Y).app (op ⦋0⦌) (ComposableArrows.mk₀ f) =
      ComposableArrows.mk₀ (markedEquivalence Q W hQ f hf).hom := by
  rw [localMap_vertex, markedEquivalence_hom]

/-- Machine-facing package for the full local-nerve action of a
pseudofunctor, including its exact 1-cell and 2-cell action, unit/compositor
homotopies, and associator/unitor coherence. -/
structure PseudofunctorNerveCore where
  /-- Simplicial map on every full local mapping nerve. -/
  localMap : ∀ X Y : B,
    LocalMappingNerve X Y ⟶ LocalMappingNerve (Q.obj X) (Q.obj Y)
  /-- The packaged local maps are the canonical nerve maps. -/
  localMap_eq : localMap = BicategoricalNerveComparison.localMap Q
  /-- Exact action on 1-cell vertices. -/
  mapsVertex : ∀ {X Y : B} (f : X ⟶ Y),
    (localMap X Y).app (op ⦋0⦌) (ComposableArrows.mk₀ f) =
      ComposableArrows.mk₀ (Q.map f)
  /-- Exact action on arbitrary 2-cell edges. -/
  mapsTwoCell : ∀ {X Y : B} {f g : X ⟶ Y} (α : f ⟶ g),
    (localMap X Y).app (op ⦋1⦌) (ComposableArrows.mk₁ α) =
      ComposableArrows.mk₁ (Q.map₂ α)
  /-- Exact action on canonical 2-simplices of vertically composable
  2-cells. -/
  mapsTwoSimplex : ∀ {X Y : B} {f g h : X ⟶ Y}
    (α : f ⟶ g) (β : g ⟶ h),
    (localMap X Y).app (op ⦋2⦌) (ComposableArrows.mk₂ α β) =
      ComposableArrows.mk₂ (Q.map₂ α) (Q.map₂ β)
  /-- Natural compositor isomorphism on local categories. -/
  compositionIso : ∀ X Y Z : B,
    composeThenMapFunctor Q X Y Z ≅ mapThenComposeFunctor Q X Y Z
  /-- Natural unit isomorphism on local identity diagrams. -/
  identityIso : ∀ X : B,
    mappedIdentityFunctor Q X ≅ targetIdentityFunctor Q X
  /-- Genuine simplicial unit homotopy on local nerves. -/
  identityHomotopy : ∀ X : B,
    SSet.Homotopy
      (CategoryTheory.nerveMap (mappedIdentityFunctor Q X))
      (CategoryTheory.nerveMap (targetIdentityFunctor Q X))
  /-- Genuine simplicial compositor homotopy on local nerves. -/
  compositionHomotopy : ∀ X Y Z : B,
    SSet.Homotopy
      (CategoryTheory.nerveMap (composeThenMapFunctor Q X Y Z))
      (CategoryTheory.nerveMap (mapThenComposeFunctor Q X Y Z))
  /-- Exact associator coherence between the local maps and compositor
  homotopies. -/
  associatorCoherence : ∀ {A B₁ C₁ D : B}
    (f : A ⟶ B₁) (g : B₁ ⟶ C₁) (h : C₁ ⟶ D),
    Q.map₂ (α_ f g h).hom =
      (Q.mapComp (f ≫ g) h).hom ≫
        (Q.mapComp f g).hom ▷ Q.map h ≫
          (α_ (Q.map f) (Q.map g) (Q.map h)).hom ≫
            Q.map f ◁ (Q.mapComp g h).inv ≫
              (Q.mapComp f (g ≫ h)).inv
  /-- Exact left-unitor coherence between the unit and compositor
  homotopies. -/
  leftUnitorCoherence : ∀ {A B₁ : B} (f : A ⟶ B₁),
    Q.map₂ (λ_ f).hom =
      (Q.mapComp (𝟙 A) f).hom ≫
        (Q.mapId A).hom ▷ Q.map f ≫ (λ_ (Q.map f)).hom
  /-- Exact right-unitor coherence between the unit and compositor
  homotopies. -/
  rightUnitorCoherence : ∀ {A B₁ : B} (f : A ⟶ B₁),
    Q.map₂ (ρ_ f).hom =
      (Q.mapComp f (𝟙 B₁)).hom ≫
        Q.map f ◁ (Q.mapId B₁).hom ≫ (ρ_ (Q.map f)).hom

/-- Package the canonical full-local-nerve action of a pseudofunctor. -/
noncomputable def pseudofunctorNerveCore : PseudofunctorNerveCore Q where
  localMap := localMap Q
  localMap_eq := rfl
  mapsVertex := localMap_vertex Q
  mapsTwoCell := localMap_twoCell Q
  mapsTwoSimplex := localMap_twoSimplex Q
  compositionIso := compositionComparisonNatIso Q
  identityIso := identityComparisonNatIso Q
  identityHomotopy := identityComparisonNerveHomotopy Q
  compositionHomotopy := compositionComparisonNerveHomotopy Q
  associatorCoherence := associatorCompatibility Q
  leftUnitorCoherence := leftUnitorCompatibility Q
  rightUnitorCoherence := rightUnitorCompatibility Q

/-- Machine-facing higher-localization comparison: the coherent full local
nerve action is bundled with the bicategorical universal property and exact
marked-vertex inversion. -/
structure HigherLocalizationNerveCore extends PseudofunctorNerveCore Q where
  /-- The underlying pseudofunctor satisfies the full 2-dimensional
  localization universal property. -/
  localization : IsHigherLocalization Q W
  /-- Every marked source vertex maps to the chosen target equivalence. -/
  markedVertex : ∀ {X Y : B} (f : X ⟶ Y) (hf : W f),
    (toPseudofunctorNerveCore.localMap X Y).app (op ⦋0⦌)
        (ComposableArrows.mk₀ f) =
      ComposableArrows.mk₀ (markedEquivalence Q W localization f hf).hom

attribute [nolint simpNF] PseudofunctorNerveCore.mk.injEq
  HigherLocalizationNerveCore.mk.injEq

/-- Every genuine locally universe-balanced bicategorical localization
canonically supplies the full higher local-nerve comparison package. -/
noncomputable def higherLocalizationNerveCore
    (hQ : IsHigherLocalization Q W) :
    HigherLocalizationNerveCore Q W where
  toPseudofunctorNerveCore := pseudofunctorNerveCore Q
  localization := hQ
  markedVertex := localMap_markedVertex Q W hQ

end Ript.Higher.BicategoricalNerveComparison
