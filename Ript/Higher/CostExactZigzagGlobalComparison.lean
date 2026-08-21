import Ript.ForMathlib.CategoryTheory.Bicategory.PseudofunctorHomotopy
import Ript.Higher.CostExactZigzagNerveComparison
import Ript.Higher.RelativeRezk

/-!
# Global two-layer comparison for the cost-exact higher localization

The actual marked-zigzag localization induces a localization-aware relative
Rezk map whose vertical source transformations are pointwise cost-exact. It
also induces an auxiliary ordinary outer map on homotopy categories and a
full non-groupoidal local nerve map retaining arbitrary 2-cells. This module
packages all three layers from the same canonical bicategorical localization.
-/

set_option autoImplicit false
set_option linter.checkUnivs false
set_option linter.style.haveILetI false

namespace Ript.Higher.CostExactZigzagGlobalComparison

open CategoryTheory
open CategoryTheory.Bicategory
open Ript.Higher.UniverseLiftedNerve

universe u v w

variable {R : Type w} [AddCommMonoid R] [PartialOrder R]

/-- Source homotopy category of the fixed-resource model bicategory. -/
abbrev SourceHomotopy :=
  HomotopyCategory (ProcessModel.{u, v, w} R)

/-- Homotopy category of the actual presented bicategorical localization. -/
abbrev TargetHomotopy :=
  HomotopyCategory (CostExactZigzag.Localization.{u, v, w} (R := R))

/-- Common-universe source category for the outer Rezk comparison. -/
abbrev SmallSource :=
  AsSmall.{max (max w (v + 1)) (u + 1)}
    (SourceHomotopy.{u, v, w} (R := R))

/-- Common-universe target category for the outer Rezk comparison. -/
abbrev SmallTarget :=
  AsSmall.{max (max w (v + 1)) (u + 1)}
    (TargetHomotopy.{u, v, w} (R := R))

/-- The canonical bicategorical localization induces a functor between its
source and target homotopy categories, lifted into one common universe. -/
noncomputable def smallHomotopyLocalizationFunctor :
    SmallSource.{u, v, w} (R := R) ⥤ SmallTarget.{u, v, w} (R := R) :=
  commonAsSmallFunctor
    (Pseudofunctor.homotopyFunctor
      (CostExactZigzag.inclusion (R := R)))

/-- The actual higher localization's induced homotopy functor inverts the
ordinary cost-exact marking descended from cost-reflecting arrows. -/
theorem homotopyLocalizationFunctor_invertsCostExactMorphisms :
    (costExactMorphisms R).IsInvertedBy
      (Pseudofunctor.homotopyFunctor
        (CostExactZigzag.inclusion (R := R))) :=
  Pseudofunctor.homotopyFunctor_inverts_toHomotopy
    (CostExactZigzag.inclusion (R := R))
    (costReflectingArrows R) (by
      intro M N f hf
      exact CostExactZigzag.inclusion_inverts f
        (costReflectingArrows_le_costExactArrows f hf))

/-- The exact cost marking transported to the common-universe source
homotopy category. -/
def relativeSmallMarking : MorphismProperty
    (SmallSource.{u, v, w} (R := R)) :=
  (costExactMorphisms R).inverseImage AsSmall.down

instance relativeSmallMarking_isMultiplicative :
    (relativeSmallMarking.{u, v, w} (R := R)).IsMultiplicative := by
  change ((costExactMorphisms R).inverseImage AsSmall.down).IsMultiplicative
  infer_instance

/-- The common-universe homotopy localization functor inverts the transported
cost-exact marking. -/
theorem smallHomotopyLocalization_invertsRelativeMarking :
    (relativeSmallMarking.{u, v, w} (R := R)).IsInvertedBy
      (smallHomotopyLocalizationFunctor (R := R)) := by
  intro X Y f hf
  change IsIso (AsSmall.up.map
    ((Pseudofunctor.homotopyFunctor
      (CostExactZigzag.inclusion (R := R))).map (AsSmall.down.map f)))
  haveI : IsIso
      ((Pseudofunctor.homotopyFunctor
        (CostExactZigzag.inclusion (R := R))).map (AsSmall.down.map f)) :=
    homotopyLocalizationFunctor_invertsCostExactMorphisms
      (R := R) (AsSmall.down.map f) hf
  infer_instance

/-- Correct relative Rezk source: outer strings in the source homotopy
category with vertical transformations pointwise cost-exact. -/
abbrev RelativeOuterSource :=
  RelativeRezk.diagram (relativeSmallMarking.{u, v, w} (R := R))

/-- All-dimensional relative outer comparison into the actual marked-zigzag
target Rezk core diagram. -/
noncomputable def relativeOuterComparison :
    RelativeOuterSource.{u, v, w} (R := R) ⟶
      RezkCore.diagram (SmallTarget.{u, v, w} (R := R)) :=
  RelativeRezk.comparison
    (relativeSmallMarking.{u, v, w} (R := R))
    (smallHomotopyLocalizationFunctor (R := R))
    (smallHomotopyLocalization_invertsRelativeMarking (R := R))

/-- Ordinary auxiliary outer Rezk comparison induced by the actual higher
localization target. The relative comparison above is the localization-aware
source. -/
noncomputable def outerComparison :
    RezkCore.diagram (SmallSource.{u, v, w} (R := R)) ⟶
      RezkCore.diagram (SmallTarget.{u, v, w} (R := R)) :=
  RezkCore.diagramMap (SmallSource.{u, v, w} (R := R))
    (smallHomotopyLocalizationFunctor (R := R))

/-- The source outer Rezk diagram's actual completeness map has an explicit
simplicial homotopy inverse. -/
noncomputable def sourceCompletenessHomotopyEquivalence :
    SSet.HomotopyEquivalenceWitness
      (RezkCore.actualCompletenessMap
        (SmallSource.{u, v, w} (R := R))) :=
  RezkCore.actualCompletenessHomotopyEquivalence
    (SmallSource.{u, v, w} (R := R))

/-- The actual marked-zigzag target outer Rezk diagram's completeness map has
an explicit simplicial homotopy inverse. -/
noncomputable def targetCompletenessHomotopyEquivalence :
    SSet.HomotopyEquivalenceWitness
      (RezkCore.actualCompletenessMap
        (SmallTarget.{u, v, w} (R := R))) :=
  RezkCore.actualCompletenessHomotopyEquivalence
    (SmallTarget.{u, v, w} (R := R))

/-- A process model as an object of the common-universe source homotopy
category. -/
def sourceObject (M : ProcessModel.{u, v, w} R) :
    SmallSource.{u, v, w} (R := R) :=
  (AsSmall.up : SourceHomotopy.{u, v, w} (R := R) ⥤
    SmallSource.{u, v, w} (R := R)).obj (HomotopyCategory.of M)

/-- A process model as an object of the common-universe target homotopy
category. -/
def targetObject (M : ProcessModel.{u, v, w} R) :
    SmallTarget.{u, v, w} (R := R) :=
  (AsSmall.up : TargetHomotopy.{u, v, w} (R := R) ⥤
    SmallTarget.{u, v, w} (R := R)).obj
      (HomotopyCategory.of (CostExactZigzag.inclusion.obj M))

/-- The lifted source arrow represented by a model morphism. -/
def sourceArrow {M N : ProcessModel.{u, v, w} R} (f : M ⟶ N) :
    sourceObject M ⟶ sourceObject N :=
  (AsSmall.up : SourceHomotopy.{u, v, w} (R := R) ⥤
    SmallSource.{u, v, w} (R := R)).map (HomotopyCategory.homMk f)

/-- A source 1-cell as the actual degree-zero simplex of its common-universe
full local mapping nerve. -/
def sourceLocalVertex {M N : ProcessModel.{u, v, w} R} (f : M ⟶ N) :
    (UniverseLiftedNerve.CommonLocalMappingNerve
      (CostExactZigzag.inclusion (R := R)) M N).obj
        (Opposite.op (SimplexCategory.mk 0)) :=
  ComposableArrows.mk₀ ((AsSmall.up :
    (M ⟶ N) ⥤ UniverseLiftedNerve.CommonSourceHom
      (CostExactZigzag.inclusion (R := R)) M N).obj f)

/-- The actual local-nerve image of a source 1-cell vertex. -/
noncomputable def mappedLocalVertex
    {M N : ProcessModel.{u, v, w} R} (f : M ⟶ N) :
    (UniverseLiftedNerve.CommonTargetMappingNerve
      (CostExactZigzag.inclusion (R := R)) M N).obj
        (Opposite.op (SimplexCategory.mk 0)) :=
  ((CostExactZigzagNerveComparison.core
    (R := R)).toPseudofunctorNerveCore.localMap M N).app
      (Opposite.op (SimplexCategory.mk 0))
      (sourceLocalVertex f)

/-- Decode the actual mapped local zero-simplex back to its target local
1-cell. -/
noncomputable def mappedLocalVertexObject
    {M N : ProcessModel.{u, v, w} R} (f : M ⟶ N) :
    UniverseLiftedNerve.CommonTargetHom
      (CostExactZigzag.inclusion (R := R)) M N :=
  CategoryTheory.nerveEquiv (mappedLocalVertex f)

/-- Mapping and then decoding a source local vertex recovers exactly the
common-universe lift of the pseudofunctor image. -/
theorem mappedLocalVertexObject_eq
    {M N : ProcessModel.{u, v, w} R} (f : M ⟶ N) :
    mappedLocalVertexObject f =
      (AsSmall.up :
        (CostExactZigzag.inclusion.obj M ⟶
          CostExactZigzag.inclusion.obj N) ⥤
            UniverseLiftedNerve.CommonTargetHom
              (CostExactZigzag.inclusion (R := R)) M N).obj
        (CostExactZigzag.inclusion.map f) := by
  unfold mappedLocalVertexObject mappedLocalVertex sourceLocalVertex
  rw [(CostExactZigzagNerveComparison.core
    (R := R)).toPseudofunctorNerveCore.mapsVertex f]
  rfl

/-- A source 2-cell as the actual degree-one simplex of its common-universe
full local mapping nerve. -/
def sourceLocalEdge {M N : ProcessModel.{u, v, w} R}
    {f g : M ⟶ N} (α : f ⟶ g) :
    (UniverseLiftedNerve.CommonLocalMappingNerve
      (CostExactZigzag.inclusion (R := R)) M N).obj
        (Opposite.op (SimplexCategory.mk 1)) :=
  ComposableArrows.mk₁ ((AsSmall.up :
    (M ⟶ N) ⥤ UniverseLiftedNerve.CommonSourceHom
      (CostExactZigzag.inclusion (R := R)) M N).map α)

/-- The actual local-nerve image of a source 2-cell edge. -/
noncomputable def mappedLocalEdge
    {M N : ProcessModel.{u, v, w} R}
    {f g : M ⟶ N} (α : f ⟶ g) :
    (UniverseLiftedNerve.CommonTargetMappingNerve
      (CostExactZigzag.inclusion (R := R)) M N).obj
        (Opposite.op (SimplexCategory.mk 1)) :=
  ((CostExactZigzagNerveComparison.core
    (R := R)).toPseudofunctorNerveCore.localMap M N).app
      (Opposite.op (SimplexCategory.mk 1)) (sourceLocalEdge α)

/-- The actual mapped local edge is exactly the common-universe lift of the
pseudofunctor image of the source 2-cell. -/
theorem mappedLocalEdge_eq
    {M N : ProcessModel.{u, v, w} R}
    {f g : M ⟶ N} (α : f ⟶ g) :
    mappedLocalEdge α =
      ComposableArrows.mk₁ ((AsSmall.up :
        (CostExactZigzag.inclusion.obj M ⟶
          CostExactZigzag.inclusion.obj N) ⥤
            UniverseLiftedNerve.CommonTargetHom
              (CostExactZigzag.inclusion (R := R)) M N).map
        (CostExactZigzag.inclusion.map₂ α)) :=
  CostExactZigzagNerveComparison.twoCell_edge_mapsExactly α

/-- The relative outer comparison acts exactly on every represented source
arrow vertex. -/
theorem relativeOuterComparison_sourceArrow
    {M N : ProcessModel.{u, v, w} R} (f : M ⟶ N) :
    ((relativeOuterComparison (R := R)).app
      (Opposite.op (SimplexCategory.mk 1))).app
        (Opposite.op (SimplexCategory.mk 0))
        (RelativeRezk.arrowVertex
          (relativeSmallMarking.{u, v, w} (R := R)) (sourceArrow f)) =
      RezkCore.arrowVertex (SmallTarget.{u, v, w} (R := R))
        ((smallHomotopyLocalizationFunctor (R := R)).map
          (sourceArrow f)) :=
  RelativeRezk.comparison_arrowVertex
    (relativeSmallMarking.{u, v, w} (R := R))
    (smallHomotopyLocalizationFunctor (R := R))
    (smallHomotopyLocalization_invertsRelativeMarking (R := R))
    (sourceArrow f)

/-- Decode a lifted local target 1-cell vertex as an arrow of the lifted
target homotopy category used by the outer Rezk direction. -/
def localVertexToOuterArrow {M N : ProcessModel.{u, v, w} R}
    (g : UniverseLiftedNerve.CommonTargetHom
      (CostExactZigzag.inclusion (R := R)) M N) :
    targetObject M ⟶ targetObject N :=
  (AsSmall.up : TargetHomotopy.{u, v, w} (R := R) ⥤
    SmallTarget.{u, v, w} (R := R)).map
      (HomotopyCategory.homMk (ULift.down g))

/-- Lift one target 1-cell to the common-universe local vertex used by the
full mapping nerve. -/
def targetLocalVertex {M N : ProcessModel.{u, v, w} R}
    (g : CostExactZigzag.inclusion.obj M ⟶
      CostExactZigzag.inclusion.obj N) :
    UniverseLiftedNerve.CommonTargetHom
      (CostExactZigzag.inclusion (R := R)) M N :=
  (AsSmall.up :
    (CostExactZigzag.inclusion.obj M ⟶
      CostExactZigzag.inclusion.obj N) ⥤
        UniverseLiftedNerve.CommonTargetHom
          (CostExactZigzag.inclusion (R := R)) M N).obj g

/-- **Outer/local vertex gluing.** Decoding the exact local image of a model
1-cell gives exactly the arrow produced by the outer homotopy-category
functor. -/
theorem localVertex_outerArrow (M N : ProcessModel.{u, v, w} R)
    (f : M ⟶ N) :
    localVertexToOuterArrow
        ((AsSmall.up :
          (CostExactZigzag.inclusion.obj M ⟶
            CostExactZigzag.inclusion.obj N) ⥤
              UniverseLiftedNerve.CommonTargetHom
                (CostExactZigzag.inclusion (R := R)) M N).obj
          (CostExactZigzag.inclusion.map f)) =
      (smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow f) := by
  dsimp [localVertexToOuterArrow, smallHomotopyLocalizationFunctor,
    sourceArrow, UniverseLiftedNerve.commonAsSmallFunctor,
    Pseudofunctor.homotopyFunctor]
  rfl

/-- **Relative-outer/local vertex gluing.** The relative Rezk image of a
source arrow vertex is exactly the target Rezk arrow obtained by mapping the
actual local-nerve vertex and decoding it to the target homotopy category. -/
theorem relativeOuter_mappedLocalVertex
    {M N : ProcessModel.{u, v, w} R} (f : M ⟶ N) :
    ((relativeOuterComparison (R := R)).app
      (Opposite.op (SimplexCategory.mk 1))).app
        (Opposite.op (SimplexCategory.mk 0))
        (RelativeRezk.arrowVertex
          (relativeSmallMarking.{u, v, w} (R := R)) (sourceArrow f)) =
      RezkCore.arrowVertex (SmallTarget.{u, v, w} (R := R))
        (localVertexToOuterArrow (mappedLocalVertexObject f)) := by
  rw [relativeOuterComparison_sourceArrow, mappedLocalVertexObject_eq,
    localVertex_outerArrow]
  rfl

/-- One-skeleton gluing proposition for an arbitrary, possibly
noninvertible, source 2-cell. It records both relative-outer/local endpoints
and the exact mapped local edge. -/
def RelativeLocalTwoCellOneSkeleton
    {M N : ProcessModel.{u, v, w} R}
    {f g : M ⟶ N} (α : f ⟶ g) : Prop :=
  (((relativeOuterComparison (R := R)).app
      (Opposite.op (SimplexCategory.mk 1))).app
        (Opposite.op (SimplexCategory.mk 0))
        (RelativeRezk.arrowVertex
          (relativeSmallMarking.{u, v, w} (R := R)) (sourceArrow f)) =
      RezkCore.arrowVertex (SmallTarget.{u, v, w} (R := R))
        (localVertexToOuterArrow (mappedLocalVertexObject f))) ∧
  (((relativeOuterComparison (R := R)).app
      (Opposite.op (SimplexCategory.mk 1))).app
        (Opposite.op (SimplexCategory.mk 0))
        (RelativeRezk.arrowVertex
          (relativeSmallMarking.{u, v, w} (R := R)) (sourceArrow g)) =
      RezkCore.arrowVertex (SmallTarget.{u, v, w} (R := R))
        (localVertexToOuterArrow (mappedLocalVertexObject g))) ∧
  mappedLocalEdge α =
    ComposableArrows.mk₁ ((AsSmall.up :
      (CostExactZigzag.inclusion.obj M ⟶
        CostExactZigzag.inclusion.obj N) ⥤
          UniverseLiftedNerve.CommonTargetHom
            (CostExactZigzag.inclusion (R := R)) M N).map
      (CostExactZigzag.inclusion.map₂ α))

/-- Every source 2-cell satisfies the full relative/local one-skeleton glue,
without an invertibility hypothesis. -/
theorem relativeLocal_twoCellOneSkeleton
    {M N : ProcessModel.{u, v, w} R}
    {f g : M ⟶ N} (α : f ⟶ g) :
    RelativeLocalTwoCellOneSkeleton α :=
  ⟨relativeOuter_mappedLocalVertex f,
    relativeOuter_mappedLocalVertex g, mappedLocalEdge_eq α⟩

/-- **Horizontal outer/local gluing.** Decoding the local composite of two
mapped 1-cells agrees exactly with composition of their outer homotopy-category
arrows. -/
theorem localComposite_outerComposition
    {M N P : ProcessModel.{u, v, w} R} (f : M ⟶ N) (g : N ⟶ P) :
    localVertexToOuterArrow
        ((AsSmall.up :
          (CostExactZigzag.inclusion.obj M ⟶
            CostExactZigzag.inclusion.obj P) ⥤
              UniverseLiftedNerve.CommonTargetHom
                (CostExactZigzag.inclusion (R := R)) M P).obj
          (CostExactZigzag.inclusion.map f ≫
            CostExactZigzag.inclusion.map g)) =
      (smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow f) ≫
        (smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow g) := by
  dsimp [localVertexToOuterArrow, smallHomotopyLocalizationFunctor,
    sourceArrow, UniverseLiftedNerve.commonAsSmallFunctor,
    Pseudofunctor.homotopyFunctor]
  rfl

/-- **Identity outer/local gluing.** Decoding the local target identity gives
the identity arrow at the corresponding outer target object. -/
theorem localIdentity_outerIdentity (M : ProcessModel.{u, v, w} R) :
    localVertexToOuterArrow
        ((AsSmall.up :
          (CostExactZigzag.inclusion.obj M ⟶
            CostExactZigzag.inclusion.obj M) ⥤
              UniverseLiftedNerve.CommonTargetHom
                (CostExactZigzag.inclusion (R := R)) M M).obj
          (𝟙 (CostExactZigzag.inclusion.obj M))) =
      𝟙 (targetObject M) := by
  change (AsSmall.up : TargetHomotopy.{u, v, w} (R := R) ⥤
      SmallTarget.{u, v, w} (R := R)).map
        (HomotopyCategory.homMk
          (𝟙 (CostExactZigzag.inclusion.obj M))) = _
  rw [HomotopyCategory.homMk_id]
  unfold targetObject
  rfl

/-- The outer composite of the mapped factors also agrees with the outer
image of the source composite; the pseudofunctor compositor becomes equality
in the target homotopy category. -/
theorem outerComposition_sourceComposite
    {M N P : ProcessModel.{u, v, w} R} (f : M ⟶ N) (g : N ⟶ P) :
    (smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow f) ≫
        (smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow g) =
      (smallHomotopyLocalizationFunctor (R := R)).map
        (sourceArrow (f ≫ g)) := by
  rw [← Functor.map_comp]
  rfl

/-- The target bicategorical associator becomes strict equality after local
vertices are decoded into the outer homotopy category. -/
theorem localAssociator_outerArrow
    {A B C D : ProcessModel.{u, v, w} R}
    (f : CostExactZigzag.inclusion.obj A ⟶
      CostExactZigzag.inclusion.obj B)
    (g : CostExactZigzag.inclusion.obj B ⟶
      CostExactZigzag.inclusion.obj C)
    (h : CostExactZigzag.inclusion.obj C ⟶
      CostExactZigzag.inclusion.obj D) :
    localVertexToOuterArrow (targetLocalVertex ((f ≫ g) ≫ h)) =
      localVertexToOuterArrow (targetLocalVertex (f ≫ (g ≫ h))) := by
  dsimp [localVertexToOuterArrow, targetLocalVertex]
  apply congrArg (fun k =>
    (AsSmall.up : TargetHomotopy.{u, v, w} (R := R) ⥤
      SmallTarget.{u, v, w} (R := R)).map k)
  exact (HomotopyCategory.homMk_eq_iff _ _).2 ⟨α_ f g h⟩

/-- The target bicategorical left unitor becomes the strict left-unit law in
the outer homotopy category. -/
theorem localLeftUnitor_outerArrow
    {A B : ProcessModel.{u, v, w} R}
    (f : CostExactZigzag.inclusion.obj A ⟶
      CostExactZigzag.inclusion.obj B) :
    localVertexToOuterArrow
        (targetLocalVertex (𝟙 (CostExactZigzag.inclusion.obj A) ≫ f)) =
      localVertexToOuterArrow (targetLocalVertex f) := by
  dsimp [localVertexToOuterArrow, targetLocalVertex]
  apply congrArg (fun k =>
    (AsSmall.up : TargetHomotopy.{u, v, w} (R := R) ⥤
      SmallTarget.{u, v, w} (R := R)).map k)
  exact (HomotopyCategory.homMk_eq_iff _ _).2 ⟨λ_ f⟩

/-- The target bicategorical right unitor becomes the strict right-unit law
in the outer homotopy category. -/
theorem localRightUnitor_outerArrow
    {A B : ProcessModel.{u, v, w} R}
    (f : CostExactZigzag.inclusion.obj A ⟶
      CostExactZigzag.inclusion.obj B) :
    localVertexToOuterArrow
        (targetLocalVertex (f ≫ 𝟙 (CostExactZigzag.inclusion.obj B))) =
      localVertexToOuterArrow (targetLocalVertex f) := by
  dsimp [localVertexToOuterArrow, targetLocalVertex]
  apply congrArg (fun k =>
    (AsSmall.up : TargetHomotopy.{u, v, w} (R := R) ⥤
      SmallTarget.{u, v, w} (R := R)).map k)
  exact (HomotopyCategory.homMk_eq_iff _ _).2 ⟨ρ_ f⟩

/-- Decode an arbitrary invertible local 2-cell as the equality between its
two outer homotopy-category arrows. -/
theorem localIsoToOuterEquality
    {A B : ProcessModel.{u, v, w} R}
    {f g : CostExactZigzag.inclusion.obj A ⟶
      CostExactZigzag.inclusion.obj B} (e : f ≅ g) :
    localVertexToOuterArrow (targetLocalVertex f) =
      localVertexToOuterArrow (targetLocalVertex g) := by
  dsimp [localVertexToOuterArrow, targetLocalVertex]
  apply congrArg (fun k =>
    (AsSmall.up : TargetHomotopy.{u, v, w} (R := R) ⥤
      SmallTarget.{u, v, w} (R := R)).map k)
  exact (HomotopyCategory.homMk_eq_iff _ _).2 ⟨e⟩

/-- Decoding a vertically composed local 2-isomorphism agrees with transitive
composition of the decoded outer equalities. -/
theorem localIsoToOuterEquality_trans
    {A B : ProcessModel.{u, v, w} R}
    {f g h : CostExactZigzag.inclusion.obj A ⟶
      CostExactZigzag.inclusion.obj B}
    (first : f ≅ g) (second : g ≅ h) :
    localIsoToOuterEquality (first ≪≫ second) =
      (localIsoToOuterEquality first).trans
        (localIsoToOuterEquality second) :=
  Subsingleton.elim _ _

/-- The two associator pastings around the bicategorical pentagon decode to
the same outer equality witness. -/
theorem localPentagon_outerEquality
    {A B C D E : ProcessModel.{u, v, w} R}
    (f : CostExactZigzag.inclusion.obj A ⟶
      CostExactZigzag.inclusion.obj B)
    (g : CostExactZigzag.inclusion.obj B ⟶
      CostExactZigzag.inclusion.obj C)
    (h : CostExactZigzag.inclusion.obj C ⟶
      CostExactZigzag.inclusion.obj D)
    (i : CostExactZigzag.inclusion.obj D ⟶
      CostExactZigzag.inclusion.obj E) :
    let leftIso :=
      whiskerRightIso (α_ f g h) i ≪≫
        (α_ f (g ≫ h) i) ≪≫
          whiskerLeftIso f (α_ g h i)
    let rightIso :=
      (α_ (f ≫ g) h i) ≪≫ (α_ f g (h ≫ i))
    localIsoToOuterEquality leftIso =
      localIsoToOuterEquality rightIso := by
  change localIsoToOuterEquality
      (whiskerRightIso (α_ f g h) i ≪≫
        (α_ f (g ≫ h) i) ≪≫ whiskerLeftIso f (α_ g h i)) =
    localIsoToOuterEquality
      ((α_ (f ≫ g) h i) ≪≫ (α_ f g (h ≫ i)))
  have hIso :
      whiskerRightIso (α_ f g h) i ≪≫
          (α_ f (g ≫ h) i) ≪≫ whiskerLeftIso f (α_ g h i) =
        (α_ (f ≫ g) h i) ≪≫ (α_ f g (h ≫ i)) := by
    apply Iso.ext
    exact Bicategory.pentagon f g h i
  rw [hIso]

/-- The associator/left-unitor and right-unitor sides of the bicategorical
triangle decode to the same outer equality witness. -/
theorem localTriangle_outerEquality
    {A B C : ProcessModel.{u, v, w} R}
    (f : CostExactZigzag.inclusion.obj A ⟶
      CostExactZigzag.inclusion.obj B)
    (g : CostExactZigzag.inclusion.obj B ⟶
      CostExactZigzag.inclusion.obj C) :
    let leftIso :=
      (α_ f (𝟙 (CostExactZigzag.inclusion.obj B)) g) ≪≫
        whiskerLeftIso f (λ_ g)
    let rightIso := whiskerRightIso (ρ_ f) g
    localIsoToOuterEquality leftIso =
      localIsoToOuterEquality rightIso := by
  change localIsoToOuterEquality
      ((α_ f (𝟙 (CostExactZigzag.inclusion.obj B)) g) ≪≫
        whiskerLeftIso f (λ_ g)) =
    localIsoToOuterEquality (whiskerRightIso (ρ_ f) g)
  have hIso :
      (α_ f (𝟙 (CostExactZigzag.inclusion.obj B)) g) ≪≫
          whiskerLeftIso f (λ_ g) =
        whiskerRightIso (ρ_ f) g := by
    apply Iso.ext
    exact Bicategory.triangle f g
  rw [hIso]

/-- Every cost-exact model arrow becomes an isomorphism under the outer
homotopy-category comparison induced by the higher localization. -/
theorem smallHomotopyLocalization_map_marked_isIso
    {M N : ProcessModel.{u, v, w} R} (f : M ⟶ N)
    (hf : costExactArrows R f) :
    IsIso ((smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow f)) := by
  let e := CostExactZigzag.markedEquivalence f hf
  haveI : IsIso (HomotopyCategory.homMk e.hom) :=
    (HomotopyCategory.isoOfEquivalence e).isIso_hom
  have he : e.hom = CostExactZigzag.inclusion.map f := by
    rfl
  change IsIso (AsSmall.up.map
    (HomotopyCategory.homMk (CostExactZigzag.inclusion.map f)))
  rw [← he]
  exact Functor.map_isIso
    (AsSmall.up : TargetHomotopy.{u, v, w} (R := R) ⥤
      SmallTarget.{u, v, w} (R := R))
    (HomotopyCategory.homMk e.hom)

/-- Actual target equivalence-arrow vertex associated with a cost-exact
source morphism. -/
noncomputable def markedTargetVertex
    {M N : ProcessModel.{u, v, w} R} (f : M ⟶ N)
    (hf : costExactArrows R f) :
    (RezkCore.actualEquivalenceSpace
      (SmallTarget.{u, v, w} (R := R))).obj
        (Opposite.op (SimplexCategory.mk 0)) := by
  letI : IsIso
      ((smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow f)) :=
    smallHomotopyLocalization_map_marked_isIso f hf
  exact RezkCore.actualEquivalenceVertexOfIso
    (SmallTarget.{u, v, w} (R := R))
    ((smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow f))

/-- The actual higher localization's outer Rezk map sends every cost-exact
arrow through the target actual-equivalence-arrow subspace. -/
theorem markedArrowFactorsThroughActualEquivalences
    {M N : ProcessModel.{u, v, w} R} (f : M ⟶ N)
    (hf : costExactArrows R f) :
    ((outerComparison (R := R)).app
      (Opposite.op (SimplexCategory.mk 1))).app
        (Opposite.op (SimplexCategory.mk 0))
        (RezkCore.arrowVertex (SmallSource.{u, v, w} (R := R))
          (sourceArrow f)) =
      (RezkCore.actualEquivalenceSpaceInclusion
        (SmallTarget.{u, v, w} (R := R))).app
          (Opposite.op (SimplexCategory.mk 0))
          (markedTargetVertex f hf) := by
  letI : IsIso
      ((smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow f)) :=
    smallHomotopyLocalization_map_marked_isIso f hf
  change (((RezkCore.diagramMap
      (SmallSource.{u, v, w} (R := R))
      (smallHomotopyLocalizationFunctor (R := R))).app
        (Opposite.op (SimplexCategory.mk 1))).app
          (Opposite.op (SimplexCategory.mk 0))
          (RezkCore.arrowVertex (SmallSource.{u, v, w} (R := R))
            (sourceArrow f))) = _
  rw [RezkCore.diagramMap_arrowVertex]
  unfold markedTargetVertex
  rw [RezkCore.actualEquivalenceSpaceInclusion_vertexOfIso]

/-- Common-universe full local nerve core of the canonical cost-exact higher
localization. -/
abbrev LocalNerveCore :=
  UniverseLiftedNerve.HigherLocalizationNerveCore
    (CostExactZigzag.inclusion (R := R)) (costExactArrows R)
    CostExactZigzag.inclusion_isBicategoricalLocalization


/-- Machine-facing global comparison. The canonical outer direction uses the
relative Rezk source, the auxiliary ordinary direction records the induced
homotopy functor, and the local direction retains all 2-cells through the
common-universe nerve comparison. -/
structure GlobalComparisonCore where
  /-- Localization-aware all-dimensional relative Rezk comparison. -/
  relativeOuter : RelativeOuterSource.{u, v, w} (R := R) ⟶
    RezkCore.diagram (SmallTarget.{u, v, w} (R := R))
  /-- The relative map is the canonical comparison induced by the actual
  inverting functor. -/
  relativeOuter_eq : relativeOuter = relativeOuterComparison (R := R)
  /-- Outer Rezk comparison on common-universe homotopy categories. -/
  outer : RezkCore.diagram (SmallSource.{u, v, w} (R := R)) ⟶
    RezkCore.diagram (SmallTarget.{u, v, w} (R := R))
  /-- The outer map is induced by the homotopy functor of the canonical
  higher localization. -/
  outer_eq : outer = outerComparison (R := R)
  /-- Full non-groupoidal local comparison, with exact 2-cell action and
  compositor simplicial homotopy. -/
  localNerve : LocalNerveCore.{w, v, u} (R := R)
  /-- Explicit simplicial homotopy-equivalence witness for source outer
  completeness. -/
  sourceCompleteness : SSet.HomotopyEquivalenceWitness
    (RezkCore.actualCompletenessMap
      (SmallSource.{u, v, w} (R := R)))
  /-- Explicit simplicial homotopy-equivalence witness for target outer
  completeness. -/
  targetCompleteness : SSet.HomotopyEquivalenceWitness
    (RezkCore.actualCompletenessMap
      (SmallTarget.{u, v, w} (R := R)))
  /-- Exact action of the relative outer comparison on represented source
  arrow vertices. -/
  relativeArrowGlue : ∀ {M N : ProcessModel.{u, v, w} R} (f : M ⟶ N),
    ((relativeOuter.app
      (Opposite.op (SimplexCategory.mk 1))).app
        (Opposite.op (SimplexCategory.mk 0))
        (RelativeRezk.arrowVertex
          (relativeSmallMarking.{u, v, w} (R := R)) (sourceArrow f))) =
      RezkCore.arrowVertex (SmallTarget.{u, v, w} (R := R))
        ((smallHomotopyLocalizationFunctor (R := R)).map
          (sourceArrow f))
  /-- Exact decoding of the actual mapped local zero-simplex. -/
  mappedLocalVertexExact : ∀ {M N : ProcessModel.{u, v, w} R}
    (f : M ⟶ N),
    mappedLocalVertexObject f =
      (AsSmall.up :
        (CostExactZigzag.inclusion.obj M ⟶
          CostExactZigzag.inclusion.obj N) ⥤
            UniverseLiftedNerve.CommonTargetHom
              (CostExactZigzag.inclusion (R := R)) M N).obj
        (CostExactZigzag.inclusion.map f)
  /-- Exact gluing of the relative outer arrow vertex to the arrow decoded
  from the actual mapped local zero-simplex. -/
  relativeLocalVertexGlue : ∀ {M N : ProcessModel.{u, v, w} R}
    (f : M ⟶ N),
    ((relativeOuter.app
      (Opposite.op (SimplexCategory.mk 1))).app
        (Opposite.op (SimplexCategory.mk 0))
        (RelativeRezk.arrowVertex
          (relativeSmallMarking.{u, v, w} (R := R)) (sourceArrow f))) =
      RezkCore.arrowVertex (SmallTarget.{u, v, w} (R := R))
        (localVertexToOuterArrow (mappedLocalVertexObject f))
  /-- Relative/local one-skeleton gluing for every source 2-cell, including
  noninvertible ones. -/
  relativeLocalTwoCellGlue : ∀ {M N : ProcessModel.{u, v, w} R}
    {f g : M ⟶ N} (α : f ⟶ g),
    RelativeLocalTwoCellOneSkeleton α
  /-- Exact gluing of mapped local 1-cell vertices to outer Rezk arrows. -/
  vertexGlue : ∀ (M N : ProcessModel.{u, v, w} R) (f : M ⟶ N),
    localVertexToOuterArrow
        ((AsSmall.up :
          (CostExactZigzag.inclusion.obj M ⟶
            CostExactZigzag.inclusion.obj N) ⥤
              UniverseLiftedNerve.CommonTargetHom
                (CostExactZigzag.inclusion (R := R)) M N).obj
          (CostExactZigzag.inclusion.map f)) =
      (smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow f)
  /-- Exact horizontal-composition gluing between local vertices and outer
  arrows. -/
  compositionGlue : ∀ {M N P : ProcessModel.{u, v, w} R}
    (f : M ⟶ N) (g : N ⟶ P),
    localVertexToOuterArrow
        ((AsSmall.up :
          (CostExactZigzag.inclusion.obj M ⟶
            CostExactZigzag.inclusion.obj P) ⥤
              UniverseLiftedNerve.CommonTargetHom
                (CostExactZigzag.inclusion (R := R)) M P).obj
          (CostExactZigzag.inclusion.map f ≫
            CostExactZigzag.inclusion.map g)) =
      (smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow f) ≫
        (smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow g)
  /-- Exact identity gluing between the local and outer target layers. -/
  identityGlue : ∀ (M : ProcessModel.{u, v, w} R),
    localVertexToOuterArrow
        ((AsSmall.up :
          (CostExactZigzag.inclusion.obj M ⟶
            CostExactZigzag.inclusion.obj M) ⥤
              UniverseLiftedNerve.CommonTargetHom
                (CostExactZigzag.inclusion (R := R)) M M).obj
          (𝟙 (CostExactZigzag.inclusion.obj M))) =
      𝟙 (targetObject M)
  /-- Associator gluing between the local bicategory and outer homotopy
  category. -/
  associatorGlue : ∀ {A B C D : ProcessModel.{u, v, w} R}
    (f : CostExactZigzag.inclusion.obj A ⟶
      CostExactZigzag.inclusion.obj B)
    (g : CostExactZigzag.inclusion.obj B ⟶
      CostExactZigzag.inclusion.obj C)
    (h : CostExactZigzag.inclusion.obj C ⟶
      CostExactZigzag.inclusion.obj D),
    localVertexToOuterArrow (targetLocalVertex ((f ≫ g) ≫ h)) =
      localVertexToOuterArrow (targetLocalVertex (f ≫ (g ≫ h)))
  /-- Left-unitor gluing between the two layers. -/
  leftUnitorGlue : ∀ {A B : ProcessModel.{u, v, w} R}
    (f : CostExactZigzag.inclusion.obj A ⟶
      CostExactZigzag.inclusion.obj B),
    localVertexToOuterArrow
        (targetLocalVertex (𝟙 (CostExactZigzag.inclusion.obj A) ≫ f)) =
      localVertexToOuterArrow (targetLocalVertex f)
  /-- Right-unitor gluing between the two layers. -/
  rightUnitorGlue : ∀ {A B : ProcessModel.{u, v, w} R}
    (f : CostExactZigzag.inclusion.obj A ⟶
      CostExactZigzag.inclusion.obj B),
    localVertexToOuterArrow
        (targetLocalVertex (f ≫ 𝟙 (CostExactZigzag.inclusion.obj B))) =
      localVertexToOuterArrow (targetLocalVertex f)
  /-- Every invertible local 2-cell decodes to equality of the corresponding
  outer arrows. -/
  localIsoGlue : ∀ {A B : ProcessModel.{u, v, w} R}
    {f g : CostExactZigzag.inclusion.obj A ⟶
      CostExactZigzag.inclusion.obj B} (_e : f ≅ g),
    localVertexToOuterArrow (targetLocalVertex f) =
      localVertexToOuterArrow (targetLocalVertex g)
  /-- The decoded local associators satisfy the bicategorical pentagon. -/
  pentagonGlue : ∀ {A B C D E : ProcessModel.{u, v, w} R}
    (f : CostExactZigzag.inclusion.obj A ⟶
      CostExactZigzag.inclusion.obj B)
    (g : CostExactZigzag.inclusion.obj B ⟶
      CostExactZigzag.inclusion.obj C)
    (h : CostExactZigzag.inclusion.obj C ⟶
      CostExactZigzag.inclusion.obj D)
    (i : CostExactZigzag.inclusion.obj D ⟶
      CostExactZigzag.inclusion.obj E),
    let leftIso :=
      whiskerRightIso (α_ f g h) i ≪≫
        (α_ f (g ≫ h) i) ≪≫ whiskerLeftIso f (α_ g h i)
    let rightIso :=
      (α_ (f ≫ g) h i) ≪≫ (α_ f g (h ≫ i))
    localIsoToOuterEquality leftIso =
      localIsoToOuterEquality rightIso
  /-- The decoded local associator and unitors satisfy the bicategorical
  triangle. -/
  triangleGlue : ∀ {A B C : ProcessModel.{u, v, w} R}
    (f : CostExactZigzag.inclusion.obj A ⟶
      CostExactZigzag.inclusion.obj B)
    (g : CostExactZigzag.inclusion.obj B ⟶
      CostExactZigzag.inclusion.obj C),
    let leftIso :=
      (α_ f (𝟙 (CostExactZigzag.inclusion.obj B)) g) ≪≫
        whiskerLeftIso f (λ_ g)
    let rightIso := whiskerRightIso (ρ_ f) g
    localIsoToOuterEquality leftIso =
      localIsoToOuterEquality rightIso
  /-- Marked outer arrows factor through actual target equivalences. -/
  markedOuter : ∀ {M N : ProcessModel.{u, v, w} R}
    (f : M ⟶ N) (hf : costExactArrows R f),
    (outer.app (Opposite.op (SimplexCategory.mk 1))).app
        (Opposite.op (SimplexCategory.mk 0))
        (RezkCore.arrowVertex (SmallSource.{u, v, w} (R := R))
          (sourceArrow f)) =
      (RezkCore.actualEquivalenceSpaceInclusion
        (SmallTarget.{u, v, w} (R := R))).app
          (Opposite.op (SimplexCategory.mk 0))
          (markedTargetVertex f hf)

/-- Package the outer and full-local comparisons induced by the same actual
cost-exact bicategorical localization. -/
noncomputable def core : GlobalComparisonCore.{u, v, w} (R := R) where
  relativeOuter := relativeOuterComparison (R := R)
  relativeOuter_eq := rfl
  outer := outerComparison (R := R)
  outer_eq := rfl
  localNerve := CostExactZigzagNerveComparison.core (R := R)
  sourceCompleteness := sourceCompletenessHomotopyEquivalence (R := R)
  targetCompleteness := targetCompletenessHomotopyEquivalence (R := R)
  relativeArrowGlue := relativeOuterComparison_sourceArrow
  mappedLocalVertexExact := mappedLocalVertexObject_eq
  relativeLocalVertexGlue := relativeOuter_mappedLocalVertex
  relativeLocalTwoCellGlue := relativeLocal_twoCellOneSkeleton
  vertexGlue := localVertex_outerArrow
  compositionGlue := localComposite_outerComposition
  identityGlue := localIdentity_outerIdentity
  associatorGlue := localAssociator_outerArrow
  leftUnitorGlue := localLeftUnitor_outerArrow
  rightUnitorGlue := localRightUnitor_outerArrow
  localIsoGlue := localIsoToOuterEquality
  pentagonGlue := localPentagon_outerEquality
  triangleGlue := localTriangle_outerEquality
  markedOuter := markedArrowFactorsThroughActualEquivalences

end Ript.Higher.CostExactZigzagGlobalComparison
