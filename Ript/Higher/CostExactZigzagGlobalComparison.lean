import Ript.ForMathlib.CategoryTheory.Bicategory.PseudofunctorHomotopy
import Ript.Higher.CostExactZigzagMappingSpace
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

/-- The homotopy-category functor of the presented cost-exact localization
is surjective on objects because the presented target retains exactly the
source object set. -/
theorem homotopyLocalizationFunctor_obj_surjective : Function.Surjective
    (Pseudofunctor.homotopyFunctor
      (CostExactZigzag.inclusion (R := R))).obj := by
  intro Y
  rcases CostExactZigzag.inclusion_obj_surjective Y.as with ⟨X, hX⟩
  refine ⟨HomotopyCategory.of X, ?_⟩
  apply HomotopyCategory.ext
  exact hX

/-- The common-universe outer localization functor is essentially
surjective. This establishes the object condition of the intended
Dwyer--Kan comparison independently of the still-open derived mapping-space
correctness theorem. -/
theorem smallHomotopyLocalizationFunctor_essSurj :
    (smallHomotopyLocalizationFunctor (R := R)).EssSurj where
  mem_essImage Y := by
    let F := Pseudofunctor.homotopyFunctor
      (CostExactZigzag.inclusion (R := R))
    have hsurj : Function.Surjective F.obj :=
      homotopyLocalizationFunctor_obj_surjective (R := R)
    rcases hsurj (AsSmall.down.obj Y) with ⟨X, hX⟩
    refine ⟨AsSmall.up.obj X, ⟨?_⟩⟩
    exact (AsSmall.up.mapIso (eqToIso hX)).trans
      (AsSmall.equiv.counitIso.app Y)

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

/-- Two composable model morphisms as a relative outer degree-two vertex. -/
def sourceTwoArrow
    {M N P : ProcessModel.{u, v, w} R} (f : M ⟶ N) (g : N ⟶ P) :
    ((RelativeOuterSource.{u, v, w} (R := R)).obj
      (Opposite.op (SimplexCategory.mk 2))).obj
        (Opposite.op (SimplexCategory.mk 0)) :=
  RelativeRezk.twoArrowVertex
    (relativeSmallMarking.{u, v, w} (R := R)) (sourceArrow f) (sourceArrow g)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Composition of represented source arrows is the represented composite in
the source homotopy category. -/
theorem sourceArrow_comp
    {M N P : ProcessModel.{u, v, w} R} (f : M ⟶ N) (g : N ⟶ P) :
    sourceArrow f ≫ sourceArrow g = sourceArrow (f ≫ g) := by
  unfold sourceArrow
  rw [← Functor.map_comp]
  rw [← HomotopyCategory.homMk_comp]

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

/-- Two vertically composable source 2-cells as the canonical degree-two
simplex of the common-universe full local mapping nerve. -/
def sourceLocalTwoSimplex
    {M N : ProcessModel.{u, v, w} R}
    {f g h : M ⟶ N} (α : f ⟶ g) (β : g ⟶ h) :
    (UniverseLiftedNerve.CommonLocalMappingNerve
      (CostExactZigzag.inclusion (R := R)) M N).obj
        (Opposite.op (SimplexCategory.mk 2)) :=
  ComposableArrows.mk₂
    ((AsSmall.up :
      (M ⟶ N) ⥤ UniverseLiftedNerve.CommonSourceHom
        (CostExactZigzag.inclusion (R := R)) M N).map α)
    ((AsSmall.up :
      (M ⟶ N) ⥤ UniverseLiftedNerve.CommonSourceHom
        (CostExactZigzag.inclusion (R := R)) M N).map β)

/-- The actual local-nerve image of a vertically composable pair of source
2-cells. -/
noncomputable def mappedLocalTwoSimplex
    {M N : ProcessModel.{u, v, w} R}
    {f g h : M ⟶ N} (α : f ⟶ g) (β : g ⟶ h) :
    (UniverseLiftedNerve.CommonTargetMappingNerve
      (CostExactZigzag.inclusion (R := R)) M N).obj
        (Opposite.op (SimplexCategory.mk 2)) :=
  ((CostExactZigzagNerveComparison.core
    (R := R)).toPseudofunctorNerveCore.localMap M N).app
      (Opposite.op (SimplexCategory.mk 2)) (sourceLocalTwoSimplex α β)

/-- The mapped local 2-simplex is exactly the canonical simplex of the two
lifted `map₂` images. -/
theorem mappedLocalTwoSimplex_eq
    {M N : ProcessModel.{u, v, w} R}
    {f g h : M ⟶ N} (α : f ⟶ g) (β : g ⟶ h) :
    mappedLocalTwoSimplex α β =
      ComposableArrows.mk₂
        ((AsSmall.up :
          (CostExactZigzag.inclusion.obj M ⟶
            CostExactZigzag.inclusion.obj N) ⥤
              UniverseLiftedNerve.CommonTargetHom
                (CostExactZigzag.inclusion (R := R)) M N).map
            (CostExactZigzag.inclusion.map₂ α))
        ((AsSmall.up :
          (CostExactZigzag.inclusion.obj M ⟶
            CostExactZigzag.inclusion.obj N) ⥤
              UniverseLiftedNerve.CommonTargetHom
                (CostExactZigzag.inclusion (R := R)) M N).map
            (CostExactZigzag.inclusion.map₂ β)) :=
  CostExactZigzagNerveComparison.twoCell_twoSimplex_mapsExactly α β

/-- Proposition that the long diagonal of the mapped local 2-simplex is the
exact lifted image of the vertical composite source 2-cell. `HEq` records the
necessary dependent endpoint transport. -/
def MappedLocalTwoSimplexDiagonal
    {M N : ProcessModel.{u, v, w} R}
    {f g h : M ⟶ N} (α : f ⟶ g) (β : g ⟶ h) : Prop :=
  HEq ((mappedLocalTwoSimplex α β).map' 0 2)
      ((AsSmall.up :
        (CostExactZigzag.inclusion.obj M ⟶
          CostExactZigzag.inclusion.obj N) ⥤
            UniverseLiftedNerve.CommonTargetHom
              (CostExactZigzag.inclusion (R := R)) M N).map
        (CostExactZigzag.inclusion.map₂ (α ≫ β)))

/-- The mapped local 2-simplex has the exact lifted composite diagonal. -/
theorem mappedLocalTwoSimplex_diagonal
    {M N : ProcessModel.{u, v, w} R}
    {f g h : M ⟶ N} (α : f ⟶ g) (β : g ⟶ h) :
    MappedLocalTwoSimplexDiagonal α β := by
  unfold MappedLocalTwoSimplexDiagonal
  rw [mappedLocalTwoSimplex_eq]
  apply heq_of_eq
  change _ ≫ _ = _
  simp
  rfl

/-- The relative outer comparison acts exactly on every represented finite
source-homotopy string vertex. -/
theorem relativeOuterComparison_stringVertex
    {n : ℕ}
    (F : ComposableArrows (SmallSource.{u, v, w} (R := R)) n) :
    ((relativeOuterComparison (R := R)).app
      (Opposite.op (SimplexCategory.mk n))).app
        (Opposite.op (SimplexCategory.mk 0))
        (RelativeRezk.stringVertex
          (relativeSmallMarking.{u, v, w} (R := R)) F) =
      RezkCore.stringVertex (SmallTarget.{u, v, w} (R := R))
        (((smallHomotopyLocalizationFunctor (R := R)).mapComposableArrows n).obj
          F) :=
  RelativeRezk.comparison_stringVertex
    (relativeSmallMarking.{u, v, w} (R := R))
    (smallHomotopyLocalizationFunctor (R := R))
    (smallHomotopyLocalization_invertsRelativeMarking (R := R)) F

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

/-- The relative outer comparison acts exactly on every represented
two-arrow source vertex. -/
theorem relativeOuterComparison_sourceTwoArrow
    {M N P : ProcessModel.{u, v, w} R} (f : M ⟶ N) (g : N ⟶ P) :
    ((relativeOuterComparison (R := R)).app
      (Opposite.op (SimplexCategory.mk 2))).app
        (Opposite.op (SimplexCategory.mk 0)) (sourceTwoArrow f g) =
      RezkCore.twoArrowVertex (SmallTarget.{u, v, w} (R := R))
        ((smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow f))
        ((smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow g)) :=
  RelativeRezk.comparison_twoArrowVertex
    (relativeSmallMarking.{u, v, w} (R := R))
    (smallHomotopyLocalizationFunctor (R := R))
    (smallHomotopyLocalization_invertsRelativeMarking (R := R))
    (sourceArrow f) (sourceArrow g)

/-- The zero-th relative outer face of a represented source pair is the
second represented arrow. -/
theorem sourceTwoArrow_face_zero
    {M N P : ProcessModel.{u, v, w} R} (f : M ⟶ N) (g : N ⟶ P) :
    ((RelativeOuterSource.{u, v, w} (R := R)).δ (0 : Fin 3)).app
        (Opposite.op (SimplexCategory.mk 0)) (sourceTwoArrow f g) =
      RelativeRezk.arrowVertex
        (relativeSmallMarking.{u, v, w} (R := R)) (sourceArrow g) := by
  unfold sourceTwoArrow
  apply RelativeRezk.twoArrowVertex_face_zero

/-- The middle relative outer face is the represented source composite. -/
theorem sourceTwoArrow_face_one
    {M N P : ProcessModel.{u, v, w} R} (f : M ⟶ N) (g : N ⟶ P) :
    ((RelativeOuterSource.{u, v, w} (R := R)).δ (1 : Fin 3)).app
        (Opposite.op (SimplexCategory.mk 0)) (sourceTwoArrow f g) =
      RelativeRezk.arrowVertex
        (relativeSmallMarking.{u, v, w} (R := R))
        (sourceArrow (f ≫ g)) := by
  unfold sourceTwoArrow
  rw [RelativeRezk.twoArrowVertex_face_one, sourceArrow_comp]

/-- The last relative outer face of a represented source pair is the first
represented arrow. -/
theorem sourceTwoArrow_face_two
    {M N P : ProcessModel.{u, v, w} R} (f : M ⟶ N) (g : N ⟶ P) :
    ((RelativeOuterSource.{u, v, w} (R := R)).δ (2 : Fin 3)).app
        (Opposite.op (SimplexCategory.mk 0)) (sourceTwoArrow f g) =
      RelativeRezk.arrowVertex
        (relativeSmallMarking.{u, v, w} (R := R)) (sourceArrow f) := by
  unfold sourceTwoArrow
  apply RelativeRezk.twoArrowVertex_face_two

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

/-- Full relative/local two-simplex gluing proposition for two vertically
composable, possibly noninvertible, source 2-cells. It contains both
one-skeleton witnesses, the exact mapped triangle, and its composite
diagonal. -/
def RelativeLocalTwoSimplexGlue
    {M N : ProcessModel.{u, v, w} R}
    {f g h : M ⟶ N} (α : f ⟶ g) (β : g ⟶ h) : Prop :=
  RelativeLocalTwoCellOneSkeleton α ∧
  RelativeLocalTwoCellOneSkeleton β ∧
  mappedLocalTwoSimplex α β =
    ComposableArrows.mk₂
      ((AsSmall.up :
        (CostExactZigzag.inclusion.obj M ⟶
          CostExactZigzag.inclusion.obj N) ⥤
            UniverseLiftedNerve.CommonTargetHom
              (CostExactZigzag.inclusion (R := R)) M N).map
          (CostExactZigzag.inclusion.map₂ α))
      ((AsSmall.up :
        (CostExactZigzag.inclusion.obj M ⟶
          CostExactZigzag.inclusion.obj N) ⥤
            UniverseLiftedNerve.CommonTargetHom
              (CostExactZigzag.inclusion (R := R)) M N).map
          (CostExactZigzag.inclusion.map₂ β)) ∧
  MappedLocalTwoSimplexDiagonal α β

/-- Every vertically composable pair of source 2-cells satisfies the complete
relative/local two-simplex gluing interface. -/
theorem relativeLocal_twoSimplexGlue
    {M N : ProcessModel.{u, v, w} R}
    {f g h : M ⟶ N} (α : f ⟶ g) (β : g ⟶ h) :
    RelativeLocalTwoSimplexGlue α β :=
  ⟨relativeLocal_twoCellOneSkeleton α,
    relativeLocal_twoCellOneSkeleton β,
    mappedLocalTwoSimplex_eq α β,
    mappedLocalTwoSimplex_diagonal α β⟩

/-- Simultaneous horizontal composition of two source 2-cells. -/
def sourceHorizontalTwoCell
    {M N P : ProcessModel.{u, v, w} R}
    {f₀ f₁ : M ⟶ N} {g₀ g₁ : N ⟶ P}
    (α : f₀ ⟶ f₁) (β : g₀ ⟶ g₁) :
    f₀ ≫ g₀ ⟶ f₁ ≫ g₁ :=
  UniverseLiftedNerve.horizontalTwoCell α β

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

/-- The local vertex obtained by mapping a source composite decodes to the
outer composite of the two mapped factors. The pseudofunctor compositor is
the exact invertible local 2-cell connecting these presentations. -/
theorem mappedCompositeVertex_outerComposition
    {M N P : ProcessModel.{u, v, w} R}
    (f : M ⟶ N) (g : N ⟶ P) :
    localVertexToOuterArrow (mappedLocalVertexObject (f ≫ g)) =
      (smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow f) ≫
        (smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow g) := by
  rw [mappedLocalVertexObject_eq, localVertex_outerArrow]
  exact (outerComposition_sourceComposite f g).symm

/-- The target outer degree-two vertex represented by the mapped factors of
two composable source morphisms. -/
noncomputable def targetTwoArrow
    {M N P : ProcessModel.{u, v, w} R} (f : M ⟶ N) (g : N ⟶ P) :=
  RezkCore.twoArrowVertex (SmallTarget.{u, v, w} (R := R))
    ((smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow f))
    ((smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow g))

/-- The zero-th target outer face is the arrow decoded from the exact mapped
local vertex of the second factor. -/
theorem targetTwoArrow_face_zero_mappedLocalVertex
    {M N P : ProcessModel.{u, v, w} R} (f : M ⟶ N) (g : N ⟶ P) :
    ((RezkCore.diagram (SmallTarget.{u, v, w} (R := R))).δ
      (0 : Fin 3)).app (Opposite.op (SimplexCategory.mk 0))
        (targetTwoArrow f g) =
      RezkCore.arrowVertex (SmallTarget.{u, v, w} (R := R))
        (localVertexToOuterArrow (mappedLocalVertexObject g)) := by
  unfold targetTwoArrow
  rw [RezkCore.twoArrowVertex_face_zero]
  rw [mappedLocalVertexObject_eq, localVertex_outerArrow]
  rfl

/-- The middle target outer face is the arrow decoded from the exact mapped
local vertex of the source composite. -/
theorem targetTwoArrow_face_one_mappedComposite
    {M N P : ProcessModel.{u, v, w} R} (f : M ⟶ N) (g : N ⟶ P) :
    ((RezkCore.diagram (SmallTarget.{u, v, w} (R := R))).δ
      (1 : Fin 3)).app (Opposite.op (SimplexCategory.mk 0))
        (targetTwoArrow f g) =
      RezkCore.arrowVertex (SmallTarget.{u, v, w} (R := R))
        (localVertexToOuterArrow (mappedLocalVertexObject (f ≫ g))) := by
  unfold targetTwoArrow
  rw [RezkCore.twoArrowVertex_face_one]
  rw [mappedCompositeVertex_outerComposition]
  rfl

/-- The last target outer face is the arrow decoded from the exact mapped
local vertex of the first factor. -/
theorem targetTwoArrow_face_two_mappedLocalVertex
    {M N P : ProcessModel.{u, v, w} R} (f : M ⟶ N) (g : N ⟶ P) :
    ((RezkCore.diagram (SmallTarget.{u, v, w} (R := R))).δ
      (2 : Fin 3)).app (Opposite.op (SimplexCategory.mk 0))
        (targetTwoArrow f g) =
      RezkCore.arrowVertex (SmallTarget.{u, v, w} (R := R))
        (localVertexToOuterArrow (mappedLocalVertexObject f)) := by
  unfold targetTwoArrow
  rw [RezkCore.twoArrowVertex_face_two]
  rw [mappedLocalVertexObject_eq, localVertex_outerArrow]
  rfl

/-- Mixed horizontal relative/local gluing proposition for two arbitrary,
possibly noninvertible, 2-cells. It packages the two factor one-skeletons,
their horizontally composed one-skeleton, both outer composite endpoints,
the exact degree-one actions of the two compositor-homotopy maps, and the
commuting compositor naturality square. -/
def RelativeLocalHorizontalTwoCellGlue
    {M N P : ProcessModel.{u, v, w} R}
    {f₀ f₁ : M ⟶ N} {g₀ g₁ : N ⟶ P}
    (α : f₀ ⟶ f₁) (β : g₀ ⟶ g₁) : Prop :=
  RelativeLocalTwoCellOneSkeleton α ∧
  RelativeLocalTwoCellOneSkeleton β ∧
  RelativeLocalTwoCellOneSkeleton (sourceHorizontalTwoCell α β) ∧
  localVertexToOuterArrow (mappedLocalVertexObject (f₀ ≫ g₀)) =
    (smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow f₀) ≫
      (smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow g₀) ∧
  localVertexToOuterArrow (mappedLocalVertexObject (f₁ ≫ g₁)) =
    (smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow f₁) ≫
      (smallHomotopyLocalizationFunctor (R := R)).map (sourceArrow g₁) ∧
  CommonHorizontalCompositionGlue
    (CostExactZigzag.inclusion (R := R)) α β

/-- Every horizontal pair of source 2-cells satisfies the complete mixed
relative/local degree-one gluing interface. -/
theorem relativeLocal_horizontalTwoCellGlue
    {M N P : ProcessModel.{u, v, w} R}
    {f₀ f₁ : M ⟶ N} {g₀ g₁ : N ⟶ P}
    (α : f₀ ⟶ f₁) (β : g₀ ⟶ g₁) :
    RelativeLocalHorizontalTwoCellGlue α β :=
  ⟨relativeLocal_twoCellOneSkeleton α,
    relativeLocal_twoCellOneSkeleton β,
    relativeLocal_twoCellOneSkeleton (sourceHorizontalTwoCell α β),
    mappedCompositeVertex_outerComposition f₀ g₀,
    mappedCompositeVertex_outerComposition f₁ g₁,
    CostExactZigzagNerveComparison.horizontalTwoCell_compositionGlue α β⟩

/-- Source-level interchange for two vertically composable horizontal
2-cell pairs. -/
theorem sourceHorizontalTwoCell_comp
    {M N P : ProcessModel.{u, v, w} R}
    {f₀ f₁ f₂ : M ⟶ N} {g₀ g₁ g₂ : N ⟶ P}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) :
    sourceHorizontalTwoCell (α₀ ≫ α₁) (β₀ ≫ β₁) =
      sourceHorizontalTwoCell α₀ β₀ ≫
        sourceHorizontalTwoCell α₁ β₁ :=
  UniverseLiftedNerve.horizontalTwoCell_comp α₀ α₁ β₀ β₁

/-- Mixed degree-two relative/local pasting proposition. It packages both
factor triangles, the triangle of horizontally composed 2-cells, each
degree-one horizontal square, source interchange, and the exact
common-universe compositor rectangle. -/
def RelativeLocalHorizontalPastingGlue
    {M N P : ProcessModel.{u, v, w} R}
    {f₀ f₁ f₂ : M ⟶ N} {g₀ g₁ g₂ : N ⟶ P}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) : Prop :=
  RelativeLocalTwoSimplexGlue α₀ α₁ ∧
  RelativeLocalTwoSimplexGlue β₀ β₁ ∧
  RelativeLocalTwoSimplexGlue
    (sourceHorizontalTwoCell α₀ β₀)
    (sourceHorizontalTwoCell α₁ β₁) ∧
  RelativeLocalHorizontalTwoCellGlue α₀ β₀ ∧
  RelativeLocalHorizontalTwoCellGlue α₁ β₁ ∧
  RelativeLocalHorizontalTwoCellGlue (α₀ ≫ α₁) (β₀ ≫ β₁) ∧
  sourceHorizontalTwoCell (α₀ ≫ α₁) (β₀ ≫ β₁) =
    sourceHorizontalTwoCell α₀ β₀ ≫
      sourceHorizontalTwoCell α₁ β₁ ∧
  CommonHorizontalCompositionPastingGlue
    (CostExactZigzag.inclusion (R := R)) α₀ α₁ β₀ β₁

/-- Every vertically composable pair of horizontal source 2-cell pairs
satisfies the complete mixed degree-two relative/local pasting interface. -/
theorem relativeLocal_horizontalPastingGlue
    {M N P : ProcessModel.{u, v, w} R}
    {f₀ f₁ f₂ : M ⟶ N} {g₀ g₁ g₂ : N ⟶ P}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) :
    RelativeLocalHorizontalPastingGlue α₀ α₁ β₀ β₁ :=
  ⟨relativeLocal_twoSimplexGlue α₀ α₁,
    relativeLocal_twoSimplexGlue β₀ β₁,
    relativeLocal_twoSimplexGlue
      (sourceHorizontalTwoCell α₀ β₀)
      (sourceHorizontalTwoCell α₁ β₁),
    relativeLocal_horizontalTwoCellGlue α₀ β₀,
    relativeLocal_horizontalTwoCellGlue α₁ β₁,
    relativeLocal_horizontalTwoCellGlue (α₀ ≫ α₁) (β₀ ≫ β₁),
    sourceHorizontalTwoCell_comp α₀ α₁ β₀ β₁,
    CostExactZigzagNerveComparison.horizontalTwoCell_pastingGlue
      α₀ α₁ β₀ β₁⟩

/-- One of the three actual target-local 3-simplices in the global
cost-exact compositor prism. -/
noncomputable def mappedCompositionPrismSimplex
    {M N P : ProcessModel.{u, v, w} R}
    {f₀ f₁ f₂ : M ⟶ N} {g₀ g₁ g₂ : N ⟶ P}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂)
    (i : Fin 3) :=
  CostExactZigzagNerveComparison.horizontalTwoCellCompositionPrismSimplex
    α₀ α₁ β₀ β₁ i

/-- Full relative/local compositor-prism proposition. It combines the
degree-two factor and pasting boundary with the three genuine target-local
3-simplices and their complete twelve-face identification. -/
def RelativeLocalHorizontalPrismGlue
    {M N P : ProcessModel.{u, v, w} R}
    {f₀ f₁ f₂ : M ⟶ N} {g₀ g₁ g₂ : N ⟶ P}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) : Prop :=
  RelativeLocalHorizontalPastingGlue α₀ α₁ β₀ β₁ ∧
  CommonCompositionPrismGlue
    (CostExactZigzag.inclusion (R := R)) α₀ α₁ β₀ β₁

/-- Every vertically composable horizontal source pair admits the complete
relative/local three-tetrahedron compositor prism. -/
theorem relativeLocal_horizontalPrismGlue
    {M N P : ProcessModel.{u, v, w} R}
    {f₀ f₁ f₂ : M ⟶ N} {g₀ g₁ g₂ : N ⟶ P}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) :
    RelativeLocalHorizontalPrismGlue α₀ α₁ β₀ β₁ :=
  ⟨relativeLocal_horizontalPastingGlue α₀ α₁ β₀ β₁,
    CostExactZigzagNerveComparison.horizontalTwoCell_compositionPrismGlue
      α₀ α₁ β₀ β₁⟩

/-- Full relative-outer/local gluing for one represented two-arrow vertex.
It contains the exact relative comparison plus all three source and target
outer face identifications, with target faces decoded from actual mapped local
vertices. -/
def RelativeOuterLocalTwoArrowGlue
    {M N P : ProcessModel.{u, v, w} R} (f : M ⟶ N) (g : N ⟶ P) : Prop :=
  ((relativeOuterComparison (R := R)).app
      (Opposite.op (SimplexCategory.mk 2))).app
        (Opposite.op (SimplexCategory.mk 0)) (sourceTwoArrow f g) =
      targetTwoArrow f g ∧
  ((RelativeOuterSource.{u, v, w} (R := R)).δ (0 : Fin 3)).app
      (Opposite.op (SimplexCategory.mk 0)) (sourceTwoArrow f g) =
    RelativeRezk.arrowVertex
      (relativeSmallMarking.{u, v, w} (R := R)) (sourceArrow g) ∧
  ((RelativeOuterSource.{u, v, w} (R := R)).δ (1 : Fin 3)).app
      (Opposite.op (SimplexCategory.mk 0)) (sourceTwoArrow f g) =
    RelativeRezk.arrowVertex
      (relativeSmallMarking.{u, v, w} (R := R))
      (sourceArrow (f ≫ g)) ∧
  ((RelativeOuterSource.{u, v, w} (R := R)).δ (2 : Fin 3)).app
      (Opposite.op (SimplexCategory.mk 0)) (sourceTwoArrow f g) =
    RelativeRezk.arrowVertex
      (relativeSmallMarking.{u, v, w} (R := R)) (sourceArrow f) ∧
  ((RezkCore.diagram (SmallTarget.{u, v, w} (R := R))).δ
      (0 : Fin 3)).app (Opposite.op (SimplexCategory.mk 0))
        (targetTwoArrow f g) =
    RezkCore.arrowVertex (SmallTarget.{u, v, w} (R := R))
      (localVertexToOuterArrow (mappedLocalVertexObject g)) ∧
  ((RezkCore.diagram (SmallTarget.{u, v, w} (R := R))).δ
      (1 : Fin 3)).app (Opposite.op (SimplexCategory.mk 0))
        (targetTwoArrow f g) =
    RezkCore.arrowVertex (SmallTarget.{u, v, w} (R := R))
      (localVertexToOuterArrow (mappedLocalVertexObject (f ≫ g))) ∧
  ((RezkCore.diagram (SmallTarget.{u, v, w} (R := R))).δ
      (2 : Fin 3)).app (Opposite.op (SimplexCategory.mk 0))
        (targetTwoArrow f g) =
    RezkCore.arrowVertex (SmallTarget.{u, v, w} (R := R))
      (localVertexToOuterArrow (mappedLocalVertexObject f))

/-- Every represented source pair satisfies the complete relative-outer/local
two-arrow face gluing interface. -/
theorem relativeOuterLocal_twoArrowGlue
    {M N P : ProcessModel.{u, v, w} R} (f : M ⟶ N) (g : N ⟶ P) :
    RelativeOuterLocalTwoArrowGlue f g :=
  ⟨relativeOuterComparison_sourceTwoArrow f g,
    sourceTwoArrow_face_zero f g,
    sourceTwoArrow_face_one f g,
    sourceTwoArrow_face_two f g,
    targetTwoArrow_face_zero_mappedLocalVertex f g,
    targetTwoArrow_face_one_mappedComposite f g,
    targetTwoArrow_face_two_mappedLocalVertex f g⟩

/-- Relative-outer/local vertex boundary for the entire degree-two compositor
prism: all three horizontal pair vertices carry exact two-arrow face gluing,
and the actual local three-tetrahedron prism is retained. -/
def RelativeOuterLocalPrismVerticesGlue
    {M N P : ProcessModel.{u, v, w} R}
    {f₀ f₁ f₂ : M ⟶ N} {g₀ g₁ g₂ : N ⟶ P}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) : Prop :=
  RelativeOuterLocalTwoArrowGlue f₀ g₀ ∧
  RelativeOuterLocalTwoArrowGlue f₁ g₁ ∧
  RelativeOuterLocalTwoArrowGlue f₂ g₂ ∧
  RelativeLocalHorizontalPrismGlue α₀ α₁ β₀ β₁

/-- Every degree-two compositor prism has all three horizontal pair vertices
glued to relative outer degree two and its three outer faces. -/
theorem relativeOuterLocal_prismVerticesGlue
    {M N P : ProcessModel.{u, v, w} R}
    {f₀ f₁ f₂ : M ⟶ N} {g₀ g₁ g₂ : N ⟶ P}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) :
    RelativeOuterLocalPrismVerticesGlue α₀ α₁ β₀ β₁ :=
  ⟨relativeOuterLocal_twoArrowGlue f₀ g₀,
    relativeOuterLocal_twoArrowGlue f₁ g₁,
    relativeOuterLocal_twoArrowGlue f₂ g₂,
    relativeLocal_horizontalPrismGlue α₀ α₁ β₀ β₁⟩

/-- Decode one vertex of an arbitrary common-universe horizontal-product
source simplex back to its pair of source 1-cells. -/
def sourceHorizontalPairAt
    {M N P : ProcessModel.{u, v, w} R} {n : ℕ}
    (x : (CategoryTheory.nerve
      (CommonHorizontalSource
        (_Q := CostExactZigzag.inclusion (R := R)) M N P)).obj
          (Opposite.op (SimplexCategory.mk n)))
    (j : Fin (n + 1)) : (M ⟶ N) × (N ⟶ P) :=
  (AsSmall.down :
    CommonHorizontalSource
      (_Q := CostExactZigzag.inclusion (R := R)) M N P ⥤
        ((M ⟶ N) × (N ⟶ P))).obj (x.obj j)

/-- Decoding a source pair after any local-nerve restriction is strictly the
same as decoding the corresponding original vertex. This single formula
covers every face and degeneracy projection. -/
theorem sourceHorizontalPairAt_restriction
    {M N P : ProcessModel.{u, v, w} R} {m n : ℕ}
    (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (x : (CategoryTheory.nerve
      (CommonHorizontalSource
        (_Q := CostExactZigzag.inclusion (R := R)) M N P)).obj
          (Opposite.op (SimplexCategory.mk n)))
    (j : Fin (m + 1)) :
    sourceHorizontalPairAt
        (((CategoryTheory.nerve
          (CommonHorizontalSource
            (_Q := CostExactZigzag.inclusion (R := R)) M N P)).map
              φ.op).hom' x) j =
      sourceHorizontalPairAt x
        ((SimplexCategory.toCat.map φ).toFunctor.obj j) := by
  rfl

/-- All-degree relative-outer/local prism vertex package. It combines the
all-degree local prism core with exact two-arrow outer/local gluing for every
vertex of every horizontal-product source simplex. -/
def RelativeOuterLocalAllPrismVerticesGlue
    (M N P : ProcessModel.{u, v, w} R) : Prop :=
  CommonCompositionPrismCore
    (CostExactZigzag.inclusion (R := R)) M N P ∧
  ∀ (n : ℕ)
    (x : (CategoryTheory.nerve
      (CommonHorizontalSource
        (_Q := CostExactZigzag.inclusion (R := R)) M N P)).obj
          (Opposite.op (SimplexCategory.mk n)))
    (j : Fin (n + 1)),
    RelativeOuterLocalTwoArrowGlue
      (sourceHorizontalPairAt x j).1 (sourceHorizontalPairAt x j).2

/-- Every cost-exact compositor prism has all source vertices glued to the
relative outer two-arrow layer in every simplicial degree. -/
theorem relativeOuterLocal_allPrismVerticesGlue
    (M N P : ProcessModel.{u, v, w} R) :
    RelativeOuterLocalAllPrismVerticesGlue M N P := by
  refine ⟨CostExactZigzagNerveComparison.compositionPrismCore M N P, ?_⟩
  intro n x j
  exact relativeOuterLocal_twoArrowGlue
    (sourceHorizontalPairAt x j).1 (sourceHorizontalPairAt x j).2

/-- All-degree relative-outer/local restriction-vertex package. It retains
the complete all-prism vertex glue, proves strict vertex decoding under every
simplex restriction, and attaches complete relative two-arrow glue to every
restricted vertex. -/
def RelativeOuterLocalAllPrismRestrictionVerticesGlue
    (M N P : ProcessModel.{u, v, w} R) : Prop :=
  RelativeOuterLocalAllPrismVerticesGlue M N P ∧
  ∀ (m n : ℕ) (φ : SimplexCategory.mk m ⟶ SimplexCategory.mk n)
    (x : (CategoryTheory.nerve
      (CommonHorizontalSource
        (_Q := CostExactZigzag.inclusion (R := R)) M N P)).obj
          (Opposite.op (SimplexCategory.mk n)))
    (j : Fin (m + 1)),
    sourceHorizontalPairAt
        (((CategoryTheory.nerve
          (CommonHorizontalSource
            (_Q := CostExactZigzag.inclusion (R := R)) M N P)).map
              φ.op).hom' x) j =
      sourceHorizontalPairAt x
        ((SimplexCategory.toCat.map φ).toFunctor.obj j) ∧
    RelativeOuterLocalTwoArrowGlue
      (sourceHorizontalPairAt
        (((CategoryTheory.nerve
          (CommonHorizontalSource
            (_Q := CostExactZigzag.inclusion (R := R)) M N P)).map
              φ.op).hom' x) j).1
      (sourceHorizontalPairAt
        (((CategoryTheory.nerve
          (CommonHorizontalSource
            (_Q := CostExactZigzag.inclusion (R := R)) M N P)).map
              φ.op).hom' x) j).2

/-- Every face, degeneracy, and arbitrary simplex restriction of every
cost-exact compositor-prism source simplex has strictly compatible decoded
vertices and complete relative two-arrow gluing. -/
theorem relativeOuterLocal_allPrismRestrictionVerticesGlue
    (M N P : ProcessModel.{u, v, w} R) :
    RelativeOuterLocalAllPrismRestrictionVerticesGlue M N P := by
  refine ⟨relativeOuterLocal_allPrismVerticesGlue M N P, ?_⟩
  intro m n φ x j
  exact ⟨sourceHorizontalPairAt_restriction φ x j,
    relativeOuterLocal_twoArrowGlue
      (sourceHorizontalPairAt
        (((CategoryTheory.nerve
          (CommonHorizontalSource
            (_Q := CostExactZigzag.inclusion (R := R)) M N P)).map
              φ.op).hom' x) j).1
      (sourceHorizontalPairAt
        (((CategoryTheory.nerve
          (CommonHorizontalSource
            (_Q := CostExactZigzag.inclusion (R := R)) M N P)).map
              φ.op).hom' x) j).2⟩

/-- An arbitrary-degree target-local simplex in the global cost-exact
compositor prism. -/
noncomputable def mappedCompositionPrismSimplexAt
    (M N P : ProcessModel.{u, v, w} R) {n : ℕ}
    (x : (CategoryTheory.nerve
      (CommonHorizontalSource
        (_Q := CostExactZigzag.inclusion (R := R)) M N P)).obj
          (Opposite.op (SimplexCategory.mk n)))
    (i : Fin (n + 1)) :=
  CostExactZigzagNerveComparison.compositionPrismSimplexAt M N P x i

/-- One actual vertex of one face of an arbitrary-degree target-local
compositor-prism simplex. -/
noncomputable def mappedCompositionPrismFaceVertexAt
    (M N P : ProcessModel.{u, v, w} R) {n : ℕ}
    (x : (CategoryTheory.nerve
      (CommonHorizontalSource
        (_Q := CostExactZigzag.inclusion (R := R)) M N P)).obj
          (Opposite.op (SimplexCategory.mk n)))
    (i : Fin (n + 1)) (face : Fin (n + 2)) (j : Fin (n + 1)) :
    UniverseLiftedNerve.CommonTargetHom
      (CostExactZigzag.inclusion (R := R)) M P :=
  (((CategoryTheory.nerve
    (UniverseLiftedNerve.CommonTargetHom
      (CostExactZigzag.inclusion (R := R)) M P)).δ face).hom'
        (mappedCompositionPrismSimplexAt M N P x i)).obj j

/-- A target-prism face vertex is literally the corresponding vertex of the
unrestricted target prism simplex. -/
@[simp]
theorem mappedCompositionPrismFaceVertexAt_eq
    (M N P : ProcessModel.{u, v, w} R) {n : ℕ}
    (x : (CategoryTheory.nerve
      (CommonHorizontalSource
        (_Q := CostExactZigzag.inclusion (R := R)) M N P)).obj
          (Opposite.op (SimplexCategory.mk n)))
    (i : Fin (n + 1)) (face : Fin (n + 2)) (j : Fin (n + 1)) :
    mappedCompositionPrismFaceVertexAt M N P x i face j =
      (mappedCompositionPrismSimplexAt M N P x i).obj
        (face.succAbove j) := by
  rfl

/-- Before the switch, each target-prism vertex is exactly the local lift of
the pseudofunctor image of the corresponding source composite. -/
theorem mappedCompositionPrismVertex_castSucc
    (M N P : ProcessModel.{u, v, w} R) {n : ℕ}
    (x : (CategoryTheory.nerve
      (CommonHorizontalSource
        (_Q := CostExactZigzag.inclusion (R := R)) M N P)).obj
          (Opposite.op (SimplexCategory.mk n)))
    (i j : Fin (n + 1)) (hji : j ≤ i) :
    (mappedCompositionPrismSimplexAt M N P x i).obj j.castSucc =
      targetLocalVertex (CostExactZigzag.inclusion.map
        ((sourceHorizontalPairAt x j).1 ≫
          (sourceHorizontalPairAt x j).2)) := by
  unfold mappedCompositionPrismSimplexAt
  rw [CostExactZigzagNerveComparison.compositionPrismSimplexAt_obj_castSucc_of_le
    M N P x i j hji]
  rfl

/-- After the switch, each target-prism vertex is exactly the local composite
of the two mapped factors of the corresponding source pair. -/
theorem mappedCompositionPrismVertex_succ
    (M N P : ProcessModel.{u, v, w} R) {n : ℕ}
    (x : (CategoryTheory.nerve
      (CommonHorizontalSource
        (_Q := CostExactZigzag.inclusion (R := R)) M N P)).obj
          (Opposite.op (SimplexCategory.mk n)))
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    (mappedCompositionPrismSimplexAt M N P x i).obj j.succ =
      targetLocalVertex
        (CostExactZigzag.inclusion.map (sourceHorizontalPairAt x j).1 ≫
          CostExactZigzag.inclusion.map (sourceHorizontalPairAt x j).2) := by
  unfold mappedCompositionPrismSimplexAt
  rw [CostExactZigzagNerveComparison.compositionPrismSimplexAt_obj_succ_of_le
    M N P x i j hij]
  rfl

/-- Before the switch, decoding the actual target-prism vertex gives the
outer composite represented by the corresponding source pair. -/
theorem mappedCompositionPrismVertex_castSucc_outer
    (M N P : ProcessModel.{u, v, w} R) {n : ℕ}
    (x : (CategoryTheory.nerve
      (CommonHorizontalSource
        (_Q := CostExactZigzag.inclusion (R := R)) M N P)).obj
          (Opposite.op (SimplexCategory.mk n)))
    (i j : Fin (n + 1)) (hji : j ≤ i) :
    localVertexToOuterArrow
        ((mappedCompositionPrismSimplexAt M N P x i).obj j.castSucc) =
      (smallHomotopyLocalizationFunctor (R := R)).map
          (sourceArrow (sourceHorizontalPairAt x j).1) ≫
        (smallHomotopyLocalizationFunctor (R := R)).map
          (sourceArrow (sourceHorizontalPairAt x j).2) := by
  rw [mappedCompositionPrismVertex_castSucc M N P x i j hji]
  calc
    _ = (smallHomotopyLocalizationFunctor (R := R)).map
          (sourceArrow ((sourceHorizontalPairAt x j).1 ≫
            (sourceHorizontalPairAt x j).2)) :=
      localVertex_outerArrow M P
        ((sourceHorizontalPairAt x j).1 ≫
          (sourceHorizontalPairAt x j).2)
    _ = _ := (outerComposition_sourceComposite
      (sourceHorizontalPairAt x j).1
      (sourceHorizontalPairAt x j).2).symm

/-- After the switch, decoding the actual target-prism vertex gives the same
outer composite represented by the corresponding source pair. -/
theorem mappedCompositionPrismVertex_succ_outer
    (M N P : ProcessModel.{u, v, w} R) {n : ℕ}
    (x : (CategoryTheory.nerve
      (CommonHorizontalSource
        (_Q := CostExactZigzag.inclusion (R := R)) M N P)).obj
          (Opposite.op (SimplexCategory.mk n)))
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    localVertexToOuterArrow
        ((mappedCompositionPrismSimplexAt M N P x i).obj j.succ) =
      (smallHomotopyLocalizationFunctor (R := R)).map
          (sourceArrow (sourceHorizontalPairAt x j).1) ≫
        (smallHomotopyLocalizationFunctor (R := R)).map
          (sourceArrow (sourceHorizontalPairAt x j).2) := by
  rw [mappedCompositionPrismVertex_succ M N P x i j hij]
  exact localComposite_outerComposition
    (sourceHorizontalPairAt x j).1 (sourceHorizontalPairAt x j).2

/-- Complete outer/local glue for one actual target-prism vertex. It records
which side of the compositor switch presents the vertex, its exact local
1-cell, its decoded outer composite, and the full relative two-arrow glue of
the source pair. -/
def RelativeOuterLocalPrismTargetVertexGlue
    (M N P : ProcessModel.{u, v, w} R) {n : ℕ}
    (x : (CategoryTheory.nerve
      (CommonHorizontalSource
        (_Q := CostExactZigzag.inclusion (R := R)) M N P)).obj
          (Opposite.op (SimplexCategory.mk n)))
    (i : Fin (n + 1)) (k : Fin (n + 2)) : Prop :=
  (∃ j : Fin (n + 1), j ≤ i ∧ k = j.castSucc ∧
    (mappedCompositionPrismSimplexAt M N P x i).obj k =
      targetLocalVertex (CostExactZigzag.inclusion.map
        ((sourceHorizontalPairAt x j).1 ≫
          (sourceHorizontalPairAt x j).2)) ∧
    localVertexToOuterArrow
        ((mappedCompositionPrismSimplexAt M N P x i).obj k) =
      (smallHomotopyLocalizationFunctor (R := R)).map
          (sourceArrow (sourceHorizontalPairAt x j).1) ≫
        (smallHomotopyLocalizationFunctor (R := R)).map
          (sourceArrow (sourceHorizontalPairAt x j).2) ∧
    RelativeOuterLocalTwoArrowGlue
      (sourceHorizontalPairAt x j).1 (sourceHorizontalPairAt x j).2) ∨
  (∃ j : Fin (n + 1), i ≤ j ∧ k = j.succ ∧
    (mappedCompositionPrismSimplexAt M N P x i).obj k =
      targetLocalVertex
        (CostExactZigzag.inclusion.map (sourceHorizontalPairAt x j).1 ≫
          CostExactZigzag.inclusion.map (sourceHorizontalPairAt x j).2) ∧
    localVertexToOuterArrow
        ((mappedCompositionPrismSimplexAt M N P x i).obj k) =
      (smallHomotopyLocalizationFunctor (R := R)).map
          (sourceArrow (sourceHorizontalPairAt x j).1) ≫
        (smallHomotopyLocalizationFunctor (R := R)).map
          (sourceArrow (sourceHorizontalPairAt x j).2) ∧
    RelativeOuterLocalTwoArrowGlue
      (sourceHorizontalPairAt x j).1 (sourceHorizontalPairAt x j).2)

/-- Every vertex of every actual target-local compositor-prism simplex has
the complete side-sensitive outer/local glue. -/
theorem relativeOuterLocal_prismTargetVertexGlue
    (M N P : ProcessModel.{u, v, w} R) {n : ℕ}
    (x : (CategoryTheory.nerve
      (CommonHorizontalSource
        (_Q := CostExactZigzag.inclusion (R := R)) M N P)).obj
          (Opposite.op (SimplexCategory.mk n)))
    (i : Fin (n + 1)) (k : Fin (n + 2)) :
    RelativeOuterLocalPrismTargetVertexGlue M N P x i k := by
  rcases SSet.Homotopy.prismVertex_castSucc_or_succ i k with
    ⟨j, hji, rfl⟩ | ⟨j, hij, rfl⟩
  · left
    exact ⟨j, hji, rfl,
      mappedCompositionPrismVertex_castSucc M N P x i j hji,
      mappedCompositionPrismVertex_castSucc_outer M N P x i j hji,
      relativeOuterLocal_twoArrowGlue
        (sourceHorizontalPairAt x j).1 (sourceHorizontalPairAt x j).2⟩
  · right
    exact ⟨j, hij, rfl,
      mappedCompositionPrismVertex_succ M N P x i j hij,
      mappedCompositionPrismVertex_succ_outer M N P x i j hij,
      relativeOuterLocal_twoArrowGlue
        (sourceHorizontalPairAt x j).1 (sourceHorizontalPairAt x j).2⟩

/-- Complete glue for one actual target-prism face vertex: the categorical
nerve face projection is retained literally and the projected vertex has the
side-sensitive target/local/outer certificate. -/
def RelativeOuterLocalPrismTargetFaceVertexGlue
    (M N P : ProcessModel.{u, v, w} R) {n : ℕ}
    (x : (CategoryTheory.nerve
      (CommonHorizontalSource
        (_Q := CostExactZigzag.inclusion (R := R)) M N P)).obj
          (Opposite.op (SimplexCategory.mk n)))
    (i : Fin (n + 1)) (face : Fin (n + 2)) (j : Fin (n + 1)) : Prop :=
  mappedCompositionPrismFaceVertexAt M N P x i face j =
      (mappedCompositionPrismSimplexAt M N P x i).obj
        (face.succAbove j) ∧
    RelativeOuterLocalPrismTargetVertexGlue M N P x i (face.succAbove j)

/-- Every vertex of every face of every actual target-local prism simplex
has complete projection and outer/local gluing. -/
theorem relativeOuterLocal_prismTargetFaceVertexGlue
    (M N P : ProcessModel.{u, v, w} R) {n : ℕ}
    (x : (CategoryTheory.nerve
      (CommonHorizontalSource
        (_Q := CostExactZigzag.inclusion (R := R)) M N P)).obj
          (Opposite.op (SimplexCategory.mk n)))
    (i : Fin (n + 1)) (face : Fin (n + 2)) (j : Fin (n + 1)) :
    RelativeOuterLocalPrismTargetFaceVertexGlue M N P x i face j :=
  ⟨mappedCompositionPrismFaceVertexAt_eq M N P x i face j,
    relativeOuterLocal_prismTargetVertexGlue M N P x i (face.succAbove j)⟩

/-- All-degree target-face projection package. It combines the complete
source restriction and local prism coherence with exact outer/local gluing
for every actual target face vertex. -/
def RelativeOuterLocalAllPrismTargetFacesGlue
    (M N P : ProcessModel.{u, v, w} R) : Prop :=
  RelativeOuterLocalAllPrismRestrictionVerticesGlue M N P ∧
  ∀ (n : ℕ)
    (x : (CategoryTheory.nerve
      (CommonHorizontalSource
        (_Q := CostExactZigzag.inclusion (R := R)) M N P)).obj
          (Opposite.op (SimplexCategory.mk n)))
    (i : Fin (n + 1)) (face : Fin (n + 2)) (j : Fin (n + 1)),
    RelativeOuterLocalPrismTargetFaceVertexGlue M N P x i face j

/-- Every actual target-prism face projection in every simplicial degree is
retained by the local prism core and has complete outer/local vertex glue. -/
theorem relativeOuterLocal_allPrismTargetFacesGlue
    (M N P : ProcessModel.{u, v, w} R) :
    RelativeOuterLocalAllPrismTargetFacesGlue M N P := by
  refine ⟨relativeOuterLocal_allPrismRestrictionVerticesGlue M N P, ?_⟩
  intro n x i face j
  exact relativeOuterLocal_prismTargetFaceVertexGlue M N P x i face j

/-- All-degree relative/local compositor-prism core for one triple of source
models. -/
def RelativeLocalAllDegreePrismCore
    (M N P : ProcessModel.{u, v, w} R) : Prop :=
  CommonCompositionPrismCore
    (CostExactZigzag.inclusion (R := R)) M N P

/-- The global cost-exact comparison carries endpoint, side-face,
shared-face, and degeneracy coherence in every compositor-prism degree. -/
theorem relativeLocal_allDegreePrismCore
    (M N P : ProcessModel.{u, v, w} R) :
    RelativeLocalAllDegreePrismCore M N P :=
  CostExactZigzagNerveComparison.compositionPrismCore M N P

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

/-- Project-local presented Dwyer--Kan criterion for the actual cost-exact
localization. It records outer essential surjectivity and, for every model
pair, categorical-nerve equivalence plus explicit simplicial homotopy inverse,
the target-independent algebraic/simplicial presentation core, strict
factorization of the source local map, and exact action in every degree.

The source mapping spaces in this criterion are the compiled presented
relative-zigzag nerves. Thus this proposition is intentionally weaker than a
standard Dwyer--Kan theorem based on an independently constructed hammock or
derived localization. -/
def PresentedDwyerKanCore : Prop :=
  (smallHomotopyLocalizationFunctor.{u, v, w} (R := R)).EssSurj ∧
  ∀ (M N : ProcessModel.{u, v, w} R),
    Nonempty (SSet.NerveEquivalenceWitness
      (CostExactZigzagMappingSpace.comparison M N)) ∧
    Nonempty (SSet.HomotopyEquivalenceWitness
      (CostExactZigzagMappingSpace.comparison M N)) ∧
    CostExactZigzagMappingSpace.LocalPresentationCore M N ∧
    (CostExactZigzagNerveComparison.core
      (R := R)).toPseudofunctorNerveCore.localMap M N =
        CostExactZigzagMappingSpace.forwardMap M N ≫
          CostExactZigzagMappingSpace.comparison M N ∧
    ∀ {n : ℕ}
      (simplex : (CostExactZigzagMappingSpace.RelativeZigzagMappingNerve
        M N).obj (Opposite.op (SimplexCategory.mk n))),
      (CostExactZigzagMappingSpace.comparison M N).app
        (Opposite.op (SimplexCategory.mk n)) simplex = simplex

/-- The actual cost-exact localization satisfies the complete project-local
presented Dwyer--Kan criterion. -/
theorem presentedDwyerKanCore : PresentedDwyerKanCore.{u, v, w} (R := R) := by
  refine ⟨smallHomotopyLocalizationFunctor_essSurj (R := R), ?_⟩
  intro M N
  exact ⟨⟨CostExactZigzagMappingSpace.comparisonNerveEquivalence M N⟩,
    ⟨CostExactZigzagMappingSpace.comparisonHomotopyEquivalence M N⟩,
    CostExactZigzagMappingSpace.localPresentationCore M N,
    CostExactZigzagMappingSpace.localMap_factorization M N,
    CostExactZigzagMappingSpace.comparison_simplex M N⟩

/-- Project-local linear-hammock Dwyer--Kan criterion. Its source mapping
spaces are independently defined right-associated typed step lists, and each
maps directly to the actual target local nerve by a categorical-nerve
equivalence with an explicit simplicial homotopy inverse.

The linear model now has a fixed-shape aligned multi-column fragment and
elementary executable forward-column refinements, but not the general common-
refinement quotient and reduced-hammock invariance of the classical arbitrary-
grid localization, so this is not yet the standard Dwyer--Kan theorem. -/
def LinearHammockDwyerKanCore : Prop :=
  (smallHomotopyLocalizationFunctor.{u, v, w} (R := R)).EssSurj ∧
  ∀ (M N : ProcessModel.{u, v, w} R),
    Nonempty (SSet.NerveEquivalenceWitness
      (CostExactZigzagMappingSpace.linearTargetComparison M N)) ∧
    Nonempty (SSet.HomotopyEquivalenceWitness
      (CostExactZigzagMappingSpace.linearTargetComparison M N))

/-- The actual cost-exact localization satisfies the project-local linear-
hammock Dwyer--Kan criterion. -/
theorem linearHammockDwyerKanCore :
    LinearHammockDwyerKanCore.{u, v, w} (R := R) := by
  refine ⟨smallHomotopyLocalizationFunctor_essSurj (R := R), ?_⟩
  intro M N
  exact ⟨⟨CostExactZigzagMappingSpace.linearTargetNerveEquivalence M N⟩,
    ⟨CostExactZigzagMappingSpace.linearTargetHomotopyEquivalence M N⟩⟩


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
  /-- The outer localization functor satisfies the object-essential-
  surjectivity condition of a Dwyer--Kan comparison. -/
  outerEssentiallySurjective :
    (smallHomotopyLocalizationFunctor.{u, v, w} (R := R)).EssSurj
  /-- Full non-groupoidal local comparison, with exact 2-cell action and
  compositor simplicial homotopy. -/
  localNerve : LocalNerveCore.{w, v, u} (R := R)
  /-- Represented relative-zigzag mapping-space comparison for every source
  object pair, including nerve equivalence, explicit homotopy inverse, and
  strict factorization of the full local map. -/
  relativeZigzagMappingSpace : ∀
    (M N : ProcessModel.{u, v, w} R),
    CostExactZigzagMappingSpace.MappingSpaceCore M N
  /-- Project-local presented Dwyer--Kan evidence: outer essential
  surjectivity plus the complete presented mapping-space condition for every
  model pair. -/
  presentedDwyerKan : PresentedDwyerKanCore.{u, v, w} (R := R)
  /-- Project-local Dwyer--Kan evidence using the independently defined
  linear hammock mapping nerves. -/
  linearHammockDwyerKan :
    LinearHammockDwyerKanCore.{u, v, w} (R := R)
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
  /-- Exact relative comparison action on every finite source-homotopy string
  vertex. -/
  relativeStringGlue : ∀ {n : ℕ}
    (F : ComposableArrows (SmallSource.{u, v, w} (R := R)) n),
    ((relativeOuter.app
      (Opposite.op (SimplexCategory.mk n))).app
        (Opposite.op (SimplexCategory.mk 0))
        (RelativeRezk.stringVertex
          (relativeSmallMarking.{u, v, w} (R := R)) F)) =
      RezkCore.stringVertex (SmallTarget.{u, v, w} (R := R))
        (((smallHomotopyLocalizationFunctor (R := R)).mapComposableArrows n).obj
          F)
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
  /-- Relative/local two-simplex gluing for every vertically composable pair
  of source 2-cells. -/
  relativeLocalTwoSimplexGlue : ∀ {M N : ProcessModel.{u, v, w} R}
    {f g h : M ⟶ N} (α : f ⟶ g) (β : g ⟶ h),
    RelativeLocalTwoSimplexGlue α β
  /-- Mixed relative/local horizontal gluing for every pair of arbitrary
  source 2-cells. -/
  relativeLocalHorizontalTwoCellGlue : ∀
    {M N P : ProcessModel.{u, v, w} R}
    {f₀ f₁ : M ⟶ N} {g₀ g₁ : N ⟶ P}
    (α : f₀ ⟶ f₁) (β : g₀ ⟶ g₁),
    RelativeLocalHorizontalTwoCellGlue α β
  /-- Mixed degree-two horizontal/vertical pasting glue for every vertically
  composable pair of horizontal 2-cell pairs. -/
  relativeLocalHorizontalPastingGlue : ∀
    {M N P : ProcessModel.{u, v, w} R}
    {f₀ f₁ f₂ : M ⟶ N} {g₀ g₁ g₂ : N ⟶ P}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂),
    RelativeLocalHorizontalPastingGlue α₀ α₁ β₀ β₁
  /-- Three genuine target-local compositor-prism 3-simplices with their
  complete relative/local boundary package. -/
  relativeLocalHorizontalPrismGlue : ∀
    {M N P : ProcessModel.{u, v, w} R}
    {f₀ f₁ f₂ : M ⟶ N} {g₀ g₁ g₂ : N ⟶ P}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂),
    RelativeLocalHorizontalPrismGlue α₀ α₁ β₀ β₁
  /-- Relative comparison and all three source/target faces for every
  represented two-arrow vertex. -/
  relativeOuterLocalTwoArrowGlue : ∀
    {M N P : ProcessModel.{u, v, w} R} (f : M ⟶ N) (g : N ⟶ P),
    RelativeOuterLocalTwoArrowGlue f g
  /-- Relative-outer/local gluing of all three horizontal pair vertices in
  every degree-two compositor prism. -/
  relativeOuterLocalPrismVerticesGlue : ∀
    {M N P : ProcessModel.{u, v, w} R}
    {f₀ f₁ f₂ : M ⟶ N} {g₀ g₁ g₂ : N ⟶ P}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂),
    RelativeOuterLocalPrismVerticesGlue α₀ α₁ β₀ β₁
  /-- Relative two-arrow gluing for every source vertex of every all-degree
  compositor prism. -/
  relativeOuterLocalAllPrismVerticesGlue : ∀
    (M N P : ProcessModel.{u, v, w} R),
    RelativeOuterLocalAllPrismVerticesGlue M N P
  /-- Strict restriction naturality and relative two-arrow gluing for every
  face/degeneracy vertex of every all-degree compositor prism. -/
  relativeOuterLocalAllPrismRestrictionVerticesGlue : ∀
    (M N P : ProcessModel.{u, v, w} R),
    RelativeOuterLocalAllPrismRestrictionVerticesGlue M N P
  /-- Complete local face coherence and side-sensitive outer/local glue for
  every actual target face vertex of every all-degree compositor prism. -/
  relativeOuterLocalAllPrismTargetFacesGlue : ∀
    (M N P : ProcessModel.{u, v, w} R),
    RelativeOuterLocalAllPrismTargetFacesGlue M N P
  /-- Complete all-degree compositor-prism face and degeneracy coherence for
  every triple of source models. -/
  relativeLocalAllDegreePrismCore : ∀
    (M N P : ProcessModel.{u, v, w} R),
    RelativeLocalAllDegreePrismCore M N P
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
  outerEssentiallySurjective :=
    smallHomotopyLocalizationFunctor_essSurj (R := R)
  localNerve := CostExactZigzagNerveComparison.core (R := R)
  relativeZigzagMappingSpace := CostExactZigzagMappingSpace.core
  presentedDwyerKan := presentedDwyerKanCore (R := R)
  linearHammockDwyerKan := linearHammockDwyerKanCore (R := R)
  sourceCompleteness := sourceCompletenessHomotopyEquivalence (R := R)
  targetCompleteness := targetCompletenessHomotopyEquivalence (R := R)
  relativeArrowGlue := relativeOuterComparison_sourceArrow
  relativeStringGlue := relativeOuterComparison_stringVertex
  mappedLocalVertexExact := mappedLocalVertexObject_eq
  relativeLocalVertexGlue := relativeOuter_mappedLocalVertex
  relativeLocalTwoCellGlue := relativeLocal_twoCellOneSkeleton
  relativeLocalTwoSimplexGlue := relativeLocal_twoSimplexGlue
  relativeLocalHorizontalTwoCellGlue := relativeLocal_horizontalTwoCellGlue
  relativeLocalHorizontalPastingGlue := relativeLocal_horizontalPastingGlue
  relativeLocalHorizontalPrismGlue := relativeLocal_horizontalPrismGlue
  relativeOuterLocalTwoArrowGlue := relativeOuterLocal_twoArrowGlue
  relativeOuterLocalPrismVerticesGlue :=
    relativeOuterLocal_prismVerticesGlue
  relativeOuterLocalAllPrismVerticesGlue :=
    relativeOuterLocal_allPrismVerticesGlue
  relativeOuterLocalAllPrismRestrictionVerticesGlue :=
    relativeOuterLocal_allPrismRestrictionVerticesGlue
  relativeOuterLocalAllPrismTargetFacesGlue :=
    relativeOuterLocal_allPrismTargetFacesGlue
  relativeLocalAllDegreePrismCore := relativeLocal_allDegreePrismCore
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
