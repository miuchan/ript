import Ript.Higher.UniverseLiftedLocalizationCompleteSegal
import Ript.Higher.CostExactZigzag

/-!
# Universe-lifted nerve comparison for the cost-exact localization

This module instantiates the common-universe full-local-nerve construction for
the executable cost-exact marked-zigzag localization. It packages the proved
bicategorical universal property, exact action on arbitrary 2-cells, marked
vertices landing at target adjoint equivalences, and the compositor simplicial
homotopy together with the unit simplicial homotopy and exact lifted
associator/unitor edge coherence.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Higher.CostExactZigzagNerveComparison

open CategoryTheory
open Opposite Simplicial
open Ript.Higher.UniverseLiftedNerve

universe u v w

variable {R : Type w} [AddCommMonoid R] [PartialOrder R]

/-- Complete common-universe full-local-nerve comparison for the cost-exact
marked-zigzag localization. -/
noncomputable def core :
    HigherLocalizationNerveCore
      (CostExactZigzag.inclusion (R := R)) (costExactArrows R)
      CostExactZigzag.inclusion_isBicategoricalLocalization :=
  higherLocalizationNerveCore
    (CostExactZigzag.inclusion (R := R)) (costExactArrows R)
    CostExactZigzag.inclusion_isBicategoricalLocalization

/-- Every cost-exact source arrow maps to the lifted vertex of its chosen
target adjoint equivalence. -/
theorem markedVertex_mapsToEquivalence
    {M N : ProcessModel.{u, v, w} R} (f : M ⟶ N)
    (hf : costExactArrows R f) :
    (core.toPseudofunctorNerveCore.localMap M N).app (op ⦋0⦌)
        (ComposableArrows.mk₀ ((AsSmall.up :
          (M ⟶ N) ⥤ CommonSourceHom CostExactZigzag.inclusion M N).obj f)) =
      ComposableArrows.mk₀ ((AsSmall.up :
        (CostExactZigzag.inclusion.obj M ⟶
          CostExactZigzag.inclusion.obj N) ⥤
            CommonTargetHom CostExactZigzag.inclusion M N).obj
        (markedEquivalence CostExactZigzag.inclusion (costExactArrows R)
          CostExactZigzag.inclusion_isBicategoricalLocalization f hf).hom) :=
  core.markedVertex f hf

/-- The comparison maps every source 2-cell edge to the lifted exact
pseudofunctor image. -/
theorem twoCell_edge_mapsExactly
    {M N : ProcessModel.{u, v, w} R} {f g : M ⟶ N} (α : f ⟶ g) :
    (core.toPseudofunctorNerveCore.localMap M N).app (op ⦋1⦌)
        (ComposableArrows.mk₁ ((AsSmall.up :
          (M ⟶ N) ⥤ CommonSourceHom CostExactZigzag.inclusion M N).map α)) =
      ComposableArrows.mk₁ ((AsSmall.up :
        (CostExactZigzag.inclusion.obj M ⟶
          CostExactZigzag.inclusion.obj N) ⥤
            CommonTargetHom CostExactZigzag.inclusion M N).map
        (CostExactZigzag.inclusion.map₂ α)) :=
  core.toPseudofunctorNerveCore.mapsTwoCell α

/-- The comparison maps every vertically composable pair of source 2-cells
to the canonical 2-simplex of their lifted exact images. -/
theorem twoCell_twoSimplex_mapsExactly
    {M N : ProcessModel.{u, v, w} R}
    {f g h : M ⟶ N} (α : f ⟶ g) (β : g ⟶ h) :
    (core.toPseudofunctorNerveCore.localMap M N).app (op ⦋2⦌)
        (ComposableArrows.mk₂
          ((AsSmall.up :
            (M ⟶ N) ⥤ CommonSourceHom CostExactZigzag.inclusion M N).map α)
          ((AsSmall.up :
            (M ⟶ N) ⥤ CommonSourceHom CostExactZigzag.inclusion M N).map β)) =
      ComposableArrows.mk₂
        ((AsSmall.up :
          (CostExactZigzag.inclusion.obj M ⟶
            CostExactZigzag.inclusion.obj N) ⥤
              CommonTargetHom CostExactZigzag.inclusion M N).map
            (CostExactZigzag.inclusion.map₂ α))
        ((AsSmall.up :
          (CostExactZigzag.inclusion.obj M ⟶
            CostExactZigzag.inclusion.obj N) ⥤
              CommonTargetHom CostExactZigzag.inclusion M N).map
            (CostExactZigzag.inclusion.map₂ β)) :=
  core.toPseudofunctorNerveCore.mapsTwoSimplex α β

/-- The cost-exact comparison maps both sides of simultaneous horizontal
2-cell composition exactly and satisfies the lifted compositor naturality
square. -/
theorem horizontalTwoCell_compositionGlue
    {M N P : ProcessModel.{u, v, w} R}
    {f₀ f₁ : M ⟶ N} {g₀ g₁ : N ⟶ P}
    (α : f₀ ⟶ f₁) (β : g₀ ⟶ g₁) :
    CommonHorizontalCompositionGlue
      (CostExactZigzag.inclusion (R := R)) α β :=
  (core (R := R)).toPseudofunctorNerveCore.horizontalCompositionGlue α β

/-- In particular, the two common-universe local-nerve paths around the
cost-exact compositor square have the same composite edge. -/
theorem horizontalTwoCell_compositorSquare
    {M N P : ProcessModel.{u, v, w} R}
    {f₀ f₁ : M ⟶ N} {g₀ g₁ : N ⟶ P}
    (α : f₀ ⟶ f₁) (β : g₀ ⟶ g₁) :
    CommonHorizontalCompositionSquare
      (CostExactZigzag.inclusion (R := R)) α β :=
  (horizontalTwoCell_compositionGlue α β).2.2

/-- The cost-exact comparison maps both sides of a vertically composable
horizontal pair 2-simplex exactly and satisfies interchange plus compositor
rectangle pasting. -/
theorem horizontalTwoCell_pastingGlue
    {M N P : ProcessModel.{u, v, w} R}
    {f₀ f₁ f₂ : M ⟶ N} {g₀ g₁ g₂ : N ⟶ P}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) :
    CommonHorizontalCompositionPastingGlue
      (CostExactZigzag.inclusion (R := R)) α₀ α₁ β₀ β₁ :=
  (core (R := R)).toPseudofunctorNerveCore.horizontalCompositionPastingGlue
    α₀ α₁ β₀ β₁

/-- The lifted long edges of the cost-exact vertically pasted compositor
rectangle agree exactly. -/
theorem horizontalTwoCell_pastedCompositorSquare
    {M N P : ProcessModel.{u, v, w} R}
    {f₀ f₁ f₂ : M ⟶ N} {g₀ g₁ g₂ : N ⟶ P}
    (α₀ : f₀ ⟶ f₁) (α₁ : f₁ ⟶ f₂)
    (β₀ : g₀ ⟶ g₁) (β₁ : g₁ ⟶ g₂) :
    CommonHorizontalCompositionPastedSquare
      (CostExactZigzag.inclusion (R := R)) α₀ α₁ β₀ β₁ :=
  (horizontalTwoCell_pastingGlue α₀ α₁ β₀ β₁).2.2.2

/-- The cost-exact comparison satisfies the exact lifted associator-edge
coherence law. -/
theorem associatorEdgeCoherence
    {A B C D : ProcessModel.{u, v, w} R}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) :
    CommonAssociatorCompatibility
      (CostExactZigzag.inclusion (R := R)) f g h :=
  (core (R := R)).toPseudofunctorNerveCore.associatorCoherence f g h

/-- The cost-exact comparison satisfies the exact lifted left-unitor-edge
coherence law. -/
theorem leftUnitorEdgeCoherence
    {A B : ProcessModel.{u, v, w} R} (f : A ⟶ B) :
    CommonLeftUnitorCompatibility
      (CostExactZigzag.inclusion (R := R)) f :=
  (core (R := R)).toPseudofunctorNerveCore.leftUnitorCoherence f

/-- The cost-exact comparison satisfies the exact lifted right-unitor-edge
coherence law. -/
theorem rightUnitorEdgeCoherence
    {A B : ProcessModel.{u, v, w} R} (f : A ⟶ B) :
    CommonRightUnitorCompatibility
      (CostExactZigzag.inclusion (R := R)) f :=
  (core (R := R)).toPseudofunctorNerveCore.rightUnitorCoherence f

/-- The pseudofunctor unit constraint induces a genuine simplicial homotopy
between the mapped source identity and the localization-target identity. -/
noncomputable def identityHomotopy
    (M : ProcessModel.{u, v, w} R) :=
  (core (R := R)).toPseudofunctorNerveCore.identityHomotopy M

/-- The pseudofunctor compositor induces a genuine simplicial homotopy after
the common-universe replacement. -/
noncomputable def compositionHomotopy
    (M N P : ProcessModel.{u, v, w} R) :=
  (core (R := R)).toPseudofunctorNerveCore.compositionHomotopy M N P

end Ript.Higher.CostExactZigzagNerveComparison
