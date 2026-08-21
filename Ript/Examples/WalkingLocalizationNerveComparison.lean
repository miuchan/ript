import Ript.Examples.TwoDimensionalWalkingLocalization
import Ript.Higher.LocalizationCompleteSegal

/-!
# Full local-nerve comparison for the two-dimensional walking localization

The parameterized walking localization is already a genuine bicategorical
localization: it adjoins a reverse 1-cell while retaining a noninvertible
Boolean-discard 2-cell.  This file applies the generic bicategorical nerve
comparison to that theorem.  The resulting machine-facing object acts on the
full non-groupoidal local nerves, maps every 2-cell exactly, carries a
simplicial compositor homotopy, and sends the marked generator to the forward
map of a chosen target adjoint equivalence.

This is the first nontrivial complete higher-localization/Rezk-local-layer
comparison in the repository.  It remains a walking example rather than the
still-open construction for the entire resource-process bicategory.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Examples.WalkingLocalizationNerveComparison

open CategoryTheory
open Opposite Simplicial
open Ript.Higher.BicategoricalNerveComparison
open Ript.Examples.TwoDimensionalWalkingLocalization

/-- The complete higher-localization local-nerve comparison for the
two-dimensional walking localization. -/
noncomputable def core : HigherLocalizationNerveCore inclusion marking :=
  higherLocalizationNerveCore inclusion marking
    inclusion_isBicategoricalLocalization

/-- The marked walking generator maps exactly to the forward 1-cell of its
chosen target adjoint equivalence. -/
theorem markedArrowVertex_mapsToEquivalence :
    ((core.toPseudofunctorNerveCore.localMap sourceZero sourceOne).app
        (op ⦋0⦌)) (ComposableArrows.mk₀ markedArrow) =
      ComposableArrows.mk₀
        (markedEquivalence inclusion marking core.localization
          markedArrow markedArrow_mem).hom :=
  core.markedVertex markedArrow markedArrow_mem

/-- The local-nerve comparison maps the retained Boolean-discard edge to the
actual pseudofunctor image of that noninvertible 2-cell, without groupoid
truncation. -/
theorem discardTwoCell_edge_mapsExactly :
    ((core.toPseudofunctorNerveCore.localMap sourceZero sourceZero).app
        (op ⦋1⦌)) (ComposableArrows.mk₁ discardTwoCell) =
      ComposableArrows.mk₁ (inclusion.map₂ discardTwoCell) :=
  core.toPseudofunctorNerveCore.mapsTwoCell discardTwoCell

/-- The mapped discard edge decodes to a genuinely noninvertible target
2-cell.  Thus the complete higher comparison simultaneously witnesses formal
1-cell inversion and retention of non-groupoidal local information. -/
theorem mappedDiscardTwoCell_remainsNoninvertible :
    ¬ IsIso (inclusion.map₂ discardTwoCell) :=
  inclusion_map₂_discardTwoCell_not_isIso

/-- Horizontal composition in the walking localization comparison commutes
with the pseudofunctor action up to the compiled simplicial compositor
homotopy. -/
noncomputable def compositionHomotopy (X Y Z : Source) :
    SSet.Homotopy
      (CategoryTheory.nerveMap
        (composeThenMapFunctor inclusion X Y Z))
      (CategoryTheory.nerveMap
        (mapThenComposeFunctor inclusion X Y Z)) :=
  core.toPseudofunctorNerveCore.compositionHomotopy X Y Z

end Ript.Examples.WalkingLocalizationNerveComparison
