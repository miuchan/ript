import Ript.Higher.CostExactZigzagNerveComparison
import Ript.ForMathlib.AlgebraicTopology.GroupoidalCompleteSegal
import Ript.ForMathlib.CategoryTheory.Bicategory.MarkedZigzagLinearHammock
import Ript.ForMathlib.CategoryTheory.Bicategory.MarkedZigzagMappingNervePresentation

/-!
# Relative cost-exact zigzag mapping-space presentation

The presented cost-exact localization already constructs, from source data,
the category whose objects are typed marked-zigzag words and whose morphisms
are quotient 2-cells. This file exposes the nerve of that category as the
relative-zigzag mapping-space presentation.

For every pair of process models, the presented mapping nerve is proved
categorically equivalent to the actual full local mapping nerve of the
localization target. The comparison has a `NerveEquivalenceWitness`, an
explicit simplicial homotopy inverse, exact action in every degree, and the
existing source-to-target local nerve map factors through it strictly.

This is a representation theorem for the chosen marked-zigzag presentation.
It does not yet identify the presentation with a separately defined hammock
or other model-independent derived mapping space, and therefore is not by
itself the final Dwyer--Kan theorem.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Higher.CostExactZigzagMappingSpace

open CategoryTheory
open Opposite Simplicial
open Ript.Higher.UniverseLiftedNerve

universe u v w

variable {R : Type w} [AddCommMonoid R] [PartialOrder R]

/-- Canonical source-defined interpretation of the cost-exact local
presentation into its own quotient word category. Words are fixed and raw
cells map to their quotient representatives. -/
def identityInterpretation (M N : ProcessModel.{u, v, w} R) :
    Bicategory.MarkedZigzag.Presented.LocalInterpretation
      (costExactArrows R) M N
      (CostExactZigzag.Word (R := R) M N) where
  obj word := word
  map alpha := Bicategory.MarkedZigzag.Presented.mk
    (costExactArrows R) alpha
  map_rel relation := Quot.sound relation
  map_id _ := rfl
  map_vcomp _ _ := rfl

/-- The literal quotient-hom action is a compatible lift of the canonical
cost-exact local interpretation. -/
def identityLift (M N : ProcessModel.{u, v, w} R) :
    Bicategory.MarkedZigzag.Presented.LocalInterpretation.LocalLift
      (costExactArrows R) M N (identityInterpretation M N) where
  mapHom cell := cell
  map_id _ := rfl
  map_comp _ _ := rfl
  map_mk _ := rfl

/-- Cost-exact specialization of the target-independent local presentation
universal property. The literal quotient lift is the canonical descent, and
every compatible lift is uniquely that descent. -/
def LocalPresentationCore
    (M N : ProcessModel.{u, v, w} R) : Prop :=
  identityLift M N =
      Bicategory.MarkedZigzag.Presented.LocalInterpretation.descendLift
        (costExactArrows R) M N (identityInterpretation M N) ∧
  (∀ (L :
      Bicategory.MarkedZigzag.Presented.LocalInterpretation.LocalLift
        (costExactArrows R) M N (identityInterpretation M N)),
      L = Bicategory.MarkedZigzag.Presented.LocalInterpretation.descendLift
        (costExactArrows R) M N (identityInterpretation M N)) ∧
  ∀ (L :
      Bicategory.MarkedZigzag.Presented.LocalInterpretation.LocalLift
        (costExactArrows R) M N (identityInterpretation M N)),
    Bicategory.MarkedZigzag.Presented.LocalInterpretation.liftNerveMap
        (costExactArrows R) M N (identityInterpretation M N) L =
      Bicategory.MarkedZigzag.Presented.LocalInterpretation.nerveMap
        (costExactArrows R) M N (identityInterpretation M N)

/-- Every cost-exact model pair satisfies the source-defined local
presentation universal property. -/
theorem localPresentationCore (M N : ProcessModel.{u, v, w} R) :
    LocalPresentationCore M N := by
  refine ⟨?_, ?_, ?_⟩
  · exact
    Bicategory.MarkedZigzag.Presented.LocalInterpretation.lift_unique
      (costExactArrows R) M N (identityInterpretation M N)
        (identityLift M N)
  ·
    intro L
    exact Bicategory.MarkedZigzag.Presented.LocalInterpretation.lift_unique
      (costExactArrows R) M N (identityInterpretation M N) L
  · intro L
    exact
      Bicategory.MarkedZigzag.Presented.LocalInterpretation.liftNerveMap_unique
        (costExactArrows R) M N (identityInterpretation M N) L

/-- Common-universe small replacement of the source-defined category of
cost-exact marked-zigzag words and quotient 2-cells from `M` to `N`. -/
abbrev RelativeZigzagMappingCategory
    (M N : ProcessModel.{u, v, w} R) :=
  AsSmall.{max (max w (v + 1)) (u + 1)}
    (CostExactZigzag.Word (R := R) M N)

/-- The relative cost-exact zigzag mapping-space presentation is the
categorical nerve of the presented word/quotient-2-cell category. -/
abbrev RelativeZigzagMappingNerve
    (M N : ProcessModel.{u, v, w} R) :=
  CategoryTheory.nerve (RelativeZigzagMappingCategory M N)

/-- Independently defined right-associated linear hammock words for the
cost-exact marking. -/
abbrev LinearHammock (M N : ProcessModel.{u, v, w} R) :=
  Bicategory.MarkedZigzag.LinearWord (costExactArrows R) M N

/-- Common-universe linear hammock mapping category. -/
abbrev LinearHammockMappingCategory
    (M N : ProcessModel.{u, v, w} R) :=
  AsSmall.{max (max w (v + 1)) (u + 1)} (LinearHammock M N)

/-- Categorical nerve of the independent linear hammock mapping category. -/
abbrev LinearHammockMappingNerve
    (M N : ProcessModel.{u, v, w} R) :=
  CategoryTheory.nerve (LinearHammockMappingCategory M N)

/-- An arbitrary-height linear hammock grid. It contains `n + 1` rows of
linear hammock words, `n` adjacent quotient-2-cell edges, and the source and
target endpoint equations for every edge. -/
abbrev LinearHammockGrid
    (M N : ProcessModel.{u, v, w} R) (n : ℕ) :=
  SSet.Path (LinearHammockMappingNerve M N) n

/-- Strict-Segal representation of every linear hammock nerve simplex as an
explicit arbitrary-height row grid. -/
def linearHammockGridEquiv
    (M N : ProcessModel.{u, v, w} R) (n : ℕ) :
    (LinearHammockMappingNerve M N).obj (op ⦋n⦌) ≃
      LinearHammockGrid M N n :=
  (CategoryTheory.Nerve.strictSegal
    (LinearHammockMappingCategory M N)).spineEquiv n

/-- The `i`th row of a represented grid is the corresponding vertex
restriction of the original simplex. -/
@[simp]
theorem linearHammockGridEquiv_vertex
    (M N : ProcessModel.{u, v, w} R) {n : ℕ}
    (simplex : (LinearHammockMappingNerve M N).obj (op ⦋n⦌))
    (i : Fin (n + 1)) :
    (linearHammockGridEquiv M N n simplex).vertex i =
      (LinearHammockMappingNerve M N).map
        (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op simplex := by
  rfl

/-- The `i`th adjacent grid edge is the corresponding spine edge restriction
of the original simplex. -/
@[simp]
theorem linearHammockGridEquiv_arrow
    (M N : ProcessModel.{u, v, w} R) {n : ℕ}
    (simplex : (LinearHammockMappingNerve M N).obj (op ⦋n⦌))
    (i : Fin n) :
    (linearHammockGridEquiv M N n simplex).arrow i =
      (LinearHammockMappingNerve M N).map
        (SimplexCategory.mkOfSucc i).op simplex := by
  rfl

/-- Reconstructing a simplex from a grid and extracting its grid is the
identity. -/
theorem linearHammockGridEquiv_symm_apply
    (M N : ProcessModel.{u, v, w} R) {n : ℕ}
    (grid : LinearHammockGrid M N n) :
    linearHammockGridEquiv M N n
        ((linearHammockGridEquiv M N n).symm grid) = grid :=
  (linearHammockGridEquiv M N n).apply_symm_apply grid

/-- Extracting the grid of a simplex and reconstructing the simplex is the
identity. -/
theorem linearHammockGridEquiv_apply_symm
    (M N : ProcessModel.{u, v, w} R) {n : ℕ}
    (simplex : (LinearHammockMappingNerve M N).obj (op ⦋n⦌)) :
    (linearHammockGridEquiv M N n).symm
        (linearHammockGridEquiv M N n simplex) = simplex :=
  (linearHammockGridEquiv M N n).symm_apply_apply simplex

/-- Package one adjacent row transition as an edge with its endpoint
equations. -/
def linearHammockGridEdge
    {M N : ProcessModel.{u, v, w} R} {n : ℕ}
    (grid : LinearHammockGrid M N n) (i : Fin n) :
    (LinearHammockMappingNerve M N).Edge
      (grid.vertex i.castSucc) (grid.vertex i.succ) :=
  SSet.Edge.mk (grid.arrow i) (grid.arrow_src i) (grid.arrow_tgt i)

/-- Decode one grid row from the common-universe nerve vertex back to its raw
linear hammock word. -/
def linearHammockGridRow
    {M N : ProcessModel.{u, v, w} R} {n : ℕ}
    (grid : LinearHammockGrid M N n) (i : Fin (n + 1)) :
    LinearHammock M N :=
  AsSmall.down.obj (CategoryTheory.nerveEquiv (grid.vertex i))

/-- Row decoding of a represented grid recovers exactly the corresponding
object of the original nerve simplex. -/
@[simp]
theorem linearHammockGridRow_equiv
    (M N : ProcessModel.{u, v, w} R) {n : ℕ}
    (simplex : (LinearHammockMappingNerve M N).obj (op ⦋n⦌))
    (i : Fin (n + 1)) :
    linearHammockGridRow (linearHammockGridEquiv M N n simplex) i =
      AsSmall.down.obj (simplex.obj i) := by
  rfl

/-- The source-defined relative mapping category is categorically equivalent
to the actual local hom-category of the presented localization target. The
underlying categories are definitionally the same presentation, but this
equivalence records their two semantic roles explicitly. -/
def comparisonEquivalence (M N : ProcessModel.{u, v, w} R) :
    RelativeZigzagMappingCategory M N ≌
      CommonTargetHom (CostExactZigzag.inclusion (R := R)) M N :=
  CategoryTheory.Equivalence.refl

/-- All-dimensional simplicial comparison from the relative-zigzag mapping
nerve to the actual full local target mapping nerve. -/
def comparison (M N : ProcessModel.{u, v, w} R) :
    RelativeZigzagMappingNerve M N ⟶
      CommonTargetMappingNerve
        (CostExactZigzag.inclusion (R := R)) M N :=
  CategoryTheory.nerveMap (comparisonEquivalence M N).functor

/-- Categorical-nerve equivalence evidence for the relative-zigzag mapping
comparison. -/
def comparisonNerveEquivalence (M N : ProcessModel.{u, v, w} R) :
    SSet.NerveEquivalenceWitness (comparison M N) :=
  SSet.NerveEquivalenceWitness.ofEquivalence (comparisonEquivalence M N)

/-- Explicit inverse and both simplicial homotopies for the relative-zigzag
mapping comparison. -/
noncomputable def comparisonHomotopyEquivalence
    (M N : ProcessModel.{u, v, w} R) :
    SSet.HomotopyEquivalenceWitness (comparison M N) :=
  SSet.HomotopyEquivalenceWitness.ofCategoryEquivalence
    (comparisonEquivalence M N)

/-- Common-universe equivalence from independently defined linear hammock
words to the presented binary word/quotient-2-cell mapping category. -/
noncomputable def linearHammockEquivalence
    (M N : ProcessModel.{u, v, w} R) :
    LinearHammockMappingCategory M N ≌
      RelativeZigzagMappingCategory M N :=
  AsSmall.equiv.symm.trans
    ((Bicategory.MarkedZigzag.LinearWord.equivalence
      (costExactArrows R) M N).trans AsSmall.equiv)

/-- Simplicial comparison from the independent linear hammock nerve to the
presented relative-zigzag mapping nerve. -/
noncomputable def linearComparison (M N : ProcessModel.{u, v, w} R) :
    LinearHammockMappingNerve M N ⟶
      RelativeZigzagMappingNerve M N :=
  CategoryTheory.nerveMap (linearHammockEquivalence M N).functor

/-- Categorical-nerve equivalence evidence for the linear-to-presented
mapping-space comparison. -/
noncomputable def linearComparisonNerveEquivalence
    (M N : ProcessModel.{u, v, w} R) :
    SSet.NerveEquivalenceWitness (linearComparison M N) :=
  SSet.NerveEquivalenceWitness.ofEquivalence
    (linearHammockEquivalence M N)

/-- Explicit inverse and both simplicial homotopies for the linear-to-
presented mapping comparison. -/
noncomputable def linearComparisonHomotopyEquivalence
    (M N : ProcessModel.{u, v, w} R) :
    SSet.HomotopyEquivalenceWitness (linearComparison M N) :=
  SSet.HomotopyEquivalenceWitness.ofCategoryEquivalence
    (linearHammockEquivalence M N)

/-- Direct category equivalence from independent linear hammocks to the
actual localization-target local hom-category. -/
noncomputable def linearTargetEquivalence
    (M N : ProcessModel.{u, v, w} R) :
    LinearHammockMappingCategory M N ≌
      CommonTargetHom (CostExactZigzag.inclusion (R := R)) M N :=
  (linearHammockEquivalence M N).trans (comparisonEquivalence M N)

/-- Direct simplicial comparison from independent linear hammocks to the
actual target local mapping nerve. -/
noncomputable def linearTargetComparison
    (M N : ProcessModel.{u, v, w} R) :
    LinearHammockMappingNerve M N ⟶
      CommonTargetMappingNerve
        (CostExactZigzag.inclusion (R := R)) M N :=
  CategoryTheory.nerveMap (linearTargetEquivalence M N).functor

/-- Categorical-nerve equivalence evidence for the direct linear-hammock-to-
target comparison. -/
noncomputable def linearTargetNerveEquivalence
    (M N : ProcessModel.{u, v, w} R) :
    SSet.NerveEquivalenceWitness (linearTargetComparison M N) :=
  SSet.NerveEquivalenceWitness.ofEquivalence (linearTargetEquivalence M N)

/-- Explicit inverse and both simplicial homotopies for the direct linear-
hammock-to-target comparison. -/
noncomputable def linearTargetHomotopyEquivalence
    (M N : ProcessModel.{u, v, w} R) :
    SSet.HomotopyEquivalenceWitness (linearTargetComparison M N) :=
  SSet.HomotopyEquivalenceWitness.ofCategoryEquivalence
    (linearTargetEquivalence M N)

/-- Common-universe functor embedding every source 1-cell and 2-cell into the
relative-zigzag mapping category as a forward word and original quotient
2-cell. -/
def forwardFunctor (M N : ProcessModel.{u, v, w} R) :
    CommonSourceHom (CostExactZigzag.inclusion (R := R)) M N ⥤
      RelativeZigzagMappingCategory M N :=
  commonAsSmallFunctor (CostExactZigzag.forwardHomFunctor M N)

/-- Nerve map from the original full local source category into its
relative-zigzag mapping-space presentation. -/
def forwardMap (M N : ProcessModel.{u, v, w} R) :
    CommonLocalMappingNerve
        (CostExactZigzag.inclusion (R := R)) M N ⟶
      RelativeZigzagMappingNerve M N :=
  commonNerveMap (CostExactZigzag.forwardHomFunctor M N)

/-- A presented marked-zigzag word as a vertex of the relative mapping
nerve. -/
def relativeWordVertex {M N : ProcessModel.{u, v, w} R}
    (word : CostExactZigzag.Word (R := R) M N) :
    (RelativeZigzagMappingNerve M N).obj (op ⦋0⦌) :=
  ComposableArrows.mk₀ ((AsSmall.up :
    CostExactZigzag.Word (R := R) M N ⥤
      RelativeZigzagMappingCategory M N).obj word)

/-- The same presented word as an actual vertex of the localization target's
full local mapping nerve. -/
def targetWordVertex {M N : ProcessModel.{u, v, w} R}
    (word : CostExactZigzag.Word (R := R) M N) :
    (CommonTargetMappingNerve
      (CostExactZigzag.inclusion (R := R)) M N).obj (op ⦋0⦌) :=
  ComposableArrows.mk₀ ((AsSmall.up :
    (CostExactZigzag.inclusion.obj M ⟶ CostExactZigzag.inclusion.obj N) ⥤
      CommonTargetHom (CostExactZigzag.inclusion (R := R)) M N).obj word)

/-- A quotient 2-cell between presented words as an edge of the relative
mapping nerve. -/
def relativeCellEdge {M N : ProcessModel.{u, v, w} R}
    {first second : CostExactZigzag.Word (R := R) M N}
    (cell : first ⟶ second) :
    (RelativeZigzagMappingNerve M N).obj (op ⦋1⦌) :=
  ComposableArrows.mk₁ ((AsSmall.up :
    CostExactZigzag.Word (R := R) M N ⥤
      RelativeZigzagMappingCategory M N).map cell)

/-- The same quotient 2-cell as an actual edge of the localization target's
full local mapping nerve. -/
def targetCellEdge {M N : ProcessModel.{u, v, w} R}
    {first second : CostExactZigzag.Word (R := R) M N}
    (cell : first ⟶ second) :
    (CommonTargetMappingNerve
      (CostExactZigzag.inclusion (R := R)) M N).obj (op ⦋1⦌) :=
  ComposableArrows.mk₁ ((AsSmall.up :
    (CostExactZigzag.inclusion.obj M ⟶ CostExactZigzag.inclusion.obj N) ⥤
      CommonTargetHom (CostExactZigzag.inclusion (R := R)) M N).map cell)

/-- The mapping comparison sends every presented word vertex to the exact
same word in the actual target local nerve. -/
theorem comparison_wordVertex {M N : ProcessModel.{u, v, w} R}
    (word : CostExactZigzag.Word (R := R) M N) :
    (comparison M N).app (op ⦋0⦌) (relativeWordVertex word) =
      targetWordVertex word := by
  rfl

/-- The mapping comparison sends every quotient 2-cell edge to the exact
same target-local edge. -/
theorem comparison_cellEdge {M N : ProcessModel.{u, v, w} R}
    {first second : CostExactZigzag.Word (R := R) M N}
    (cell : first ⟶ second) :
    (comparison M N).app (op ⦋1⦌) (relativeCellEdge cell) =
      targetCellEdge cell := by
  rfl

/-- In every simplicial degree, the mapping comparison preserves the entire
presented chain literally. -/
theorem comparison_simplex (M N : ProcessModel.{u, v, w} R)
    {n : ℕ} (x : (RelativeZigzagMappingNerve M N).obj (op ⦋n⦌)) :
    (comparison M N).app (op ⦋n⦌) x = x := by
  rfl

/-- The source-to-relative map sends every source 1-cell vertex to its exact
one-step forward marked-zigzag word. -/
theorem forwardMap_vertex {M N : ProcessModel.{u, v, w} R}
    (f : M ⟶ N) :
    (forwardMap M N).app (op ⦋0⦌)
        (ComposableArrows.mk₀ ((AsSmall.up :
          (M ⟶ N) ⥤ CommonSourceHom
            (CostExactZigzag.inclusion (R := R)) M N).obj f)) =
      relativeWordVertex (CostExactZigzag.forward f) := by
  exact commonNerveMap_vertex (CostExactZigzag.forwardHomFunctor M N) f

/-- The source-to-relative map sends every arbitrary source 2-cell edge to
its exact original quotient-2-cell generator. -/
theorem forwardMap_twoCell {M N : ProcessModel.{u, v, w} R}
    {f g : M ⟶ N} (alpha : f ⟶ g) :
    (forwardMap M N).app (op ⦋1⦌)
        (ComposableArrows.mk₁ ((AsSmall.up :
          (M ⟶ N) ⥤ CommonSourceHom
            (CostExactZigzag.inclusion (R := R)) M N).map alpha)) =
      relativeCellEdge ((CostExactZigzag.forwardHomFunctor M N).map alpha) := by
  exact commonNerveMap_edge (CostExactZigzag.forwardHomFunctor M N) alpha

/-- In every simplicial degree, the source-to-relative map applies the
forward-word functor to the entire source 2-cell chain. -/
theorem forwardMap_simplex (M N : ProcessModel.{u, v, w} R)
    {n : ℕ}
    (x : (CommonLocalMappingNerve
      (CostExactZigzag.inclusion (R := R)) M N).obj (op ⦋n⦌)) :
    (forwardMap M N).app (op ⦋n⦌) x = x ⋙ forwardFunctor M N := by
  rfl

/-- **Strict mapping-space factorization.** The previously constructed full
local nerve map is exactly the composite of the source-to-relative marked-
zigzag map and the relative-zigzag-to-target comparison, in all degrees. -/
theorem localMap_factorization (M N : ProcessModel.{u, v, w} R) :
    (CostExactZigzagNerveComparison.core
      (R := R)).toPseudofunctorNerveCore.localMap M N =
      forwardMap M N ≫ comparison M N := by
  rfl

/-- Complete represented relative-zigzag mapping-space comparison for one
pair of process models. -/
structure MappingSpaceCore (M N : ProcessModel.{u, v, w} R) where
  /-- Source-defined quotient-presentation universal property. -/
  localPresentation : LocalPresentationCore M N
  /-- Arbitrary-height row-grid representation of every linear hammock nerve
  simplex. -/
  linearGridRepresentation : ∀ n : ℕ,
    (LinearHammockMappingNerve M N).obj (op ⦋n⦌) ≃
      LinearHammockGrid M N n
  /-- Independent linear hammock nerve is categorically equivalent to the
  presented relative mapping nerve. -/
  linearNerveEquivalence :
    SSet.NerveEquivalenceWitness (linearComparison M N)
  /-- Explicit simplicial homotopy inverse for the linear-to-presented
  comparison. -/
  linearHomotopyEquivalence :
    SSet.HomotopyEquivalenceWitness (linearComparison M N)
  /-- Independent linear hammock nerve is categorically equivalent directly
  to the actual target local nerve. -/
  linearTargetNerveEquivalence :
    SSet.NerveEquivalenceWitness (linearTargetComparison M N)
  /-- Explicit simplicial homotopy inverse for the direct linear-to-target
  comparison. -/
  linearTargetHomotopyEquivalence :
    SSet.HomotopyEquivalenceWitness (linearTargetComparison M N)
  /-- Categorical equivalence between the source-presented zigzag category
  and the actual target local hom-category. -/
  categoricalEquivalence : RelativeZigzagMappingCategory M N ≌
    CommonTargetHom (CostExactZigzag.inclusion (R := R)) M N
  /-- Categorical-nerve equivalence presentation of the comparison. -/
  nerveEquivalence : SSet.NerveEquivalenceWitness (comparison M N)
  /-- Explicit simplicial inverse and both homotopies. -/
  homotopyEquivalence : SSet.HomotopyEquivalenceWitness (comparison M N)
  /-- Strict all-dimensional factorization of the existing full local map. -/
  factorization :
    (CostExactZigzagNerveComparison.core
      (R := R)).toPseudofunctorNerveCore.localMap M N =
      forwardMap M N ≫ comparison M N
  /-- Exact action on every presented word vertex. -/
  mapsWordVertex : ∀ word, (comparison M N).app (op ⦋0⦌)
    (relativeWordVertex word) = targetWordVertex word
  /-- Exact action on every quotient 2-cell edge. -/
  mapsCellEdge : ∀ {first second} (cell : first ⟶ second),
    (comparison M N).app (op ⦋1⦌) (relativeCellEdge cell) =
      targetCellEdge cell
  /-- Exact action on every presented simplex in every degree. -/
  mapsSimplex : ∀ {n : ℕ}
    (x : (RelativeZigzagMappingNerve M N).obj (op ⦋n⦌)),
    (comparison M N).app (op ⦋n⦌) x = x
  /-- Exact embedding of every source 1-cell as a forward word. -/
  mapsForwardVertex : ∀ (f : M ⟶ N),
    (forwardMap M N).app (op ⦋0⦌)
        (ComposableArrows.mk₀ ((AsSmall.up :
          (M ⟶ N) ⥤ CommonSourceHom
            (CostExactZigzag.inclusion (R := R)) M N).obj f)) =
      relativeWordVertex (CostExactZigzag.forward f)
  /-- Exact embedding of arbitrary source 2-cells as original quotient
  generators. -/
  mapsTwoCell : ∀ {f g : M ⟶ N} (alpha : f ⟶ g),
    (forwardMap M N).app (op ⦋1⦌)
        (ComposableArrows.mk₁ ((AsSmall.up :
          (M ⟶ N) ⥤ CommonSourceHom
            (CostExactZigzag.inclusion (R := R)) M N).map alpha)) =
      relativeCellEdge ((CostExactZigzag.forwardHomFunctor M N).map alpha)
  /-- Exact all-dimensional source-simplex action. -/
  mapsSourceSimplex : ∀ {n : ℕ}
    (x : (CommonLocalMappingNerve
      (CostExactZigzag.inclusion (R := R)) M N).obj (op ⦋n⦌)),
    (forwardMap M N).app (op ⦋n⦌) x = x ⋙ forwardFunctor M N

/-- Every pair of process models has the complete represented relative-
zigzag mapping-space comparison. -/
noncomputable def core (M N : ProcessModel.{u, v, w} R) :
    MappingSpaceCore M N where
  localPresentation := localPresentationCore M N
  linearGridRepresentation := linearHammockGridEquiv M N
  linearNerveEquivalence := linearComparisonNerveEquivalence M N
  linearHomotopyEquivalence := linearComparisonHomotopyEquivalence M N
  linearTargetNerveEquivalence := linearTargetNerveEquivalence M N
  linearTargetHomotopyEquivalence := linearTargetHomotopyEquivalence M N
  categoricalEquivalence := comparisonEquivalence M N
  nerveEquivalence := comparisonNerveEquivalence M N
  homotopyEquivalence := comparisonHomotopyEquivalence M N
  factorization := localMap_factorization M N
  mapsWordVertex := comparison_wordVertex
  mapsCellEdge := comparison_cellEdge
  mapsSimplex := comparison_simplex M N
  mapsForwardVertex := forwardMap_vertex
  mapsTwoCell := forwardMap_twoCell
  mapsSourceSimplex := forwardMap_simplex M N

end Ript.Higher.CostExactZigzagMappingSpace
