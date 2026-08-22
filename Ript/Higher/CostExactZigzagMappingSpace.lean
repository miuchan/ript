import Ript.Higher.CostExactZigzagNerveComparison
import Ript.ForMathlib.AlgebraicTopology.GroupoidalCompleteSegal
import Ript.ForMathlib.CategoryTheory.Bicategory.MarkedZigzagAlignedHammock
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

The file also supplies an independent linear-word model, arbitrary-height row
paths, and a fixed-shape aligned multi-column hammock fragment with exact
quotient and nerve interpretation.  Elementary executable identity/composite
column refinements and marked unit/counit pair refinements now have exact
signed width and semantic round trips. Common-refinement spans now generate a
row quotient whose equality is sound for semantic isomorphism. A quotient
thin groupoid/nerve is now equivalent to the discrete quotient with an explicit
simplicial homotopy inverse. A non-thin semantic refinement-path groupoid nerve
is now equivalent to its exact refinement-generated semantic image subgroupoid.
The image includes faithfully into the full linear mapping category, the
original semantic nerve map factors through it strictly, and generator edges
retain their literal quotient-2-cell interpretations. A larger non-groupoidal
generated hammock-path nerve now adds arbitrary aligned raw cells, contains
the refinement-path nerve faithfully, and covers every source 2-cell in its
canonical one-column representation. Generated paths are now also closed under
normalized left/right whiskering and horizontal append, with exact three-model
nerve formulas. A raw-cell normalization core records the completed identity,
original, source-identity/inverse, source-composition/inverse, vertical,
whiskering, marked-pair/inverse, and transport branches, plus a conditional
all-cell induction from six remaining structural generators. Coverage of all
presented quotient 2-cells, competing-move
coherence, and reduced-hammock invariance are still absent, so these results
are not by themselves the final Dwyer--Kan theorem.
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

/-- One horizontally column-aligned raw hammock cell between two cost-exact
linear rows. -/
abbrev AlignedHammockCell {M N : ProcessModel.{u, v, w} R}
    (source target : LinearHammock M N) :=
  Bicategory.MarkedZigzag.AlignedCell (costExactArrows R) source target

/-- Executable identity/composition column refinements for cost-exact linear
hammock rows. -/
abbrev HammockColumnRefinement {M N : ProcessModel.{u, v, w} R}
    (source target : LinearHammock M N) :=
  Bicategory.MarkedZigzag.ColumnRefinement (costExactArrows R) source target

/-- An explicit aligned multi-column hammock grid of height `n`.  Every row is
a linear marked zigzag and every adjacent pair is connected by componentwise
atomic column cells with the same intermediate objects. -/
structure AlignedHammockGrid
    (M N : ProcessModel.{u, v, w} R) (n : ℕ) where
  /-- The `n + 1` horizontal rows. -/
  row : Fin (n + 1) → LinearHammock M N
  /-- The componentwise cells between adjacent rows. -/
  cell : ∀ i : Fin n, AlignedHammockCell (row i.castSucc) (row i.succ)

namespace AlignedHammockGrid

/-- Horizontal width, measured on the first row. -/
def width {M N : ProcessModel.{u, v, w} R} {n : ℕ}
    (grid : AlignedHammockGrid M N n) : ℕ :=
  Bicategory.MarkedZigzag.LinearWord.length (costExactArrows R) (grid.row 0)

/-- Every adjacent aligned cell records exactly the length of its source row. -/
theorem cell_width_source {M N : ProcessModel.{u, v, w} R} {n : ℕ}
    (grid : AlignedHammockGrid M N n) (i : Fin n) :
    Bicategory.MarkedZigzag.AlignedCell.width (costExactArrows R)
        (grid.cell i) =
      Bicategory.MarkedZigzag.LinearWord.length (costExactArrows R)
        (grid.row i.castSucc) :=
  Bicategory.MarkedZigzag.AlignedCell.width_eq_source_length
    (costExactArrows R) (grid.cell i)

/-- Every adjacent aligned cell records exactly the length of its target row. -/
theorem cell_width_target {M N : ProcessModel.{u, v, w} R} {n : ℕ}
    (grid : AlignedHammockGrid M N n) (i : Fin n) :
    Bicategory.MarkedZigzag.AlignedCell.width (costExactArrows R)
        (grid.cell i) =
      Bicategory.MarkedZigzag.LinearWord.length (costExactArrows R)
        (grid.row i.succ) :=
  Bicategory.MarkedZigzag.AlignedCell.width_eq_target_length
    (costExactArrows R) (grid.cell i)

/-- Interpret one aligned row transition as an edge of the common-universe
linear hammock nerve. -/
def edge {M N : ProcessModel.{u, v, w} R} {n : ℕ}
    (grid : AlignedHammockGrid M N n) (i : Fin n) :
    (LinearHammockMappingNerve M N).Edge
      (ComposableArrows.mk₀ ((AsSmall.up :
        LinearHammock M N ⥤ LinearHammockMappingCategory M N).obj
          (grid.row i.castSucc)))
      (ComposableArrows.mk₀ ((AsSmall.up :
        LinearHammock M N ⥤ LinearHammockMappingCategory M N).obj
          (grid.row i.succ))) :=
  CategoryTheory.nerve.edgeMk
    ((AsSmall.up : LinearHammock M N ⥤
      LinearHammockMappingCategory M N).map
        (Bicategory.MarkedZigzag.AlignedCell.toHom
          (costExactArrows R) (grid.cell i)))

/-- Forget the explicit column decomposition while retaining the represented
rows and quotient edges as an ordinary linear hammock path. -/
def toLinearGrid {M N : ProcessModel.{u, v, w} R} {n : ℕ}
    (grid : AlignedHammockGrid M N n) : LinearHammockGrid M N n where
  vertex i := ComposableArrows.mk₀ ((AsSmall.up :
    LinearHammock M N ⥤ LinearHammockMappingCategory M N).obj (grid.row i))
  arrow i := (edge grid i).edge
  arrow_src i := (edge grid i).src_eq
  arrow_tgt i := (edge grid i).tgt_eq

/-- Forgetting columns preserves every row literally. -/
@[simp]
theorem toLinearGrid_vertex {M N : ProcessModel.{u, v, w} R} {n : ℕ}
    (grid : AlignedHammockGrid M N n) (i : Fin (n + 1)) :
    (toLinearGrid grid).vertex i =
      ComposableArrows.mk₀ ((AsSmall.up :
        LinearHammock M N ⥤ LinearHammockMappingCategory M N).obj
          (grid.row i)) :=
  rfl

/-- Forgetting columns maps every adjacent cell by its exact quotient
interpretation. -/
@[simp]
theorem toLinearGrid_arrow {M N : ProcessModel.{u, v, w} R} {n : ℕ}
    (grid : AlignedHammockGrid M N n) (i : Fin n) :
    (toLinearGrid grid).arrow i =
      ComposableArrows.mk₁ ((AsSmall.up :
        LinearHammock M N ⥤ LinearHammockMappingCategory M N).map
          (Bicategory.MarkedZigzag.AlignedCell.toHom
            (costExactArrows R) (grid.cell i))) :=
  rfl

/-- Decoding a forgotten aligned grid recovers its original row exactly. -/
@[simp]
theorem linearHammockGridRow_toLinearGrid
    {M N : ProcessModel.{u, v, w} R} {n : ℕ}
    (grid : AlignedHammockGrid M N n) (i : Fin (n + 1)) :
    linearHammockGridRow (toLinearGrid grid) i = grid.row i := by
  rfl

/-- Strict-Segal reconstruction turns every aligned multi-column grid into a
genuine simplex of the linear hammock nerve. -/
def simplex {M N : ProcessModel.{u, v, w} R} {n : ℕ}
    (grid : AlignedHammockGrid M N n) :
    (LinearHammockMappingNerve M N).obj (op ⦋n⦌) :=
  (linearHammockGridEquiv M N n).symm (toLinearGrid grid)

/-- Re-extracting the row path of the reconstructed simplex forgets only the
column decomposition and returns the exact underlying linear grid. -/
@[simp]
theorem linearHammockGridEquiv_simplex
    {M N : ProcessModel.{u, v, w} R} {n : ℕ}
    (grid : AlignedHammockGrid M N n) :
    linearHammockGridEquiv M N n (simplex grid) = toLinearGrid grid :=
  (linearHammockGridEquiv M N n).apply_symm_apply (toLinearGrid grid)

end AlignedHammockGrid

/-- Machine-facing core for the aligned multi-column hammock fragment.  It
records identity and vertical-composition preservation together with exact
row/edge formulas and strict-Segal reconstruction of every explicit grid. -/
structure AlignedHammockCore
    (M N : ProcessModel.{u, v, w} R) : Prop where
  /-- Componentwise identity cells interpret as mapping-category identities. -/
  identity : ∀ (word : LinearHammock M N),
    Bicategory.MarkedZigzag.AlignedCell.toHom (costExactArrows R)
        (Bicategory.MarkedZigzag.AlignedCell.identity
          (costExactArrows R) word) =
      𝟙 (Bicategory.MarkedZigzag.LinearWord.toWord
        (costExactArrows R) word)
  /-- Componentwise vertical composition is preserved exactly. -/
  vcomp : ∀ {first middle last : LinearHammock M N}
      (alpha : AlignedHammockCell first middle)
      (beta : AlignedHammockCell middle last),
    Bicategory.MarkedZigzag.AlignedCell.toHom (costExactArrows R)
        (Bicategory.MarkedZigzag.AlignedCell.vcomp
          (costExactArrows R) alpha beta) =
      Bicategory.MarkedZigzag.AlignedCell.quotientVcomp
        (costExactArrows R)
        (Bicategory.MarkedZigzag.AlignedCell.toHom
          (costExactArrows R) alpha)
        (Bicategory.MarkedZigzag.AlignedCell.toHom
          (costExactArrows R) beta)
  /-- Strict-Segal reconstruction returns the exact underlying row path. -/
  simplex_path : ∀ {n : ℕ} (grid : AlignedHammockGrid M N n),
    linearHammockGridEquiv M N n (AlignedHammockGrid.simplex grid) =
      AlignedHammockGrid.toLinearGrid grid
  /-- Every represented vertex decodes to its original aligned row. -/
  row_exact : ∀ {n : ℕ} (grid : AlignedHammockGrid M N n)
      (i : Fin (n + 1)),
    linearHammockGridRow (AlignedHammockGrid.toLinearGrid grid) i =
      grid.row i
  /-- Every represented edge is the exact quotient interpretation of its
  aligned columns. -/
  edge_exact : ∀ {n : ℕ} (grid : AlignedHammockGrid M N n) (i : Fin n),
    (AlignedHammockGrid.toLinearGrid grid).arrow i =
      ComposableArrows.mk₁ ((AsSmall.up :
        LinearHammock M N ⥤ LinearHammockMappingCategory M N).map
          (Bicategory.MarkedZigzag.AlignedCell.toHom
            (costExactArrows R) (grid.cell i)))

/-- Machine-facing core for executable column refinement.  It records the
signed width representation, functorial interpretation, forward and marked
generator round trips, and stability of inverse moves beneath arbitrary
common prefixes. -/
structure ColumnRefinementCore
    (M N : ProcessModel.{u, v, w} R) : Prop where
  /-- Signed width change is exactly target length minus source length. -/
  width_change : ∀ {source target : LinearHammock M N}
      (refinement : HammockColumnRefinement source target),
    (Bicategory.MarkedZigzag.LinearWord.length (costExactArrows R)
        target : ℤ) =
      Bicategory.MarkedZigzag.LinearWord.length (costExactArrows R) source +
        Bicategory.MarkedZigzag.ColumnRefinement.widthChange
          (costExactArrows R) refinement
  /-- Reflexive refinement maps to the quotient identity. -/
  identity : ∀ (word : LinearHammock M N),
    Bicategory.MarkedZigzag.ColumnRefinement.toHom (costExactArrows R)
        (.identity word) =
      𝟙 (Bicategory.MarkedZigzag.LinearWord.toWord
        (costExactArrows R) word)
  /-- Transitive refinement maps to quotient vertical composition. -/
  vcomp : ∀ {first middle last : LinearHammock M N}
      (alpha : HammockColumnRefinement first middle)
      (beta : HammockColumnRefinement middle last),
    Bicategory.MarkedZigzag.ColumnRefinement.toHom (costExactArrows R)
        (.vcomp alpha beta) =
      Bicategory.MarkedZigzag.AlignedCell.quotientVcomp
        (costExactArrows R)
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) alpha)
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) beta)
  /-- Identity-column insertion and deletion cancel in both directions. -/
  identity_roundTrips : ∀ (rest : LinearHammock M N),
    Bicategory.MarkedZigzag.AlignedCell.quotientVcomp
        (costExactArrows R)
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) (.deleteIdentity rest))
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) (.insertIdentity rest)) =
      𝟙 (Bicategory.MarkedZigzag.LinearWord.toWord (costExactArrows R)
        (.cons (Bicategory.MarkedZigzag.Step.forward
          (W := costExactArrows R) (𝟙 M)) rest)) ∧
    Bicategory.MarkedZigzag.AlignedCell.quotientVcomp
        (costExactArrows R)
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) (.insertIdentity rest))
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) (.deleteIdentity rest)) =
      𝟙 (Bicategory.MarkedZigzag.LinearWord.toWord (costExactArrows R) rest)
  /-- Composite-column expansion and contraction cancel in both directions. -/
  composite_roundTrips : ∀ {P Q : ProcessModel.{u, v, w} R}
      (f : M ⟶ P) (g : P ⟶ Q) (rest : LinearHammock Q N),
    Bicategory.MarkedZigzag.AlignedCell.quotientVcomp
        (costExactArrows R)
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) (.expandForward f g rest))
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) (.contractForward f g rest)) =
      𝟙 (Bicategory.MarkedZigzag.LinearWord.toWord (costExactArrows R)
        (.cons (Bicategory.MarkedZigzag.Step.forward
          (W := costExactArrows R) (f ≫ g)) rest)) ∧
    Bicategory.MarkedZigzag.AlignedCell.quotientVcomp
        (costExactArrows R)
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) (.contractForward f g rest))
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) (.expandForward f g rest)) =
      𝟙 (Bicategory.MarkedZigzag.LinearWord.toWord (costExactArrows R)
        (.cons (Bicategory.MarkedZigzag.Step.forward
          (W := costExactArrows R) f)
          (.cons (Bicategory.MarkedZigzag.Step.forward
            (W := costExactArrows R) g) rest)))
  /-- Marked unit-pair insertion and deletion cancel in both directions. -/
  markedUnit_roundTrips : ∀ {P : ProcessModel.{u, v, w} R}
      (f : M ⟶ P) (hf : costExactArrows R f) (rest : LinearHammock M N),
    Bicategory.MarkedZigzag.AlignedCell.quotientVcomp
        (costExactArrows R)
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) (.deleteMarkedUnitPair f hf rest))
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) (.insertMarkedUnitPair f hf rest)) =
      𝟙 (Bicategory.MarkedZigzag.LinearWord.toWord (costExactArrows R)
        (.cons (Bicategory.MarkedZigzag.Step.forward
          (W := costExactArrows R) f)
          (.cons (Bicategory.MarkedZigzag.Step.backward
            (W := costExactArrows R) f hf) rest))) ∧
    Bicategory.MarkedZigzag.AlignedCell.quotientVcomp
        (costExactArrows R)
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) (.insertMarkedUnitPair f hf rest))
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) (.deleteMarkedUnitPair f hf rest)) =
      𝟙 (Bicategory.MarkedZigzag.LinearWord.toWord (costExactArrows R) rest)
  /-- Marked counit-pair insertion and deletion cancel in both directions. -/
  markedCounit_roundTrips : ∀ {P : ProcessModel.{u, v, w} R}
      (f : P ⟶ M) (hf : costExactArrows R f) (rest : LinearHammock M N),
    Bicategory.MarkedZigzag.AlignedCell.quotientVcomp
        (costExactArrows R)
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) (.deleteMarkedCounitPair f hf rest))
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) (.insertMarkedCounitPair f hf rest)) =
      𝟙 (Bicategory.MarkedZigzag.LinearWord.toWord (costExactArrows R)
        (.cons (Bicategory.MarkedZigzag.Step.backward
          (W := costExactArrows R) f hf)
          (.cons (Bicategory.MarkedZigzag.Step.forward
            (W := costExactArrows R) f) rest))) ∧
    Bicategory.MarkedZigzag.AlignedCell.quotientVcomp
        (costExactArrows R)
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) (.insertMarkedCounitPair f hf rest))
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) (.deleteMarkedCounitPair f hf rest)) =
      𝟙 (Bicategory.MarkedZigzag.LinearWord.toWord (costExactArrows R) rest)
  /-- Semantic inverse refinements remain inverse beneath a common prefix. -/
  prefix_inverse : ∀ {P : ProcessModel.{u, v, w} R}
      (step : Bicategory.MarkedZigzag.Step (costExactArrows R) M P)
      {first middle : LinearHammock P N}
      (alpha : HammockColumnRefinement first middle)
      (beta : HammockColumnRefinement middle first),
    Bicategory.MarkedZigzag.AlignedCell.quotientVcomp
        (costExactArrows R)
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) alpha)
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) beta) =
      𝟙 (Bicategory.MarkedZigzag.LinearWord.toWord
        (costExactArrows R) first) →
    Bicategory.MarkedZigzag.AlignedCell.quotientVcomp
        (costExactArrows R)
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) (.under step alpha))
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) (.under step beta)) =
      𝟙 (Bicategory.MarkedZigzag.LinearWord.toWord (costExactArrows R)
        (.cons step first))

/-- Common-refinement quotient of cost-exact linear hammock rows. -/
abbrev HammockRowQuotient (M N : ProcessModel.{u, v, w} R) :=
  Bicategory.MarkedZigzag.CommonRefinement.RowQuotient
    (costExactArrows R) M N

/-- Machine-facing common-refinement quotient and semantic soundness core. -/
structure CommonRefinementCore
    (M N : ProcessModel.{u, v, w} R) : Prop where
  /-- Reversal negates the exact signed width change. -/
  reverse_width : ∀ {first second : LinearHammock M N}
      (refinement : HammockColumnRefinement first second),
    Bicategory.MarkedZigzag.ColumnRefinement.widthChange
        (costExactArrows R)
        (Bicategory.MarkedZigzag.ColumnRefinement.reverse
          (costExactArrows R) refinement) =
      -Bicategory.MarkedZigzag.ColumnRefinement.widthChange
        (costExactArrows R) refinement
  /-- Every refinement's quotient morphism is the forward map of its unified
  semantic isomorphism. -/
  refinement_iso : ∀ {first second : LinearHammock M N}
      (refinement : HammockColumnRefinement first second),
    Bicategory.MarkedZigzag.ColumnRefinement.toHom
        (costExactArrows R) refinement =
      (Bicategory.MarkedZigzag.ColumnRefinement.toIso
        (costExactArrows R) refinement).hom
  /-- Executable reversal maps to the inverse semantic isomorphism. -/
  reverse_iso : ∀ {first second : LinearHammock M N}
      (refinement : HammockColumnRefinement first second),
    Bicategory.MarkedZigzag.ColumnRefinement.toIso
        (costExactArrows R)
        (Bicategory.MarkedZigzag.ColumnRefinement.reverse
          (costExactArrows R) refinement) =
      (Bicategory.MarkedZigzag.ColumnRefinement.toIso
        (costExactArrows R) refinement).symm
  /-- Every executable refinement identifies its endpoints in the common-
  refinement row quotient. -/
  quotient_identifies : ∀ {first second : LinearHammock M N}
      (_refinement : HammockColumnRefinement first second),
    Bicategory.MarkedZigzag.CommonRefinement.quotientMk
        (costExactArrows R) first =
      Bicategory.MarkedZigzag.CommonRefinement.quotientMk
        (costExactArrows R) second
  /-- Equality in the row quotient yields a semantic isomorphism, without
  assuming equality of the interpreted word objects. -/
  quotient_sound : ∀ {first second : LinearHammock M N},
    Bicategory.MarkedZigzag.CommonRefinement.quotientMk
        (costExactArrows R) first =
      Bicategory.MarkedZigzag.CommonRefinement.quotientMk
        (costExactArrows R) second →
    Nonempty (@Iso (CostExactZigzag.Word (R := R) M N)
      (Bicategory.MarkedZigzag.Presented.wordCategory
        (costExactArrows R) M N)
      (Bicategory.MarkedZigzag.LinearWord.toWord
        (costExactArrows R) first)
      (Bicategory.MarkedZigzag.LinearWord.toWord
        (costExactArrows R) second))

/-- Every cost-exact model pair satisfies the aligned multi-column hammock
core. -/
theorem alignedHammockCore (M N : ProcessModel.{u, v, w} R) :
    AlignedHammockCore M N where
  identity := Bicategory.MarkedZigzag.AlignedCell.toHom_identity
    (costExactArrows R)
  vcomp := Bicategory.MarkedZigzag.AlignedCell.toHom_vcomp
    (costExactArrows R)
  simplex_path := AlignedHammockGrid.linearHammockGridEquiv_simplex
  row_exact := AlignedHammockGrid.linearHammockGridRow_toLinearGrid
  edge_exact := AlignedHammockGrid.toLinearGrid_arrow

/-- Every cost-exact model pair satisfies the executable column-refinement
core. -/
theorem columnRefinementCore (M N : ProcessModel.{u, v, w} R) :
    ColumnRefinementCore M N where
  width_change :=
    Bicategory.MarkedZigzag.ColumnRefinement.target_length_eq_source_length_add_widthChange
      (costExactArrows R)
  identity := Bicategory.MarkedZigzag.ColumnRefinement.toHom_identity
    (costExactArrows R)
  vcomp := Bicategory.MarkedZigzag.ColumnRefinement.toHom_vcomp
    (costExactArrows R)
  identity_roundTrips := fun rest =>
    ⟨Bicategory.MarkedZigzag.ColumnRefinement.deleteIdentity_insertIdentity
        (costExactArrows R) rest,
      Bicategory.MarkedZigzag.ColumnRefinement.insertIdentity_deleteIdentity
        (costExactArrows R) rest⟩
  composite_roundTrips := fun f g rest =>
    ⟨Bicategory.MarkedZigzag.ColumnRefinement.expandForward_contractForward
        (costExactArrows R) f g rest,
      Bicategory.MarkedZigzag.ColumnRefinement.contractForward_expandForward
        (costExactArrows R) f g rest⟩
  markedUnit_roundTrips := fun f hf rest =>
    ⟨Bicategory.MarkedZigzag.ColumnRefinement.deleteMarkedUnitPair_insertMarkedUnitPair
        (costExactArrows R) f hf rest,
      Bicategory.MarkedZigzag.ColumnRefinement.insertMarkedUnitPair_deleteMarkedUnitPair
        (costExactArrows R) f hf rest⟩
  markedCounit_roundTrips := fun f hf rest =>
    ⟨Bicategory.MarkedZigzag.ColumnRefinement.deleteMarkedCounitPair_insertMarkedCounitPair
        (costExactArrows R) f hf rest,
      Bicategory.MarkedZigzag.ColumnRefinement.insertMarkedCounitPair_deleteMarkedCounitPair
        (costExactArrows R) f hf rest⟩
  prefix_inverse := Bicategory.MarkedZigzag.ColumnRefinement.under_inverse
    (costExactArrows R)

/-- Every cost-exact model pair satisfies the common-refinement quotient and
semantic-isomorphism soundness core. -/
theorem commonRefinementCore (M N : ProcessModel.{u, v, w} R) :
    CommonRefinementCore M N where
  reverse_width :=
    Bicategory.MarkedZigzag.ColumnRefinement.widthChange_reverse
      (costExactArrows R)
  refinement_iso :=
    Bicategory.MarkedZigzag.ColumnRefinement.toHom_eq_toIso_hom
      (costExactArrows R)
  reverse_iso := Bicategory.MarkedZigzag.ColumnRefinement.toIso_reverse
    (costExactArrows R)
  quotient_identifies :=
    Bicategory.MarkedZigzag.CommonRefinement.quotientMk_eq_of_refinement
      (costExactArrows R)
  quotient_sound :=
    Bicategory.MarkedZigzag.CommonRefinement.quotientMk_eq_semanticIso
      (costExactArrows R)

/-! ## Zero-truncated common-refinement nerve -/

/-- Equivalence from the thin common-refinement groupoid to the discrete
category of row-quotient classes. -/
noncomputable def thinRefinementEquivalence
    (M N : ProcessModel.{u, v, w} R) :
    Bicategory.MarkedZigzag.CommonRefinement.RowObject
        (costExactArrows R) M N ≌
      Discrete (HammockRowQuotient M N) :=
  Bicategory.MarkedZigzag.CommonRefinement.quotientEquivalence
    (costExactArrows R) M N

/-- Nerve comparison from the thin common-refinement groupoid to the discrete
row-quotient nerve. -/
noncomputable def thinRefinementComparison
    (M N : ProcessModel.{u, v, w} R) :=
  CategoryTheory.nerveMap (thinRefinementEquivalence M N).functor

/-- Categorical-nerve equivalence evidence for the zero-truncated common-
refinement comparison. -/
noncomputable def thinRefinementNerveEquivalence
    (M N : ProcessModel.{u, v, w} R) :
    SSet.NerveEquivalenceWitness (thinRefinementComparison M N) :=
  SSet.NerveEquivalenceWitness.ofEquivalence
    (thinRefinementEquivalence M N)

/-- Explicit simplicial inverse and both homotopies for the zero-truncated
common-refinement comparison. -/
noncomputable def thinRefinementHomotopyEquivalence
    (M N : ProcessModel.{u, v, w} R) :
    SSet.HomotopyEquivalenceWitness (thinRefinementComparison M N) :=
  SSet.HomotopyEquivalenceWitness.ofCategoryEquivalence
    (thinRefinementEquivalence M N)

/-- Exact vertex action: a represented row maps to its common-refinement
quotient class. -/
theorem thinRefinementComparison_vertex
    {M N : ProcessModel.{u, v, w} R}
    (row : LinearHammock M N) :
    (thinRefinementComparison M N).app (op ⦋0⦌)
        (ComposableArrows.mk₀
          (⟨row⟩ : Bicategory.MarkedZigzag.CommonRefinement.RowObject
            (costExactArrows R) M N)) =
      ComposableArrows.mk₀
        (Discrete.mk
          (Bicategory.MarkedZigzag.CommonRefinement.quotientMk
            (costExactArrows R) row)) := by
  exact CategoryTheory.nerveMap_app_mk₀ _ _

/-- Machine-facing zero-truncated common-refinement mapping-nerve core. -/
structure ThinRefinementNerveCore
    (M N : ProcessModel.{u, v, w} R) : Prop where
  /-- The thin refinement nerve is categorically equivalent to the discrete
  row-quotient nerve. -/
  nerve_equivalence :
    Nonempty (SSet.NerveEquivalenceWitness
      (thinRefinementComparison M N))
  /-- The comparison has an explicit simplicial inverse and both homotopies. -/
  homotopy_equivalence :
    Nonempty (SSet.HomotopyEquivalenceWitness
      (thinRefinementComparison M N))
  /-- Exact action on every raw row vertex. -/
  maps_vertex : ∀ row,
    (thinRefinementComparison M N).app (op ⦋0⦌)
        (ComposableArrows.mk₀
          (⟨row⟩ : Bicategory.MarkedZigzag.CommonRefinement.RowObject
            (costExactArrows R) M N)) =
      ComposableArrows.mk₀
        (Discrete.mk
          (Bicategory.MarkedZigzag.CommonRefinement.quotientMk
            (costExactArrows R) row))

/-- Every cost-exact model pair satisfies the zero-truncated common-refinement
nerve comparison. -/
theorem thinRefinementNerveCore (M N : ProcessModel.{u, v, w} R) :
    ThinRefinementNerveCore M N where
  nerve_equivalence := ⟨thinRefinementNerveEquivalence M N⟩
  homotopy_equivalence := ⟨thinRefinementHomotopyEquivalence M N⟩
  maps_vertex := thinRefinementComparison_vertex

/-! ## Non-thin semantic refinement-path nerve -/

/-- Nerve map from the non-thin semantic refinement-path groupoid into the
existing linear hammock mapping nerve. -/
def refinementPathSemanticComparison
    (M N : ProcessModel.{u, v, w} R) :=
  CategoryTheory.nerveMap
    (Bicategory.MarkedZigzag.RefinementPath.semanticFunctor
      (costExactArrows R) M N)

/-- Nerve map implementing zero-truncation from semantic refinement paths to
the thin common-refinement groupoid. -/
def refinementPathToThinComparison
    (M N : ProcessModel.{u, v, w} R) :=
  CategoryTheory.nerveMap
    (Bicategory.MarkedZigzag.RefinementPath.toThinFunctor
      (costExactArrows R) M N)

/-- Exact object action of the semantic refinement-path nerve map. -/
theorem refinementPathSemanticComparison_vertex
    {M N : ProcessModel.{u, v, w} R}
    (row : LinearHammock M N) :
    (refinementPathSemanticComparison M N).app (op ⦋0⦌)
        (ComposableArrows.mk₀
          (⟨row⟩ : Bicategory.MarkedZigzag.RefinementPathObject
            (costExactArrows R) M N)) =
      ComposableArrows.mk₀ row := by
  exact CategoryTheory.nerveMap_app_mk₀ _ _

/-- Exact edge action: a represented refinement path maps to its quotient-
cell interpretation. -/
theorem refinementPathSemanticComparison_edge
    {M N : ProcessModel.{u, v, w} R}
    {first second : LinearHammock M N}
    (refinement : HammockColumnRefinement first second) :
    (refinementPathSemanticComparison M N).app (op ⦋1⦌)
        (ComposableArrows.mk₁
          (Quotient.mk
            (Bicategory.MarkedZigzag.RefinementPath.setoid
              (costExactArrows R) first second) refinement)) =
      ComposableArrows.mk₁
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) refinement) := by
  exact CategoryTheory.nerveMap_app_mk₁ _ _

/-- Machine-facing non-thin semantic refinement-path nerve core.  It records
faithful semantic action without claiming fullness or weak equivalence. -/
structure RefinementPathNerveCore
    (M N : ProcessModel.{u, v, w} R) : Prop where
  /-- The semantic refinement-path source is a groupoid. -/
  source_groupoid : IsGroupoid
    (Bicategory.MarkedZigzag.RefinementPathObject
      (costExactArrows R) M N)
  /-- Semantic interpretation is faithful on refinement-path morphisms. -/
  semantic_faithful :
    (Bicategory.MarkedZigzag.RefinementPath.semanticFunctor
      (costExactArrows R) M N).Faithful
  /-- Every linear row object is in the semantic functor's essential image. -/
  semantic_essSurj :
    (Bicategory.MarkedZigzag.RefinementPath.semanticFunctor
      (costExactArrows R) M N).EssSurj
  /-- Exact vertex action. -/
  maps_vertex : ∀ row,
    (refinementPathSemanticComparison M N).app (op ⦋0⦌)
        (ComposableArrows.mk₀
          (⟨row⟩ : Bicategory.MarkedZigzag.RefinementPathObject
            (costExactArrows R) M N)) =
      ComposableArrows.mk₀ row
  /-- Exact generator/refinement edge action. -/
  maps_edge : ∀ {first second : LinearHammock M N}
      (refinement : HammockColumnRefinement first second),
    (refinementPathSemanticComparison M N).app (op ⦋1⦌)
        (ComposableArrows.mk₁
          (Quotient.mk
            (Bicategory.MarkedZigzag.RefinementPath.setoid
              (costExactArrows R) first second) refinement)) =
      ComposableArrows.mk₁
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) refinement)

/-- Every cost-exact model pair satisfies the non-thin semantic refinement-
path nerve core. -/
theorem refinementPathNerveCore (M N : ProcessModel.{u, v, w} R) :
    RefinementPathNerveCore M N where
  source_groupoid := inferInstance
  semantic_faithful := inferInstance
  semantic_essSurj := inferInstance
  maps_vertex := refinementPathSemanticComparison_vertex
  maps_edge := refinementPathSemanticComparison_edge

/-! ## Exact refinement-generated semantic image nerve -/

/-- The exact semantic image category whose morphisms are precisely quotient
2-cells generated by executable column refinements. -/
abbrev RefinementImage
    (M N : ProcessModel.{u, v, w} R) :=
  Bicategory.MarkedZigzag.RefinementImageObject
    (costExactArrows R) M N

/-- Nerve of the exact refinement-generated semantic image subgroupoid. -/
abbrev RefinementImageNerve
    (M N : ProcessModel.{u, v, w} R) :=
  CategoryTheory.nerve (RefinementImage M N)

/-- Categorical equivalence from semantic refinement paths onto their exact
generated semantic image. -/
noncomputable def refinementPathImageEquivalence
    (M N : ProcessModel.{u, v, w} R) :
    Bicategory.MarkedZigzag.RefinementPathObject
        (costExactArrows R) M N ≌
      RefinementImage M N :=
  Bicategory.MarkedZigzag.RefinementImage.pathEquivalence
    (costExactArrows R) M N

/-- Nerve comparison from semantic refinement paths to their exact generated
semantic image. -/
noncomputable def refinementPathImageComparison
    (M N : ProcessModel.{u, v, w} R) :=
  CategoryTheory.nerveMap
    (refinementPathImageEquivalence M N).functor

/-- Faithful nerve inclusion of the generated semantic image into the full
linear hammock mapping nerve. -/
def refinementImageInclusionComparison
    (M N : ProcessModel.{u, v, w} R) :=
  CategoryTheory.nerveMap
    (Bicategory.MarkedZigzag.RefinementImage.inclusion
      (costExactArrows R) M N)

/-- Categorical-nerve equivalence evidence for semantic refinement paths and
their exact generated image. -/
noncomputable def refinementPathImageNerveEquivalence
    (M N : ProcessModel.{u, v, w} R) :
    SSet.NerveEquivalenceWitness (refinementPathImageComparison M N) :=
  SSet.NerveEquivalenceWitness.ofEquivalence
    (refinementPathImageEquivalence M N)

/-- Explicit simplicial inverse and both homotopies for the path-to-image
comparison. -/
noncomputable def refinementPathImageHomotopyEquivalence
    (M N : ProcessModel.{u, v, w} R) :
    SSet.HomotopyEquivalenceWitness (refinementPathImageComparison M N) :=
  SSet.HomotopyEquivalenceWitness.ofCategoryEquivalence
    (refinementPathImageEquivalence M N)

/-- Exact object action of the refinement-path-to-image nerve comparison. -/
theorem refinementPathImageComparison_vertex
    {M N : ProcessModel.{u, v, w} R}
    (row : LinearHammock M N) :
    (refinementPathImageComparison M N).app (op ⦋0⦌)
        (ComposableArrows.mk₀
          (⟨row⟩ : Bicategory.MarkedZigzag.RefinementPathObject
            (costExactArrows R) M N)) =
      ComposableArrows.mk₀
        (⟨row⟩ : RefinementImage M N) := by
  exact CategoryTheory.nerveMap_app_mk₀ _ _

/-- Exact edge action: an executable refinement path maps to the same
quotient 2-cell equipped with its generating-refinement witness. -/
theorem refinementPathImageComparison_edge
    {M N : ProcessModel.{u, v, w} R}
    {first second : LinearHammock M N}
    (refinement : HammockColumnRefinement first second) :
    (refinementPathImageComparison M N).app (op ⦋1⦌)
        (ComposableArrows.mk₁
          (Quotient.mk
            (Bicategory.MarkedZigzag.RefinementPath.setoid
              (costExactArrows R) first second) refinement)) =
      ComposableArrows.mk₁
        (⟨Bicategory.MarkedZigzag.ColumnRefinement.toHom
            (costExactArrows R) refinement,
          ⟨refinement, rfl⟩⟩ :
          Bicategory.MarkedZigzag.RefinementImage.Hom
            (costExactArrows R) first second) := by
  exact CategoryTheory.nerveMap_app_mk₁ _ _

/-- The image inclusion forgets only the generating-refinement witness on an
edge and preserves its quotient 2-cell literally. -/
theorem refinementImageInclusionComparison_edge
    {M N : ProcessModel.{u, v, w} R}
    {first second : RefinementImage M N}
    (morphism : first ⟶ second) :
    (refinementImageInclusionComparison M N).app (op ⦋1⦌)
        (ComposableArrows.mk₁ morphism) =
      ComposableArrows.mk₁
        (Bicategory.MarkedZigzag.RefinementImage.underlying
          (costExactArrows R) morphism) := by
  exact CategoryTheory.nerveMap_app_mk₁ _ _

/-- The original semantic refinement-path nerve map factors strictly through
the exact generated image nerve and its faithful inclusion. -/
theorem refinementPathSemanticComparison_factorization
    (M N : ProcessModel.{u, v, w} R) :
    refinementPathSemanticComparison M N =
      refinementPathImageComparison M N ≫
        refinementImageInclusionComparison M N := by
  change CategoryTheory.nerveMap
      (Bicategory.MarkedZigzag.RefinementPath.semanticFunctor
        (costExactArrows R) M N) = _
  rw [Bicategory.MarkedZigzag.RefinementImage.semanticFunctor_factorization]
  rfl

/-- Machine-facing core for the exact refinement-generated semantic image.
It records the subgroupoid boundary, categorical and simplicial equivalence,
faithful inclusion, strict semantic factorization, and exact generator action. -/
structure RefinementImageNerveCore
    (M N : ProcessModel.{u, v, w} R) : Prop where
  /-- The exact generated image is a groupoid. -/
  image_groupoid : IsGroupoid (RefinementImage M N)
  /-- Its inclusion into the full linear mapping category is faithful. -/
  inclusion_faithful :
    (Bicategory.MarkedZigzag.RefinementImage.inclusion
      (costExactArrows R) M N).Faithful
  /-- Semantic paths are categorically equivalent to their exact image. -/
  path_equivalence : Nonempty
    (Bicategory.MarkedZigzag.RefinementPathObject
        (costExactArrows R) M N ≌ RefinementImage M N)
  /-- Their nerves are categorically equivalent. -/
  nerve_equivalence : Nonempty
    (SSet.NerveEquivalenceWitness (refinementPathImageComparison M N))
  /-- The nerve comparison has an explicit inverse and both homotopies. -/
  homotopy_equivalence : Nonempty
    (SSet.HomotopyEquivalenceWitness (refinementPathImageComparison M N))
  /-- The semantic nerve map factors strictly through the image inclusion. -/
  semantic_factorization :
    refinementPathSemanticComparison M N =
      refinementPathImageComparison M N ≫
        refinementImageInclusionComparison M N
  /-- Exact action on each executable generator edge. -/
  maps_edge : ∀ {first second : LinearHammock M N}
      (refinement : HammockColumnRefinement first second),
    (refinementPathImageComparison M N).app (op ⦋1⦌)
        (ComposableArrows.mk₁
          (Quotient.mk
            (Bicategory.MarkedZigzag.RefinementPath.setoid
              (costExactArrows R) first second) refinement)) =
      ComposableArrows.mk₁
        (⟨Bicategory.MarkedZigzag.ColumnRefinement.toHom
            (costExactArrows R) refinement,
          ⟨refinement, rfl⟩⟩ :
          Bicategory.MarkedZigzag.RefinementImage.Hom
            (costExactArrows R) first second)

/-- Every cost-exact model pair satisfies the exact generated-image nerve
comparison. -/
theorem refinementImageNerveCore
    (M N : ProcessModel.{u, v, w} R) :
    RefinementImageNerveCore M N where
  image_groupoid := inferInstance
  inclusion_faithful := inferInstance
  path_equivalence := ⟨refinementPathImageEquivalence M N⟩
  nerve_equivalence := ⟨refinementPathImageNerveEquivalence M N⟩
  homotopy_equivalence := ⟨refinementPathImageHomotopyEquivalence M N⟩
  semantic_factorization :=
    refinementPathSemanticComparison_factorization M N
  maps_edge := refinementPathImageComparison_edge

/-! ## Aligned-cell-augmented hammock-path nerve -/

/-- Cost-exact generated hammock-path category combining executable
refinements with arbitrary aligned raw 2-cells. -/
abbrev GeneratedHammockPath
    (M N : ProcessModel.{u, v, w} R) :=
  Bicategory.MarkedZigzag.HammockPathObject
    (costExactArrows R) M N

/-- Nerve map from generated hammock paths into the full linear mapping
nerve. -/
noncomputable def hammockPathSemanticComparison
    (M N : ProcessModel.{u, v, w} R) :=
  CategoryTheory.nerveMap
    (Bicategory.MarkedZigzag.HammockPath.semanticFunctor
      (costExactArrows R) M N)

/-- Nerve inclusion from refinement-only paths into generated hammock paths. -/
def refinementPathToHammockComparison
    (M N : ProcessModel.{u, v, w} R) :=
  CategoryTheory.nerveMap
    (Bicategory.MarkedZigzag.HammockPath.refinementFunctor
      (costExactArrows R) M N)

/-- Exact vertex action of generated hammock semantics. -/
theorem hammockPathSemanticComparison_vertex
    {M N : ProcessModel.{u, v, w} R}
    (row : LinearHammock M N) :
    (hammockPathSemanticComparison M N).app (op ⦋0⦌)
        (ComposableArrows.mk₀
          (⟨row⟩ : GeneratedHammockPath M N)) =
      ComposableArrows.mk₀ row := by
  exact CategoryTheory.nerveMap_app_mk₀ _ _

/-- Exact inclusion of an executable refinement edge into the larger path
nerve. -/
theorem refinementPathToHammockComparison_edge
    {M N : ProcessModel.{u, v, w} R}
    {first second : LinearHammock M N}
    (refinement : HammockColumnRefinement first second) :
    (refinementPathToHammockComparison M N).app (op ⦋1⦌)
        (ComposableArrows.mk₁
          (Quotient.mk
            (Bicategory.MarkedZigzag.RefinementPath.setoid
              (costExactArrows R) first second) refinement)) =
      ComposableArrows.mk₁
        (Quotient.mk
          (Bicategory.MarkedZigzag.HammockPath.setoid
            (costExactArrows R) first second)
          (Bicategory.MarkedZigzag.HammockPath.ofRefinement refinement)) := by
  exact CategoryTheory.nerveMap_app_mk₁ _ _

/-- Exact semantic action on an executable refinement edge. -/
theorem hammockPathSemanticComparison_refinementEdge
    {M N : ProcessModel.{u, v, w} R}
    {first second : LinearHammock M N}
    (refinement : HammockColumnRefinement first second) :
    (hammockPathSemanticComparison M N).app (op ⦋1⦌)
        (ComposableArrows.mk₁
          (Quotient.mk
            (Bicategory.MarkedZigzag.HammockPath.setoid
              (costExactArrows R) first second)
            (Bicategory.MarkedZigzag.HammockPath.ofRefinement refinement))) =
      ComposableArrows.mk₁
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) refinement) := by
  exact CategoryTheory.nerveMap_app_mk₁ _ _

/-- Exact semantic action on an arbitrary aligned raw-cell edge. -/
theorem hammockPathSemanticComparison_alignedEdge
    {M N : ProcessModel.{u, v, w} R}
    {first second : LinearHammock M N}
    (cell : AlignedHammockCell first second) :
    (hammockPathSemanticComparison M N).app (op ⦋1⦌)
        (ComposableArrows.mk₁
          (Bicategory.MarkedZigzag.HammockPath.alignedHom
            (costExactArrows R) cell)) =
      ComposableArrows.mk₁
        (Bicategory.MarkedZigzag.AlignedCell.toHom
          (costExactArrows R) cell) := by
  exact CategoryTheory.nerveMap_app_mk₁ _ _

/-- Exact semantic action on a generated path whiskered on the left by a
fixed linear row. -/
theorem hammockPathSemanticComparison_whiskerLeftEdge
    {M N P : ProcessModel.{u, v, w} R}
    (pre : LinearHammock M N)
    {first second : LinearHammock N P}
    (path : Bicategory.MarkedZigzag.HammockPath
      (costExactArrows R) first second) :
    (hammockPathSemanticComparison M P).app (op ⦋1⦌)
        (ComposableArrows.mk₁
          (Quotient.mk
            (Bicategory.MarkedZigzag.HammockPath.setoid
              (costExactArrows R)
              (Bicategory.MarkedZigzag.LinearWord.append
                (costExactArrows R) pre first)
              (Bicategory.MarkedZigzag.LinearWord.append
                (costExactArrows R) pre second))
            (Bicategory.MarkedZigzag.HammockPath.whiskerLeft pre path))) =
      ComposableArrows.mk₁
        (Bicategory.MarkedZigzag.HammockPath.normalizedWhiskerLeftHom
          (costExactArrows R) pre
          (Bicategory.MarkedZigzag.HammockPath.toHom
            (costExactArrows R) path)) := by
  exact CategoryTheory.nerveMap_app_mk₁ _ _

/-- Exact semantic action on a generated path whiskered on the right by a
fixed linear row. -/
theorem hammockPathSemanticComparison_whiskerRightEdge
    {M N P : ProcessModel.{u, v, w} R}
    {first second : LinearHammock M N}
    (path : Bicategory.MarkedZigzag.HammockPath
      (costExactArrows R) first second)
    (post : LinearHammock N P) :
    (hammockPathSemanticComparison M P).app (op ⦋1⦌)
        (ComposableArrows.mk₁
          (Quotient.mk
            (Bicategory.MarkedZigzag.HammockPath.setoid
              (costExactArrows R)
              (Bicategory.MarkedZigzag.LinearWord.append
                (costExactArrows R) first post)
              (Bicategory.MarkedZigzag.LinearWord.append
                (costExactArrows R) second post))
            (Bicategory.MarkedZigzag.HammockPath.whiskerRight path post))) =
      ComposableArrows.mk₁
        (Bicategory.MarkedZigzag.HammockPath.normalizedWhiskerRightHom
          (costExactArrows R) post
          (Bicategory.MarkedZigzag.HammockPath.toHom
            (costExactArrows R) path)) := by
  exact CategoryTheory.nerveMap_app_mk₁ _ _

/-- Exact semantic action on horizontal append of two generated hammock
paths. -/
theorem hammockPathSemanticComparison_appendEdge
    {M N P : ProcessModel.{u, v, w} R}
    {firstSource firstTarget : LinearHammock M N}
    {secondSource secondTarget : LinearHammock N P}
    (first : Bicategory.MarkedZigzag.HammockPath
      (costExactArrows R) firstSource firstTarget)
    (second : Bicategory.MarkedZigzag.HammockPath
      (costExactArrows R) secondSource secondTarget) :
    (hammockPathSemanticComparison M P).app (op ⦋1⦌)
        (ComposableArrows.mk₁
          (Quotient.mk
            (Bicategory.MarkedZigzag.HammockPath.setoid
              (costExactArrows R)
              (Bicategory.MarkedZigzag.LinearWord.append
                (costExactArrows R) firstSource secondSource)
              (Bicategory.MarkedZigzag.LinearWord.append
                (costExactArrows R) firstTarget secondTarget))
            (Bicategory.MarkedZigzag.HammockPath.append
              (costExactArrows R) first second))) =
      ComposableArrows.mk₁
        (Bicategory.MarkedZigzag.AlignedCell.quotientVcomp
          (costExactArrows R)
          (Bicategory.MarkedZigzag.HammockPath.normalizedWhiskerRightHom
            (costExactArrows R) secondSource
            (Bicategory.MarkedZigzag.HammockPath.toHom
              (costExactArrows R) first))
          (Bicategory.MarkedZigzag.HammockPath.normalizedWhiskerLeftHom
            (costExactArrows R) firstTarget
            (Bicategory.MarkedZigzag.HammockPath.toHom
              (costExactArrows R) second))) := by
  exact CategoryTheory.nerveMap_app_mk₁ _ _

/-- Exact semantic action on a source 2-cell in its canonical one-column
linear representation. -/
theorem hammockPathSemanticComparison_originalEdge
    {M N : ProcessModel.{u, v, w} R}
    {f g : M ⟶ N} (alpha : f ⟶ g) :
    (hammockPathSemanticComparison M N).app (op ⦋1⦌)
        (ComposableArrows.mk₁
          (Bicategory.MarkedZigzag.HammockPath.alignedHom
            (costExactArrows R)
            (Bicategory.MarkedZigzag.HammockPath.originalAlignedCell
              (costExactArrows R) alpha))) =
      ComposableArrows.mk₁
        (Bicategory.MarkedZigzag.AlignedCell.toHom
          (costExactArrows R)
          (Bicategory.MarkedZigzag.HammockPath.originalAlignedCell
            (costExactArrows R) alpha)) :=
  hammockPathSemanticComparison_alignedEdge _

/-- The old refinement semantic nerve map factors strictly through generated
hammock paths and their faithful semantic functor. -/
theorem refinementPathSemanticComparison_hammockFactorization
    (M N : ProcessModel.{u, v, w} R) :
    refinementPathSemanticComparison M N =
      refinementPathToHammockComparison M N ≫
        hammockPathSemanticComparison M N := by
  change CategoryTheory.nerveMap
      (Bicategory.MarkedZigzag.RefinementPath.semanticFunctor
        (costExactArrows R) M N) = _
  rw [Bicategory.MarkedZigzag.HammockPath.refinementSemanticFunctor_factorization]
  rfl

/-- Machine-facing core for the aligned-cell-augmented generated hammock
path nerve. It records faithful semantic action, the faithful refinement-only
subsystem, strict factorization, and exact arbitrary/source 2-cell coverage. -/
structure HammockPathNerveCore
    (M N : ProcessModel.{u, v, w} R) : Prop where
  /-- Generated hammock semantics is faithful. -/
  semantic_faithful :
    (Bicategory.MarkedZigzag.HammockPath.semanticFunctor
      (costExactArrows R) M N).Faithful
  /-- Every linear row object lies in its essential image. -/
  semantic_essSurj :
    (Bicategory.MarkedZigzag.HammockPath.semanticFunctor
      (costExactArrows R) M N).EssSurj
  /-- Refinement-only paths embed faithfully. -/
  refinement_faithful :
    (Bicategory.MarkedZigzag.HammockPath.refinementFunctor
      (costExactArrows R) M N).Faithful
  /-- The old semantic nerve map factors through generated hammock paths. -/
  refinement_factorization :
    refinementPathSemanticComparison M N =
      refinementPathToHammockComparison M N ≫
        hammockPathSemanticComparison M N
  /-- Exact action on every executable refinement edge. -/
  maps_refinement : ∀ {first second : LinearHammock M N}
      (refinement : HammockColumnRefinement first second),
    (hammockPathSemanticComparison M N).app (op ⦋1⦌)
        (ComposableArrows.mk₁
          (Quotient.mk
            (Bicategory.MarkedZigzag.HammockPath.setoid
              (costExactArrows R) first second)
            (Bicategory.MarkedZigzag.HammockPath.ofRefinement refinement))) =
      ComposableArrows.mk₁
        (Bicategory.MarkedZigzag.ColumnRefinement.toHom
          (costExactArrows R) refinement)
  /-- Exact action on every arbitrary aligned-cell edge. -/
  maps_aligned : ∀ {first second : LinearHammock M N}
      (cell : AlignedHammockCell first second),
    (hammockPathSemanticComparison M N).app (op ⦋1⦌)
        (ComposableArrows.mk₁
          (Bicategory.MarkedZigzag.HammockPath.alignedHom
            (costExactArrows R) cell)) =
      ComposableArrows.mk₁
        (Bicategory.MarkedZigzag.AlignedCell.toHom
          (costExactArrows R) cell)
  /-- Every source 2-cell has an exact one-column generated edge. -/
  maps_original : ∀ {f g : M ⟶ N} (alpha : f ⟶ g),
    (hammockPathSemanticComparison M N).app (op ⦋1⦌)
        (ComposableArrows.mk₁
          (Bicategory.MarkedZigzag.HammockPath.alignedHom
            (costExactArrows R)
            (Bicategory.MarkedZigzag.HammockPath.originalAlignedCell
              (costExactArrows R) alpha))) =
      ComposableArrows.mk₁
        (Bicategory.MarkedZigzag.AlignedCell.toHom
          (costExactArrows R)
          (Bicategory.MarkedZigzag.HammockPath.originalAlignedCell
            (costExactArrows R) alpha))

/-- Every cost-exact model pair satisfies the aligned-cell-augmented generated
hammock-path nerve core. -/
theorem hammockPathNerveCore (M N : ProcessModel.{u, v, w} R) :
    HammockPathNerveCore M N where
  semantic_faithful := inferInstance
  semantic_essSurj := inferInstance
  refinement_faithful := inferInstance
  refinement_factorization :=
    refinementPathSemanticComparison_hammockFactorization M N
  maps_refinement := hammockPathSemanticComparison_refinementEdge
  maps_aligned := hammockPathSemanticComparison_alignedEdge
  maps_original := hammockPathSemanticComparison_originalEdge

/-- Machine-facing exact three-model whiskering and append interface for the
generated hammock-path nerves. -/
structure HammockPathWhiskeringCore
    (M N P : ProcessModel.{u, v, w} R) : Prop where
  /-- Exact action on every left-whiskered generated path. -/
  maps_whiskerLeft : ∀ (pre : LinearHammock M N)
      {first second : LinearHammock N P}
      (path : Bicategory.MarkedZigzag.HammockPath
        (costExactArrows R) first second),
    (hammockPathSemanticComparison M P).app (op ⦋1⦌)
        (ComposableArrows.mk₁
          (Quotient.mk
            (Bicategory.MarkedZigzag.HammockPath.setoid
              (costExactArrows R)
              (Bicategory.MarkedZigzag.LinearWord.append
                (costExactArrows R) pre first)
              (Bicategory.MarkedZigzag.LinearWord.append
                (costExactArrows R) pre second))
            (Bicategory.MarkedZigzag.HammockPath.whiskerLeft pre path))) =
      ComposableArrows.mk₁
        (Bicategory.MarkedZigzag.HammockPath.normalizedWhiskerLeftHom
          (costExactArrows R) pre
          (Bicategory.MarkedZigzag.HammockPath.toHom
            (costExactArrows R) path))
  /-- Exact action on every right-whiskered generated path. -/
  maps_whiskerRight : ∀ {first second : LinearHammock M N}
      (path : Bicategory.MarkedZigzag.HammockPath
        (costExactArrows R) first second)
      (post : LinearHammock N P),
    (hammockPathSemanticComparison M P).app (op ⦋1⦌)
        (ComposableArrows.mk₁
          (Quotient.mk
            (Bicategory.MarkedZigzag.HammockPath.setoid
              (costExactArrows R)
              (Bicategory.MarkedZigzag.LinearWord.append
                (costExactArrows R) first post)
              (Bicategory.MarkedZigzag.LinearWord.append
                (costExactArrows R) second post))
            (Bicategory.MarkedZigzag.HammockPath.whiskerRight path post))) =
      ComposableArrows.mk₁
        (Bicategory.MarkedZigzag.HammockPath.normalizedWhiskerRightHom
          (costExactArrows R) post
          (Bicategory.MarkedZigzag.HammockPath.toHom
            (costExactArrows R) path))
  /-- Exact action on horizontal append. -/
  maps_append : ∀
      {firstSource firstTarget : LinearHammock M N}
      {secondSource secondTarget : LinearHammock N P}
      (first : Bicategory.MarkedZigzag.HammockPath
        (costExactArrows R) firstSource firstTarget)
      (second : Bicategory.MarkedZigzag.HammockPath
        (costExactArrows R) secondSource secondTarget),
    (hammockPathSemanticComparison M P).app (op ⦋1⦌)
        (ComposableArrows.mk₁
          (Quotient.mk
            (Bicategory.MarkedZigzag.HammockPath.setoid
              (costExactArrows R)
              (Bicategory.MarkedZigzag.LinearWord.append
                (costExactArrows R) firstSource secondSource)
              (Bicategory.MarkedZigzag.LinearWord.append
                (costExactArrows R) firstTarget secondTarget))
            (Bicategory.MarkedZigzag.HammockPath.append
              (costExactArrows R) first second))) =
      ComposableArrows.mk₁
        (Bicategory.MarkedZigzag.AlignedCell.quotientVcomp
          (costExactArrows R)
          (Bicategory.MarkedZigzag.HammockPath.normalizedWhiskerRightHom
            (costExactArrows R) secondSource
            (Bicategory.MarkedZigzag.HammockPath.toHom
              (costExactArrows R) first))
          (Bicategory.MarkedZigzag.HammockPath.normalizedWhiskerLeftHom
            (costExactArrows R) firstTarget
            (Bicategory.MarkedZigzag.HammockPath.toHom
              (costExactArrows R) second)))

/-- Every cost-exact model triple satisfies the exact generated-path
whiskering and append interface. -/
theorem hammockPathWhiskeringCore
    (M N P : ProcessModel.{u, v, w} R) :
    HammockPathWhiskeringCore M N P where
  maps_whiskerLeft := hammockPathSemanticComparison_whiskerLeftEdge
  maps_whiskerRight := hammockPathSemanticComparison_whiskerRightEdge
  maps_append := hammockPathSemanticComparison_appendEdge

/-- Machine-facing raw-cell normalization fragment for the cost-exact
marking. It records the completed structural-induction cases without claiming
normalization of every raw generator. -/
structure HammockRawCellNormalizationCore : Prop where
  /-- Every raw identity cell is normalizable. -/
  identity : ∀ (M N : ProcessModel.{u, v, w} R)
      (word : CostExactZigzag.Word (R := R) M N),
    Bicategory.MarkedZigzag.HammockPath.Normalizable
      (costExactArrows R) (Bicategory.MarkedZigzag.Cell.id word)
  /-- Normalizability is closed under raw vertical composition. -/
  vcomp : ∀ (M N : ProcessModel.{u, v, w} R)
      {first middle last : CostExactZigzag.Word (R := R) M N}
      {alpha : Bicategory.MarkedZigzag.Cell
        (costExactArrows R) first middle}
      {beta : Bicategory.MarkedZigzag.Cell
        (costExactArrows R) middle last},
    Bicategory.MarkedZigzag.HammockPath.Normalizable
        (costExactArrows R) alpha →
      Bicategory.MarkedZigzag.HammockPath.Normalizable
        (costExactArrows R) beta →
      Bicategory.MarkedZigzag.HammockPath.Normalizable
        (costExactArrows R)
        (Bicategory.MarkedZigzag.Cell.vcomp alpha beta)
  /-- Every original source 2-cell is normalizable. -/
  original : ∀ (M N : ProcessModel.{u, v, w} R)
      {f g : M ⟶ N} (alpha : f ⟶ g),
    Bicategory.MarkedZigzag.HammockPath.Normalizable
      (costExactArrows R)
      (Bicategory.MarkedZigzag.Cell.original
        (W := costExactArrows R) alpha)
  /-- The source-identity comparison is normalizable. -/
  sourceId : ∀ (M : ProcessModel.{u, v, w} R),
    Bicategory.MarkedZigzag.HammockPath.Normalizable
      (costExactArrows R)
      (Bicategory.MarkedZigzag.Cell.sourceId
        (W := costExactArrows R) (X := M))
  /-- The inverse source-identity comparison is normalizable. -/
  sourceIdInv : ∀ (M : ProcessModel.{u, v, w} R),
    Bicategory.MarkedZigzag.HammockPath.Normalizable
      (costExactArrows R)
      (Bicategory.MarkedZigzag.Cell.sourceIdInv
        (W := costExactArrows R) (X := M))
  /-- Source-composition comparison is normalizable. -/
  sourceComp : ∀ {M N P : ProcessModel.{u, v, w} R}
      (f : M ⟶ N) (g : N ⟶ P),
    Bicategory.MarkedZigzag.HammockPath.Normalizable
      (costExactArrows R)
      (Bicategory.MarkedZigzag.Cell.sourceComp
        (W := costExactArrows R) f g)
  /-- Inverse source-composition comparison is normalizable. -/
  sourceCompInv : ∀ {M N P : ProcessModel.{u, v, w} R}
      (f : M ⟶ N) (g : N ⟶ P),
    Bicategory.MarkedZigzag.HammockPath.Normalizable
      (costExactArrows R)
      (Bicategory.MarkedZigzag.Cell.sourceCompInv
        (W := costExactArrows R) f g)
  /-- Marked unit is normalizable. -/
  markedUnit : ∀ {M N : ProcessModel.{u, v, w} R}
      (f : M ⟶ N) (hf : costExactArrows R f),
    Bicategory.MarkedZigzag.HammockPath.Normalizable
      (costExactArrows R)
      (Bicategory.MarkedZigzag.Cell.markedUnit
        (W := costExactArrows R) f hf)
  /-- Inverse marked unit is normalizable. -/
  markedUnitInv : ∀ {M N : ProcessModel.{u, v, w} R}
      (f : M ⟶ N) (hf : costExactArrows R f),
    Bicategory.MarkedZigzag.HammockPath.Normalizable
      (costExactArrows R)
      (Bicategory.MarkedZigzag.Cell.markedUnitInv
        (W := costExactArrows R) f hf)
  /-- Marked counit is normalizable. -/
  markedCounit : ∀ {M N : ProcessModel.{u, v, w} R}
      (f : M ⟶ N) (hf : costExactArrows R f),
    Bicategory.MarkedZigzag.HammockPath.Normalizable
      (costExactArrows R)
      (Bicategory.MarkedZigzag.Cell.markedCounit
        (W := costExactArrows R) f hf)
  /-- Inverse marked counit is normalizable. -/
  markedCounitInv : ∀ {M N : ProcessModel.{u, v, w} R}
      (f : M ⟶ N) (hf : costExactArrows R f),
    Bicategory.MarkedZigzag.HammockPath.Normalizable
      (costExactArrows R)
      (Bicategory.MarkedZigzag.Cell.markedCounitInv
        (W := costExactArrows R) f hf)
  /-- Raw left whiskering preserves normalizability. -/
  whiskerLeft : ∀ (M N P : ProcessModel.{u, v, w} R)
      (pre : CostExactZigzag.Word (R := R) M N)
      {first second : CostExactZigzag.Word (R := R) N P}
      {cell : Bicategory.MarkedZigzag.Cell
        (costExactArrows R) first second},
    Bicategory.MarkedZigzag.HammockPath.Normalizable
        (costExactArrows R) cell →
      Bicategory.MarkedZigzag.HammockPath.Normalizable
        (costExactArrows R)
        (Bicategory.MarkedZigzag.Cell.whiskerLeft pre cell)
  /-- Raw right whiskering preserves normalizability. -/
  whiskerRight : ∀ (M N P : ProcessModel.{u, v, w} R)
      {first second : CostExactZigzag.Word (R := R) M N}
      {cell : Bicategory.MarkedZigzag.Cell
        (costExactArrows R) first second}
      (post : CostExactZigzag.Word (R := R) N P),
    Bicategory.MarkedZigzag.HammockPath.Normalizable
        (costExactArrows R) cell →
      Bicategory.MarkedZigzag.HammockPath.Normalizable
        (costExactArrows R)
        (Bicategory.MarkedZigzag.Cell.whiskerRight cell post)
  /-- Equality transport preserves normalizability. -/
  transport : ∀ (M N : ProcessModel.{u, v, w} R)
      {first second first' second' : CostExactZigzag.Word (R := R) M N}
      (sourceEquality : first = first')
      (targetEquality : second = second')
      {cell : Bicategory.MarkedZigzag.Cell
        (costExactArrows R) first second},
    Bicategory.MarkedZigzag.HammockPath.Normalizable
        (costExactArrows R) cell →
      Bicategory.MarkedZigzag.HammockPath.Normalizable
        (costExactArrows R)
        (Bicategory.MarkedZigzag.Cell.transport
          sourceEquality targetEquality cell)
  /-- The remaining explicit structural-generator obligations suffice for
  normalization of every cost-exact raw cell. -/
  structural_induction : ∀ (M N : ProcessModel.{u, v, w} R),
      (@Bicategory.MarkedZigzag.HammockPath.StructuralGeneratorNormalizable
          (ProcessModel.{u, v, w} R) _ (costExactArrows R)) →
      ∀ {first second : CostExactZigzag.Word (R := R) M N}
        (cell : Bicategory.MarkedZigzag.Cell
          (costExactArrows R) first second),
      Bicategory.MarkedZigzag.HammockPath.Normalizable
        (costExactArrows R) cell

/-- The completed raw-cell induction branches hold uniformly for the
cost-exact marking. -/
theorem hammockRawCellNormalizationCore :
    HammockRawCellNormalizationCore (R := R) where
  identity := fun _ _ word =>
    Bicategory.MarkedZigzag.HammockPath.identity_normalizable
      (costExactArrows R) word
  vcomp := fun _ _ {_ _ _} {_} {_} hAlpha hBeta =>
    Bicategory.MarkedZigzag.HammockPath.vcomp_normalizable
      (costExactArrows R) hAlpha hBeta
  original := fun _ _ {_ _} alpha =>
    Bicategory.MarkedZigzag.HammockPath.original_normalizable
      (costExactArrows R) alpha
  sourceId := fun _ =>
    Bicategory.MarkedZigzag.HammockPath.sourceId_normalizable
      (costExactArrows R)
  sourceIdInv := fun _ =>
    Bicategory.MarkedZigzag.HammockPath.sourceIdInv_normalizable
      (costExactArrows R)
  sourceComp := fun f g =>
    Bicategory.MarkedZigzag.HammockPath.sourceComp_normalizable
      (costExactArrows R) f g
  sourceCompInv := fun f g =>
    Bicategory.MarkedZigzag.HammockPath.sourceCompInv_normalizable
      (costExactArrows R) f g
  markedUnit := fun f hf =>
    Bicategory.MarkedZigzag.HammockPath.markedUnit_normalizable
      (costExactArrows R) f hf
  markedUnitInv := fun f hf =>
    Bicategory.MarkedZigzag.HammockPath.markedUnitInv_normalizable
      (costExactArrows R) f hf
  markedCounit := fun f hf =>
    Bicategory.MarkedZigzag.HammockPath.markedCounit_normalizable
      (costExactArrows R) f hf
  markedCounitInv := fun f hf =>
    Bicategory.MarkedZigzag.HammockPath.markedCounitInv_normalizable
      (costExactArrows R) f hf
  whiskerLeft := fun _ _ _ pre {_ _} {_} member =>
    Bicategory.MarkedZigzag.HammockPath.whiskerLeft_normalizable
      (costExactArrows R) pre member
  whiskerRight := fun _ _ _ {_ _} {_} post member =>
    Bicategory.MarkedZigzag.HammockPath.whiskerRight_normalizable
      (costExactArrows R) member post
  transport := fun _ _ {_ _ _ _} sourceEquality targetEquality {_} member =>
    Bicategory.MarkedZigzag.HammockPath.transport_normalizable
      (costExactArrows R) sourceEquality targetEquality member
  structural_induction := fun _ _ generators {_ _} cell =>
    Bicategory.MarkedZigzag.HammockPath.normalizable_of_structuralGenerators
      (costExactArrows R) generators cell

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
  /-- Explicit aligned multi-column hammock syntax and its exact row/edge
  interpretation laws. -/
  alignedHammock : AlignedHammockCore M N
  /-- Executable column insertion/deletion and composite expansion/contraction
  with exact signed width and semantic round-trip laws. -/
  columnRefinement : ColumnRefinementCore M N
  /-- Common-refinement row quotient with sound semantic isomorphisms. -/
  commonRefinement : CommonRefinementCore M N
  /-- Zero-truncated common-refinement groupoid nerve and its discrete-
  quotient equivalence. -/
  thinRefinementNerve : ThinRefinementNerveCore M N
  /-- Non-thin semantic refinement-path groupoid nerve with faithful exact
  edge interpretation. -/
  refinementPathNerve : RefinementPathNerveCore M N
  /-- Exact refinement-generated semantic image subgroupoid, its equivalence
  with semantic paths, and its faithful inclusion into the full linear nerve. -/
  refinementImageNerve : RefinementImageNerveCore M N
  /-- Non-groupoidal generated hammock paths combining refinements with
  arbitrary aligned/source 2-cells and strictly extending refinement paths. -/
  hammockPathNerve : HammockPathNerveCore M N
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
  alignedHammock := alignedHammockCore M N
  columnRefinement := columnRefinementCore M N
  commonRefinement := commonRefinementCore M N
  thinRefinementNerve := thinRefinementNerveCore M N
  refinementPathNerve := refinementPathNerveCore M N
  refinementImageNerve := refinementImageNerveCore M N
  hammockPathNerve := hammockPathNerveCore M N
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
