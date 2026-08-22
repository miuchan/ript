import Ript.ForMathlib.CategoryTheory.Bicategory.MarkedZigzagLinearHammock
import Mathlib.CategoryTheory.Groupoid.Discrete

/-!
# Column-aligned hammocks for marked bicategories

This file refines the linear marked-zigzag object model by making horizontal
columns explicit.  An `AlignedCell` consists of one raw atomic 2-cell in every
column between two linear words with the same intermediate objects.  Columns
append horizontally, compose vertically componentwise, and interpret as one
quotient 2-cell in the existing linear mapping category.

The file also gives executable elementary column refinements: forward identity
columns can be inserted/deleted, forward composite columns can be
expanded/contracted, marked unit/counit pairs can be inserted/deleted, and
moves lift beneath arbitrary prefixes and compose. Their signed width changes
and quotient interpretations are exact, and inverse generator moves cancel
semantically. Every refinement now has an executable reverse and one unified
semantic isomorphism. Explicit common-refinement spans form an equivalence
relation and a row quotient, whose equality is sound for semantic isomorphism
without assuming object equality. The induced thin refinement groupoid is
equivalent to the discrete row quotient. A non-thin semantic refinement-path
groupoid now retains paths up to equality of their quotient-cell semantics and
embeds faithfully into the linear mapping category. Fullness/image
characterization, critical-pair coherence, and reduced-hammock invariance are
still absent, so this is not by itself the classical Dwyer--Kan hammock
localization.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace CategoryTheory.Bicategory.MarkedZigzag

open CategoryTheory
open CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory

universe u v w

variable {B : Type u} [Bicategory.{w, v} B]
variable (W : Bicategory.MorphismProperty B)

/-- A horizontally column-aligned raw hammock cell.  Source and target rows
have the same intermediate objects, and each column carries an atomic raw
2-cell. -/
inductive AlignedCell : ∀ {X Y : B},
    LinearWord W X Y → LinearWord W X Y → Type max u v w where
  /-- The unique empty aligned hammock at an object. -/
  | nil (X : B) : AlignedCell (.nil X) (.nil X)
  /-- Prepend one atomic column to an aligned tail. -/
  | cons {X Y Z : B} {sourceStep targetStep : Step W X Y}
      {sourceRest targetRest : LinearWord W Y Z}
      (column : Cell W (.atom sourceStep) (.atom targetStep))
      (rest : AlignedCell sourceRest targetRest) :
      AlignedCell (.cons sourceStep sourceRest)
        (.cons targetStep targetRest)

namespace AlignedCell

/-- Number of explicit horizontal columns in an aligned hammock. -/
def width {X Y : B} {source target : LinearWord W X Y} :
    AlignedCell W source target → ℕ
  | .nil _ => 0
  | .cons _ rest => 1 + width rest

/-- The width of an aligned hammock is exactly the length of its source row. -/
@[simp]
theorem width_eq_source_length {X Y : B}
    {source target : LinearWord W X Y}
    (cell : AlignedCell W source target) :
    width W cell = LinearWord.length W source := by
  induction cell with
  | nil => rfl
  | cons column rest ih =>
      simp [width, LinearWord.length, ih]

/-- Aligned source and target rows have exactly the same number of steps. -/
theorem source_length_eq_target_length {X Y : B}
    {source target : LinearWord W X Y}
    (cell : AlignedCell W source target) :
    LinearWord.length W source = LinearWord.length W target := by
  induction cell with
  | nil => rfl
  | cons column rest ih =>
      simp [LinearWord.length, ih]

/-- The width of an aligned hammock is exactly the length of its target row. -/
theorem width_eq_target_length {X Y : B}
    {source target : LinearWord W X Y}
    (cell : AlignedCell W source target) :
    width W cell = LinearWord.length W target :=
  (width_eq_source_length W cell).trans
    (source_length_eq_target_length W cell)

/-- The componentwise identity aligned hammock on a linear word. -/
def identity {X Y : B} (word : LinearWord W X Y) :
    AlignedCell W word word :=
  match word with
  | .nil X => .nil X
  | .cons step rest =>
      .cons (Cell.id (.atom step)) (identity rest)

/-- Componentwise vertical composition of aligned hammocks. -/
def vcomp {X Y : B} {first middle last : LinearWord W X Y} :
    AlignedCell W first middle → AlignedCell W middle last →
      AlignedCell W first last
  | .nil _, .nil _ => .nil _
  | .cons firstColumn firstRest, .cons secondColumn secondRest =>
      .cons (.vcomp firstColumn secondColumn)
        (vcomp firstRest secondRest)

/-- Structurally recursive horizontal concatenation with the second hammock
fixed.  Making the changing source object explicit keeps this indexed
recursion executable by Lean's code generator. -/
def appendAux {Y Z : B}
    {secondSource secondTarget : LinearWord W Y Z}
    (second : AlignedCell W secondSource secondTarget) :
    (X : B) → (firstSource firstTarget : LinearWord W X Y) →
      AlignedCell W firstSource firstTarget →
        AlignedCell W (LinearWord.append W firstSource secondSource)
          (LinearWord.append W firstTarget secondTarget)
  | _, .nil _, .nil _, .nil _ => second
  | _, .cons _ _, .cons _ _, .cons column rest =>
      .cons column (appendAux second _ _ _ rest)

/-- Executable horizontal concatenation of aligned hammocks. -/
def append {X Y Z : B}
    {firstSource firstTarget : LinearWord W X Y}
    {secondSource secondTarget : LinearWord W Y Z}
    (first : AlignedCell W firstSource firstTarget)
    (second : AlignedCell W secondSource secondTarget) :
    AlignedCell W (LinearWord.append W firstSource secondSource)
      (LinearWord.append W firstTarget secondTarget) :=
  appendAux W second X firstSource firstTarget first

/-- Horizontal concatenation adds the explicit column widths. -/
theorem width_append {X Y Z : B}
    {firstSource firstTarget : LinearWord W X Y}
    {secondSource secondTarget : LinearWord W Y Z}
    (first : AlignedCell W firstSource firstTarget)
    (second : AlignedCell W secondSource secondTarget) :
    width W (append W first second) = width W first + width W second := by
  calc
    width W (append W first second) =
        LinearWord.length W
          (LinearWord.append W firstSource secondSource) :=
      width_eq_source_length W _
    _ = LinearWord.length W firstSource +
        LinearWord.length W secondSource :=
      LinearWord.length_append W firstSource secondSource
    _ = width W first + width W second := by
      rw [width_eq_source_length W first, width_eq_source_length W second]

/-- Interpret the explicit columns as one raw 2-cell between the binary
expansions of the two linear rows. -/
def toCell {X Y : B} {source target : LinearWord W X Y} :
    AlignedCell W source target →
      Cell W (LinearWord.toWord W source) (LinearWord.toWord W target)
  | .nil X => Cell.id (.nil X)
  | @AlignedCell.cons _ _ _ _ _ _ sourceStep targetStep sourceRest targetRest
      column rest =>
      Cell.vcomp
        (Cell.whiskerRight column (LinearWord.toWord W sourceRest))
        (Cell.whiskerLeft (.atom targetStep) (toCell rest))

/-- Explicit vertical composition in one presented word mapping category. -/
def quotientVcomp {X Y : B} {first middle last : Word W X Y}
    (alpha : Presented.Hom W first middle)
    (beta : Presented.Hom W middle last) : Presented.Hom W first last :=
  @CategoryStruct.comp (Word W X Y)
    (Presented.wordCategory W X Y).toCategoryStruct
    first middle last alpha beta

/-- Quotient interpretation of an aligned hammock in the linear mapping
category. -/
def toHom {X Y : B} {source target : LinearWord W X Y}
    (cell : AlignedCell W source target) :
    Presented.Hom W (LinearWord.toWord W source)
      (LinearWord.toWord W target) :=
  Presented.mk W (toCell W cell)

/-- Column interpretation is horizontal pasting of the leading atomic cell
with the recursively interpreted tail. -/
@[simp]
theorem toHom_cons {X Y Z : B}
    {sourceStep targetStep : Step W X Y}
    {sourceRest targetRest : LinearWord W Y Z}
    (column : Cell W (.atom sourceStep) (.atom targetStep))
    (rest : AlignedCell W sourceRest targetRest) :
    toHom W (.cons column rest) =
      quotientVcomp W
        (Presented.whiskerRightHom W (LinearWord.toWord W sourceRest)
          (Presented.mk W column))
        (Presented.whiskerLeftHom W (.atom targetStep) (toHom W rest)) :=
  rfl

/-- Right whiskering preserves arbitrary quotient vertical composites. -/
theorem whiskerRightHom_vcomp {X Y Z : B}
    {first middle last : Word W X Y}
    (postword : Word W Y Z)
    (alpha : Presented.Hom W first middle)
    (beta : Presented.Hom W middle last) :
    Presented.whiskerRightHom W postword (quotientVcomp W alpha beta) =
      quotientVcomp W
        (Presented.whiskerRightHom W postword alpha)
        (Presented.whiskerRightHom W postword beta) := by
  rcases alpha with ⟨alpha⟩
  rcases beta with ⟨beta⟩
  exact Quot.sound (Presented.Rel.whisker_right_vcomp postword alpha beta)

/-- Left whiskering preserves arbitrary quotient vertical composites. -/
theorem whiskerLeftHom_vcomp {X Y Z : B}
    (preword : Word W X Y) {first middle last : Word W Y Z}
    (alpha : Presented.Hom W first middle)
    (beta : Presented.Hom W middle last) :
    Presented.whiskerLeftHom W preword (quotientVcomp W alpha beta) =
      quotientVcomp W
        (Presented.whiskerLeftHom W preword alpha)
        (Presented.whiskerLeftHom W preword beta) := by
  rcases alpha with ⟨alpha⟩
  rcases beta with ⟨beta⟩
  exact Quot.sound (Presented.Rel.whisker_left_vcomp preword alpha beta)

/-- Quotient horizontal exchange for arbitrary atomic-column and tail
morphisms. -/
theorem whisker_exchange {X Y Z : B}
    {first first' : Word W X Y} {second second' : Word W Y Z}
    (alpha : Presented.Hom W first first')
    (beta : Presented.Hom W second second') :
    quotientVcomp W
        (Presented.whiskerLeftHom W first beta)
        (Presented.whiskerRightHom W second' alpha) =
      quotientVcomp W
        (Presented.whiskerRightHom W second alpha)
        (Presented.whiskerLeftHom W first' beta) := by
  rcases alpha with ⟨alpha⟩
  rcases beta with ⟨beta⟩
  exact Quot.sound (Presented.Rel.whisker_exchange alpha beta)

/-- Interpreting the componentwise identity hammock gives the identity
morphism of the linear mapping category. -/
@[simp]
theorem toHom_identity {X Y : B} (word : LinearWord W X Y) :
    toHom W (identity W word) = 𝟙 (LinearWord.toWord W word) := by
  induction word with
  | nil => rfl
  | cons step rest ih =>
      change toHom W
          (.cons (Cell.id (Word.atom step)) (identity W rest)) = _
      rw [toHom_cons, ih]
      have rightIdentity :
          Presented.whiskerRightHom W (LinearWord.toWord W rest)
              (Presented.mk W (Cell.id (Word.atom step))) =
            𝟙 (Word.append (W := W) (Word.atom step)
              (LinearWord.toWord W rest)) :=
        Quot.sound (Presented.Rel.whisker_right_id
          (Word.atom step) (LinearWord.toWord W rest))
      have leftIdentity :
          Presented.whiskerLeftHom W (Word.atom step)
              (𝟙 (LinearWord.toWord W rest)) =
            𝟙 (Word.append (W := W) (Word.atom step)
              (LinearWord.toWord W rest)) :=
        Quot.sound (Presented.Rel.whisker_left_id
          (Word.atom step) (LinearWord.toWord W rest))
      rw [rightIdentity, leftIdentity]
      exact Category.id_comp _

/-- Interpreting componentwise vertical composition agrees exactly with
vertical composition in the presented linear mapping category. -/
theorem toHom_vcomp {X Y : B}
    {first middle last : LinearWord W X Y}
    (alpha : AlignedCell W first middle)
    (beta : AlignedCell W middle last) :
    toHom W (vcomp W alpha beta) =
      quotientVcomp W (toHom W alpha) (toHom W beta) := by
  induction alpha with
  | nil =>
      cases beta
      exact (Quot.sound
        (Presented.Rel.id_vcomp (Cell.id (Word.nil _)))).symm
  | @cons X' Y' Z' sourceStep middleStep sourceRest middleRest
      firstColumn firstRest ih =>
      cases beta with
      | @cons _ _ _ _ targetStep _ targetRest secondColumn secondRest =>
          change quotientVcomp W
              (Presented.whiskerRightHom W
                (LinearWord.toWord W sourceRest)
                (Presented.mk W (Cell.vcomp firstColumn secondColumn)))
              (Presented.whiskerLeftHom W (Word.atom targetStep)
                (toHom W (vcomp W firstRest secondRest))) = _
          rw [ih]
          change quotientVcomp W
              (Presented.whiskerRightHom W
                (LinearWord.toWord W sourceRest)
                (quotientVcomp W (Presented.mk W firstColumn)
                  (Presented.mk W secondColumn)))
              (Presented.whiskerLeftHom W (Word.atom targetStep)
                (quotientVcomp W (toHom W firstRest)
                  (toHom W secondRest))) = _
          rw [whiskerRightHom_vcomp, whiskerLeftHom_vcomp]
          let rightFirst :=
            Presented.whiskerRightHom W
              (LinearWord.toWord W sourceRest)
              (Presented.mk W firstColumn)
          let rightSecond :=
            Presented.whiskerRightHom W
              (LinearWord.toWord W sourceRest)
              (Presented.mk W secondColumn)
          let leftFirst :=
            Presented.whiskerLeftHom W (Word.atom targetStep)
              (toHom W firstRest)
          let leftSecond :=
            Presented.whiskerLeftHom W (Word.atom targetStep)
              (toHom W secondRest)
          let middleLeft :=
            Presented.whiskerLeftHom W (Word.atom middleStep)
              (toHom W firstRest)
          let middleRight :=
            Presented.whiskerRightHom W
              (LinearWord.toWord W middleRest)
              (Presented.mk W secondColumn)
          have exchange :
              quotientVcomp W middleLeft middleRight =
                quotientVcomp W rightSecond leftFirst :=
            whisker_exchange W (Presented.mk W secondColumn)
              (toHom W firstRest)
          change quotientVcomp W
              (quotientVcomp W rightFirst rightSecond)
              (quotientVcomp W leftFirst leftSecond) =
            quotientVcomp W
              (quotientVcomp W rightFirst middleLeft)
              (quotientVcomp W middleRight leftSecond)
          calc
            quotientVcomp W
                (quotientVcomp W rightFirst rightSecond)
                (quotientVcomp W leftFirst leftSecond) =
              quotientVcomp W rightFirst
                (quotientVcomp W
                  (quotientVcomp W rightSecond leftFirst) leftSecond) := by
                    simp only [quotientVcomp, Category.assoc]
            _ = quotientVcomp W rightFirst
                (quotientVcomp W
                  (quotientVcomp W middleLeft middleRight) leftSecond) := by
                    rw [exchange]
            _ = quotientVcomp W
                (quotientVcomp W rightFirst middleLeft)
                (quotientVcomp W middleRight leftSecond) := by
                    simp only [quotientVcomp, Category.assoc]

end AlignedCell

/-! ## Executable column refinements -/

/-- Executable column-refinement moves between linear hammock rows.  The
generators insert/delete a forward identity column, expand/contract one
forward composite column, or insert/delete a marked unit/counit pair. `under`
performs a move beneath any common prefix, and `vcomp` closes the moves under
transitive composition. -/
inductive ColumnRefinement : ∀ {X Y : B},
    LinearWord W X Y → LinearWord W X Y → Type max u v where
  /-- Reflexive refinement. -/
  | identity {X Y : B} (word : LinearWord W X Y) :
      ColumnRefinement word word
  /-- Transitive composition of refinements. -/
  | vcomp {X Y : B} {first middle last : LinearWord W X Y}
      (alpha : ColumnRefinement first middle)
      (beta : ColumnRefinement middle last) : ColumnRefinement first last
  /-- Delete a leading forward identity column. -/
  | deleteIdentity {X Y : B} (rest : LinearWord W X Y) :
      ColumnRefinement
        (.cons (Step.forward (W := W) (𝟙 X)) rest) rest
  /-- Insert a leading forward identity column. -/
  | insertIdentity {X Y : B} (rest : LinearWord W X Y) :
      ColumnRefinement rest
        (.cons (Step.forward (W := W) (𝟙 X)) rest)
  /-- Expand a leading forward composite into two forward columns. -/
  | expandForward {X Y Z T : B} (f : X ⟶ Y) (g : Y ⟶ Z)
      (rest : LinearWord W Z T) :
      ColumnRefinement
        (.cons (Step.forward (W := W) (f ≫ g)) rest)
        (.cons (Step.forward (W := W) f)
          (.cons (Step.forward (W := W) g) rest))
  /-- Contract two leading forward columns into their composite. -/
  | contractForward {X Y Z T : B} (f : X ⟶ Y) (g : Y ⟶ Z)
      (rest : LinearWord W Z T) :
      ColumnRefinement
        (.cons (Step.forward (W := W) f)
          (.cons (Step.forward (W := W) g) rest))
        (.cons (Step.forward (W := W) (f ≫ g)) rest)
  /-- Delete a leading marked unit pair `f ; f⁻¹`. -/
  | deleteMarkedUnitPair {X Y T : B} (f : X ⟶ Y) (hf : W f)
      (rest : LinearWord W X T) :
      ColumnRefinement
        (.cons (Step.forward (W := W) f)
          (.cons (Step.backward (W := W) f hf) rest)) rest
  /-- Insert a leading marked unit pair `f ; f⁻¹`. -/
  | insertMarkedUnitPair {X Y T : B} (f : X ⟶ Y) (hf : W f)
      (rest : LinearWord W X T) :
      ColumnRefinement rest
        (.cons (Step.forward (W := W) f)
          (.cons (Step.backward (W := W) f hf) rest))
  /-- Delete a leading marked counit pair `f⁻¹ ; f`. -/
  | deleteMarkedCounitPair {X Y T : B} (f : X ⟶ Y) (hf : W f)
      (rest : LinearWord W Y T) :
      ColumnRefinement
        (.cons (Step.backward (W := W) f hf)
          (.cons (Step.forward (W := W) f) rest)) rest
  /-- Insert a leading marked counit pair `f⁻¹ ; f`. -/
  | insertMarkedCounitPair {X Y T : B} (f : X ⟶ Y) (hf : W f)
      (rest : LinearWord W Y T) :
      ColumnRefinement rest
        (.cons (Step.backward (W := W) f hf)
          (.cons (Step.forward (W := W) f) rest))
  /-- Perform a refinement beneath one common oriented prefix column. -/
  | under {X Y Z : B} (step : Step W X Y)
      {first last : LinearWord W Y Z}
      (refinement : ColumnRefinement first last) :
      ColumnRefinement (.cons step first) (.cons step last)

namespace ColumnRefinement

/-- Signed change in horizontal width: positive values insert/expand columns
and negative values delete/contract them. -/
def widthChange {X Y : B} {source target : LinearWord W X Y} :
    ColumnRefinement W source target → ℤ
  | .identity _ => 0
  | .vcomp alpha beta => widthChange alpha + widthChange beta
  | .deleteIdentity _ => -1
  | .insertIdentity _ => 1
  | .expandForward _ _ _ => 1
  | .contractForward _ _ _ => -1
  | .deleteMarkedUnitPair _ _ _ => -2
  | .insertMarkedUnitPair _ _ _ => 2
  | .deleteMarkedCounitPair _ _ _ => -2
  | .insertMarkedCounitPair _ _ _ => 2
  | .under _ refinement => widthChange refinement

/-- Executable reversal of every elementary, prefixed, or composite column
refinement. -/
def reverse {X Y : B} {source target : LinearWord W X Y} :
    ColumnRefinement W source target → ColumnRefinement W target source
  | .identity word => .identity word
  | .vcomp alpha beta => .vcomp (reverse beta) (reverse alpha)
  | .deleteIdentity rest => .insertIdentity rest
  | .insertIdentity rest => .deleteIdentity rest
  | .expandForward f g rest => .contractForward f g rest
  | .contractForward f g rest => .expandForward f g rest
  | .deleteMarkedUnitPair f hf rest => .insertMarkedUnitPair f hf rest
  | .insertMarkedUnitPair f hf rest => .deleteMarkedUnitPair f hf rest
  | .deleteMarkedCounitPair f hf rest => .insertMarkedCounitPair f hf rest
  | .insertMarkedCounitPair f hf rest => .deleteMarkedCounitPair f hf rest
  | .under step refinement => .under step (reverse refinement)

/-- Reversing a refinement negates its exact signed width change. -/
theorem widthChange_reverse {X Y : B}
    {source target : LinearWord W X Y}
    (refinement : ColumnRefinement W source target) :
    widthChange W (reverse W refinement) = -widthChange W refinement := by
  induction refinement
  case vcomp alpha beta ihAlpha ihBeta =>
    simp only [reverse, widthChange, ihAlpha, ihBeta]
    omega
  all_goals simp [reverse, widthChange, *]

/-- The signed refinement counter is exactly the target width minus the
source width, for every composite and prefixed refinement. -/
theorem target_length_eq_source_length_add_widthChange
    {X Y : B} {source target : LinearWord W X Y}
    (refinement : ColumnRefinement W source target) :
    (LinearWord.length W target : ℤ) =
      LinearWord.length W source + widthChange W refinement := by
  induction refinement <;>
    simp only [widthChange, LinearWord.length] at * <;> omega

/-- Interpret an executable refinement as one raw 2-cell between the binary
expansions of its source and target rows. -/
def toCell {X Y : B} {source target : LinearWord W X Y} :
    ColumnRefinement W source target →
      Cell W (LinearWord.toWord W source) (LinearWord.toWord W target)
  | .identity word => Cell.id (LinearWord.toWord W word)
  | .vcomp alpha beta => Cell.vcomp (toCell alpha) (toCell beta)
  | .deleteIdentity rest =>
      Cell.vcomp
        (Cell.whiskerRight (Cell.sourceId (W := W))
          (LinearWord.toWord W rest))
        (Cell.leftUnitor (W := W) (LinearWord.toWord W rest))
  | .insertIdentity rest =>
      Cell.vcomp
        (Cell.leftUnitorInv (W := W) (LinearWord.toWord W rest))
        (Cell.whiskerRight (Cell.sourceIdInv (W := W))
          (LinearWord.toWord W rest))
  | .expandForward f g rest =>
      Cell.vcomp
        (Cell.whiskerRight (Cell.sourceComp (W := W) f g)
          (LinearWord.toWord W rest))
        (Cell.associator (W := W) (Word.forward W f) (Word.forward W g)
          (LinearWord.toWord W rest))
  | .contractForward f g rest =>
      Cell.vcomp
        (Cell.associatorInv (W := W) (Word.forward W f) (Word.forward W g)
          (LinearWord.toWord W rest))
        (Cell.whiskerRight (Cell.sourceCompInv (W := W) f g)
          (LinearWord.toWord W rest))
  | .deleteMarkedUnitPair f hf rest =>
      Cell.vcomp
        (Cell.associatorInv (W := W) (Word.forward W f)
          (Word.backward W f hf) (LinearWord.toWord W rest))
        (Cell.vcomp
          (Cell.whiskerRight (Cell.markedUnitInv (W := W) f hf)
            (LinearWord.toWord W rest))
          (Cell.leftUnitor (W := W) (LinearWord.toWord W rest)))
  | .insertMarkedUnitPair f hf rest =>
      Cell.vcomp
        (Cell.leftUnitorInv (W := W) (LinearWord.toWord W rest))
        (Cell.vcomp
          (Cell.whiskerRight (Cell.markedUnit (W := W) f hf)
            (LinearWord.toWord W rest))
          (Cell.associator (W := W) (Word.forward W f)
            (Word.backward W f hf) (LinearWord.toWord W rest)))
  | .deleteMarkedCounitPair f hf rest =>
      Cell.vcomp
        (Cell.associatorInv (W := W) (Word.backward W f hf)
          (Word.forward W f) (LinearWord.toWord W rest))
        (Cell.vcomp
          (Cell.whiskerRight (Cell.markedCounit (W := W) f hf)
            (LinearWord.toWord W rest))
          (Cell.leftUnitor (W := W) (LinearWord.toWord W rest)))
  | .insertMarkedCounitPair f hf rest =>
      Cell.vcomp
        (Cell.leftUnitorInv (W := W) (LinearWord.toWord W rest))
        (Cell.vcomp
          (Cell.whiskerRight (Cell.markedCounitInv (W := W) f hf)
            (LinearWord.toWord W rest))
          (Cell.associator (W := W) (Word.backward W f hf)
            (Word.forward W f) (LinearWord.toWord W rest)))
  | .under step refinement =>
      Cell.whiskerLeft (Word.atom step) (toCell refinement)

/-- Quotient interpretation of an executable column refinement. -/
def toHom {X Y : B} {source target : LinearWord W X Y}
    (refinement : ColumnRefinement W source target) :
    Presented.Hom W (LinearWord.toWord W source)
      (LinearWord.toWord W target) :=
  Presented.mk W (toCell W refinement)

/-- Reflexive refinement interprets as the mapping-category identity. -/
@[simp]
theorem toHom_identity {X Y : B} (word : LinearWord W X Y) :
    toHom W (.identity word) = 𝟙 (LinearWord.toWord W word) :=
  rfl

/-- Transitive refinement composition interprets as quotient vertical
composition. -/
@[simp]
theorem toHom_vcomp {X Y : B}
    {first middle last : LinearWord W X Y}
    (alpha : ColumnRefinement W first middle)
    (beta : ColumnRefinement W middle last) :
    toHom W (.vcomp alpha beta) =
      AlignedCell.quotientVcomp W (toHom W alpha) (toHom W beta) :=
  rfl

/-- Exact interpretation of forward identity-column deletion. -/
theorem toHom_deleteIdentity {X Y : B} (rest : LinearWord W X Y) :
    toHom W (.deleteIdentity rest) =
      AlignedCell.quotientVcomp W
        (Presented.whiskerRightHom W (LinearWord.toWord W rest)
          (Presented.mk W (Cell.sourceId (W := W))))
        (Presented.mk W
          (Cell.leftUnitor (W := W) (LinearWord.toWord W rest))) :=
  rfl

/-- Exact interpretation of forward identity-column insertion. -/
theorem toHom_insertIdentity {X Y : B} (rest : LinearWord W X Y) :
    toHom W (.insertIdentity rest) =
      AlignedCell.quotientVcomp W
        (Presented.mk W
          (Cell.leftUnitorInv (W := W) (LinearWord.toWord W rest)))
        (Presented.whiskerRightHom W (LinearWord.toWord W rest)
          (Presented.mk W (Cell.sourceIdInv (W := W)))) :=
  rfl

/-- Exact interpretation of forward composite-column expansion. -/
theorem toHom_expandForward {X Y Z T : B} (f : X ⟶ Y) (g : Y ⟶ Z)
    (rest : LinearWord W Z T) :
    toHom W (.expandForward f g rest) =
      AlignedCell.quotientVcomp W
        (Presented.whiskerRightHom W (LinearWord.toWord W rest)
          (Presented.mk W (Cell.sourceComp (W := W) f g)))
        (Presented.mk W
          (Cell.associator (W := W) (Word.forward W f) (Word.forward W g)
            (LinearWord.toWord W rest))) :=
  rfl

/-- Exact interpretation of forward composite-column contraction. -/
theorem toHom_contractForward {X Y Z T : B} (f : X ⟶ Y) (g : Y ⟶ Z)
    (rest : LinearWord W Z T) :
    toHom W (.contractForward f g rest) =
      AlignedCell.quotientVcomp W
        (Presented.mk W
          (Cell.associatorInv (W := W) (Word.forward W f) (Word.forward W g)
            (LinearWord.toWord W rest)))
        (Presented.whiskerRightHom W (LinearWord.toWord W rest)
          (Presented.mk W (Cell.sourceCompInv (W := W) f g))) :=
  rfl

/-- Refinement beneath a common prefix interprets by exact left
whiskering. -/
theorem toHom_under {X Y Z : B} (step : Step W X Y)
    {first last : LinearWord W Y Z}
    (refinement : ColumnRefinement W first last) :
    toHom W (.under step refinement) =
      Presented.whiskerLeftHom W (Word.atom step) (toHom W refinement) :=
  rfl

/-- The semantic isomorphism implemented by identity-column deletion and
insertion. -/
noncomputable def identityColumnIso {X Y : B} (rest : LinearWord W X Y) :
    Word.append (W := W) (Word.forward W (𝟙 X))
        (LinearWord.toWord W rest) ≅ LinearWord.toWord W rest :=
  whiskerRightIso (B := Presented.Localization W)
      (Presented.sourceIdIso W X) (LinearWord.toWord W rest) ≪≫
    Presented.wordLeftUnitorIso W (LinearWord.toWord W rest)

/-- Identity-column deletion is exactly the forward map of its semantic
isomorphism. -/
theorem toHom_deleteIdentity_eq_hom {X Y : B}
    (rest : LinearWord W X Y) :
    toHom W (.deleteIdentity rest) = (identityColumnIso W rest).hom := by
  rfl

/-- Identity-column insertion is exactly the inverse map of its semantic
isomorphism. -/
theorem toHom_insertIdentity_eq_inv {X Y : B}
    (rest : LinearWord W X Y) :
    toHom W (.insertIdentity rest) = (identityColumnIso W rest).inv := by
  rfl

/-- Deleting and reinserting a forward identity column is semantically the
identity on the wider row. -/
theorem deleteIdentity_insertIdentity {X Y : B}
    (rest : LinearWord W X Y) :
    AlignedCell.quotientVcomp W
        (toHom W (.deleteIdentity rest))
        (toHom W (.insertIdentity rest)) =
      𝟙 (LinearWord.toWord W
        (.cons (Step.forward (W := W) (𝟙 X)) rest)) := by
  rw [toHom_deleteIdentity_eq_hom, toHom_insertIdentity_eq_inv]
  exact (identityColumnIso W rest).hom_inv_id

/-- Inserting and deleting a forward identity column is semantically the
identity on the narrower row. -/
theorem insertIdentity_deleteIdentity {X Y : B}
    (rest : LinearWord W X Y) :
    AlignedCell.quotientVcomp W
        (toHom W (.insertIdentity rest))
        (toHom W (.deleteIdentity rest)) =
      𝟙 (LinearWord.toWord W rest) := by
  rw [toHom_insertIdentity_eq_inv, toHom_deleteIdentity_eq_hom]
  exact (identityColumnIso W rest).inv_hom_id

/-- The semantic isomorphism implemented by expansion and contraction of a
forward composite column. -/
noncomputable def compositeColumnIso {X Y Z T : B}
    (f : X ⟶ Y) (g : Y ⟶ Z) (rest : LinearWord W Z T) :
    Word.append (W := W) (Word.forward W (f ≫ g))
        (LinearWord.toWord W rest) ≅
      Word.append (W := W) (Word.forward W f)
        (Word.append (W := W) (Word.forward W g)
          (LinearWord.toWord W rest)) :=
  whiskerRightIso (B := Presented.Localization W)
      (Presented.sourceCompIso W f g) (LinearWord.toWord W rest) ≪≫
    Presented.wordAssociatorIso W (Word.forward W f) (Word.forward W g)
      (LinearWord.toWord W rest)

/-- Composite-column expansion is exactly the forward map of its semantic
isomorphism. -/
theorem toHom_expandForward_eq_hom {X Y Z T : B}
    (f : X ⟶ Y) (g : Y ⟶ Z) (rest : LinearWord W Z T) :
    toHom W (.expandForward f g rest) =
      (compositeColumnIso W f g rest).hom := by
  rfl

/-- Composite-column contraction is exactly the inverse map of its semantic
isomorphism. -/
theorem toHom_contractForward_eq_inv {X Y Z T : B}
    (f : X ⟶ Y) (g : Y ⟶ Z) (rest : LinearWord W Z T) :
    toHom W (.contractForward f g rest) =
      (compositeColumnIso W f g rest).inv := by
  rfl

/-- Expanding and contracting a forward composite column is semantically the
identity on the one-column row. -/
theorem expandForward_contractForward {X Y Z T : B}
    (f : X ⟶ Y) (g : Y ⟶ Z) (rest : LinearWord W Z T) :
    AlignedCell.quotientVcomp W
        (toHom W (.expandForward f g rest))
        (toHom W (.contractForward f g rest)) =
      𝟙 (LinearWord.toWord W
        (.cons (Step.forward (W := W) (f ≫ g)) rest)) := by
  rw [toHom_expandForward_eq_hom, toHom_contractForward_eq_inv]
  exact (compositeColumnIso W f g rest).hom_inv_id

/-- Contracting and expanding two forward columns is semantically the
identity on the two-column row. -/
theorem contractForward_expandForward {X Y Z T : B}
    (f : X ⟶ Y) (g : Y ⟶ Z) (rest : LinearWord W Z T) :
    AlignedCell.quotientVcomp W
        (toHom W (.contractForward f g rest))
        (toHom W (.expandForward f g rest)) =
      𝟙 (LinearWord.toWord W
        (.cons (Step.forward (W := W) f)
          (.cons (Step.forward (W := W) g) rest))) := by
  rw [toHom_contractForward_eq_inv, toHom_expandForward_eq_hom]
  exact (compositeColumnIso W f g rest).inv_hom_id

/-- The semantic isomorphism implemented by deletion/insertion of a marked
unit pair `f ; f⁻¹`. -/
noncomputable def markedUnitPairIso {X Y T : B}
    (f : X ⟶ Y) (hf : W f) (rest : LinearWord W X T) :
    Word.append (W := W) (Word.forward W f)
        (Word.append (W := W) (Word.backward W f hf)
          (LinearWord.toWord W rest)) ≅
      LinearWord.toWord W rest :=
  (Presented.wordAssociatorIso W (Word.forward W f)
      (Word.backward W f hf) (LinearWord.toWord W rest)).symm ≪≫
    whiskerRightIso (B := Presented.Localization W)
      (Presented.markedUnitIso W f hf).symm
      (LinearWord.toWord W rest) ≪≫
    Presented.wordLeftUnitorIso W (LinearWord.toWord W rest)

/-- Marked-unit-pair deletion is exactly the forward map of its semantic
isomorphism. -/
theorem toHom_deleteMarkedUnitPair_eq_hom {X Y T : B}
    (f : X ⟶ Y) (hf : W f) (rest : LinearWord W X T) :
    toHom W (.deleteMarkedUnitPair f hf rest) =
      (markedUnitPairIso W f hf rest).hom := by
  rfl

/-- Marked-unit-pair insertion is exactly the inverse map of its semantic
isomorphism. -/
theorem toHom_insertMarkedUnitPair_eq_inv {X Y T : B}
    (f : X ⟶ Y) (hf : W f) (rest : LinearWord W X T) :
    toHom W (.insertMarkedUnitPair f hf rest) =
      (markedUnitPairIso W f hf rest).inv := by
  change
    (Presented.wordLeftUnitorIso W (LinearWord.toWord W rest)).inv ≫
        ((whiskerRightIso (B := Presented.Localization W)
          (Presented.markedUnitIso W f hf)
          (LinearWord.toWord W rest)).hom ≫
        (Presented.wordAssociatorIso W (Word.forward W f)
          (Word.backward W f hf) (LinearWord.toWord W rest)).hom) =
      ((Presented.wordLeftUnitorIso W (LinearWord.toWord W rest)).inv ≫
        (whiskerRightIso (B := Presented.Localization W)
          (Presented.markedUnitIso W f hf)
          (LinearWord.toWord W rest)).hom) ≫
        (Presented.wordAssociatorIso W (Word.forward W f)
          (Word.backward W f hf) (LinearWord.toWord W rest)).hom
  exact (Category.assoc _ _ _).symm

/-- Deleting and reinserting a marked unit pair is semantically the identity
on the wider row. -/
theorem deleteMarkedUnitPair_insertMarkedUnitPair {X Y T : B}
    (f : X ⟶ Y) (hf : W f) (rest : LinearWord W X T) :
    AlignedCell.quotientVcomp W
        (toHom W (.deleteMarkedUnitPair f hf rest))
        (toHom W (.insertMarkedUnitPair f hf rest)) =
      𝟙 (LinearWord.toWord W
        (.cons (Step.forward (W := W) f)
          (.cons (Step.backward (W := W) f hf) rest))) := by
  rw [toHom_deleteMarkedUnitPair_eq_hom,
    toHom_insertMarkedUnitPair_eq_inv]
  exact (markedUnitPairIso W f hf rest).hom_inv_id

/-- Inserting and deleting a marked unit pair is semantically the identity on
the narrower row. -/
theorem insertMarkedUnitPair_deleteMarkedUnitPair {X Y T : B}
    (f : X ⟶ Y) (hf : W f) (rest : LinearWord W X T) :
    AlignedCell.quotientVcomp W
        (toHom W (.insertMarkedUnitPair f hf rest))
        (toHom W (.deleteMarkedUnitPair f hf rest)) =
      𝟙 (LinearWord.toWord W rest) := by
  rw [toHom_insertMarkedUnitPair_eq_inv,
    toHom_deleteMarkedUnitPair_eq_hom]
  exact (markedUnitPairIso W f hf rest).inv_hom_id

/-- The semantic isomorphism implemented by deletion/insertion of a marked
counit pair `f⁻¹ ; f`. -/
noncomputable def markedCounitPairIso {X Y T : B}
    (f : X ⟶ Y) (hf : W f) (rest : LinearWord W Y T) :
    Word.append (W := W) (Word.backward W f hf)
        (Word.append (W := W) (Word.forward W f)
          (LinearWord.toWord W rest)) ≅
      LinearWord.toWord W rest :=
  (Presented.wordAssociatorIso W (Word.backward W f hf)
      (Word.forward W f) (LinearWord.toWord W rest)).symm ≪≫
    whiskerRightIso (B := Presented.Localization W)
      (Presented.markedCounitIso W f hf)
      (LinearWord.toWord W rest) ≪≫
    Presented.wordLeftUnitorIso W (LinearWord.toWord W rest)

/-- Marked-counit-pair deletion is exactly the forward map of its semantic
isomorphism. -/
theorem toHom_deleteMarkedCounitPair_eq_hom {X Y T : B}
    (f : X ⟶ Y) (hf : W f) (rest : LinearWord W Y T) :
    toHom W (.deleteMarkedCounitPair f hf rest) =
      (markedCounitPairIso W f hf rest).hom := by
  rfl

/-- Marked-counit-pair insertion is exactly the inverse map of its semantic
isomorphism. -/
theorem toHom_insertMarkedCounitPair_eq_inv {X Y T : B}
    (f : X ⟶ Y) (hf : W f) (rest : LinearWord W Y T) :
    toHom W (.insertMarkedCounitPair f hf rest) =
      (markedCounitPairIso W f hf rest).inv := by
  change
    (Presented.wordLeftUnitorIso W (LinearWord.toWord W rest)).inv ≫
        ((whiskerRightIso (B := Presented.Localization W)
          (Presented.markedCounitIso W f hf).symm
          (LinearWord.toWord W rest)).hom ≫
        (Presented.wordAssociatorIso W (Word.backward W f hf)
          (Word.forward W f) (LinearWord.toWord W rest)).hom) =
      ((Presented.wordLeftUnitorIso W (LinearWord.toWord W rest)).inv ≫
        (whiskerRightIso (B := Presented.Localization W)
          (Presented.markedCounitIso W f hf).symm
          (LinearWord.toWord W rest)).hom) ≫
        (Presented.wordAssociatorIso W (Word.backward W f hf)
          (Word.forward W f) (LinearWord.toWord W rest)).hom
  exact (Category.assoc _ _ _).symm

/-- Deleting and reinserting a marked counit pair is semantically the identity
on the wider row. -/
theorem deleteMarkedCounitPair_insertMarkedCounitPair {X Y T : B}
    (f : X ⟶ Y) (hf : W f) (rest : LinearWord W Y T) :
    AlignedCell.quotientVcomp W
        (toHom W (.deleteMarkedCounitPair f hf rest))
        (toHom W (.insertMarkedCounitPair f hf rest)) =
      𝟙 (LinearWord.toWord W
        (.cons (Step.backward (W := W) f hf)
          (.cons (Step.forward (W := W) f) rest))) := by
  rw [toHom_deleteMarkedCounitPair_eq_hom,
    toHom_insertMarkedCounitPair_eq_inv]
  exact (markedCounitPairIso W f hf rest).hom_inv_id

/-- Inserting and deleting a marked counit pair is semantically the identity
on the narrower row. -/
theorem insertMarkedCounitPair_deleteMarkedCounitPair {X Y T : B}
    (f : X ⟶ Y) (hf : W f) (rest : LinearWord W Y T) :
    AlignedCell.quotientVcomp W
        (toHom W (.insertMarkedCounitPair f hf rest))
        (toHom W (.deleteMarkedCounitPair f hf rest)) =
      𝟙 (LinearWord.toWord W rest) := by
  rw [toHom_insertMarkedCounitPair_eq_inv,
    toHom_deleteMarkedCounitPair_eq_hom]
  exact (markedCounitPairIso W f hf rest).inv_hom_id

/-- Every executable column refinement denotes a semantic isomorphism in the
presented linear mapping category. -/
noncomputable def toIso {X Y : B}
    {source target : LinearWord W X Y} :
    ColumnRefinement W source target →
      @Iso (Word W X Y) (Presented.wordCategory W X Y)
        (LinearWord.toWord W source) (LinearWord.toWord W target)
  | .identity word => Iso.refl (LinearWord.toWord W word)
  | .vcomp alpha beta => toIso alpha ≪≫ toIso beta
  | .deleteIdentity rest => identityColumnIso W rest
  | .insertIdentity rest => (identityColumnIso W rest).symm
  | .expandForward f g rest => compositeColumnIso W f g rest
  | .contractForward f g rest => (compositeColumnIso W f g rest).symm
  | .deleteMarkedUnitPair f hf rest => markedUnitPairIso W f hf rest
  | .insertMarkedUnitPair f hf rest => (markedUnitPairIso W f hf rest).symm
  | .deleteMarkedCounitPair f hf rest => markedCounitPairIso W f hf rest
  | .insertMarkedCounitPair f hf rest =>
      (markedCounitPairIso W f hf rest).symm
  | .under step refinement =>
      whiskerLeftIso (B := Presented.Localization W) (Word.atom step)
        (toIso refinement)

/-- The quotient-cell interpretation of every refinement is exactly the
forward map of its unified semantic isomorphism. -/
theorem toHom_eq_toIso_hom {X Y : B}
    {source target : LinearWord W X Y}
    (refinement : ColumnRefinement W source target) :
    toHom W refinement = (toIso W refinement).hom := by
  induction refinement with
  | identity => rfl
  | vcomp alpha beta ihAlpha ihBeta =>
      rw [toHom_vcomp, ihAlpha, ihBeta]
      rfl
  | deleteIdentity rest => exact toHom_deleteIdentity_eq_hom W rest
  | insertIdentity rest => exact toHom_insertIdentity_eq_inv W rest
  | expandForward f g rest => exact toHom_expandForward_eq_hom W f g rest
  | contractForward f g rest => exact toHom_contractForward_eq_inv W f g rest
  | deleteMarkedUnitPair f hf rest =>
      exact toHom_deleteMarkedUnitPair_eq_hom W f hf rest
  | insertMarkedUnitPair f hf rest =>
      exact toHom_insertMarkedUnitPair_eq_inv W f hf rest
  | deleteMarkedCounitPair f hf rest =>
      exact toHom_deleteMarkedCounitPair_eq_hom W f hf rest
  | insertMarkedCounitPair f hf rest =>
      exact toHom_insertMarkedCounitPair_eq_inv W f hf rest
  | under step refinement ih =>
      rw [toHom_under, ih]
      rfl

/-- The unified semantic isomorphism of an executable reverse refinement is
the inverse of the original semantic isomorphism. -/
theorem toIso_reverse {X Y : B}
    {source target : LinearWord W X Y}
    (refinement : ColumnRefinement W source target) :
    toIso W (reverse W refinement) = (toIso W refinement).symm := by
  induction refinement <;> simp [reverse, toIso, *]
  all_goals (apply Iso.ext; rfl)

/-- Any semantic inverse pair remains inverse after refinement beneath one
common prefix column.  Iterating `under` therefore transports the generator
round trips to an arbitrary executable prefix. -/
theorem under_inverse {X Y Z : B} (step : Step W X Y)
    {first middle : LinearWord W Y Z}
    (alpha : ColumnRefinement W first middle)
    (beta : ColumnRefinement W middle first)
    (inverse : AlignedCell.quotientVcomp W
        (toHom W alpha) (toHom W beta) =
      𝟙 (LinearWord.toWord W first)) :
    AlignedCell.quotientVcomp W
        (toHom W (.under step alpha))
        (toHom W (.under step beta)) =
      𝟙 (LinearWord.toWord W (.cons step first)) := by
  rw [toHom_under, toHom_under]
  change AlignedCell.quotientVcomp W
      (Presented.whiskerLeftHom W (Word.atom step) (toHom W alpha))
      (Presented.whiskerLeftHom W (Word.atom step) (toHom W beta)) =
    𝟙 (Word.append (W := W) (Word.atom step)
      (LinearWord.toWord W first))
  rw [← AlignedCell.whiskerLeftHom_vcomp W (Word.atom step)
    (toHom W alpha) (toHom W beta)]
  rw [inverse]
  exact Quot.sound (Presented.Rel.whisker_left_id
    (Word.atom step) (LinearWord.toWord W first))

end ColumnRefinement

/-! ## Common-refinement spans and quotient -/

/-- A common-refinement span between two parallel linear hammock rows.  Both
legs are executable refinements into one explicit apex row. -/
structure CommonRefinement {X Y : B}
    (first second : LinearWord W X Y) where
  /-- The common apex row. -/
  apex : LinearWord W X Y
  /-- Refinement of the first row to the apex. -/
  firstLeg : ColumnRefinement W first apex
  /-- Refinement of the second row to the apex. -/
  secondLeg : ColumnRefinement W second apex

namespace CommonRefinement

/-- Reflexive common refinement. -/
def refl {X Y : B} (word : LinearWord W X Y) :
    CommonRefinement W word word where
  apex := word
  firstLeg := .identity word
  secondLeg := .identity word

/-- Symmetry swaps the two legs without changing the apex. -/
def symm {X Y : B} {first second : LinearWord W X Y}
    (span : CommonRefinement W first second) :
    CommonRefinement W second first where
  apex := span.apex
  firstLeg := span.secondLeg
  secondLeg := span.firstLeg

/-- Transitivity uses executable reversal of the middle leg to transport the
first span into the apex of the second span. -/
def trans {X Y : B} {first middle last : LinearWord W X Y}
    (left : CommonRefinement W first middle)
    (right : CommonRefinement W middle last) :
    CommonRefinement W first last where
  apex := right.apex
  firstLeg := .vcomp left.firstLeg
    (.vcomp (ColumnRefinement.reverse W left.secondLeg) right.firstLeg)
  secondLeg := right.secondLeg

/-- A common-refinement span induces an isomorphism between the two row
interpretations through its apex. -/
noncomputable def semanticIso {X Y : B}
    {first second : LinearWord W X Y}
    (span : CommonRefinement W first second) :
    @Iso (Word W X Y) (Presented.wordCategory W X Y)
      (LinearWord.toWord W first) (LinearWord.toWord W second) :=
  ColumnRefinement.toIso W span.firstLeg ≪≫
    (ColumnRefinement.toIso W span.secondLeg).symm

/-- Common-refinability of two rows. -/
def Related {X Y : B} (first second : LinearWord W X Y) : Prop :=
  Nonempty (CommonRefinement W first second)

/-- Common-refinability is reflexive. -/
theorem related_refl {X Y : B} (word : LinearWord W X Y) :
    Related W word word :=
  ⟨refl W word⟩

/-- Common-refinability is symmetric. -/
theorem related_symm {X Y : B} {first second : LinearWord W X Y} :
    Related W first second → Related W second first := by
  rintro ⟨span⟩
  exact ⟨symm W span⟩

/-- Common-refinability is transitive. -/
theorem related_trans {X Y : B}
    {first middle last : LinearWord W X Y} :
    Related W first middle → Related W middle last → Related W first last := by
  rintro ⟨left⟩ ⟨right⟩
  exact ⟨trans W left right⟩

/-- The common-refinement equivalence relation on parallel rows. -/
def setoid (X Y : B) : Setoid (LinearWord W X Y) where
  r := Related W
  iseqv := ⟨related_refl W, related_symm W, related_trans W⟩

/-- Typeclass form of the common-refinement relation. -/
instance rowSetoid (X Y : B) : Setoid (LinearWord W X Y) :=
  setoid W X Y

/-- Object quotient of linear hammock rows by executable common refinement. -/
abbrev RowQuotient (X Y : B) := Quotient (setoid W X Y)

/-- Canonical row in the common-refinement quotient. -/
def quotientMk {X Y : B} (word : LinearWord W X Y) : RowQuotient W X Y :=
  Quotient.mk' word

/-- Every executable refinement identifies its endpoints in the row
quotient. -/
theorem quotientMk_eq_of_refinement {X Y : B}
    {first second : LinearWord W X Y}
    (refinement : ColumnRefinement W first second) :
    quotientMk W first = quotientMk W second :=
  Quotient.sound ⟨{
    apex := second
    firstLeg := refinement
    secondLeg := .identity second }⟩

/-- Equality of represented quotient rows is exactly common-refinability. -/
theorem quotientMk_eq_iff_related {X Y : B}
    (first second : LinearWord W X Y) :
    quotientMk W first = quotientMk W second ↔ Related W first second :=
  by
    constructor
    · intro equality
      exact Quotient.exact equality
    · intro related
      apply Quotient.sound
      exact related

/-- Every common-refinement witness yields a semantic isomorphism between the
two rows; no object equality or univalence principle is assumed. -/
theorem related_semanticIso {X Y : B}
    {first second : LinearWord W X Y} :
    Related W first second →
      Nonempty (@Iso (Word W X Y) (Presented.wordCategory W X Y)
        (LinearWord.toWord W first) (LinearWord.toWord W second)) := by
  rintro ⟨span⟩
  exact ⟨semanticIso W span⟩

/-- Equality in the common-refinement quotient is sound for semantic
isomorphism in the presented mapping category. -/
theorem quotientMk_eq_semanticIso {X Y : B}
    {first second : LinearWord W X Y}
    (equality : quotientMk W first = quotientMk W second) :
    Nonempty (@Iso (Word W X Y) (Presented.wordCategory W X Y)
      (LinearWord.toWord W first) (LinearWord.toWord W second)) :=
  related_semanticIso W ((quotientMk_eq_iff_related W first second).mp equality)

/-! ### Zero-truncated quotient mapping category -/

/-- Wrapper for rows regarded only through common-refinement morphisms.  A
wrapper is necessary because raw `LinearWord`s already carry the richer
quotient-2-cell mapping category. -/
structure RowObject (X Y : B) where
  /-- Underlying linear hammock row. -/
  row : LinearWord W X Y

/-- The thin common-refinement category: there is at most one morphism between
two rows, inhabited exactly when they have a common refinement. -/
instance rowObjectCategory (X Y : B) : Category (RowObject W X Y) where
  Hom first second := ULift (PLift (Related W first.row second.row))
  id first := ⟨⟨related_refl W first.row⟩⟩
  comp first second :=
    ⟨⟨related_trans W first.down.down second.down.down⟩⟩
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

instance rowObjectHomSubsingleton (X Y : B)
    (first second : RowObject W X Y) : Subsingleton (first ⟶ second) where
  allEq left right := by
    rcases left with ⟨⟨left⟩⟩
    rcases right with ⟨⟨right⟩⟩
    rfl

/-- Projection from the thin common-refinement category to the discrete row
quotient. -/
def quotientFunctor (X Y : B) :
    RowObject W X Y ⥤ Discrete (RowQuotient W X Y) where
  obj row := Discrete.mk (quotientMk W row.row)
  map refinement := Discrete.eqToHom (Quotient.sound refinement.down.down)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

instance quotientFunctor_faithful (X Y : B) :
    (quotientFunctor W X Y).Faithful where
  map_injective {X Y} first second _ := by
    rcases first with ⟨⟨first⟩⟩
    rcases second with ⟨⟨second⟩⟩
    rfl

instance quotientFunctor_full (X Y : B) :
    (quotientFunctor W X Y).Full where
  map_surjective {first second} morphism := by
    have equality : quotientMk W first.row = quotientMk W second.row :=
      Discrete.eq_of_hom morphism
    refine ⟨⟨⟨(quotientMk_eq_iff_related W first.row second.row).mp equality⟩⟩, ?_⟩
    exact Subsingleton.elim _ _

instance quotientFunctor_essSurj (X Y : B) :
    (quotientFunctor W X Y).EssSurj where
  mem_essImage target := by
    rcases target with ⟨target⟩
    induction target using Quotient.inductionOn with
    | _ row =>
        exact ⟨⟨row⟩, ⟨Iso.refl _⟩⟩

instance quotientFunctor_isEquivalence (X Y : B) :
    (quotientFunctor W X Y).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := inferInstance

/-- The zero-truncated common-refinement mapping category is equivalent to the
discrete category of row-quotient classes. -/
noncomputable def quotientEquivalence (X Y : B) :
    RowObject W X Y ≌ Discrete (RowQuotient W X Y) :=
  (quotientFunctor W X Y).asEquivalence

/-- The thin common-refinement category is a groupoid. -/
instance rowObjectIsGroupoid (X Y : B) : IsGroupoid (RowObject W X Y) :=
  isGroupoid_of_reflects_iso (quotientFunctor W X Y)

end CommonRefinement

/-! ## Non-thin refinement-path category -/

/-- Wrapper for a linear row regarded as an object of the non-thin
refinement-path category. -/
structure RefinementPathObject (X Y : B) where
  /-- Underlying row. -/
  row : LinearWord W X Y

namespace RefinementPath

/-- Two executable refinement paths are equivalent exactly when their
quotient-cell interpretations agree. -/
def Rel {X Y : B} {first second : LinearWord W X Y}
    (alpha beta : ColumnRefinement W first second) : Prop :=
  ColumnRefinement.toHom W alpha = ColumnRefinement.toHom W beta

/-- Semantic path equality is an equivalence relation. -/
def setoid {X Y : B} (first second : LinearWord W X Y) :
    Setoid (ColumnRefinement W first second) where
  r := Rel W
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Morphisms are executable refinement paths modulo equality of their
quotient-cell semantics. -/
abbrev Hom {X Y : B} (first second : LinearWord W X Y) :=
  Quotient (setoid W first second)

/-- Vertical composition respects semantic path equality. -/
theorem rel_vcomp {X Y : B}
    {first middle last : LinearWord W X Y}
    {alpha alpha' : ColumnRefinement W first middle}
    {beta beta' : ColumnRefinement W middle last}
    (hAlpha : Rel W alpha alpha') (hBeta : Rel W beta beta') :
    Rel W (.vcomp alpha beta) (.vcomp alpha' beta') := by
  dsimp [Rel] at hAlpha hBeta ⊢
  rw [hAlpha, hBeta]

/-- Non-thin category of semantic refinement paths. -/
instance category (X Y : B) : Category (RefinementPathObject W X Y) where
  Hom first second := Hom W first.row second.row
  id first := Quotient.mk (setoid W first.row first.row) (.identity first.row)
  comp := Quotient.map₂ ColumnRefinement.vcomp
    (fun alpha alpha' hAlpha beta beta' hBeta => by
      change Rel W alpha alpha' at hAlpha
      change Rel W beta beta' at hBeta
      exact rel_vcomp W hAlpha hBeta)
  id_comp := by
    rintro first second ⟨refinement⟩
    apply Quotient.sound
    change Rel W (.vcomp (.identity first.row) refinement) refinement
    unfold Rel
    rw [ColumnRefinement.toHom_vcomp,
      ColumnRefinement.toHom_identity]
    exact Category.id_comp _
  comp_id := by
    rintro first second ⟨refinement⟩
    apply Quotient.sound
    change Rel W (.vcomp refinement (.identity second.row)) refinement
    unfold Rel
    rw [ColumnRefinement.toHom_vcomp,
      ColumnRefinement.toHom_identity]
    exact Category.comp_id _
  assoc := by
    rintro first second third fourth ⟨alpha⟩ ⟨beta⟩ ⟨gamma⟩
    apply Quotient.sound
    change Rel W (.vcomp (.vcomp alpha beta) gamma)
      (.vcomp alpha (.vcomp beta gamma))
    unfold Rel
    rw [ColumnRefinement.toHom_vcomp, ColumnRefinement.toHom_vcomp,
      ColumnRefinement.toHom_vcomp, ColumnRefinement.toHom_vcomp]
    exact Category.assoc _ _ _

/-- Semantic path equality is preserved by executable reversal. -/
theorem rel_reverse {X Y : B}
    {first second : LinearWord W X Y}
    {alpha beta : ColumnRefinement W first second}
    (equality : Rel W alpha beta) :
    Rel W (ColumnRefinement.reverse W alpha)
      (ColumnRefinement.reverse W beta) := by
  unfold Rel at equality ⊢
  rw [ColumnRefinement.toHom_eq_toIso_hom,
    ColumnRefinement.toIso_reverse,
    ColumnRefinement.toHom_eq_toIso_hom,
    ColumnRefinement.toIso_reverse]
  have isoEquality : ColumnRefinement.toIso W alpha =
      ColumnRefinement.toIso W beta := by
    apply Iso.ext
    rw [← ColumnRefinement.toHom_eq_toIso_hom,
      ← ColumnRefinement.toHom_eq_toIso_hom]
    exact equality
  rw [isoEquality]

/-- Reverse a semantic refinement-path morphism. -/
def reverseHom {X Y : B}
    {first second : RefinementPathObject W X Y} :
    (first ⟶ second) → (second ⟶ first) :=
  Quotient.map (ColumnRefinement.reverse W)
    (fun alpha beta equality => by
      change Rel W alpha beta at equality
      exact rel_reverse W equality)

/-- A refinement path followed by its reverse is the identity. -/
theorem comp_reverseHom {X Y : B}
    {first second : RefinementPathObject W X Y}
    (path : first ⟶ second) : path ≫ reverseHom W path = 𝟙 first := by
  rcases path with ⟨refinement⟩
  apply Quotient.sound
  change Rel W (.vcomp refinement (ColumnRefinement.reverse W refinement))
    (.identity first.row)
  unfold Rel
  rw [ColumnRefinement.toHom_vcomp, ColumnRefinement.toHom_identity,
    ColumnRefinement.toHom_eq_toIso_hom,
    ColumnRefinement.toHom_eq_toIso_hom,
    ColumnRefinement.toIso_reverse]
  exact (ColumnRefinement.toIso W refinement).hom_inv_id

/-- A reversed refinement path followed by the original is the identity. -/
theorem reverseHom_comp {X Y : B}
    {first second : RefinementPathObject W X Y}
    (path : first ⟶ second) : reverseHom W path ≫ path = 𝟙 second := by
  rcases path with ⟨refinement⟩
  apply Quotient.sound
  change Rel W (.vcomp (ColumnRefinement.reverse W refinement) refinement)
    (.identity second.row)
  unfold Rel
  rw [ColumnRefinement.toHom_vcomp, ColumnRefinement.toHom_identity,
    ColumnRefinement.toHom_eq_toIso_hom,
    ColumnRefinement.toIso_reverse,
    ColumnRefinement.toHom_eq_toIso_hom]
  exact (ColumnRefinement.toIso W refinement).inv_hom_id

/-- The non-thin semantic refinement-path category is a groupoid. -/
instance isGroupoid (X Y : B) : IsGroupoid (RefinementPathObject W X Y) where
  all_isIso path := ⟨⟨reverseHom W path,
    comp_reverseHom W path, reverseHom_comp W path⟩⟩

/-- Faithful semantic functor from refinement paths into the existing linear
mapping category. -/
def semanticFunctor (X Y : B) :
    RefinementPathObject W X Y ⥤ LinearWord W X Y where
  obj row := row.row
  map := Quotient.lift (ColumnRefinement.toHom W)
    (fun alpha beta equality => by
      change Rel W alpha beta at equality
      exact equality)
  map_id row := ColumnRefinement.toHom_identity W row.row
  map_comp alpha beta := by
    rcases alpha with ⟨alpha⟩
    rcases beta with ⟨beta⟩
    exact ColumnRefinement.toHom_vcomp W alpha beta

instance semanticFunctor_faithful (X Y : B) :
    (semanticFunctor W X Y).Faithful where
  map_injective {first second} alpha beta equality := by
    rcases alpha with ⟨alpha⟩
    rcases beta with ⟨beta⟩
    apply Quotient.sound
    change Rel W alpha beta
    exact equality

instance semanticFunctor_essSurj (X Y : B) :
    (semanticFunctor W X Y).EssSurj where
  mem_essImage row := ⟨⟨row⟩, ⟨Iso.refl _⟩⟩

/-- Every semantic image of a refinement path is invertible. -/
theorem semanticFunctor_map_isIso {X Y : B}
    {first second : RefinementPathObject W X Y}
    (path : first ⟶ second) :
    IsIso ((semanticFunctor W X Y).map path) := by
  infer_instance

/-- Send one semantic refinement path to the unique thin common-refinement
morphism between the same rows. -/
def toThinHom {X Y : B}
    {first second : RefinementPathObject W X Y} :
    (first ⟶ second) →
      ((⟨first.row⟩ : CommonRefinement.RowObject W X Y) ⟶
        (⟨second.row⟩ : CommonRefinement.RowObject W X Y)) :=
  Quotient.lift
    (fun refinement => ⟨⟨⟨{
      apex := second.row
      firstLeg := refinement
      secondLeg := .identity second.row }⟩⟩⟩)
    (fun _ _ _ => Subsingleton.elim _ _)

/-- Zero-truncation functor from semantic refinement paths to the thin
common-refinement groupoid. -/
def toThinFunctor (X Y : B) :
    RefinementPathObject W X Y ⥤ CommonRefinement.RowObject W X Y where
  obj row := ⟨row.row⟩
  map := toThinHom W
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

instance toThinFunctor_full (X Y : B) :
    (toThinFunctor W X Y).Full where
  map_surjective {first second} morphism := by
    rcases morphism.down.down with ⟨span⟩
    let refinement : ColumnRefinement W first.row second.row :=
      .vcomp span.firstLeg (ColumnRefinement.reverse W span.secondLeg)
    refine ⟨Quotient.mk (setoid W first.row second.row) refinement, ?_⟩
    exact Subsingleton.elim _ _

instance toThinFunctor_essSurj (X Y : B) :
    (toThinFunctor W X Y).EssSurj where
  mem_essImage row := ⟨⟨row.row⟩, ⟨Iso.refl _⟩⟩

end RefinementPath

/-! ## Exact refinement-generated semantic image -/

/-- Wrapper for rows in the refinement-generated semantic image subgroupoid
of the linear mapping category. -/
structure RefinementImageObject (X Y : B) where
  /-- Underlying linear row. -/
  row : LinearWord W X Y

namespace RefinementImage

/-- A quotient 2-cell together with the proposition that it is generated by
an executable column refinement. -/
abbrev Hom {X Y : B} (first second : LinearWord W X Y) :=
  { hom : Presented.Hom W (LinearWord.toWord W first)
      (LinearWord.toWord W second) //
    ∃ refinement : ColumnRefinement W first second,
      ColumnRefinement.toHom W refinement = hom }

/-- Forget the generating-refinement witness while retaining the represented
quotient 2-cell. -/
def underlying {X Y : B} {first second : LinearWord W X Y} :
    Hom W first second →
      Presented.Hom W (LinearWord.toWord W first)
        (LinearWord.toWord W second) :=
  Subtype.val

/-- Refinement-generated semantic morphisms form a category. -/
instance category (X Y : B) : Category (RefinementImageObject W X Y) where
  Hom first second := Hom W first.row second.row
  id first := ⟨𝟙 (LinearWord.toWord W first.row),
    ⟨.identity first.row, ColumnRefinement.toHom_identity W first.row⟩⟩
  comp alpha beta :=
    ⟨AlignedCell.quotientVcomp W alpha.1 beta.1, by
      rcases alpha.2 with ⟨alphaRefinement, hAlpha⟩
      rcases beta.2 with ⟨betaRefinement, hBeta⟩
      refine ⟨.vcomp alphaRefinement betaRefinement, ?_⟩
      rw [ColumnRefinement.toHom_vcomp, hAlpha, hBeta]⟩
  id_comp morphism := by
    apply Subtype.ext
    exact @Category.id_comp (Word W X Y) (Presented.wordCategory W X Y)
      _ _ morphism.1
  comp_id morphism := by
    apply Subtype.ext
    exact @Category.comp_id (Word W X Y) (Presented.wordCategory W X Y)
      _ _ morphism.1
  assoc alpha beta gamma := by
    apply Subtype.ext
    change AlignedCell.quotientVcomp W
        (AlignedCell.quotientVcomp W alpha.1 beta.1) gamma.1 =
      AlignedCell.quotientVcomp W alpha.1
        (AlignedCell.quotientVcomp W beta.1 gamma.1)
    exact @Category.assoc (Word W X Y) (Presented.wordCategory W X Y)
      _ _ _ _ alpha.1 beta.1 gamma.1

/-- The refinement-generated semantic image is a groupoid. -/
instance isGroupoid (X Y : B) : IsGroupoid (RefinementImageObject W X Y) where
  all_isIso {first second} morphism := by
    change Hom W first.row second.row at morphism
    rcases morphism.2 with ⟨refinement, hRefinement⟩
    let inverse : Hom W second.row first.row :=
      ⟨ColumnRefinement.toHom W (ColumnRefinement.reverse W refinement),
        ⟨ColumnRefinement.reverse W refinement, rfl⟩⟩
    refine ⟨⟨inverse, ?_, ?_⟩⟩
    · apply Subtype.ext
      change AlignedCell.quotientVcomp W morphism.1 inverse.1 =
        𝟙 (LinearWord.toWord W _)
      rw [← hRefinement]
      change AlignedCell.quotientVcomp W
          (ColumnRefinement.toHom W refinement)
          (ColumnRefinement.toHom W
            (ColumnRefinement.reverse W refinement)) =
        𝟙 (LinearWord.toWord W first.row)
      rw [ColumnRefinement.toHom_eq_toIso_hom,
        ColumnRefinement.toHom_eq_toIso_hom,
        ColumnRefinement.toIso_reverse]
      exact (ColumnRefinement.toIso W refinement).hom_inv_id
    · apply Subtype.ext
      change AlignedCell.quotientVcomp W inverse.1 morphism.1 =
        𝟙 (LinearWord.toWord W _)
      rw [← hRefinement]
      change AlignedCell.quotientVcomp W
          (ColumnRefinement.toHom W
            (ColumnRefinement.reverse W refinement))
          (ColumnRefinement.toHom W refinement) =
        𝟙 (LinearWord.toWord W second.row)
      rw [ColumnRefinement.toHom_eq_toIso_hom,
        ColumnRefinement.toIso_reverse,
        ColumnRefinement.toHom_eq_toIso_hom]
      exact (ColumnRefinement.toIso W refinement).inv_hom_id

/-- Faithful inclusion of the exact refinement-generated image into the full
linear mapping category. -/
def inclusion (X Y : B) :
    RefinementImageObject W X Y ⥤ LinearWord W X Y where
  obj row := row.row
  map := underlying W
  map_id _ := rfl
  map_comp _ _ := rfl

instance inclusion_faithful (X Y : B) : (inclusion W X Y).Faithful where
  map_injective {first second} alpha beta equality := by
    change Hom W first.row second.row at alpha beta
    exact Subtype.ext equality

/-- Convert a semantic refinement path to the corresponding morphism in its
exact generated image. -/
def ofPath {X Y : B}
    {first second : RefinementPathObject W X Y} :
    (first ⟶ second) → Hom W first.row second.row :=
  Quotient.lift
    (fun refinement =>
      ⟨ColumnRefinement.toHom W refinement, ⟨refinement, rfl⟩⟩)
    (fun _ _ equality => Subtype.ext equality)

/-- The semantic refinement-path groupoid maps onto its exact generated image. -/
def pathFunctor (X Y : B) :
    RefinementPathObject W X Y ⥤ RefinementImageObject W X Y where
  obj row := ⟨row.row⟩
  map := ofPath W
  map_id _ := by
    apply Subtype.ext
    exact ColumnRefinement.toHom_identity W _
  map_comp alpha beta := by
    apply Subtype.ext
    rcases alpha with ⟨alpha⟩
    rcases beta with ⟨beta⟩
    exact ColumnRefinement.toHom_vcomp W alpha beta

instance pathFunctor_faithful (X Y : B) : (pathFunctor W X Y).Faithful where
  map_injective {first second} alpha beta equality := by
    rcases alpha with ⟨alpha⟩
    rcases beta with ⟨beta⟩
    apply Quotient.sound
    change RefinementPath.Rel W alpha beta
    change (⟨ColumnRefinement.toHom W alpha, ⟨alpha, rfl⟩⟩ :
        Hom W first.row second.row) =
      (⟨ColumnRefinement.toHom W beta, ⟨beta, rfl⟩⟩ :
        Hom W first.row second.row) at equality
    exact congrArg Subtype.val equality

instance pathFunctor_full (X Y : B) : (pathFunctor W X Y).Full where
  map_surjective {first second} morphism := by
    change Hom W first.row second.row at morphism
    rcases morphism.2 with ⟨refinement, hRefinement⟩
    refine ⟨Quotient.mk (RefinementPath.setoid W first.row second.row)
      refinement, ?_⟩
    apply Subtype.ext
    exact hRefinement

instance pathFunctor_essSurj (X Y : B) : (pathFunctor W X Y).EssSurj where
  mem_essImage row := by
    refine ⟨⟨row.row⟩, ?_⟩
    exact ⟨Iso.refl row⟩

instance pathFunctor_isEquivalence (X Y : B) :
    (pathFunctor W X Y).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := inferInstance

/-- Equivalence between semantic refinement paths and their exact generated
image subgroupoid. -/
noncomputable def pathEquivalence (X Y : B) :
    RefinementPathObject W X Y ≌ RefinementImageObject W X Y :=
  (pathFunctor W X Y).asEquivalence

/-- The original semantic functor factors strictly through its exact generated
image. -/
theorem semanticFunctor_factorization (X Y : B) :
    RefinementPath.semanticFunctor W X Y =
      pathFunctor W X Y ⋙ inclusion W X Y := by
  apply Functor.hext
  · intro row
    rfl
  · intro first second path
    rcases path with ⟨refinement⟩
    rfl

end RefinementImage

end CategoryTheory.Bicategory.MarkedZigzag
