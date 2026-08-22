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
embeds faithfully into the linear mapping category. Its exact generated image
is internalized as a subgroupoid. A larger non-groupoidal hammock-path syntax
now alternates arbitrary aligned cells with invertible refinements, retains
all source 2-cells in one-column form, and is closed under normalized left/right
whiskering and horizontal append. Normalization is natural for raw whiskering;
identity, original, source-identity/inverse, composition-closure, whiskering,
source-composition/inverse, and equality-transport induction branches are
complete; marked unit/counit pairs and inverses plus left unitor and inverse
are complete too. Four explicit associator/right-unitor obligations remain.
Coverage of every presented quotient
2-cell, critical-pair coherence, and reduced-hammock invariance are still
absent, so this is not by itself the classical Dwyer--Kan hammock localization.
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

/-- Explicit associativity of quotient vertical composition. -/
theorem quotientVcomp_assoc {X Y : B}
    {first second third fourth : Word W X Y}
    (alpha : Presented.Hom W first second)
    (beta : Presented.Hom W second third)
    (gamma : Presented.Hom W third fourth) :
    quotientVcomp W (quotientVcomp W alpha beta) gamma =
      quotientVcomp W alpha (quotientVcomp W beta gamma) :=
  @Category.assoc (Word W X Y) (Presented.wordCategory W X Y)
    _ _ _ _ alpha beta gamma

/-- Explicit left identity law for quotient vertical composition. -/
theorem quotientVcomp_id_comp {X Y : B} {first second : Word W X Y}
    (alpha : Presented.Hom W first second) :
    quotientVcomp W (𝟙 first) alpha = alpha :=
  @Category.id_comp (Word W X Y) (Presented.wordCategory W X Y)
    first second alpha

/-- Explicit right identity law for quotient vertical composition. -/
theorem quotientVcomp_comp_id {X Y : B} {first second : Word W X Y}
    (alpha : Presented.Hom W first second) :
    quotientVcomp W alpha (𝟙 second) = alpha :=
  @Category.comp_id (Word W X Y) (Presented.wordCategory W X Y)
    first second alpha

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

/-! ## Aligned-cell-augmented hammock paths -/

/-- Wrapper for linear rows in the aligned-cell-augmented hammock-path
category. -/
structure HammockPathObject (X Y : B) where
  /-- Underlying linear row. -/
  row : LinearWord W X Y

namespace HammockPath

/-- Naturality of binary append isomorphisms around a left-whiskered
quotient 2-cell. -/
theorem appendIso_inv_whiskerLeft_appendIso_hom {X Y Z : B}
    {pre pre' : Word W X Y}
    {first first' second second' : Word W Y Z}
    (left : pre ≅ pre') (source : first ≅ first')
    (target : second ≅ second')
    (alpha : Presented.Hom W first second) :
    (LinearWord.appendIso W left source).inv ≫
        Presented.whiskerLeftHom W pre alpha ≫
          (LinearWord.appendIso W left target).hom =
      Presented.whiskerLeftHom W pre'
        (source.inv ≫ alpha ≫ target.hom) := by
  simp only [LinearWord.appendIso, Iso.trans_hom, Iso.trans_inv,
    Bicategory.whiskerLeftIso, Bicategory.whiskerRightIso]
  simp only [Category.assoc]
  change AlignedCell.quotientVcomp W
      (Presented.whiskerLeftHom W pre' source.inv)
      (AlignedCell.quotientVcomp W
        (Presented.whiskerRightHom W first left.inv)
        (AlignedCell.quotientVcomp W
          (Presented.whiskerLeftHom W pre alpha)
          (AlignedCell.quotientVcomp W
            (Presented.whiskerRightHom W second left.hom)
            (Presented.whiskerLeftHom W pre' target.hom)))) =
    Presented.whiskerLeftHom W pre'
      (AlignedCell.quotientVcomp W source.inv
        (AlignedCell.quotientVcomp W alpha target.hom))
  rw [← AlignedCell.quotientVcomp_assoc W
    (Presented.whiskerRightHom W first left.inv)
    (Presented.whiskerLeftHom W pre alpha)]
  rw [← AlignedCell.whisker_exchange W left.inv alpha]
  rw [AlignedCell.quotientVcomp_assoc]
  rw [← AlignedCell.quotientVcomp_assoc W
    (Presented.whiskerRightHom W second left.inv)
    (Presented.whiskerRightHom W second left.hom)]
  rw [← AlignedCell.whiskerRightHom_vcomp W second left.inv left.hom]
  have leftCancellation :
      AlignedCell.quotientVcomp W left.inv left.hom = 𝟙 pre' :=
    left.inv_hom_id
  rw [leftCancellation]
  have whiskerIdentity :
      Presented.whiskerRightHom W second (𝟙 pre') =
        𝟙 (Word.append (W := W) pre' second) :=
    Quot.sound (Presented.Rel.whisker_right_id pre' second)
  rw [whiskerIdentity, AlignedCell.quotientVcomp_id_comp]
  rw [← AlignedCell.whiskerLeftHom_vcomp W pre' alpha target.hom]
  rw [← AlignedCell.whiskerLeftHom_vcomp W pre' source.inv
    (AlignedCell.quotientVcomp W alpha target.hom)]

/-- Naturality of binary append isomorphisms around a right-whiskered
quotient 2-cell. -/
theorem appendIso_inv_whiskerRight_appendIso_hom {X Y Z : B}
    {first first' second second' : Word W X Y}
    {post post' : Word W Y Z}
    (source : first ≅ first') (target : second ≅ second')
    (right : post ≅ post')
    (alpha : Presented.Hom W first second) :
    (LinearWord.appendIso W source right).inv ≫
        Presented.whiskerRightHom W post alpha ≫
          (LinearWord.appendIso W target right).hom =
      Presented.whiskerRightHom W post'
        (source.inv ≫ alpha ≫ target.hom) := by
  simp only [LinearWord.appendIso, Iso.trans_hom, Iso.trans_inv,
    Bicategory.whiskerLeftIso, Bicategory.whiskerRightIso]
  simp only [Category.assoc]
  change AlignedCell.quotientVcomp W
      (Presented.whiskerLeftHom W first' right.inv)
      (AlignedCell.quotientVcomp W
        (Presented.whiskerRightHom W post source.inv)
        (AlignedCell.quotientVcomp W
          (Presented.whiskerRightHom W post alpha)
          (AlignedCell.quotientVcomp W
            (Presented.whiskerRightHom W post target.hom)
            (Presented.whiskerLeftHom W second' right.hom)))) =
    Presented.whiskerRightHom W post'
      (AlignedCell.quotientVcomp W source.inv
        (AlignedCell.quotientVcomp W alpha target.hom))
  rw [← AlignedCell.quotientVcomp_assoc W
    (Presented.whiskerRightHom W post alpha)
    (Presented.whiskerRightHom W post target.hom)]
  rw [← AlignedCell.whiskerRightHom_vcomp W post alpha target.hom]
  rw [← AlignedCell.quotientVcomp_assoc W
    (Presented.whiskerRightHom W post source.inv)
    (Presented.whiskerRightHom W post
      (AlignedCell.quotientVcomp W alpha target.hom))]
  rw [← AlignedCell.whiskerRightHom_vcomp W post source.inv
    (AlignedCell.quotientVcomp W alpha target.hom)]
  rw [← AlignedCell.quotientVcomp_assoc W
    (Presented.whiskerLeftHom W first' right.inv)
    (Presented.whiskerRightHom W post
      (AlignedCell.quotientVcomp W source.inv
        (AlignedCell.quotientVcomp W alpha target.hom)))]
  rw [AlignedCell.whisker_exchange W
    (AlignedCell.quotientVcomp W source.inv
      (AlignedCell.quotientVcomp W alpha target.hom)) right.inv]
  rw [AlignedCell.quotientVcomp_assoc]
  rw [← AlignedCell.whiskerLeftHom_vcomp W second' right.inv right.hom]
  have rightCancellation :
      AlignedCell.quotientVcomp W right.inv right.hom = 𝟙 post' :=
    right.inv_hom_id
  rw [rightCancellation]
  have whiskerIdentity :
      Presented.whiskerLeftHom W second' (𝟙 post') =
        𝟙 (Word.append (W := W) second' post') :=
    Quot.sound (Presented.Rel.whisker_left_id second' post')
  rw [whiskerIdentity, AlignedCell.quotientVcomp_comp_id]

/-- Left whiskering of a quotient 2-cell between linear normal forms. The
canonical append isomorphisms enter the binary word presentation and return
to the right-associated linear normal form. -/
noncomputable def normalizedWhiskerLeftHom {X Y Z : B}
    (pre : LinearWord W X Y) {first second : LinearWord W Y Z}
    (alpha : Presented.Hom W (LinearWord.toWord W first)
      (LinearWord.toWord W second)) :
    Presented.Hom W
      (LinearWord.toWord W (LinearWord.append W pre first))
      (LinearWord.toWord W (LinearWord.append W pre second)) :=
  AlignedCell.quotientVcomp W
    (LinearWord.toWordAppendIso W pre first).hom
    (AlignedCell.quotientVcomp W
      (Presented.whiskerLeftHom W (LinearWord.toWord W pre) alpha)
      (LinearWord.toWordAppendIso W pre second).inv)

/-- Right whiskering of a quotient 2-cell between linear normal forms, with
canonical transport through binary word append. -/
noncomputable def normalizedWhiskerRightHom {X Y Z : B}
    {first second : LinearWord W X Y} (post : LinearWord W Y Z)
    (alpha : Presented.Hom W (LinearWord.toWord W first)
      (LinearWord.toWord W second)) :
    Presented.Hom W
      (LinearWord.toWord W (LinearWord.append W first post))
      (LinearWord.toWord W (LinearWord.append W second post)) :=
  AlignedCell.quotientVcomp W
    (LinearWord.toWordAppendIso W first post).hom
    (AlignedCell.quotientVcomp W
      (Presented.whiskerRightHom W (LinearWord.toWord W post) alpha)
      (LinearWord.toWordAppendIso W second post).inv)

/-- Transport an arbitrary quotient 2-cell to the linear normal forms of its
two binary word endpoints. -/
noncomputable def normalizedHom {X Y : B}
    {first second : Word W X Y} (alpha : Presented.Hom W first second) :
    Presented.Hom W
      (LinearWord.toWord W (LinearWord.flatten W first))
      (LinearWord.toWord W (LinearWord.flatten W second)) :=
  AlignedCell.quotientVcomp W
    (LinearWord.normalizationIso W first).inv
    (AlignedCell.quotientVcomp W
      alpha
      (LinearWord.normalizationIso W second).hom)

/-- Transport an arbitrary raw presented cell to the linear normal forms of
its two binary word endpoints. -/
noncomputable def normalizedCellHom {X Y : B}
    {first second : Word W X Y} (cell : Cell W first second) :
    Presented.Hom W
      (LinearWord.toWord W (LinearWord.flatten W first))
      (LinearWord.toWord W (LinearWord.flatten W second)) :=
  normalizedHom W (Presented.mk W cell)

/-- Presented raw-cell relations induce equality of normalized semantics. -/
theorem normalizedCellHom_eq_of_rel {X Y : B}
    {first second : Word W X Y} {alpha beta : Cell W first second}
    (relation : Presented.Rel (W := W) alpha beta) :
    normalizedCellHom W alpha = normalizedCellHom W beta := by
  unfold normalizedCellHom
  rw [show Presented.mk W alpha = Presented.mk W beta from Quot.sound relation]

/-- Normalization commutes exactly with raw left whiskering. -/
theorem normalizedHom_whiskerLeft {X Y Z : B} (pre : Word W X Y)
    {first second : Word W Y Z} (alpha : Presented.Hom W first second) :
    normalizedHom W (Presented.whiskerLeftHom W pre alpha) =
      normalizedWhiskerLeftHom W (LinearWord.flatten W pre)
        (normalizedHom W alpha) := by
  unfold normalizedHom normalizedWhiskerLeftHom
  simp only [Word.append_eq_comp, LinearWord.flatten_append]
  rw [LinearWord.normalizationIso_append W pre first]
  rw [LinearWord.normalizationIso_append W pre second]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv]
  let sourceComparison := (LinearWord.toWordAppendIso W
    (LinearWord.flatten W pre) (LinearWord.flatten W first)).hom
  let targetComparison := (LinearWord.toWordAppendIso W
    (LinearWord.flatten W pre) (LinearWord.flatten W second)).inv
  let sourceAppend := (LinearWord.appendIso W
    (LinearWord.normalizationIso W pre)
    (LinearWord.normalizationIso W first)).inv
  let targetAppend := (LinearWord.appendIso W
    (LinearWord.normalizationIso W pre)
    (LinearWord.normalizationIso W second)).hom
  let whiskered := Presented.whiskerLeftHom W pre alpha
  let normalized := Presented.whiskerLeftHom W
    (LinearWord.toWord W (LinearWord.flatten W pre))
    (AlignedCell.quotientVcomp W (LinearWord.normalizationIso W first).inv
      (AlignedCell.quotientVcomp W alpha
        (LinearWord.normalizationIso W second).hom))
  change AlignedCell.quotientVcomp W
      (AlignedCell.quotientVcomp W sourceComparison sourceAppend)
      (AlignedCell.quotientVcomp W whiskered
        (AlignedCell.quotientVcomp W targetAppend targetComparison)) =
    AlignedCell.quotientVcomp W sourceComparison
      (AlignedCell.quotientVcomp W normalized targetComparison)
  calc
    _ = AlignedCell.quotientVcomp W sourceComparison
        (AlignedCell.quotientVcomp W
          (AlignedCell.quotientVcomp W sourceAppend
            (AlignedCell.quotientVcomp W whiskered targetAppend))
          targetComparison) := by
      simp only [AlignedCell.quotientVcomp_assoc]
    _ = AlignedCell.quotientVcomp W sourceComparison
        (AlignedCell.quotientVcomp W normalized targetComparison) := by
      rw [show AlignedCell.quotientVcomp W sourceAppend
          (AlignedCell.quotientVcomp W whiskered targetAppend) = normalized by
        dsimp [sourceAppend, whiskered, targetAppend, normalized]
        exact appendIso_inv_whiskerLeft_appendIso_hom W
          (LinearWord.normalizationIso W pre)
          (LinearWord.normalizationIso W first)
          (LinearWord.normalizationIso W second) alpha]

/-- Normalization commutes exactly with raw right whiskering. -/
theorem normalizedHom_whiskerRight {X Y Z : B}
    {first second : Word W X Y} (alpha : Presented.Hom W first second)
    (post : Word W Y Z) :
    normalizedHom W (Presented.whiskerRightHom W post alpha) =
      normalizedWhiskerRightHom W (LinearWord.flatten W post)
        (normalizedHom W alpha) := by
  unfold normalizedHom normalizedWhiskerRightHom
  simp only [Word.append_eq_comp, LinearWord.flatten_append]
  rw [LinearWord.normalizationIso_append W first post]
  rw [LinearWord.normalizationIso_append W second post]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv]
  let sourceComparison := (LinearWord.toWordAppendIso W
    (LinearWord.flatten W first) (LinearWord.flatten W post)).hom
  let targetComparison := (LinearWord.toWordAppendIso W
    (LinearWord.flatten W second) (LinearWord.flatten W post)).inv
  let sourceAppend := (LinearWord.appendIso W
    (LinearWord.normalizationIso W first)
    (LinearWord.normalizationIso W post)).inv
  let targetAppend := (LinearWord.appendIso W
    (LinearWord.normalizationIso W second)
    (LinearWord.normalizationIso W post)).hom
  let whiskered := Presented.whiskerRightHom W post alpha
  let normalized := Presented.whiskerRightHom W
    (LinearWord.toWord W (LinearWord.flatten W post))
    (AlignedCell.quotientVcomp W (LinearWord.normalizationIso W first).inv
      (AlignedCell.quotientVcomp W alpha
        (LinearWord.normalizationIso W second).hom))
  change AlignedCell.quotientVcomp W
      (AlignedCell.quotientVcomp W sourceComparison sourceAppend)
      (AlignedCell.quotientVcomp W whiskered
        (AlignedCell.quotientVcomp W targetAppend targetComparison)) =
    AlignedCell.quotientVcomp W sourceComparison
      (AlignedCell.quotientVcomp W normalized targetComparison)
  calc
    _ = AlignedCell.quotientVcomp W sourceComparison
        (AlignedCell.quotientVcomp W
          (AlignedCell.quotientVcomp W sourceAppend
            (AlignedCell.quotientVcomp W whiskered targetAppend))
          targetComparison) := by
      simp only [AlignedCell.quotientVcomp_assoc]
    _ = AlignedCell.quotientVcomp W sourceComparison
        (AlignedCell.quotientVcomp W normalized targetComparison) := by
      rw [show AlignedCell.quotientVcomp W sourceAppend
          (AlignedCell.quotientVcomp W whiskered targetAppend) = normalized by
        dsimp [sourceAppend, whiskered, targetAppend, normalized]
        exact appendIso_inv_whiskerRight_appendIso_hom W
          (LinearWord.normalizationIso W first)
          (LinearWord.normalizationIso W second)
          (LinearWord.normalizationIso W post) alpha]

end HammockPath

/-- A generated hammock path may apply an invertible structural refinement,
an arbitrary aligned raw 2-cell, normalized whiskering, or a vertical
composite of such moves. -/
inductive HammockPath : ∀ {X Y : B},
    LinearWord W X Y → LinearWord W X Y → Type max u v w where
  /-- Empty vertical path. -/
  | identity {X Y : B} (row : LinearWord W X Y) : HammockPath row row
  /-- Vertical composition of generated paths. -/
  | vcomp {X Y : B} {first middle last : LinearWord W X Y}
      (alpha : HammockPath first middle)
      (beta : HammockPath middle last) : HammockPath first last
  /-- An executable invertible structural refinement. -/
  | ofRefinement {X Y : B} {first second : LinearWord W X Y}
      (refinement : ColumnRefinement W first second) :
      HammockPath first second
  /-- An arbitrary componentwise aligned raw 2-cell. -/
  | ofAligned {X Y : B} {first second : LinearWord W X Y}
      (cell : AlignedCell W first second) : HammockPath first second
  /-- Whisker a generated path on the left by a fixed linear row. -/
  | whiskerLeft {X Y Z : B} (pre : LinearWord W X Y)
      {first second : LinearWord W Y Z}
      (path : HammockPath first second) :
      HammockPath (LinearWord.append W pre first)
        (LinearWord.append W pre second)
  /-- Whisker a generated path on the right by a fixed linear row. -/
  | whiskerRight {X Y Z : B} {first second : LinearWord W X Y}
      (path : HammockPath first second) (post : LinearWord W Y Z) :
      HammockPath (LinearWord.append W first post)
        (LinearWord.append W second post)
  /-- Whisker beneath one common atomic prefix step without introducing
  singleton-row normalization comparisons. -/
  | under {X Y Z : B} (step : Step W X Y)
      {first second : LinearWord W Y Z}
      (path : HammockPath first second) :
      HammockPath (.cons step first) (.cons step second)

namespace HammockPath

/-- Interpret a generated hammock path as one quotient 2-cell. Normalized
whiskering is semantic and therefore intentionally noncomputable. -/
noncomputable def toHom {X Y : B} {first second : LinearWord W X Y} :
    HammockPath W first second →
      Presented.Hom W (LinearWord.toWord W first)
        (LinearWord.toWord W second)
  | .identity row => 𝟙 (LinearWord.toWord W row)
  | .vcomp alpha beta =>
      AlignedCell.quotientVcomp W (toHom alpha) (toHom beta)
  | .ofRefinement refinement => ColumnRefinement.toHom W refinement
  | .ofAligned cell => AlignedCell.toHom W cell
  | .whiskerLeft pre path => normalizedWhiskerLeftHom W pre (toHom path)
  | .whiskerRight path post => normalizedWhiskerRightHom W post (toHom path)
  | .under step path =>
      Presented.whiskerLeftHom W (Word.atom step) (toHom path)

@[simp]
theorem toHom_identity {X Y : B} (row : LinearWord W X Y) :
    toHom W (.identity row) = 𝟙 (LinearWord.toWord W row) :=
  rfl

@[simp]
theorem toHom_vcomp {X Y : B}
    {first middle last : LinearWord W X Y}
    (alpha : HammockPath W first middle)
    (beta : HammockPath W middle last) :
    toHom W (.vcomp alpha beta) =
      AlignedCell.quotientVcomp W (toHom W alpha) (toHom W beta) :=
  rfl

@[simp]
theorem toHom_ofRefinement {X Y : B}
    {first second : LinearWord W X Y}
    (refinement : ColumnRefinement W first second) :
    toHom W (.ofRefinement refinement) =
      ColumnRefinement.toHom W refinement :=
  rfl

@[simp]
theorem toHom_ofAligned {X Y : B}
    {first second : LinearWord W X Y}
    (cell : AlignedCell W first second) :
    toHom W (.ofAligned cell) = AlignedCell.toHom W cell :=
  rfl

@[simp]
theorem toHom_whiskerLeft {X Y Z : B} (pre : LinearWord W X Y)
    {first second : LinearWord W Y Z}
    (path : HammockPath W first second) :
    toHom W (.whiskerLeft pre path) =
      normalizedWhiskerLeftHom W pre (toHom W path) :=
  rfl

@[simp]
theorem toHom_whiskerRight {X Y Z : B}
    {first second : LinearWord W X Y}
    (path : HammockPath W first second) (post : LinearWord W Y Z) :
    toHom W (.whiskerRight path post) =
      normalizedWhiskerRightHom W post (toHom W path) :=
  rfl

@[simp]
theorem toHom_under {X Y Z : B} (step : Step W X Y)
    {first second : LinearWord W Y Z}
    (path : HammockPath W first second) :
    toHom W (.under step path) =
      Presented.whiskerLeftHom W (Word.atom step) (toHom W path) :=
  rfl

/-- Horizontal append of two generated paths, implemented by right
whiskering the first and left whiskering the second. -/
def append {X Y Z : B}
    {firstSource firstTarget : LinearWord W X Y}
    {secondSource secondTarget : LinearWord W Y Z}
    (first : HammockPath W firstSource firstTarget)
    (second : HammockPath W secondSource secondTarget) :
    HammockPath W
      (LinearWord.append W firstSource secondSource)
      (LinearWord.append W firstTarget secondTarget) :=
  .vcomp (.whiskerRight first secondSource)
    (.whiskerLeft firstTarget second)

/-- A propositional equality of linear rows yields the transported identity
generated path. -/
def ofEq {X Y : B} {first second : LinearWord W X Y}
    (equality : first = second) : HammockPath W first second := by
  subst second
  exact .identity first

/-- The equality path reduces to the identity after equality elimination. -/
@[simp]
theorem toHom_ofEq {X Y : B} {first second : LinearWord W X Y}
    (equality : first = second) :
    toHom W (ofEq W equality) = equality ▸ 𝟙 (LinearWord.toWord W first) := by
  subst second
  rfl

/-- Equality transport of an identity is the categorical equality morphism
induced after binary expansion. -/
theorem castIdentity_eqToHom {X Y : B}
    {first second : LinearWord W X Y} (equality : first = second) :
    equality ▸ 𝟙 (LinearWord.toWord W first) =
      eqToHom (congrArg (LinearWord.toWord W) equality) := by
  subst second
  rfl

/-- Recursive generated path implementing the right-unit equation for a
linear row. -/
def rightUnitPath {X Y : B} :
    (row : LinearWord W X Y) →
      HammockPath W (LinearWord.append W row (.nil Y)) row
  | .nil X => .identity (.nil X)
  | .cons step rest => .under step (rightUnitPath rest)

/-- Recursive inverse generated path for the right-unit equation. -/
def rightUnitPathInv {X Y : B} :
    (row : LinearWord W X Y) →
      HammockPath W row (LinearWord.append W row (.nil Y))
  | .nil X => .identity (.nil X)
  | .cons step rest => .under step (rightUnitPathInv rest)

/-- Recursive generated path implementing associativity of linear row
append. -/
def associatorPath {X Y Z T : B} :
    (first : LinearWord W X Y) →
    (second : LinearWord W Y Z) →
    (third : LinearWord W Z T) →
      HammockPath W
        (LinearWord.append W (LinearWord.append W first second) third)
        (LinearWord.append W first (LinearWord.append W second third))
  | .nil _, second, third => .identity (LinearWord.append W second third)
  | .cons step rest, second, third =>
      .under step (associatorPath rest second third)

/-- Recursive inverse generated path implementing the inverse associativity
equation for linear row append. -/
def associatorPathInv {X Y Z T : B} :
    (first : LinearWord W X Y) →
    (second : LinearWord W Y Z) →
    (third : LinearWord W Z T) →
      HammockPath W
        (LinearWord.append W first (LinearWord.append W second third))
        (LinearWord.append W (LinearWord.append W first second) third)
  | .nil _, second, third => .identity (LinearWord.append W second third)
  | .cons step rest, second, third =>
      .under step (associatorPathInv rest second third)

/-- Exact semantic formula for the recursive right-unit path. -/
theorem toHom_rightUnitPath {X Y : B} (row : LinearWord W X Y) :
    toHom W (rightUnitPath W row) =
      AlignedCell.quotientVcomp W
        (LinearWord.toWordAppendIso W row (.nil Y)).hom
        (Presented.wordRightUnitorIso W (LinearWord.toWord W row)).hom := by
  induction row with
  | nil X =>
      change 𝟙 (Word.nil X) =
        AlignedCell.quotientVcomp W
          (Presented.wordLeftUnitorIso W (.nil X)).inv
          (Presented.wordRightUnitorIso W (.nil X)).hom
      have unitors :
          (Presented.wordLeftUnitorIso W (.nil X)).inv =
            (Presented.wordRightUnitorIso W (.nil X)).inv := by
        change (λ_ (𝟙 (⟨X⟩ : Presented.Localization W))).inv =
          (ρ_ (𝟙 (⟨X⟩ : Presented.Localization W))).inv
        exact unitors_inv_equal
      rw [unitors]
      exact (Presented.wordRightUnitorIso W (.nil X)).inv_hom_id.symm
  | @cons X Y Z step rest ih =>
      rw [LinearWord.toWordAppendIso_cons W step rest (.nil Z)]
      simp only [rightUnitPath, LinearWord.append, toHom_under,
        Iso.trans_hom, Bicategory.whiskerLeftIso, Iso.symm_hom]
      rw [ih]
      exact LinearWord.rightUnit_step_coherence
        (C := Presented.Localization W) (Word.atom step)
        (LinearWord.toWord W rest)
        (LinearWord.toWordAppendIso W rest (.nil Z)).hom

/-- Exact semantic formula for the inverse recursive right-unit path. -/
theorem toHom_rightUnitPathInv {X Y : B} (row : LinearWord W X Y) :
    toHom W (rightUnitPathInv W row) =
      AlignedCell.quotientVcomp W
        (Presented.wordRightUnitorIso W (LinearWord.toWord W row)).inv
        (LinearWord.toWordAppendIso W row (.nil Y)).inv := by
  induction row with
  | nil X =>
      change 𝟙 (Word.nil X) =
        AlignedCell.quotientVcomp W
          (Presented.wordRightUnitorIso W (.nil X)).inv
          (Presented.wordLeftUnitorIso W (.nil X)).hom
      have unitors :
          (Presented.wordRightUnitorIso W (.nil X)).inv =
            (Presented.wordLeftUnitorIso W (.nil X)).inv := by
        change (ρ_ (𝟙 (⟨X⟩ : Presented.Localization W))).inv =
          (λ_ (𝟙 (⟨X⟩ : Presented.Localization W))).inv
        exact unitors_inv_equal.symm
      rw [unitors]
      exact (Presented.wordLeftUnitorIso W (.nil X)).inv_hom_id.symm
  | @cons X Y Z step rest ih =>
      rw [LinearWord.toWordAppendIso_cons W step rest (.nil Z)]
      simp only [rightUnitPathInv, LinearWord.append, toHom_under,
        Iso.trans_inv, Bicategory.whiskerLeftIso, Iso.symm_inv]
      rw [ih]
      exact (LinearWord.rightUnit_inv_step_coherence
        (C := Presented.Localization W) (Word.atom step)
        (LinearWord.toWord W rest)
        (LinearWord.toWordAppendIso W rest (.nil Z)).inv).symm

/-- The recursive right-unit path followed by its recursive inverse denotes
the identity on the row with a terminal empty suffix. -/
theorem rightUnitPath_hom_inv {X Y : B} (row : LinearWord W X Y) :
    AlignedCell.quotientVcomp W
        (toHom W (rightUnitPath W row))
        (toHom W (rightUnitPathInv W row)) =
      𝟙 (LinearWord.toWord W
        (LinearWord.append W row (.nil Y))) := by
  induction row with
  | nil X =>
      change (𝟙 (Word.nil X)) ≫ 𝟙 (Word.nil X) = 𝟙 (Word.nil X)
      exact Category.id_comp _
  | @cons X Y Z step rest ih =>
      simp only [rightUnitPath, rightUnitPathInv, LinearWord.append,
        toHom_under]
      change AlignedCell.quotientVcomp W
          (Presented.whiskerLeftHom W (Word.atom step)
            (toHom W (rightUnitPath W rest)))
          (Presented.whiskerLeftHom W (Word.atom step)
            (toHom W (rightUnitPathInv W rest))) =
        𝟙 (Word.append (W := W) (Word.atom step)
          (LinearWord.toWord W
            (LinearWord.append W rest (.nil Z))))
      rw [← AlignedCell.whiskerLeftHom_vcomp W (Word.atom step)]
      rw [ih]
      exact Quot.sound (Presented.Rel.whisker_left_id
        (Word.atom step)
        (LinearWord.toWord W (LinearWord.append W rest (.nil Z))))

/-- The recursive associator path is exactly the canonical comparison between
the two binary expansions of associative linear append. -/
theorem toHom_associatorPath {X Y Z T : B}
    (first : LinearWord W X Y) (second : LinearWord W Y Z)
    (third : LinearWord W Z T) :
    toHom W (associatorPath W first second third) =
      (LinearWord.associatorIso W first second third).hom := by
  induction first with
  | nil X =>
      rw [LinearWord.associatorIso_nil]
      rfl
  | @cons X Y U step rest ih =>
      simp only [LinearWord.append, associatorPath, toHom_under]
      rw [LinearWord.associatorIso_cons]
      simp only [Bicategory.whiskerLeftIso]
      rw [ih]
      rfl

/-- The inverse recursive associator path is the inverse canonical linear
associator comparison. -/
theorem toHom_associatorPathInv {X Y Z T : B}
    (first : LinearWord W X Y) (second : LinearWord W Y Z)
    (third : LinearWord W Z T) :
    toHom W (associatorPathInv W first second third) =
      (LinearWord.associatorIso W first second third).inv := by
  induction first with
  | nil X =>
      rw [LinearWord.associatorIso_nil]
      rfl
  | @cons X Y U step rest ih =>
      simp only [LinearWord.append, associatorPathInv, toHom_under]
      rw [LinearWord.associatorIso_cons]
      simp only [Bicategory.whiskerLeftIso]
      rw [ih]
      rfl

/-- The recursive associator path followed by its inverse denotes identity. -/
theorem associatorPath_hom_inv {X Y Z T : B}
    (first : LinearWord W X Y) (second : LinearWord W Y Z)
    (third : LinearWord W Z T) :
    AlignedCell.quotientVcomp W
        (toHom W (associatorPath W first second third))
        (toHom W (associatorPathInv W first second third)) =
      𝟙 (LinearWord.toWord W
        (LinearWord.append W (LinearWord.append W first second) third)) := by
  rw [toHom_associatorPath, toHom_associatorPathInv]
  exact (LinearWord.associatorIso W first second third).hom_inv_id

/-- The inverse recursive associator path followed by the forward path also
denotes identity. -/
theorem associatorPath_inv_hom {X Y Z T : B}
    (first : LinearWord W X Y) (second : LinearWord W Y Z)
    (third : LinearWord W Z T) :
    AlignedCell.quotientVcomp W
        (toHom W (associatorPathInv W first second third))
        (toHom W (associatorPath W first second third)) =
      𝟙 (LinearWord.toWord W
        (LinearWord.append W first (LinearWord.append W second third))) := by
  rw [toHom_associatorPathInv, toHom_associatorPath]
  exact (LinearWord.associatorIso W first second third).inv_hom_id

/-- Exact quotient interpretation of horizontal path append. -/
@[simp]
theorem toHom_append {X Y Z : B}
    {firstSource firstTarget : LinearWord W X Y}
    {secondSource secondTarget : LinearWord W Y Z}
    (first : HammockPath W firstSource firstTarget)
    (second : HammockPath W secondSource secondTarget) :
    toHom W (append W first second) =
      AlignedCell.quotientVcomp W
        (normalizedWhiskerRightHom W secondSource (toHom W first))
        (normalizedWhiskerLeftHom W firstTarget (toHom W second)) :=
  rfl

/-- Generated paths are semantically equal when their quotient 2-cell
interpretations agree. -/
def Rel {X Y : B} {first second : LinearWord W X Y}
    (alpha beta : HammockPath W first second) : Prop :=
  toHom W alpha = toHom W beta

/-- Semantic equality is an equivalence relation on generated paths. -/
def setoid {X Y : B} (first second : LinearWord W X Y) :
    Setoid (HammockPath W first second) where
  r := Rel W
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Morphisms are aligned-cell-augmented paths modulo equality of their
quotient-cell semantics. -/
abbrev Hom {X Y : B} (first second : LinearWord W X Y) :=
  Quotient (setoid W first second)

/-- Semantic equality is stable under vertical path composition. -/
theorem rel_vcomp {X Y : B}
    {first middle last : LinearWord W X Y}
    {alpha alpha' : HammockPath W first middle}
    {beta beta' : HammockPath W middle last}
    (hAlpha : Rel W alpha alpha') (hBeta : Rel W beta beta') :
    Rel W (.vcomp alpha beta) (.vcomp alpha' beta') := by
  unfold Rel at hAlpha hBeta ⊢
  change AlignedCell.quotientVcomp W (toHom W alpha) (toHom W beta) =
    AlignedCell.quotientVcomp W (toHom W alpha') (toHom W beta')
  rw [hAlpha, hBeta]

/-- Semantic equality is stable under normalized left whiskering. -/
theorem rel_whiskerLeft {X Y Z : B} (pre : LinearWord W X Y)
    {first second : LinearWord W Y Z}
    {alpha beta : HammockPath W first second}
    (equality : Rel W alpha beta) :
    Rel W (.whiskerLeft pre alpha) (.whiskerLeft pre beta) := by
  unfold Rel at equality ⊢
  change normalizedWhiskerLeftHom W pre (toHom W alpha) =
    normalizedWhiskerLeftHom W pre (toHom W beta)
  rw [equality]

/-- Semantic equality is stable under normalized right whiskering. -/
theorem rel_whiskerRight {X Y Z : B}
    {first second : LinearWord W X Y} (post : LinearWord W Y Z)
    {alpha beta : HammockPath W first second}
    (equality : Rel W alpha beta) :
    Rel W (.whiskerRight alpha post) (.whiskerRight beta post) := by
  unfold Rel at equality ⊢
  change normalizedWhiskerRightHom W post (toHom W alpha) =
    normalizedWhiskerRightHom W post (toHom W beta)
  rw [equality]

/-- Semantic equality is stable beneath an atomic prefix step. -/
theorem rel_under {X Y Z : B} (step : Step W X Y)
    {first second : LinearWord W Y Z}
    {alpha beta : HammockPath W first second}
    (equality : Rel W alpha beta) :
    Rel W (.under step alpha) (.under step beta) := by
  unfold Rel at equality ⊢
  change Presented.whiskerLeftHom W (Word.atom step) (toHom W alpha) =
    Presented.whiskerLeftHom W (Word.atom step) (toHom W beta)
  rw [equality]

/-- Semantic equality is stable under horizontal append. -/
theorem rel_append {X Y Z : B}
    {firstSource firstTarget : LinearWord W X Y}
    {secondSource secondTarget : LinearWord W Y Z}
    {first first' : HammockPath W firstSource firstTarget}
    {second second' : HammockPath W secondSource secondTarget}
    (hFirst : Rel W first first') (hSecond : Rel W second second') :
    Rel W (append W first second) (append W first' second') := by
  apply rel_vcomp W
  · exact rel_whiskerRight W secondSource hFirst
  · exact rel_whiskerLeft W firstTarget hSecond

/-- Aligned-cell-augmented semantic paths form a category. -/
instance category (X Y : B) : Category (HammockPathObject W X Y) where
  Hom first second := Hom W first.row second.row
  id first := Quotient.mk (setoid W first.row first.row) (.identity first.row)
  comp := Quotient.map₂ HammockPath.vcomp
    (fun alpha alpha' hAlpha beta beta' hBeta => by
      change Rel W alpha alpha' at hAlpha
      change Rel W beta beta' at hBeta
      exact rel_vcomp W hAlpha hBeta)
  id_comp := by
    rintro first second ⟨path⟩
    apply Quotient.sound
    change Rel W (.vcomp (.identity first.row) path) path
    unfold Rel
    exact Category.id_comp _
  comp_id := by
    rintro first second ⟨path⟩
    apply Quotient.sound
    change Rel W (.vcomp path (.identity second.row)) path
    unfold Rel
    exact Category.comp_id _
  assoc := by
    rintro first second third fourth ⟨alpha⟩ ⟨beta⟩ ⟨gamma⟩
    apply Quotient.sound
    change Rel W (.vcomp (.vcomp alpha beta) gamma)
      (.vcomp alpha (.vcomp beta gamma))
    unfold Rel
    exact Category.assoc _ _ _

/-- Faithful semantic interpretation into the full linear mapping category. -/
noncomputable def semanticFunctor (X Y : B) :
    HammockPathObject W X Y ⥤ LinearWord W X Y where
  obj row := row.row
  map := Quotient.lift (toHom W)
    (fun alpha beta equality => by
      change Rel W alpha beta at equality
      exact equality)
  map_id _ := rfl
  map_comp alpha beta := by
    rcases alpha with ⟨alpha⟩
    rcases beta with ⟨beta⟩
    rfl

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

/-- Embed one semantic refinement path into the larger generated hammock-path
category. -/
def ofRefinementHom {X Y : B}
    {first second : RefinementPathObject W X Y} :
    (first ⟶ second) → Hom W first.row second.row :=
  Quotient.map HammockPath.ofRefinement
    (fun alpha beta equality => by
      change RefinementPath.Rel W alpha beta at equality
      change Rel W (.ofRefinement alpha) (.ofRefinement beta)
      exact equality)

/-- Refinement-only semantic paths embed into aligned-cell-augmented paths. -/
def refinementFunctor (X Y : B) :
    RefinementPathObject W X Y ⥤ HammockPathObject W X Y where
  obj row := ⟨row.row⟩
  map := ofRefinementHom W
  map_id row := by
    apply Quotient.sound
    change Rel W (.ofRefinement (.identity row.row)) (.identity row.row)
    rfl
  map_comp alpha beta := by
    rcases alpha with ⟨alpha⟩
    rcases beta with ⟨beta⟩
    apply Quotient.sound
    change Rel W (.ofRefinement (.vcomp alpha beta))
      (.vcomp (.ofRefinement alpha) (.ofRefinement beta))
    rfl

instance refinementFunctor_faithful (X Y : B) :
    (refinementFunctor W X Y).Faithful where
  map_injective {first second} alpha beta equality := by
    rcases alpha with ⟨alpha⟩
    rcases beta with ⟨beta⟩
    apply Quotient.sound
    change RefinementPath.Rel W alpha beta
    have mappedEquality := congrArg (semanticFunctor W X Y).map equality
    change toHom W (.ofRefinement alpha) =
      toHom W (.ofRefinement beta) at mappedEquality
    exact mappedEquality

instance refinementFunctor_essSurj (X Y : B) :
    (refinementFunctor W X Y).EssSurj where
  mem_essImage row := ⟨⟨row.row⟩, ⟨Iso.refl _⟩⟩

/-- Refinement semantics factors strictly through the larger generated
hammock-path category. -/
theorem refinementSemanticFunctor_factorization (X Y : B) :
    RefinementPath.semanticFunctor W X Y =
      refinementFunctor W X Y ⋙ semanticFunctor W X Y := by
  apply Functor.hext
  · intro row
    rfl
  · intro first second path
    rcases path with ⟨refinement⟩
    rfl

/-- Include one aligned cell as a generated semantic hammock morphism. -/
def alignedHom {X Y : B} {first second : LinearWord W X Y}
    (cell : AlignedCell W first second) : Hom W first second :=
  Quotient.mk (setoid W first second) (.ofAligned cell)

/-- The semantic functor maps an included aligned cell to its exact quotient
interpretation. -/
@[simp]
theorem semanticFunctor_map_aligned {X Y : B}
    {first second : LinearWord W X Y}
    (cell : AlignedCell W first second) :
    (semanticFunctor W X Y).map (alignedHom W cell) =
      AlignedCell.toHom W cell :=
  rfl

/-- A quotient 2-cell lies in the generated hammock semantic image when some
raw generated path denotes it. -/
def InSemanticImage {X Y : B} {first second : LinearWord W X Y}
    (morphism : Presented.Hom W (LinearWord.toWord W first)
      (LinearWord.toWord W second)) : Prop :=
  ∃ path : HammockPath W first second, toHom W path = morphism

/-- A raw cell is hammock-normalizable when its transport between the linear
normal forms of its endpoints lies in the generated semantic image. -/
def Normalizable {X Y : B} {first second : Word W X Y}
    (cell : Cell W first second) : Prop :=
  InSemanticImage W (normalizedCellHom W cell)

/-- Exact image characterization through morphisms of the semantic path
category. -/
theorem inSemanticImage_iff_exists_map {X Y : B}
    {first second : LinearWord W X Y}
    (morphism : Presented.Hom W (LinearWord.toWord W first)
      (LinearWord.toWord W second)) :
    InSemanticImage W morphism ↔
      ∃ path : (⟨first⟩ : HammockPathObject W X Y) ⟶ ⟨second⟩,
        (semanticFunctor W X Y).map path = morphism := by
  constructor
  · rintro ⟨path, equality⟩
    exact ⟨Quotient.mk (setoid W first second) path, equality⟩
  · rintro ⟨⟨path⟩, equality⟩
    exact ⟨path, equality⟩

/-- Every executable structural refinement belongs to the enlarged semantic
image. -/
theorem refinement_mem_semanticImage {X Y : B}
    {first second : LinearWord W X Y}
    (refinement : ColumnRefinement W first second) :
    InSemanticImage W (ColumnRefinement.toHom W refinement) :=
  ⟨.ofRefinement refinement, rfl⟩

/-- Every arbitrary aligned raw 2-cell belongs to the enlarged semantic
image. -/
theorem aligned_mem_semanticImage {X Y : B}
    {first second : LinearWord W X Y}
    (cell : AlignedCell W first second) :
    InSemanticImage W (AlignedCell.toHom W cell) :=
  ⟨.ofAligned cell, rfl⟩

/-- The semantic image is closed under vertical composition. -/
theorem vcomp_mem_semanticImage {X Y : B}
    {first middle last : LinearWord W X Y}
    {alpha : Presented.Hom W (LinearWord.toWord W first)
      (LinearWord.toWord W middle)}
    {beta : Presented.Hom W (LinearWord.toWord W middle)
      (LinearWord.toWord W last)}
    (hAlpha : InSemanticImage W alpha)
    (hBeta : InSemanticImage W beta) :
    InSemanticImage W (AlignedCell.quotientVcomp W alpha beta) := by
  rcases hAlpha with ⟨alphaPath, hAlpha⟩
  rcases hBeta with ⟨betaPath, hBeta⟩
  exact ⟨.vcomp alphaPath betaPath, by rw [toHom_vcomp, hAlpha, hBeta]⟩

/-- The semantic image is closed under normalized left whiskering. -/
theorem whiskerLeft_mem_semanticImage {X Y Z : B}
    (pre : LinearWord W X Y) {first second : LinearWord W Y Z}
    {morphism : Presented.Hom W (LinearWord.toWord W first)
      (LinearWord.toWord W second)}
    (member : InSemanticImage W morphism) :
    InSemanticImage W (normalizedWhiskerLeftHom W pre morphism) := by
  rcases member with ⟨path, equality⟩
  exact ⟨.whiskerLeft pre path, by rw [toHom_whiskerLeft, equality]⟩

/-- The semantic image is closed under normalized right whiskering. -/
theorem whiskerRight_mem_semanticImage {X Y Z : B}
    {first second : LinearWord W X Y} (post : LinearWord W Y Z)
    {morphism : Presented.Hom W (LinearWord.toWord W first)
      (LinearWord.toWord W second)}
    (member : InSemanticImage W morphism) :
    InSemanticImage W (normalizedWhiskerRightHom W post morphism) := by
  rcases member with ⟨path, equality⟩
  exact ⟨.whiskerRight path post, by rw [toHom_whiskerRight, equality]⟩

/-- The semantic image is closed under horizontal append of represented
quotient 2-cells. -/
theorem append_mem_semanticImage {X Y Z : B}
    {firstSource firstTarget : LinearWord W X Y}
    {secondSource secondTarget : LinearWord W Y Z}
    {first : Presented.Hom W (LinearWord.toWord W firstSource)
      (LinearWord.toWord W firstTarget)}
    {second : Presented.Hom W (LinearWord.toWord W secondSource)
      (LinearWord.toWord W secondTarget)}
    (hFirst : InSemanticImage W first)
    (hSecond : InSemanticImage W second) :
    InSemanticImage W
      (AlignedCell.quotientVcomp W
        (normalizedWhiskerRightHom W secondSource first)
        (normalizedWhiskerLeftHom W firstTarget second)) := by
  rcases hFirst with ⟨firstPath, firstEquality⟩
  rcases hSecond with ⟨secondPath, secondEquality⟩
  refine ⟨append W firstPath secondPath, ?_⟩
  rw [toHom_append, firstEquality, secondEquality]

/-- Normalizing a raw identity cell gives the identity of the linear normal
form. -/
@[simp]
theorem normalizedCellHom_id {X Y : B} (word : Word W X Y) :
    normalizedCellHom W (Cell.id word) =
      𝟙 (LinearWord.toWord W (LinearWord.flatten W word)) := by
  change (LinearWord.normalizationIso W word).inv ≫
      (𝟙 word) ≫ (LinearWord.normalizationIso W word).hom = _
  simp

/-- Normalization preserves vertical composition of raw cells exactly. -/
@[simp]
theorem normalizedCellHom_vcomp {X Y : B}
    {first middle last : Word W X Y}
    (alpha : Cell W first middle) (beta : Cell W middle last) :
    normalizedCellHom W (.vcomp alpha beta) =
      AlignedCell.quotientVcomp W
        (normalizedCellHom W alpha) (normalizedCellHom W beta) := by
  change (LinearWord.normalizationIso W first).inv ≫
      (Presented.mk W alpha ≫ Presented.mk W beta) ≫
        (LinearWord.normalizationIso W last).hom =
    ((LinearWord.normalizationIso W first).inv ≫
      Presented.mk W alpha ≫ (LinearWord.normalizationIso W middle).hom) ≫
    ((LinearWord.normalizationIso W middle).inv ≫
      Presented.mk W beta ≫ (LinearWord.normalizationIso W last).hom)
  simp [Category.assoc]

/-- Raw left whiskering is transported exactly to normalized left
whiskering. -/
@[simp]
theorem normalizedCellHom_whiskerLeft {X Y Z : B}
    (pre : Word W X Y) {first second : Word W Y Z}
    (cell : Cell W first second) :
    normalizedCellHom W (.whiskerLeft pre cell) =
      normalizedWhiskerLeftHom W (LinearWord.flatten W pre)
        (normalizedCellHom W cell) := by
  exact normalizedHom_whiskerLeft W pre (Presented.mk W cell)

/-- Raw right whiskering is transported exactly to normalized right
whiskering. -/
@[simp]
theorem normalizedCellHom_whiskerRight {X Y Z : B}
    {first second : Word W X Y} (cell : Cell W first second)
    (post : Word W Y Z) :
    normalizedCellHom W (.whiskerRight cell post) =
      normalizedWhiskerRightHom W (LinearWord.flatten W post)
        (normalizedCellHom W cell) := by
  exact normalizedHom_whiskerRight W (Presented.mk W cell) post

/-- The source-identity comparison normalizes to executable deletion of one
forward identity column. -/
@[simp]
theorem normalizedCellHom_sourceId {X : B} :
    normalizedCellHom W (Cell.sourceId (W := W) (X := X)) =
      ColumnRefinement.toHom W (.deleteIdentity (.nil X)) := by
  unfold normalizedCellHom normalizedHom
  simp only [LinearWord.flatten_forward, LinearWord.flatten]
  rw [show LinearWord.normalizationIso W (Word.forward W (𝟙 X)) =
      (Presented.wordRightUnitorIso W (Word.forward W (𝟙 X))).symm from rfl]
  rw [LinearWord.normalizationIso_nil W X]
  simp only [Iso.symm_inv, Iso.refl_hom]
  rw [ColumnRefinement.toHom_deleteIdentity]
  change AlignedCell.quotientVcomp W
      (Presented.wordRightUnitorIso W (Word.forward W (𝟙 X))).hom
      (AlignedCell.quotientVcomp W
        (Presented.mk W (Cell.sourceId (W := W))) (𝟙 (Word.nil X))) =
    AlignedCell.quotientVcomp W
      (Presented.whiskerRightHom W (.nil X)
        (Presented.mk W (Cell.sourceId (W := W))))
      (Presented.wordLeftUnitorIso W (.nil X)).hom
  rw [AlignedCell.quotientVcomp_comp_id]
  have whiskerEquality :
      Presented.whiskerRightHom W (.nil X)
          (Presented.mk W (Cell.sourceId (W := W))) =
        AlignedCell.quotientVcomp W
          (Presented.wordRightUnitorIso W (Word.forward W (𝟙 X))).hom
          (AlignedCell.quotientVcomp W
            (Presented.mk W (Cell.sourceId (W := W)))
            (Presented.wordRightUnitorIso W (.nil X)).inv) :=
    Quot.sound (Presented.Rel.whisker_right_id_word
      (Cell.sourceId (W := W)))
  rw [whiskerEquality]
  rw [AlignedCell.quotientVcomp_assoc]
  rw [AlignedCell.quotientVcomp_assoc W
    (Presented.mk W (Cell.sourceId (W := W)))
    (Presented.wordRightUnitorIso W (.nil X)).inv
    (Presented.wordLeftUnitorIso W (.nil X)).hom]
  have unitCancellation :
      AlignedCell.quotientVcomp W
          (Presented.wordRightUnitorIso W (.nil X)).inv
          (Presented.wordLeftUnitorIso W (.nil X)).hom =
        𝟙 (Word.nil X) := by
    change (ρ_ (𝟙 (⟨X⟩ : Presented.Localization W))).inv ≫
      (λ_ (𝟙 (⟨X⟩ : Presented.Localization W))).hom = _
    rw [← unitors_inv_equal]
    exact (Presented.wordLeftUnitorIso W (.nil X)).inv_hom_id
  rw [unitCancellation, AlignedCell.quotientVcomp_comp_id]

/-- The inverse source-identity comparison normalizes to executable insertion
of one forward identity column. -/
@[simp]
theorem normalizedCellHom_sourceIdInv {X : B} :
    normalizedCellHom W (Cell.sourceIdInv (W := W) (X := X)) =
      ColumnRefinement.toHom W (.insertIdentity (.nil X)) := by
  unfold normalizedCellHom normalizedHom
  simp only [LinearWord.flatten_forward, LinearWord.flatten]
  rw [LinearWord.normalizationIso_nil W X]
  rw [show LinearWord.normalizationIso W (Word.forward W (𝟙 X)) =
      (Presented.wordRightUnitorIso W (Word.forward W (𝟙 X))).symm from rfl]
  simp only [Iso.refl_inv, Iso.symm_hom]
  rw [ColumnRefinement.toHom_insertIdentity]
  change AlignedCell.quotientVcomp W (𝟙 (Word.nil X))
      (AlignedCell.quotientVcomp W
        (Presented.mk W (Cell.sourceIdInv (W := W)))
        (Presented.wordRightUnitorIso W (Word.forward W (𝟙 X))).inv) =
    AlignedCell.quotientVcomp W
      (Presented.wordLeftUnitorIso W (.nil X)).inv
      (Presented.whiskerRightHom W (.nil X)
        (Presented.mk W (Cell.sourceIdInv (W := W))))
  rw [AlignedCell.quotientVcomp_id_comp]
  have whiskerEquality :
      Presented.whiskerRightHom W (.nil X)
          (Presented.mk W (Cell.sourceIdInv (W := W))) =
        AlignedCell.quotientVcomp W
          (Presented.wordRightUnitorIso W (.nil X)).hom
          (AlignedCell.quotientVcomp W
            (Presented.mk W (Cell.sourceIdInv (W := W)))
            (Presented.wordRightUnitorIso W
              (Word.forward W (𝟙 X))).inv) :=
    Quot.sound (Presented.Rel.whisker_right_id_word
      (Cell.sourceIdInv (W := W)))
  rw [whiskerEquality]
  rw [← AlignedCell.quotientVcomp_assoc W
    (Presented.wordLeftUnitorIso W (.nil X)).inv
    (Presented.wordRightUnitorIso W (.nil X)).hom]
  have unitCancellation :
      AlignedCell.quotientVcomp W
          (Presented.wordLeftUnitorIso W (.nil X)).inv
          (Presented.wordRightUnitorIso W (.nil X)).hom =
        𝟙 (Word.nil X) := by
    change (λ_ (𝟙 (⟨X⟩ : Presented.Localization W))).inv ≫
      (ρ_ (𝟙 (⟨X⟩ : Presented.Localization W))).hom = _
    rw [unitors_inv_equal]
    exact (Presented.wordRightUnitorIso W (.nil X)).inv_hom_id
  rw [unitCancellation, AlignedCell.quotientVcomp_id_comp]

/-- The source-composition comparison normalizes to executable expansion of
one forward composite into two forward columns. -/
@[simp]
theorem normalizedCellHom_sourceComp {X Y Z : B}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    normalizedCellHom W (Cell.sourceComp (W := W) f g) =
      ColumnRefinement.toHom W (.expandForward f g (.nil Z)) := by
  unfold normalizedCellHom normalizedHom
  simp only [Word.append_eq_comp, LinearWord.flatten_append,
    Word.forward, Word.single]
  rw [show LinearWord.normalizationIso W
      (Word.atom (Step.forward (f ≫ g))) =
    (Presented.wordRightUnitorIso W
      (Word.atom (Step.forward (f ≫ g)))).symm from rfl]
  rw [LinearWord.normalizationIso_twoAtoms_hom W
    (Step.forward (W := W) f) (Step.forward (W := W) g)]
  simp only [Iso.symm_inv]
  rw [ColumnRefinement.toHom_expandForward]
  change AlignedCell.quotientVcomp W
      (Presented.wordRightUnitorIso W
        (Word.atom (Step.forward (f ≫ g)))).hom
      (AlignedCell.quotientVcomp W
        (Presented.mk W (Cell.sourceComp (W := W) f g))
        (AlignedCell.quotientVcomp W
          (Presented.wordRightUnitorIso W
            (.comp (Word.atom (Step.forward f))
              (Word.atom (Step.forward g)))).inv
          (Presented.wordAssociatorIso W (Word.forward W f)
            (Word.forward W g) (.nil Z)).hom)) =
    AlignedCell.quotientVcomp W
      (Presented.whiskerRightHom W (.nil Z)
        (Presented.mk W (Cell.sourceComp (W := W) f g)))
      (Presented.wordAssociatorIso W (Word.forward W f)
        (Word.forward W g) (.nil Z)).hom
  rw [← AlignedCell.quotientVcomp_assoc]
  have whiskerEquality :
      Presented.whiskerRightHom W (.nil Z)
          (Presented.mk W (Cell.sourceComp (W := W) f g)) =
        AlignedCell.quotientVcomp W
          (Presented.wordRightUnitorIso W (Word.forward W (f ≫ g))).hom
          (AlignedCell.quotientVcomp W
            (Presented.mk W (Cell.sourceComp (W := W) f g))
            (Presented.wordRightUnitorIso W
              (Word.append (W := W) (Word.forward W f)
                (Word.forward W g))).inv) :=
    Quot.sound (Presented.Rel.whisker_right_id_word
      (Cell.sourceComp (W := W) f g))
  rw [whiskerEquality]
  simp only [AlignedCell.quotientVcomp_assoc]
  rfl

/-- The inverse source-composition comparison normalizes to executable
contraction of two forward columns. -/
@[simp]
theorem normalizedCellHom_sourceCompInv {X Y Z : B}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    normalizedCellHom W (Cell.sourceCompInv (W := W) f g) =
      ColumnRefinement.toHom W (.contractForward f g (.nil Z)) := by
  unfold normalizedCellHom normalizedHom
  simp only [Word.append_eq_comp, LinearWord.flatten_append,
    Word.forward, Word.single]
  rw [LinearWord.normalizationIso_twoAtoms_inv W
    (Step.forward (W := W) f) (Step.forward (W := W) g)]
  rw [show LinearWord.normalizationIso W
      (Word.atom (Step.forward (f ≫ g))) =
    (Presented.wordRightUnitorIso W
      (Word.atom (Step.forward (f ≫ g)))).symm from rfl]
  simp only [Iso.symm_hom]
  rw [ColumnRefinement.toHom_contractForward]
  change AlignedCell.quotientVcomp W
      (AlignedCell.quotientVcomp W
        (Presented.wordAssociatorIso W
          (Word.forward W f) (Word.forward W g) (.nil Z)).inv
        (Presented.wordRightUnitorIso W
          (Word.append (W := W) (Word.forward W f)
            (Word.forward W g))).hom)
      (AlignedCell.quotientVcomp W
        (Presented.mk W (Cell.sourceCompInv (W := W) f g))
        (Presented.wordRightUnitorIso W (Word.forward W (f ≫ g))).inv) =
    AlignedCell.quotientVcomp W
      (Presented.wordAssociatorIso W
        (Word.forward W f) (Word.forward W g) (.nil Z)).inv
      (Presented.whiskerRightHom W (.nil Z)
        (Presented.mk W (Cell.sourceCompInv (W := W) f g)))
  rw [AlignedCell.quotientVcomp_assoc]
  have whiskerEquality :
      Presented.whiskerRightHom W (.nil Z)
          (Presented.mk W (Cell.sourceCompInv (W := W) f g)) =
        AlignedCell.quotientVcomp W
          (Presented.wordRightUnitorIso W
            (Word.append (W := W) (Word.forward W f)
              (Word.forward W g))).hom
          (AlignedCell.quotientVcomp W
            (Presented.mk W (Cell.sourceCompInv (W := W) f g))
            (Presented.wordRightUnitorIso W
              (Word.forward W (f ≫ g))).inv) :=
    Quot.sound (Presented.Rel.whisker_right_id_word
      (Cell.sourceCompInv (W := W) f g))
  rw [whiskerEquality]

/-- Generic normalization of a raw cell from the empty word to a closed
two-atomic-step word. -/
theorem normalizedCellHom_nil_twoAtoms {X Y : B}
    (first : Step W X Y) (second : Step W Y X)
    (cell : Cell W (.nil X)
      (Word.append (W := W) (.atom first) (.atom second))) :
    normalizedCellHom W cell =
      AlignedCell.quotientVcomp W
        (Presented.wordLeftUnitorIso W (.nil X)).inv
        (AlignedCell.quotientVcomp W
          (Presented.whiskerRightHom W (.nil X) (Presented.mk W cell))
          (Presented.wordAssociatorIso W
            (.atom first) (.atom second) (.nil X)).hom) := by
  unfold normalizedCellHom normalizedHom
  simp only [Word.append_eq_comp, LinearWord.flatten_append,
    LinearWord.flatten]
  rw [LinearWord.normalizationIso_nil W X]
  rw [LinearWord.normalizationIso_twoAtoms_hom W first second]
  simp only [Iso.refl_inv]
  change AlignedCell.quotientVcomp W (𝟙 (Word.nil X))
      (AlignedCell.quotientVcomp W (Presented.mk W cell)
        (AlignedCell.quotientVcomp W
          (Presented.wordRightUnitorIso W
            (.comp (.atom first) (.atom second))).inv
          (Presented.wordAssociatorIso W
            (.atom first) (.atom second) (.nil X)).hom)) =
    AlignedCell.quotientVcomp W
      (Presented.wordLeftUnitorIso W (.nil X)).inv
      (AlignedCell.quotientVcomp W
        (Presented.whiskerRightHom W (.nil X) (Presented.mk W cell))
        (Presented.wordAssociatorIso W
          (.atom first) (.atom second) (.nil X)).hom)
  rw [AlignedCell.quotientVcomp_id_comp]
  have whiskerEquality :
      Presented.whiskerRightHom W (.nil X) (Presented.mk W cell) =
        AlignedCell.quotientVcomp W
          (Presented.wordRightUnitorIso W (.nil X)).hom
          (AlignedCell.quotientVcomp W (Presented.mk W cell)
            (Presented.wordRightUnitorIso W
              (Word.append (W := W) (.atom first) (.atom second))).inv) :=
    Quot.sound (Presented.Rel.whisker_right_id_word cell)
  rw [whiskerEquality]
  simp only [AlignedCell.quotientVcomp_assoc]
  rw [← AlignedCell.quotientVcomp_assoc W
    (Presented.wordLeftUnitorIso W (.nil X)).inv
    (Presented.wordRightUnitorIso W (.nil X)).hom]
  have unitCancellation :
      AlignedCell.quotientVcomp W
          (Presented.wordLeftUnitorIso W (.nil X)).inv
          (Presented.wordRightUnitorIso W (.nil X)).hom =
        𝟙 (Word.nil X) := by
    change (λ_ (𝟙 (⟨X⟩ : Presented.Localization W))).inv ≫
      (ρ_ (𝟙 (⟨X⟩ : Presented.Localization W))).hom = _
    rw [unitors_inv_equal]
    exact (Presented.wordRightUnitorIso W (.nil X)).inv_hom_id
  rw [unitCancellation, AlignedCell.quotientVcomp_id_comp]
  rfl

/-- Generic normalization of a raw cell from a closed two-atomic-step word
to the empty word. -/
theorem normalizedCellHom_twoAtoms_nil {X Y : B}
    (first : Step W X Y) (second : Step W Y X)
    (cell : Cell W
      (Word.append (W := W) (.atom first) (.atom second)) (.nil X)) :
    normalizedCellHom W cell =
      AlignedCell.quotientVcomp W
        (Presented.wordAssociatorIso W
          (.atom first) (.atom second) (.nil X)).inv
        (AlignedCell.quotientVcomp W
          (Presented.whiskerRightHom W (.nil X) (Presented.mk W cell))
          (Presented.wordLeftUnitorIso W (.nil X)).hom) := by
  unfold normalizedCellHom normalizedHom
  simp only [Word.append_eq_comp, LinearWord.flatten_append,
    LinearWord.flatten]
  rw [LinearWord.normalizationIso_twoAtoms_inv W first second]
  rw [LinearWord.normalizationIso_nil W X]
  simp only [Iso.refl_hom]
  change AlignedCell.quotientVcomp W
      (AlignedCell.quotientVcomp W
        (Presented.wordAssociatorIso W
          (.atom first) (.atom second) (.nil X)).inv
        (Presented.wordRightUnitorIso W
          (Word.append (W := W) (.atom first) (.atom second))).hom)
      (AlignedCell.quotientVcomp W (Presented.mk W cell) (𝟙 (Word.nil X))) =
    AlignedCell.quotientVcomp W
      (Presented.wordAssociatorIso W
        (.atom first) (.atom second) (.nil X)).inv
      (AlignedCell.quotientVcomp W
        (Presented.whiskerRightHom W (.nil X) (Presented.mk W cell))
        (Presented.wordLeftUnitorIso W (.nil X)).hom)
  rw [AlignedCell.quotientVcomp_comp_id]
  rw [AlignedCell.quotientVcomp_assoc]
  have whiskerEquality :
      Presented.whiskerRightHom W (.nil X) (Presented.mk W cell) =
        AlignedCell.quotientVcomp W
          (Presented.wordRightUnitorIso W
            (Word.append (W := W) (.atom first) (.atom second))).hom
          (AlignedCell.quotientVcomp W (Presented.mk W cell)
            (Presented.wordRightUnitorIso W (.nil X)).inv) :=
    Quot.sound (Presented.Rel.whisker_right_id_word cell)
  rw [whiskerEquality]
  rw [AlignedCell.quotientVcomp_assoc W
    (Presented.wordRightUnitorIso W
      (Word.append (W := W) (.atom first) (.atom second))).hom
    (AlignedCell.quotientVcomp W (Presented.mk W cell)
      (Presented.wordRightUnitorIso W (.nil X)).inv)
    (Presented.wordLeftUnitorIso W (.nil X)).hom]
  rw [AlignedCell.quotientVcomp_assoc W
    (Presented.mk W cell)
    (Presented.wordRightUnitorIso W (.nil X)).inv
    (Presented.wordLeftUnitorIso W (.nil X)).hom]
  have unitCancellation :
      AlignedCell.quotientVcomp W
          (Presented.wordRightUnitorIso W (.nil X)).inv
          (Presented.wordLeftUnitorIso W (.nil X)).hom =
        𝟙 (Word.nil X) := by
    change (ρ_ (𝟙 (⟨X⟩ : Presented.Localization W))).inv ≫
      (λ_ (𝟙 (⟨X⟩ : Presented.Localization W))).hom = _
    rw [← unitors_inv_equal]
    exact (Presented.wordLeftUnitorIso W (.nil X)).inv_hom_id
  rw [unitCancellation, AlignedCell.quotientVcomp_comp_id]

/-- Marked unit normalizes to executable insertion of its forward/reverse
pair. -/
@[simp]
theorem normalizedCellHom_markedUnit {X Y : B}
    (f : X ⟶ Y) (hf : W f) :
    normalizedCellHom W (Cell.markedUnit (W := W) f hf) =
      ColumnRefinement.toHom W (.insertMarkedUnitPair f hf (.nil X)) := by
  change normalizedCellHom W (Cell.markedUnit (W := W) f hf) =
    AlignedCell.quotientVcomp W
      (Presented.wordLeftUnitorIso W (.nil X)).inv
      (AlignedCell.quotientVcomp W
        (Presented.whiskerRightHom W (.nil X)
          (Presented.mk W (Cell.markedUnit (W := W) f hf)))
        (Presented.wordAssociatorIso W (Word.forward W f)
          (Word.backward W f hf) (.nil X)).hom)
  exact normalizedCellHom_nil_twoAtoms W
    (.forward f) (.backward f hf) (.markedUnit f hf)

/-- Inverse marked unit normalizes to executable deletion of its
forward/reverse pair. -/
@[simp]
theorem normalizedCellHom_markedUnitInv {X Y : B}
    (f : X ⟶ Y) (hf : W f) :
    normalizedCellHom W (Cell.markedUnitInv (W := W) f hf) =
      ColumnRefinement.toHom W (.deleteMarkedUnitPair f hf (.nil X)) := by
  change normalizedCellHom W (Cell.markedUnitInv (W := W) f hf) =
    AlignedCell.quotientVcomp W
      (Presented.wordAssociatorIso W (Word.forward W f)
        (Word.backward W f hf) (.nil X)).inv
      (AlignedCell.quotientVcomp W
        (Presented.whiskerRightHom W (.nil X)
          (Presented.mk W (Cell.markedUnitInv (W := W) f hf)))
        (Presented.wordLeftUnitorIso W (.nil X)).hom)
  exact normalizedCellHom_twoAtoms_nil W
    (.forward f) (.backward f hf) (.markedUnitInv f hf)

/-- Marked counit normalizes to executable deletion of its reverse/forward
pair. -/
@[simp]
theorem normalizedCellHom_markedCounit {X Y : B}
    (f : X ⟶ Y) (hf : W f) :
    normalizedCellHom W (Cell.markedCounit (W := W) f hf) =
      ColumnRefinement.toHom W (.deleteMarkedCounitPair f hf (.nil Y)) := by
  change normalizedCellHom W (Cell.markedCounit (W := W) f hf) =
    AlignedCell.quotientVcomp W
      (Presented.wordAssociatorIso W (Word.backward W f hf)
        (Word.forward W f) (.nil Y)).inv
      (AlignedCell.quotientVcomp W
        (Presented.whiskerRightHom W (.nil Y)
          (Presented.mk W (Cell.markedCounit (W := W) f hf)))
        (Presented.wordLeftUnitorIso W (.nil Y)).hom)
  exact normalizedCellHom_twoAtoms_nil W
    (.backward f hf) (.forward f) (.markedCounit f hf)

/-- Inverse marked counit normalizes to executable insertion of its
reverse/forward pair. -/
@[simp]
theorem normalizedCellHom_markedCounitInv {X Y : B}
    (f : X ⟶ Y) (hf : W f) :
    normalizedCellHom W (Cell.markedCounitInv (W := W) f hf) =
      ColumnRefinement.toHom W (.insertMarkedCounitPair f hf (.nil Y)) := by
  change normalizedCellHom W (Cell.markedCounitInv (W := W) f hf) =
    AlignedCell.quotientVcomp W
      (Presented.wordLeftUnitorIso W (.nil Y)).inv
      (AlignedCell.quotientVcomp W
        (Presented.whiskerRightHom W (.nil Y)
          (Presented.mk W (Cell.markedCounitInv (W := W) f hf)))
        (Presented.wordAssociatorIso W (Word.backward W f hf)
          (Word.forward W f) (.nil Y)).hom)
  exact normalizedCellHom_nil_twoAtoms W
    (.backward f hf) (.forward f) (.markedCounitInv f hf)

/-- Raw left unitor normalizes to the identity of the linear normal form. -/
@[simp]
theorem normalizedCellHom_leftUnitor {X Y : B} (word : Word W X Y) :
    normalizedCellHom W (Cell.leftUnitor (W := W) word) =
      𝟙 (LinearWord.toWord W (LinearWord.flatten W word)) := by
  unfold normalizedCellHom normalizedHom
  simp only [Word.append_eq_comp, LinearWord.flatten_append]
  rw [LinearWord.normalizationIso_append W (.nil X) word]
  rw [LinearWord.normalizationIso_nil W X]
  simp only [LinearWord.flatten_nil]
  rw [LinearWord.toWordAppendIso_nil W (LinearWord.flatten W word)]
  simp only [Iso.trans_inv]
  unfold LinearWord.appendIso
  simp only [Iso.trans_inv, Bicategory.whiskerLeftIso,
    Bicategory.whiskerRightIso, LinearWord.toWord_nil]
  let iso := LinearWord.normalizationIso W word
  let target := LinearWord.toWord W (LinearWord.flatten W word)
  change AlignedCell.quotientVcomp W
      (AlignedCell.quotientVcomp W
        (Presented.wordLeftUnitorIso W target).inv
        (AlignedCell.quotientVcomp W
          (Presented.whiskerLeftHom W (.nil X) iso.inv)
          (Presented.whiskerRightHom W word (𝟙 (Word.nil X)))))
      (AlignedCell.quotientVcomp W
        (Presented.wordLeftUnitorIso W word).hom iso.hom) =
    𝟙 target
  have whiskerIdentity :
      Presented.whiskerRightHom W word (𝟙 (Word.nil X)) =
        𝟙 (Word.append (W := W) (.nil X) word) :=
    Quot.sound (Presented.Rel.whisker_right_id (.nil X) word)
  rw [whiskerIdentity, AlignedCell.quotientVcomp_comp_id]
  simp only [AlignedCell.quotientVcomp_assoc]
  exact LinearWord.leftUnitor_conjugation
    (C := Presented.Localization W) iso

/-- Raw inverse left unitor also normalizes to identity. -/
@[simp]
theorem normalizedCellHom_leftUnitorInv {X Y : B} (word : Word W X Y) :
    normalizedCellHom W (Cell.leftUnitorInv (W := W) word) =
      𝟙 (LinearWord.toWord W (LinearWord.flatten W word)) := by
  have relationEquality := normalizedCellHom_eq_of_rel W
    (Presented.Rel.left_unitor_inv_hom (W := W) word)
  rw [normalizedCellHom_vcomp, normalizedCellHom_leftUnitor,
    normalizedCellHom_id] at relationEquality
  exact (AlignedCell.quotientVcomp_comp_id W _).symm.trans relationEquality

/-- Raw associator normalizes to the recursive canonical linear associator
path comparison. -/
@[simp]
theorem normalizedCellHom_associator {X Y Z T : B}
    (first : Word W X Y) (second : Word W Y Z)
    (third : Word W Z T) :
    normalizedCellHom W
        (Cell.associator (W := W) first second third) =
      toHom W (associatorPath W (LinearWord.flatten W first)
        (LinearWord.flatten W second) (LinearWord.flatten W third)) := by
  rw [toHom_associatorPath]
  unfold normalizedCellHom normalizedHom
  change ((LinearWord.appendIso W
      (LinearWord.appendIso W (LinearWord.normalizationIso W first)
          (LinearWord.normalizationIso W second) ≪≫
        (LinearWord.toWordAppendIso W (LinearWord.flatten W first)
          (LinearWord.flatten W second)).symm)
      (LinearWord.normalizationIso W third) ≪≫
    (LinearWord.toWordAppendIso W
      (LinearWord.append W (LinearWord.flatten W first)
        (LinearWord.flatten W second))
      (LinearWord.flatten W third)).symm).inv ≫
    (Presented.wordAssociatorIso W first second third).hom ≫
    (LinearWord.appendIso W (LinearWord.normalizationIso W first)
      (LinearWord.appendIso W (LinearWord.normalizationIso W second)
          (LinearWord.normalizationIso W third) ≪≫
        (LinearWord.toWordAppendIso W (LinearWord.flatten W second)
          (LinearWord.flatten W third)).symm) ≪≫
      (LinearWord.toWordAppendIso W (LinearWord.flatten W first)
        (LinearWord.append W (LinearWord.flatten W second)
          (LinearWord.flatten W third))).symm).hom) = _
  unfold LinearWord.associatorIso
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv]
  let sourceComparison := LinearWord.toWordAppendIso W
    (LinearWord.append W (LinearWord.flatten W first)
      (LinearWord.flatten W second)) (LinearWord.flatten W third)
  let targetComparison := LinearWord.toWordAppendIso W
    (LinearWord.flatten W first)
    (LinearWord.append W (LinearWord.flatten W second)
      (LinearWord.flatten W third))
  simp only [Category.assoc]
  rw [cancel_epi sourceComparison.hom]
  simp only [← Category.assoc]
  rw [cancel_mono targetComparison.inv]
  convert LinearWord.appendIso_associator_normalization W
      (LinearWord.normalizationIso W first)
      (LinearWord.normalizationIso W second)
      (LinearWord.normalizationIso W third)
      (LinearWord.toWordAppendIso W (LinearWord.flatten W first)
        (LinearWord.flatten W second))
      (LinearWord.toWordAppendIso W (LinearWord.flatten W second)
        (LinearWord.flatten W third)) using 1 <;>
    simp only [Category.assoc] <;> rfl

/-- Raw inverse associator normalizes to the inverse recursive canonical
linear associator path. -/
@[simp]
theorem normalizedCellHom_associatorInv {X Y Z T : B}
    (first : Word W X Y) (second : Word W Y Z)
    (third : Word W Z T) :
    normalizedCellHom W
        (Cell.associatorInv (W := W) first second third) =
      toHom W (associatorPathInv W (LinearWord.flatten W first)
        (LinearWord.flatten W second) (LinearWord.flatten W third)) := by
  let firstRow := LinearWord.flatten W first
  let secondRow := LinearWord.flatten W second
  let thirdRow := LinearWord.flatten W third
  let leftRow := LinearWord.append W
    (LinearWord.append W firstRow secondRow) thirdRow
  let rightRow := LinearWord.append W firstRow
    (LinearWord.append W secondRow thirdRow)
  let forward : Presented.Hom W
      (LinearWord.toWord W leftRow) (LinearWord.toWord W rightRow) :=
    toHom W (associatorPath W firstRow secondRow thirdRow)
  let inverse : Presented.Hom W
      (LinearWord.toWord W rightRow) (LinearWord.toWord W leftRow) :=
    toHom W (associatorPathInv W firstRow secondRow thirdRow)
  let candidate : Presented.Hom W
      (LinearWord.toWord W rightRow) (LinearWord.toWord W leftRow) :=
    normalizedCellHom W
      (Cell.associatorInv (W := W) first second third)
  have forwardInverse :
      forward ≫ inverse = 𝟙 (LinearWord.toWord W leftRow) := by
    exact associatorPath_hom_inv W firstRow secondRow thirdRow
  have relationEquality :
      candidate ≫ forward = 𝟙 (LinearWord.toWord W rightRow) := by
    have equality := normalizedCellHom_eq_of_rel W
      (Presented.Rel.associator_inv_hom (W := W) first second third)
    rw [normalizedCellHom_vcomp, normalizedCellHom_associator,
      normalizedCellHom_id] at equality
    exact equality
  change candidate = inverse
  calc
    candidate = candidate ≫ 𝟙 (LinearWord.toWord W leftRow) := by
      exact (AlignedCell.quotientVcomp_comp_id W candidate).symm
    _ = candidate ≫ (forward ≫ inverse) := by
      rw [forwardInverse]
    _ = (candidate ≫ forward) ≫ inverse := (Category.assoc _ _ _).symm
    _ = 𝟙 (LinearWord.toWord W rightRow) ≫ inverse := by
      rw [relationEquality]
    _ = inverse := AlignedCell.quotientVcomp_id_comp W inverse

/-- Raw right unitor normalizes to the recursive generated path deleting the
terminal empty row. -/
@[simp]
theorem normalizedCellHom_rightUnitor {X Y : B} (word : Word W X Y) :
    normalizedCellHom W (Cell.rightUnitor (W := W) word) =
      toHom W (rightUnitPath W (LinearWord.flatten W word)) := by
  unfold normalizedCellHom normalizedHom
  simp only [Word.append_eq_comp, LinearWord.flatten_append]
  rw [LinearWord.normalizationIso_append W word (.nil Y)]
  rw [LinearWord.normalizationIso_nil W Y]
  simp only [LinearWord.flatten_nil, Iso.trans_inv, Iso.symm_inv]
  unfold LinearWord.appendIso
  simp only [Iso.trans_inv, Bicategory.whiskerLeftIso,
    Bicategory.whiskerRightIso]
  let iso := LinearWord.normalizationIso W word
  let comparison := LinearWord.toWordAppendIso W
    (LinearWord.flatten W word) (.nil Y)
  change AlignedCell.quotientVcomp W
      (AlignedCell.quotientVcomp W comparison.hom
        (AlignedCell.quotientVcomp W
          (Presented.whiskerLeftHom W
            (LinearWord.toWord W (LinearWord.flatten W word))
            (𝟙 (LinearWord.toWord W (.nil Y))))
          (Presented.whiskerRightHom W
            (LinearWord.toWord W (.nil Y)) iso.inv)))
      (AlignedCell.quotientVcomp W
        (Presented.wordRightUnitorIso W word).hom iso.hom) =
    toHom W (rightUnitPath W (LinearWord.flatten W word))
  have leftIdentity :
      Presented.whiskerLeftHom W
          (LinearWord.toWord W (LinearWord.flatten W word))
          (𝟙 (LinearWord.toWord W (.nil Y))) =
        𝟙 (Word.append (W := W)
          (LinearWord.toWord W (LinearWord.flatten W word))
          (LinearWord.toWord W (.nil Y))) :=
    Quot.sound (Presented.Rel.whisker_left_id
      (LinearWord.toWord W (LinearWord.flatten W word))
      (LinearWord.toWord W (.nil Y)))
  rw [leftIdentity, AlignedCell.quotientVcomp_id_comp]
  simp only [AlignedCell.quotientVcomp_assoc]
  have conjugation :
      AlignedCell.quotientVcomp W
          (Presented.whiskerRightHom W
            (LinearWord.toWord W (.nil Y)) iso.inv)
          (AlignedCell.quotientVcomp W
            (Presented.wordRightUnitorIso W word).hom iso.hom) =
        (Presented.wordRightUnitorIso W
          (LinearWord.toWord W (LinearWord.flatten W word))).hom := by
    change (iso.inv ▷ 𝟙 (⟨Y⟩ : Presented.Localization W)) ≫
      (ρ_ word).hom ≫ iso.hom = _
    exact LinearWord.rightUnitor_conjugation
      (C := Presented.Localization W) iso
  rw [conjugation]
  exact (toHom_rightUnitPath W (LinearWord.flatten W word)).symm

/-- Raw inverse right unitor normalizes to the inverse recursive generated
path inserting a terminal empty row. -/
@[simp]
theorem normalizedCellHom_rightUnitorInv {X Y : B} (word : Word W X Y) :
    normalizedCellHom W (Cell.rightUnitorInv (W := W) word) =
      toHom W (rightUnitPathInv W (LinearWord.flatten W word)) := by
  let row := LinearWord.flatten W word
  let forward := toHom W (rightUnitPath W row)
  let inverse := toHom W (rightUnitPathInv W row)
  let candidate : Presented.Hom W
      (LinearWord.toWord W row)
      (LinearWord.toWord W (LinearWord.append W row (.nil Y))) :=
    normalizedCellHom W (Cell.rightUnitorInv (W := W) word)
  have forwardInverse :
      forward ≫ inverse =
        𝟙 (LinearWord.toWord W (LinearWord.append W row (.nil Y))) := by
    exact rightUnitPath_hom_inv W row
  have relationEquality :
      candidate ≫ forward =
        𝟙 (LinearWord.toWord W row) := by
    have equality := normalizedCellHom_eq_of_rel W
      (Presented.Rel.right_unitor_inv_hom (W := W) word)
    rw [normalizedCellHom_vcomp, normalizedCellHom_rightUnitor,
      normalizedCellHom_id] at equality
    exact equality
  change candidate = inverse
  calc
    candidate = candidate ≫
        𝟙 (LinearWord.toWord W
          (LinearWord.append W row (.nil Y))) := by
      exact (AlignedCell.quotientVcomp_comp_id W candidate).symm
    _ = candidate ≫ (forward ≫ inverse) := by
      rw [forwardInverse]
    _ = (candidate ≫ forward) ≫ inverse := (Category.assoc _ _ _).symm
    _ = 𝟙 (LinearWord.toWord W row) ≫ inverse := by
      rw [relationEquality]
    _ = inverse := AlignedCell.quotientVcomp_id_comp W inverse

/-- Equality transport does not change normalized quotient semantics. -/
@[simp]
theorem normalizedCellHom_transport {X Y : B}
    {first second first' second' : Word W X Y}
    (sourceEquality : first = first') (targetEquality : second = second')
    (cell : Cell W first second) :
    normalizedCellHom W (.transport sourceEquality targetEquality cell) =
      sourceEquality ▸ targetEquality ▸ normalizedCellHom W cell := by
  subst first'
  subst second'
  unfold normalizedCellHom
  have transportEquality :
      Presented.mk W (Cell.transport (W := W) rfl rfl cell) =
        Presented.mk W cell :=
    Quot.sound (Presented.Rel.transport_refl cell)
  rw [transportEquality]

/-- One-step linear row representing a source 1-cell. -/
def forwardRow {X Y : B} (f : X ⟶ Y) : LinearWord W X Y :=
  .cons (.forward f) (.nil Y)

/-- One-column aligned representative of an arbitrary source 2-cell. -/
def originalAlignedCell {X Y : B} {f g : X ⟶ Y} (alpha : f ⟶ g) :
    AlignedCell W (forwardRow W f) (forwardRow W g) :=
  .cons (.original alpha) (.nil Y)

/-- The aligned one-column interpretation is the original source 2-cell
conjugated by the canonical right-unitors of the linear one-step rows. -/
theorem originalAlignedCell_toHom {X Y : B} {f g : X ⟶ Y}
    (alpha : f ⟶ g) :
    AlignedCell.toHom W (originalAlignedCell W alpha) =
      AlignedCell.quotientVcomp W
        (Presented.wordRightUnitorIso W (Word.forward W f)).hom
        (AlignedCell.quotientVcomp W
          (Presented.mk W (Cell.original (W := W) alpha))
          (Presented.wordRightUnitorIso W (Word.forward W g)).inv) := by
  change AlignedCell.quotientVcomp W
      (Presented.whiskerRightHom W (.nil Y)
        (Presented.mk W (Cell.original (W := W) alpha)))
      (Presented.whiskerLeftHom W (Word.forward W g)
        (Presented.mk W (Cell.id (.nil Y)))) = _
  have leftIdentity :
      Presented.whiskerLeftHom W (Word.forward W g)
          (Presented.mk W (Cell.id (.nil Y))) =
        𝟙 (Word.append (W := W) (Word.forward W g) (.nil Y)) :=
    Quot.sound (Presented.Rel.whisker_left_id
      (Word.forward W g) (.nil Y))
  rw [leftIdentity]
  have rightIdentity :
      AlignedCell.quotientVcomp W
          (Presented.whiskerRightHom W (.nil Y)
            (Presented.mk W (Cell.original (W := W) alpha)))
          (𝟙 (Word.append (W := W) (Word.forward W g) (.nil Y))) =
        Presented.whiskerRightHom W (.nil Y)
          (Presented.mk W (Cell.original (W := W) alpha)) := by
    exact @Category.comp_id (Word W X Y) (Presented.wordCategory W X Y)
      _ _ (Presented.whiskerRightHom W (.nil Y)
        (Presented.mk W (Cell.original (W := W) alpha)))
  rw [rightIdentity]
  exact Quot.sound
    (Presented.Rel.whisker_right_id_word
      (Cell.original (W := W) alpha))

/-- Every source 2-cell therefore belongs to the generated hammock semantic
image in its canonical one-column linear representation. -/
theorem originalCell_mem_semanticImage {X Y : B} {f g : X ⟶ Y}
    (alpha : f ⟶ g) :
    InSemanticImage W
      (AlignedCell.toHom W (originalAlignedCell W alpha)) :=
  aligned_mem_semanticImage W (originalAlignedCell W alpha)

/-- Normalizing an original source 2-cell recovers its canonical aligned
one-column interpretation. -/
@[simp]
theorem normalizedCellHom_original {X Y : B} {f g : X ⟶ Y}
    (alpha : f ⟶ g) :
    normalizedCellHom W (Cell.original (W := W) alpha) =
      AlignedCell.toHom W (originalAlignedCell W alpha) := by
  change AlignedCell.quotientVcomp W
      (Presented.wordRightUnitorIso W (Word.forward W f)).hom
      (AlignedCell.quotientVcomp W
        (Presented.mk W (Cell.original (W := W) alpha))
        (Presented.wordRightUnitorIso W (Word.forward W g)).inv) = _
  exact (originalAlignedCell_toHom W alpha).symm

/-- Raw identity cells are hammock-normalizable. -/
theorem identity_normalizable {X Y : B} (word : Word W X Y) :
    Normalizable W (Cell.id word) := by
  rw [Normalizable, normalizedCellHom_id]
  exact ⟨.identity (LinearWord.flatten W word), rfl⟩

/-- Vertical composites of normalizable raw cells remain normalizable. -/
theorem vcomp_normalizable {X Y : B}
    {first middle last : Word W X Y}
    {alpha : Cell W first middle} {beta : Cell W middle last}
    (hAlpha : Normalizable W alpha) (hBeta : Normalizable W beta) :
    Normalizable W (.vcomp alpha beta) := by
  rw [Normalizable, normalizedCellHom_vcomp]
  exact vcomp_mem_semanticImage W hAlpha hBeta

/-- Left whiskering preserves raw-cell normalizability. -/
theorem whiskerLeft_normalizable {X Y Z : B}
    (pre : Word W X Y) {first second : Word W Y Z}
    {cell : Cell W first second} (member : Normalizable W cell) :
    Normalizable W (.whiskerLeft pre cell) := by
  rw [Normalizable, normalizedCellHom_whiskerLeft]
  exact whiskerLeft_mem_semanticImage W (LinearWord.flatten W pre) member

/-- Right whiskering preserves raw-cell normalizability. -/
theorem whiskerRight_normalizable {X Y Z : B}
    {first second : Word W X Y} {cell : Cell W first second}
    (member : Normalizable W cell) (post : Word W Y Z) :
    Normalizable W (.whiskerRight cell post) := by
  rw [Normalizable, normalizedCellHom_whiskerRight]
  exact whiskerRight_mem_semanticImage W (LinearWord.flatten W post) member

/-- The source-identity comparison is hammock-normalizable. -/
theorem sourceId_normalizable {X : B} :
    Normalizable W (Cell.sourceId (W := W) (X := X)) := by
  rw [Normalizable, normalizedCellHom_sourceId]
  exact refinement_mem_semanticImage W (.deleteIdentity (.nil X))

/-- The inverse source-identity comparison is hammock-normalizable. -/
theorem sourceIdInv_normalizable {X : B} :
    Normalizable W (Cell.sourceIdInv (W := W) (X := X)) := by
  rw [Normalizable, normalizedCellHom_sourceIdInv]
  exact refinement_mem_semanticImage W (.insertIdentity (.nil X))

/-- Source-composition comparison is hammock-normalizable. -/
theorem sourceComp_normalizable {X Y Z : B}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Normalizable W (Cell.sourceComp (W := W) f g) := by
  rw [Normalizable, normalizedCellHom_sourceComp]
  exact refinement_mem_semanticImage W (.expandForward f g (.nil Z))

/-- Inverse source-composition comparison is hammock-normalizable. -/
theorem sourceCompInv_normalizable {X Y Z : B}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Normalizable W (Cell.sourceCompInv (W := W) f g) := by
  rw [Normalizable, normalizedCellHom_sourceCompInv]
  exact refinement_mem_semanticImage W (.contractForward f g (.nil Z))

/-- Marked unit is hammock-normalizable. -/
theorem markedUnit_normalizable {X Y : B}
    (f : X ⟶ Y) (hf : W f) :
    Normalizable W (Cell.markedUnit (W := W) f hf) := by
  rw [Normalizable, normalizedCellHom_markedUnit]
  exact refinement_mem_semanticImage W (.insertMarkedUnitPair f hf (.nil X))

/-- Inverse marked unit is hammock-normalizable. -/
theorem markedUnitInv_normalizable {X Y : B}
    (f : X ⟶ Y) (hf : W f) :
    Normalizable W (Cell.markedUnitInv (W := W) f hf) := by
  rw [Normalizable, normalizedCellHom_markedUnitInv]
  exact refinement_mem_semanticImage W (.deleteMarkedUnitPair f hf (.nil X))

/-- Marked counit is hammock-normalizable. -/
theorem markedCounit_normalizable {X Y : B}
    (f : X ⟶ Y) (hf : W f) :
    Normalizable W (Cell.markedCounit (W := W) f hf) := by
  rw [Normalizable, normalizedCellHom_markedCounit]
  exact refinement_mem_semanticImage W (.deleteMarkedCounitPair f hf (.nil Y))

/-- Inverse marked counit is hammock-normalizable. -/
theorem markedCounitInv_normalizable {X Y : B}
    (f : X ⟶ Y) (hf : W f) :
    Normalizable W (Cell.markedCounitInv (W := W) f hf) := by
  rw [Normalizable, normalizedCellHom_markedCounitInv]
  exact refinement_mem_semanticImage W (.insertMarkedCounitPair f hf (.nil Y))

/-- Left unitor is hammock-normalizable. -/
theorem leftUnitor_normalizable {X Y : B} (word : Word W X Y) :
    Normalizable W (Cell.leftUnitor (W := W) word) := by
  rw [Normalizable, normalizedCellHom_leftUnitor]
  exact ⟨.identity (LinearWord.flatten W word), rfl⟩

/-- Inverse left unitor is hammock-normalizable. -/
theorem leftUnitorInv_normalizable {X Y : B} (word : Word W X Y) :
    Normalizable W (Cell.leftUnitorInv (W := W) word) := by
  rw [Normalizable, normalizedCellHom_leftUnitorInv]
  exact ⟨.identity (LinearWord.flatten W word), rfl⟩

/-- Right unitor is hammock-normalizable by the recursive terminal-empty-row
deletion path. -/
theorem rightUnitor_normalizable {X Y : B} (word : Word W X Y) :
    Normalizable W (Cell.rightUnitor (W := W) word) := by
  rw [Normalizable, normalizedCellHom_rightUnitor]
  exact ⟨rightUnitPath W (LinearWord.flatten W word), rfl⟩

/-- Inverse right unitor is hammock-normalizable by the recursive
terminal-empty-row insertion path. -/
theorem rightUnitorInv_normalizable {X Y : B} (word : Word W X Y) :
    Normalizable W (Cell.rightUnitorInv (W := W) word) := by
  rw [Normalizable, normalizedCellHom_rightUnitorInv]
  exact ⟨rightUnitPathInv W (LinearWord.flatten W word), rfl⟩

/-- Associator is hammock-normalizable by the recursive linear associator
path. -/
theorem associator_normalizable {X Y Z T : B}
    (first : Word W X Y) (second : Word W Y Z)
    (third : Word W Z T) :
    Normalizable W (Cell.associator (W := W) first second third) := by
  rw [Normalizable, normalizedCellHom_associator]
  exact ⟨associatorPath W (LinearWord.flatten W first)
    (LinearWord.flatten W second) (LinearWord.flatten W third), rfl⟩

/-- Inverse associator is hammock-normalizable by the inverse recursive linear
associator path. -/
theorem associatorInv_normalizable {X Y Z T : B}
    (first : Word W X Y) (second : Word W Y Z)
    (third : Word W Z T) :
    Normalizable W (Cell.associatorInv (W := W) first second third) := by
  rw [Normalizable, normalizedCellHom_associatorInv]
  exact ⟨associatorPathInv W (LinearWord.flatten W first)
    (LinearWord.flatten W second) (LinearWord.flatten W third), rfl⟩

/-- Equality transport preserves raw-cell normalizability. -/
theorem transport_normalizable {X Y : B}
    {first second first' second' : Word W X Y}
    (sourceEquality : first = first') (targetEquality : second = second')
    {cell : Cell W first second} (member : Normalizable W cell) :
    Normalizable W (.transport sourceEquality targetEquality cell) := by
  subst first'
  subst second'
  rw [Normalizable, normalizedCellHom_transport]
  exact member

/-- Every raw presented cell is hammock-normalizable. This is the unconditional
structural induction: all generators, both whiskerings, vertical composition,
and equality transport have explicit generated-path witnesses. -/
theorem allCells_normalizable :
    ∀ {X Y : B} {first second : Word W X Y}
      (cell : Cell W first second), Normalizable W cell := by
  intro X Y first second cell
  induction cell with
  | id word => exact identity_normalizable W word
  | vcomp alpha beta hAlpha hBeta =>
      exact vcomp_normalizable W hAlpha hBeta
  | original alpha =>
      rw [Normalizable, normalizedCellHom_original]
      exact originalCell_mem_semanticImage W alpha
  | sourceId => exact sourceId_normalizable W
  | sourceIdInv => exact sourceIdInv_normalizable W
  | sourceComp f g => exact sourceComp_normalizable W f g
  | sourceCompInv f g => exact sourceCompInv_normalizable W f g
  | markedUnit f hf => exact markedUnit_normalizable W f hf
  | markedUnitInv f hf => exact markedUnitInv_normalizable W f hf
  | markedCounit f hf => exact markedCounit_normalizable W f hf
  | markedCounitInv f hf => exact markedCounitInv_normalizable W f hf
  | whiskerLeft pre cell member =>
      exact whiskerLeft_normalizable W pre member
  | whiskerRight cell post member =>
      exact whiskerRight_normalizable W member post
  | associator first second third =>
      exact associator_normalizable W first second third
  | associatorInv first second third =>
      exact associatorInv_normalizable W first second third
  | leftUnitor word => exact leftUnitor_normalizable W word
  | leftUnitorInv word => exact leftUnitorInv_normalizable W word
  | rightUnitor word => exact rightUnitor_normalizable W word
  | rightUnitorInv word => exact rightUnitorInv_normalizable W word
  | transport sourceEquality targetEquality cell member =>
      exact transport_normalizable W sourceEquality targetEquality member

/-- Every quotient 2-cell between binary expansions of linear rows is in the
generated hammock semantic image. The representative is first conjugated so
that raw-cell normalization recovers the requested morphism exactly; equality
paths then transport the flattened endpoints back to the original rows. -/
theorem all_mem_semanticImage {X Y : B}
    {first second : LinearWord W X Y}
    (alpha : Presented.Hom W (LinearWord.toWord W first)
      (LinearWord.toWord W second)) :
    InSemanticImage W alpha := by
  let firstEquality := LinearWord.flatten_toWord W first
  let secondEquality := LinearWord.flatten_toWord W second
  let alphaNormalized : Presented.Hom W
      (LinearWord.toWord W
        (LinearWord.flatten W (LinearWord.toWord W first)))
      (LinearWord.toWord W
        (LinearWord.flatten W (LinearWord.toWord W second))) :=
    eqToHom (congrArg (LinearWord.toWord W) firstEquality) ≫ alpha ≫
      eqToHom (congrArg (LinearWord.toWord W) secondEquality).symm
  let beta : Presented.Hom W (LinearWord.toWord W first)
      (LinearWord.toWord W second) :=
    (LinearWord.normalizationIso W (LinearWord.toWord W first)).hom ≫
      alphaNormalized ≫
      (LinearWord.normalizationIso W (LinearWord.toWord W second)).inv
  rcases Quot.exists_rep beta with ⟨cell, cellEquality⟩
  change Presented.mk W cell = beta at cellEquality
  have member := allCells_normalizable W cell
  have normalizedEquality :
      normalizedCellHom W cell = alphaNormalized := by
    unfold normalizedCellHom normalizedHom
    rw [cellEquality]
    dsimp only [beta]
    change (LinearWord.normalizationIso W
        (LinearWord.toWord W first)).inv ≫
      ((LinearWord.normalizationIso W (LinearWord.toWord W first)).hom ≫
        alphaNormalized ≫
        (LinearWord.normalizationIso W (LinearWord.toWord W second)).inv) ≫
      (LinearWord.normalizationIso W (LinearWord.toWord W second)).hom =
      alphaNormalized
    simp
  change InSemanticImage W (normalizedCellHom W cell) at member
  rw [normalizedEquality] at member
  rcases member with ⟨path, pathEquality⟩
  refine ⟨.vcomp (ofEq W firstEquality.symm)
    (.vcomp path (ofEq W secondEquality)), ?_⟩
  simp only [toHom_vcomp, toHom_ofEq]
  rw [pathEquality]
  dsimp only [alphaNormalized]
  rw [castIdentity_eqToHom W firstEquality.symm]
  rw [castIdentity_eqToHom W secondEquality]
  change eqToHom (congrArg (LinearWord.toWord W) firstEquality).symm ≫
      ((eqToHom (congrArg (LinearWord.toWord W) firstEquality) ≫ alpha ≫
        eqToHom (congrArg (LinearWord.toWord W) secondEquality).symm) ≫
      eqToHom (congrArg (LinearWord.toWord W) secondEquality)) = alpha
  simp

instance semanticFunctor_full (X Y : B) :
    (semanticFunctor W X Y).Full where
  map_surjective alpha :=
    (inSemanticImage_iff_exists_map W alpha).mp
      (all_mem_semanticImage W alpha)

instance semanticFunctor_isEquivalence (X Y : B) :
    (semanticFunctor W X Y).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := inferInstance

/-- The generated hammock-path category is categorically equivalent to the
entire linear mapping category, not merely to a refinement-generated image. -/
noncomputable def semanticEquivalence (X Y : B) :
    HammockPathObject W X Y ≌ LinearWord W X Y :=
  (semanticFunctor W X Y).asEquivalence

/-- Original source 2-cells are hammock-normalizable. -/
theorem original_normalizable {X Y : B} {f g : X ⟶ Y}
    (alpha : f ⟶ g) :
    Normalizable W (Cell.original (W := W) alpha) := by
  rw [Normalizable, normalizedCellHom_original]
  exact originalCell_mem_semanticImage W alpha

end HammockPath

end CategoryTheory.Bicategory.MarkedZigzag
