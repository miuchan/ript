import Ript.ForMathlib.CategoryTheory.Bicategory.MarkedZigzagLinearHammock

/-!
# Column-aligned hammocks for marked bicategories

This file refines the linear marked-zigzag object model by making horizontal
columns explicit.  An `AlignedCell` consists of one raw atomic 2-cell in every
column between two linear words with the same intermediate objects.  Columns
append horizontally, compose vertically componentwise, and interpret as one
quotient 2-cell in the existing linear mapping category.

This is the aligned multi-column fragment of a hammock presentation.  It does
not yet identify grids up to insertion, deletion, or common refinement of
columns, and therefore is not by itself the classical Dwyer--Kan hammock
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

/-- Horizontal concatenation of aligned hammocks. -/
noncomputable def append {X Y Z : B}
    {firstSource firstTarget : LinearWord W X Y}
    {secondSource secondTarget : LinearWord W Y Z}
    (first : AlignedCell W firstSource firstTarget)
    (second : AlignedCell W secondSource secondTarget) :
    AlignedCell W (LinearWord.append W firstSource secondSource)
      (LinearWord.append W firstTarget secondTarget) := by
  induction first with
  | nil => exact second
  | cons column rest ih => exact .cons column (ih second)

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

end CategoryTheory.Bicategory.MarkedZigzag
