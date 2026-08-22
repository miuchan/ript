import Ript.ForMathlib.CategoryTheory.Bicategory.MarkedZigzag
import Mathlib.Tactic.CategoryTheory.Bicategory.PureCoherence

/-!
# Linear hammock words for marked bicategories

The executable marked-zigzag syntax uses binary composition trees so that
bicategorical associativity remains visible. This file constructs an
independent linear object model: a right-associated typed list of oriented
marked steps.

Linear words have executable append, conversion to binary words, and a
flattening map from binary words. Their lengths agree exactly. Bicategorical
associators and unitors provide a canonical isomorphism from every binary word
to its flattened linear normal form. Pulling the quotient 2-cell hom-sets back
along conversion makes linear words into a mapping category. The conversion
functor is faithful, full, and essentially surjective, hence an equivalence of
categories.

This supplies an independently defined linear hammock-object presentation of
the same local category. It is not yet the classical arbitrary-grid Dwyer--Kan
hammock localization.
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

/-- A right-associated typed list of oriented marked-zigzag steps. -/
inductive LinearWord : B → B → Type max u v where
  /-- Empty linear word at one object. -/
  | nil (X : B) : LinearWord X X
  /-- Prepend one oriented step to a remaining linear word. -/
  | cons {X Y Z : B} (step : Step W X Y) (rest : LinearWord Y Z) :
      LinearWord X Z

namespace LinearWord

/-- Executable concatenation of composable linear marked-zigzag words. -/
def append {X Y Z : B} :
    LinearWord W X Y → LinearWord W Y Z → LinearWord W X Z
  | .nil _, second => second
  | .cons step rest, second => .cons step (append rest second)

/-- Appending an empty row on the right returns the original linear row. -/
@[simp]
theorem append_nil {X Y : B} (word : LinearWord W X Y) :
    append W word (.nil Y) = word := by
  induction word with
  | nil => rfl
  | cons step rest ih =>
      simp only [append]
      rw [ih]

/-- Linear row append is associative. -/
theorem append_assoc {X Y Z T : B}
    (first : LinearWord W X Y) (second : LinearWord W Y Z)
    (third : LinearWord W Z T) :
    append W (append W first second) third =
      append W first (append W second third) := by
  induction first with
  | nil => rfl
  | cons step rest ih =>
      simp only [append]
      rw [ih]

/-- Convert a right-associated linear word to the binary marked-zigzag
syntax. -/
def toWord {X Y : B} : LinearWord W X Y → Word W X Y
  | .nil X => .nil X
  | .cons step rest =>
      Word.append (W := W) (.atom step) (toWord rest)

/-- The empty linear row converts to the empty binary word. -/
@[simp]
theorem toWord_nil (X : B) : toWord W (.nil X) = .nil X :=
  rfl

/-- Flatten a binary marked-zigzag composition tree to a linear word. -/
def flatten {X Y : B} : Word W X Y → LinearWord W X Y
  | .atom step => .cons step (.nil _)
  | .nil X => .nil X
  | .comp first second => append W (flatten first) (flatten second)

/-- The empty binary word flattens to the empty linear row. -/
@[simp]
theorem flatten_nil (X : B) : flatten W (.nil X) = .nil X :=
  rfl

/-- Flattening a one-step forward word gives the corresponding singleton
linear row. -/
@[simp]
theorem flatten_forward {X Y : B} (f : X ⟶ Y) :
    flatten W (Word.forward W f) =
      .cons (.forward f) (.nil Y) :=
  rfl

/-- Flattening a one-step marked reverse gives the corresponding singleton
linear row. -/
@[simp]
theorem flatten_backward {X Y : B} (f : X ⟶ Y) (hf : W f) :
    flatten W (Word.backward W f hf) =
      .cons (.backward f hf) (.nil X) :=
  rfl

/-- Flattening the binary expansion of a linear row recovers the row exactly. -/
@[simp]
theorem flatten_toWord {X Y : B} (row : LinearWord W X Y) :
    flatten W (toWord W row) = row := by
  induction row with
  | nil X => rfl
  | cons step rest ih =>
      simp only [toWord, Word.append_eq_comp, flatten, append]
      rw [ih]

/-- Number of oriented steps in a linear word. -/
def length {X Y : B} : LinearWord W X Y → ℕ
  | .nil _ => 0
  | .cons _ rest => 1 + length rest

/-- Linear append has additive length. -/
@[simp]
theorem length_append {X Y Z : B}
    (first : LinearWord W X Y) (second : LinearWord W Y Z) :
    length W (append W first second) =
      length W first + length W second := by
  induction first with
  | nil => simp [append, length]
  | cons step rest ih =>
      simp [append, length, ih, Nat.add_assoc]

/-- Converting a linear word to binary syntax preserves length exactly. -/
@[simp]
theorem length_toWord {X Y : B} (word : LinearWord W X Y) :
    Word.length (W := W) (toWord W word) = length W word := by
  induction word with
  | nil => simp [toWord, length]
  | cons step rest ih =>
      simp [toWord, length, ih]

/-- Flattening a binary word preserves length exactly. -/
@[simp]
theorem length_flatten {X Y : B} (word : Word W X Y) :
    length W (flatten W word) = Word.length (W := W) word := by
  induction word with
  | atom step => simp [flatten, length]
  | nil => simp [flatten, length]
  | comp first second ihFirst ihSecond =>
      simp [flatten, length_append, ihFirst, ihSecond]

/-- Horizontal composition of two isomorphisms in an arbitrary bicategory. -/
noncomputable def horizontalIso {C : Type u} [Bicategory.{w, v} C]
    {X Y Z : C} {first first' : X ⟶ Y}
    {second second' : Y ⟶ Z}
    (left : first ≅ first') (right : second ≅ second') :
    first ≫ second ≅ first' ≫ second' :=
  whiskerRightIso left second ≪≫ whiskerLeftIso first' right

/-- Horizontal composition of isomorphisms between binary words. -/
noncomputable def appendIso
    {X Y Z : B} {first first' : Word W X Y}
    {second second' : Word W Y Z}
    (left : first ≅ first') (right : second ≅ second') :
    Word.append (W := W) first second ≅
      Word.append (W := W) first' second' := by
  exact whiskerRightIso (B := Presented.Localization W) left second ≪≫
    whiskerLeftIso (B := Presented.Localization W) first' right

/-- Conjugating an associator by three arbitrary isomorphisms gives the
associator of their targets. -/
theorem associator_conjugation {C : Type u} [Bicategory.{w, v} C]
    {A B D E : C} {first first' : A ⟶ B}
    {second second' : B ⟶ D} {third third' : D ⟶ E}
    (left : first ≅ first') (middle : second ≅ second')
    (right : third ≅ third') :
    ((first' ≫ second') ◁ right.inv ≫
        ((first' ◁ middle.inv) ≫ (left.inv ▷ second)) ▷ third) ≫
      (α_ first second third).hom ≫
      (left.hom ▷ (second ≫ third) ≫
        first' ◁ ((middle.hom ▷ third) ≫ (second' ◁ right.hom))) =
    (α_ first' second' third').hom := by
  simp only [Category.assoc, Bicategory.comp_whiskerRight,
    Bicategory.whiskerLeft_comp]
  rw [Bicategory.associator_naturality_left_assoc]
  rw [← Bicategory.comp_whiskerRight_assoc]
  rw [left.inv_hom_id]
  simp only [Bicategory.id_whiskerRight, Category.id_comp]
  rw [Bicategory.associator_naturality_middle_assoc]
  rw [← Bicategory.whiskerLeft_comp_assoc]
  rw [← Bicategory.comp_whiskerRight]
  rw [middle.inv_hom_id]
  simp only [Bicategory.id_whiskerRight, Bicategory.whiskerLeft_id,
    Category.id_comp]
  rw [Bicategory.associator_naturality_right_assoc]
  rw [← Bicategory.whiskerLeft_comp]
  rw [← Bicategory.whiskerLeft_comp]
  rw [right.inv_hom_id]
  simp

/-- Normalizing all three factors horizontally transports a raw associator
to the associator between the chosen composite normal forms. -/
theorem horizontalIso_associator_normalization
    {C : Type u} [Bicategory.{w, v} C]
    {A B D E : C} {first first' : A ⟶ B}
    {second second' : B ⟶ D} {third third' : D ⟶ E}
    {firstSecond : A ⟶ D} {secondThird : B ⟶ E}
    (left : first ≅ first') (middle : second ≅ second')
    (right : third ≅ third')
    (firstSecondComparison : firstSecond ≅ first' ≫ second')
    (secondThirdComparison : secondThird ≅ second' ≫ third') :
    (horizontalIso
        (horizontalIso left middle ≪≫ firstSecondComparison.symm) right).inv ≫
      (α_ first second third).hom ≫
      (horizontalIso left
        (horizontalIso middle right ≪≫ secondThirdComparison.symm)).hom =
    (whiskerRightIso firstSecondComparison third').hom ≫
      (α_ first' second' third').hom ≫
      (whiskerLeftIso first' secondThirdComparison.symm).hom := by
  unfold horizontalIso
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Bicategory.whiskerLeftIso, Bicategory.whiskerRightIso,
    Bicategory.comp_whiskerRight, Bicategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [Bicategory.whisker_exchange_assoc]
  rw [cancel_epi (firstSecondComparison.hom ▷ third')]
  simp only [← Category.assoc]
  rw [cancel_mono (first' ◁ secondThirdComparison.inv)]
  simpa only [Category.assoc, Bicategory.comp_whiskerRight,
    Bicategory.whiskerLeft_comp] using
    associator_conjugation left middle right

/-- The preceding normalization formula specialized to binary marked-zigzag
words. -/
theorem appendIso_associator_normalization
    {X Y Z T : B} {first first' : Word W X Y}
    {second second' : Word W Y Z} {third third' : Word W Z T}
    (left : first ≅ first') (middle : second ≅ second')
    (right : third ≅ third')
    {firstSecond : Word W X Z}
    (firstSecondComparison : firstSecond ≅ .comp first' second')
    {secondThird : Word W Y T}
    (secondThirdComparison : secondThird ≅ .comp second' third') :
    (appendIso W
        (appendIso W left middle ≪≫ firstSecondComparison.symm) right).inv ≫
      (Presented.wordAssociatorIso W first second third).hom ≫
      (appendIso W left
        (appendIso W middle right ≪≫ secondThirdComparison.symm)).hom =
    (whiskerRightIso (B := Presented.Localization W)
        firstSecondComparison third').hom ≫
      (Presented.wordAssociatorIso W first' second' third').hom ≫
      (whiskerLeftIso (B := Presented.Localization W)
        first' secondThirdComparison.symm).hom :=
  horizontalIso_associator_normalization
    (C := Presented.Localization W) left middle right
      firstSecondComparison secondThirdComparison

/-- Coherence at the empty-prefix base of the recursive linear associator. -/
theorem associator_unit_coherence {C : Type u} [Bicategory.{w, v} C]
    {A B D : C} (second : A ⟶ B) (third : B ⟶ D)
    {target : A ⟶ D} (comparison : target ≅ second ≫ third) :
    comparison.hom ≫ ((λ_ second).inv ▷ third) ≫
      (α_ (𝟙 A) second third).hom ≫
      (𝟙 A ◁ comparison.inv) ≫ (λ_ target).hom = 𝟙 target := by
  rw [Bicategory.leftUnitor_inv_whiskerRight_assoc]
  rw [Iso.inv_hom_id_assoc]
  rw [Bicategory.leftUnitor_naturality]
  simp

/-- Coherence for transporting the canonical linear associator beneath one
common leading 1-morphism. -/
theorem associator_step_coherence {C : Type u} [Bicategory.{w, v} C]
    {A B D E F : C} (pre : A ⟶ B) (first : B ⟶ D)
    (second : D ⟶ E) (third : E ⟶ F)
    {firstSecond : B ⟶ E} {secondThird : D ⟶ F}
    {leftTarget rightTarget : B ⟶ F}
    (firstSecondComparison : firstSecond ≅ first ≫ second)
    (leftTargetComparison : leftTarget ≅ firstSecond ≫ third)
    (secondThirdComparison : secondThird ≅ second ≫ third)
    (rightTargetComparison : rightTarget ≅ first ≫ secondThird) :
    (whiskerLeftIso pre leftTargetComparison ≪≫
        (α_ pre firstSecond third).symm) ≪≫
      whiskerRightIso
        (whiskerLeftIso pre firstSecondComparison ≪≫
          (α_ pre first second).symm) third ≪≫
      (α_ (pre ≫ first) second third) ≪≫
      whiskerLeftIso (pre ≫ first) secondThirdComparison.symm ≪≫
      (whiskerLeftIso pre rightTargetComparison ≪≫
        (α_ pre first secondThird).symm).symm =
    whiskerLeftIso pre
      (leftTargetComparison ≪≫
        whiskerRightIso firstSecondComparison third ≪≫
        (α_ first second third) ≪≫
        whiskerLeftIso first secondThirdComparison.symm ≪≫
        rightTargetComparison.symm) := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Bicategory.whiskerLeftIso,
    Bicategory.whiskerRightIso]
  simp

/-- Conversion of linear append agrees with binary append up to the canonical
bicategorical associator and unitor isomorphisms. -/
noncomputable def toWordAppendIso {X Y Z : B}
    (first : LinearWord W X Y) (second : LinearWord W Y Z) :
    toWord W (append W first second) ≅
      Word.append (W := W) (toWord W first) (toWord W second) := by
  induction first with
  | nil X =>
      exact (Presented.wordLeftUnitorIso W (toWord W second)).symm
  | @cons X Y T step rest ih =>
      change Word.append (W := W) (Word.atom step)
          (toWord W (append W rest second)) ≅
        Word.append (W := W)
          (Word.append (W := W) (Word.atom step) (toWord W rest))
          (toWord W second)
      exact whiskerLeftIso (B := Presented.Localization W)
        (Word.atom step) (ih second) ≪≫
        (Presented.wordAssociatorIso W
          (Word.atom step) (toWord W rest) (toWord W second)).symm

/-- The append comparison with an empty first row is inverse left unitor. -/
theorem toWordAppendIso_nil {X Y : B} (second : LinearWord W X Y) :
    toWordAppendIso W (.nil X) second =
      (Presented.wordLeftUnitorIso W (toWord W second)).symm :=
  rfl

/-- Recursive equation for the append comparison under one leading step. -/
theorem toWordAppendIso_cons {X Y Z T : B} (step : Step W X Y)
    (rest : LinearWord W Y Z) (second : LinearWord W Z T) :
    toWordAppendIso W (.cons step rest) second =
      whiskerLeftIso (B := Presented.Localization W) (Word.atom step)
          (toWordAppendIso W rest second) ≪≫
        (Presented.wordAssociatorIso W
          (Word.atom step) (toWord W rest) (toWord W second)).symm :=
  rfl

/-- Canonical comparison between the two binary expansions of an associative
linear append. -/
noncomputable def associatorIso {X Y Z T : B}
    (first : LinearWord W X Y) (second : LinearWord W Y Z)
    (third : LinearWord W Z T) :
    toWord W (append W (append W first second) third) ≅
      toWord W (append W first (append W second third)) :=
  toWordAppendIso W (append W first second) third ≪≫
    whiskerRightIso (B := Presented.Localization W)
      (toWordAppendIso W first second) (toWord W third) ≪≫
    Presented.wordAssociatorIso W (toWord W first)
      (toWord W second) (toWord W third) ≪≫
    whiskerLeftIso (B := Presented.Localization W) (toWord W first)
      (toWordAppendIso W second third).symm ≪≫
    (toWordAppendIso W first (append W second third)).symm

/-- The canonical linear associator is identity at an empty prefix. -/
theorem associatorIso_nil {X Y Z : B}
    (second : LinearWord W X Y) (third : LinearWord W Y Z) :
    associatorIso W (.nil X) second third =
      Iso.refl (toWord W (append W second third)) := by
  apply Iso.ext
  unfold associatorIso
  rw [toWordAppendIso_nil]
  rw [toWordAppendIso_nil]
  simp only [Iso.trans_hom, Bicategory.whiskerRightIso,
    Bicategory.whiskerLeftIso, Iso.symm_hom]
  exact associator_unit_coherence
    (C := Presented.Localization W) (toWord W second) (toWord W third)
      (toWordAppendIso W second third)

/-- The canonical linear associator beneath a leading step is the left
whiskering of the associator for the remaining rows. -/
theorem associatorIso_cons {X Y Z T U : B} (step : Step W X Y)
    (rest : LinearWord W Y Z) (second : LinearWord W Z T)
    (third : LinearWord W T U) :
    associatorIso W (.cons step rest) second third =
      whiskerLeftIso (B := Presented.Localization W) (Word.atom step)
        (associatorIso W rest second third) := by
  unfold associatorIso
  simp only [append]
  rw [toWordAppendIso_cons]
  rw [toWordAppendIso_cons]
  rw [toWordAppendIso_cons]
  exact associator_step_coherence
    (C := Presented.Localization W) (Word.atom step) (toWord W rest)
      (toWord W second) (toWord W third)
      (toWordAppendIso W rest second)
      (toWordAppendIso W (append W rest second) third)
      (toWordAppendIso W second third)
      (toWordAppendIso W rest (append W second third))

/-- The append comparison for a singleton first row is the left-unitor
comparison on the second row followed by inverse associativity. -/
theorem toWordAppendIso_singleton {X Y Z : B} (step : Step W X Y)
    (second : LinearWord W Y Z) :
    toWordAppendIso W (.cons step (.nil Y)) second =
      whiskerLeftIso (B := Presented.Localization W) (Word.atom step)
          (Presented.wordLeftUnitorIso W (toWord W second)).symm ≪≫
        (Presented.wordAssociatorIso W
          (Word.atom step) (.nil Y) (toWord W second)).symm :=
  rfl

/-- The inverse singleton append comparison is associativity followed by the
left unitor on the second row. -/
theorem toWordAppendIso_singleton_inv {X Y Z : B} (step : Step W X Y)
    (second : LinearWord W Y Z) :
    (toWordAppendIso W (.cons step (.nil Y)) second).inv =
      (Presented.wordAssociatorIso W
        (Word.atom step) (.nil Y) (toWord W second)).hom ≫
      Presented.whiskerLeftHom W (Word.atom step)
        (Presented.wordLeftUnitorIso W (toWord W second)).hom := by
  rw [toWordAppendIso_singleton]
  rfl

/-- The hom of the symmetric singleton append comparison is the same explicit
associator/unitor composite. -/
theorem toWordAppendIso_singleton_symm_hom {X Y Z : B}
    (step : Step W X Y) (second : LinearWord W Y Z) :
    (toWordAppendIso W (.cons step (.nil Y)) second).symm.hom =
      (Presented.wordAssociatorIso W
        (Word.atom step) (.nil Y) (toWord W second)).hom ≫
      Presented.whiskerLeftHom W (Word.atom step)
        (Presented.wordLeftUnitorIso W (toWord W second)).hom := by
  rw [toWordAppendIso_singleton]
  rfl

/-- Every binary word is canonically isomorphic to the binary expansion of
its flattened linear normal form. -/
noncomputable def normalizationIso {X Y : B} (word : Word W X Y) :
    word ≅ toWord W (flatten W word) := by
  induction word with
  | atom step =>
      exact (Presented.wordRightUnitorIso W (Word.atom step)).symm
  | nil X => exact Iso.refl _
  | @comp X Y Z first second ihFirst ihSecond =>
      exact appendIso W ihFirst ihSecond ≪≫
        (toWordAppendIso W (flatten W first) (flatten W second)).symm

/-- Normalization of one atomic word is inverse right unitor. -/
theorem normalizationIso_atom {X Y : B} (step : Step W X Y) :
    normalizationIso W (Word.atom step) =
      (Presented.wordRightUnitorIso W (Word.atom step)).symm :=
  rfl

/-- The empty word is already in linear normal form. -/
theorem normalizationIso_nil (X : B) :
    normalizationIso W (Word.nil X) = Iso.refl (Word.nil X) :=
  rfl

/-- Flattening binary append is exactly linear append. -/
@[simp]
theorem flatten_append {X Y Z : B}
    (first : Word W X Y) (second : Word W Y Z) :
    flatten W (.comp first second) =
      append W (flatten W first) (flatten W second) :=
  rfl

/-- The canonical normalization of a binary append is horizontal append of
the two endpoint normalizations followed by the canonical linear append
comparison. -/
theorem normalizationIso_append {X Y Z : B}
    (first : Word W X Y) (second : Word W Y Z) :
    normalizationIso W (.comp first second) =
      appendIso W (normalizationIso W first) (normalizationIso W second) ≪≫
        (toWordAppendIso W (flatten W first) (flatten W second)).symm :=
  rfl

/-- Pure bicategorical coherence used by normalization of a two-step linear
row. -/
theorem rightAssociatedPair_coherence {C : Type u} [Bicategory.{w, v} C]
    {X Y Z : C} (first : X ⟶ Y) (second : Y ⟶ Z) :
    (((ρ_ first).inv ▷ second) ≫
        ((first ≫ 𝟙 Y) ◁ (ρ_ second).inv)) ≫
      (α_ first (𝟙 Y) (second ≫ 𝟙 Z)).hom ≫
      (first ◁ (λ_ (second ≫ 𝟙 Z)).hom) =
    (ρ_ (first ≫ second)).inv ≫
      (α_ first second (𝟙 Z)).hom := by
  bicategory_coherence

/-- Conjugating a left unitor along an arbitrary isomorphism cancels. -/
theorem leftUnitor_conjugation {C : Type u} [Bicategory.{w, v} C]
    {X Y : C} {first second : X ⟶ Y} (iso : first ≅ second) :
    (λ_ second).inv ≫ (𝟙 X ◁ iso.inv) ≫
      (λ_ first).hom ≫ iso.hom = 𝟙 second := by
  simp

/-- Inverse left-unitor conjugation along an arbitrary isomorphism also
cancels. -/
theorem leftUnitor_inv_conjugation {C : Type u} [Bicategory.{w, v} C]
    {X Y : C} {first second : X ⟶ Y} (iso : first ≅ second) :
    iso.inv ≫ (λ_ first).inv ≫ (𝟙 X ◁ iso.hom) ≫
      (λ_ second).hom = 𝟙 second := by
  simp

/-- Coherence step for recursively transporting a right-unit comparison
beneath one leading 1-morphism. -/
theorem rightUnit_step_coherence {C : Type u} [Bicategory.{w, v} C]
    {X Y Z : C} (first : X ⟶ Y) (second : Y ⟶ Z)
    {source : Y ⟶ Z} (comparison : source ⟶ second ≫ 𝟙 Z) :
    first ◁ (comparison ≫ (ρ_ second).hom) =
      (first ◁ comparison ≫ (α_ first second (𝟙 Z)).inv) ≫
        (ρ_ (first ≫ second)).hom := by
  simp

/-- Right-unitor naturality along an arbitrary isomorphism. -/
theorem rightUnitor_conjugation {C : Type u} [Bicategory.{w, v} C]
    {X Y : C} {first second : X ⟶ Y} (iso : first ≅ second) :
    (iso.inv ▷ 𝟙 Y) ≫ (ρ_ first).hom ≫ iso.hom =
      (ρ_ second).hom := by
  simp

/-- Inverse right-unitor naturality along an arbitrary isomorphism. -/
theorem rightUnitor_inv_conjugation {C : Type u} [Bicategory.{w, v} C]
    {X Y : C} {first second : X ⟶ Y} (iso : first ≅ second) :
    iso.inv ≫ (ρ_ first).inv ≫ (iso.hom ▷ 𝟙 Y) =
      (ρ_ second).inv := by
  simp

/-- Coherence step for the inverse recursive right-unit path. -/
theorem rightUnit_inv_step_coherence {C : Type u} [Bicategory.{w, v} C]
    {X Y Z : C} (first : X ⟶ Y) (second : Y ⟶ Z)
    {target : Y ⟶ Z} (comparison : second ≫ 𝟙 Z ⟶ target) :
    (ρ_ (first ≫ second)).inv ≫ (α_ first second (𝟙 Z)).hom ≫
      (first ◁ comparison) =
    first ◁ ((ρ_ second).inv ≫ comparison) := by
  simp

/-- Normalizing a binary word of two atomic steps is exactly inverse right
unitor followed by the associator into the canonical right-associated row. -/
theorem normalizationIso_twoAtoms_hom {X Y Z : B}
    (first : Step W X Y) (second : Step W Y Z) :
    (normalizationIso W (.comp (.atom first) (.atom second))).hom =
    (Presented.wordRightUnitorIso W
      (.comp (.atom first) (.atom second))).inv ≫
      (Presented.wordAssociatorIso W
        (.atom first) (.atom second) (.nil Z)).hom := by
  rw [show normalizationIso W
      (.comp (.atom first) (.atom second)) =
    appendIso W (normalizationIso W (.atom first))
        (normalizationIso W (.atom second)) ≪≫
      (toWordAppendIso W (flatten W (.atom first))
        (flatten W (.atom second))).symm from rfl]
  simp only [flatten]
  rw [normalizationIso_atom W first]
  rw [normalizationIso_atom W second]
  simp only [Iso.trans_hom]
  rw [toWordAppendIso_singleton_symm_hom W first
    (.cons second (.nil Z))]
  unfold appendIso
  simp only [Iso.trans_hom, Bicategory.whiskerLeftIso,
    Bicategory.whiskerRightIso, toWord]
  rw [show (Presented.wordRightUnitorIso W (Word.atom first)).symm.hom =
      (Presented.wordRightUnitorIso W (Word.atom first)).inv from rfl]
  rw [show (Presented.wordRightUnitorIso W (Word.atom second)).symm.hom =
      (Presented.wordRightUnitorIso W (Word.atom second)).inv from rfl]
  exact rightAssociatedPair_coherence
    (C := Presented.Localization W) (Word.atom first) (Word.atom second)

/-- Inverse of the two-atomic-step normalization: inverse associativity
followed by the whole-word right unitor. -/
theorem normalizationIso_twoAtoms_inv {X Y Z : B}
    (first : Step W X Y) (second : Step W Y Z) :
    (normalizationIso W (.comp (.atom first) (.atom second))).inv =
      (Presented.wordAssociatorIso W
        (.atom first) (.atom second) (.nil Z)).inv ≫
      (Presented.wordRightUnitorIso W
        (.comp (.atom first) (.atom second))).hom := by
  have isoEquality :
      normalizationIso W (.comp (.atom first) (.atom second)) =
        (Presented.wordRightUnitorIso W
          (.comp (.atom first) (.atom second))).symm ≪≫
        Presented.wordAssociatorIso W
          (.atom first) (.atom second) (.nil Z) := by
    apply Iso.ext
    exact normalizationIso_twoAtoms_hom W first second
  rw [isoEquality]
  rfl

/-- Linear words form a mapping category by pulling back the quotient
2-cell hom-sets between their binary expansions. -/
instance category (X Y : B) : Category (LinearWord W X Y) where
  Hom first second := toWord W first ⟶ toWord W second
  id _ := 𝟙 _
  comp first second := first ≫ second
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

/-- Conversion from linear hammock words to binary marked-zigzag words as a
functor of mapping categories. -/
def toWordFunctor (X Y : B) : LinearWord W X Y ⥤ Word W X Y where
  obj := toWord W
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

instance toWordFunctor_faithful (X Y : B) :
    (toWordFunctor W X Y).Faithful where
  map_injective h := h

instance toWordFunctor_full (X Y : B) :
    (toWordFunctor W X Y).Full where
  map_surjective f := ⟨f, rfl⟩

instance toWordFunctor_essSurj (X Y : B) :
    (toWordFunctor W X Y).EssSurj where
  mem_essImage word :=
    ⟨flatten W word, ⟨(normalizationIso W word).symm⟩⟩

instance toWordFunctor_isEquivalence (X Y : B) :
    (toWordFunctor W X Y).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := inferInstance

/-- The linear hammock mapping category is equivalent to the binary
word/quotient-2-cell mapping category. -/
noncomputable def equivalence (X Y : B) :
    LinearWord W X Y ≌ Word W X Y :=
  (toWordFunctor W X Y).asEquivalence

end LinearWord

end CategoryTheory.Bicategory.MarkedZigzag
