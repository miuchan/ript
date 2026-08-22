import Ript.ForMathlib.CategoryTheory.Bicategory.MarkedZigzag

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

/-- Convert a right-associated linear word to the binary marked-zigzag
syntax. -/
def toWord {X Y : B} : LinearWord W X Y → Word W X Y
  | .nil X => .nil X
  | .cons step rest =>
      Word.append (W := W) (.atom step) (toWord rest)

/-- Flatten a binary marked-zigzag composition tree to a linear word. -/
def flatten {X Y : B} : Word W X Y → LinearWord W X Y
  | .atom step => .cons step (.nil _)
  | .nil X => .nil X
  | .comp first second => append W (flatten first) (flatten second)

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

/-- Horizontal composition of isomorphisms between binary words. -/
noncomputable def appendIso
    {X Y Z : B} {first first' : Word W X Y}
    {second second' : Word W Y Z}
    (left : first ≅ first') (right : second ≅ second') :
    Word.append (W := W) first second ≅
      Word.append (W := W) first' second' := by
  exact whiskerRightIso (B := Presented.Localization W) left second ≪≫
    whiskerLeftIso (B := Presented.Localization W) first' right

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
