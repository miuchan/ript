import Ript.ForMathlib.CategoryTheory.Bicategory.Localization

/-!
# Marked zigzags in a bicategory

This file constructs the computable 1-cell syntax underlying a genuine
bicategorical localization.  A marked zigzag is a typed word whose forward
steps are arbitrary source 1-cells and whose backward steps are permitted
only for marked 1-cells.  Concatenation is executable and has proved unit and
associativity laws.

For a pseudofunctor equipped with chosen adjoint-equivalence images of the
marking, every zigzag has a single recursively defined interpretation.  The
interpretation preserves concatenation up to the canonical bicategorical
associator/unitor isomorphism.  A non-chosen `IsInvertedBy` witness can be
converted to chosen data noncomputably, keeping that choice outside the raw
zigzag syntax.  In particular, the forward/backward and backward/forward
words of a marked arrow evaluate to the unit and counit cancellation shapes.

The file then freely generates 2-cells, imposes vertical and horizontal
bicategorical relations, constructs quotient local categories and the target
bicategory, and defines the canonical source pseudofunctor. Marked unit and
counit generators yield explicit adjoint equivalences, so every marked arrow
is proved inverted. Every marking-inverting pseudofunctor has an explicit
lift whose restriction is adjoint equivalent to the original pseudofunctor.
The remaining downstream theorem is local equivalence on strong
transformations and modifications.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace CategoryTheory.Bicategory.MarkedZigzag

open CategoryTheory
open CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans

universe u₁ v₁ w₁ u₂ v₂ w₂

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]
variable (W : Bicategory.MorphismProperty B)

/-- One oriented step in a marked zigzag.  Forward steps contain arbitrary
1-cells; backward steps contain a source 1-cell together with proof that it
belongs to the marking. -/
inductive Step : B → B → Type max u₁ v₁ where
  /-- Traverse an arbitrary source 1-cell in its given direction. -/
  | forward {X Y : B} (f : X ⟶ Y) : Step X Y
  /-- Traverse a marked source 1-cell in the reverse direction. -/
  | backward {X Y : B} (f : X ⟶ Y) (hf : W f) : Step Y X

/-- A typed binary expression of forward arrows and formal reverses of marked
arrows. The endpoint indices rule out ill-composable expressions by
construction. Binary composition is intentionally not definitionally
associative: its associator is genuine 2-dimensional data. -/
inductive Word : B → B → Type max u₁ v₁ where
  /-- One atomic oriented step. -/
  | atom {X Y : B} (step : Step W X Y) : Word X Y
  /-- The identity word at an object. -/
  | nil (X : B) : Word X X
  /-- Binary composition of typed words. -/
  | comp {X Y Z : B} (first : Word X Y) (second : Word Y Z) : Word X Z

namespace Word

/-- The one-step word associated with an oriented step. -/
def single {X Y : B} (step : Step W X Y) : Word W X Y :=
  Word.atom step

/-- The one-step forward word associated with a source 1-cell. -/
def forward {X Y : B} (f : X ⟶ Y) : Word W X Y :=
  single W (Step.forward (W := W) f)

/-- The one-step reverse word associated with a marked source 1-cell. -/
def backward {X Y : B} (f : X ⟶ Y) (hf : W f) : Word W Y X :=
  single W (Step.backward (W := W) f hf)

/-- Executable binary composition of composable marked zigzags. -/
def append {X Y Z : B} : Word W X Y → Word W Y Z → Word W X Z
  | first, second => .comp first second

/-- The number of oriented steps in a marked zigzag. -/
def length {X Y : B} : Word W X Y → ℕ
  | .atom _ => 1
  | .nil _ => 0
  | .comp first second => length first + length second

@[simp]
theorem append_eq_comp {X Y Z : B} (first : Word W X Y)
    (second : Word W Y Z) :
    append (W := W) first second = .comp first second :=
  rfl

@[simp]
theorem length_atom {X Y : B} (step : Step W X Y) :
    length (W := W) (.atom step) = 1 :=
  rfl

@[simp]
theorem length_nil (X : B) :
    length (W := W) (.nil X : Word W X X) = 0 :=
  rfl

@[simp]
theorem length_comp {X Y Z : B} (first : Word W X Y)
    (second : Word W Y Z) :
    length (W := W) (.comp first second) =
      length (W := W) first + length (W := W) second :=
  rfl

@[simp]
theorem length_append {X Y Z : B} (first : Word W X Y)
    (second : Word W Y Z) :
    length (W := W) (append (W := W) first second) =
      length (W := W) first + length (W := W) second :=
  rfl

@[simp]
theorem length_forward {X Y : B} (f : X ⟶ Y) :
    length (W := W) (forward W f) = 1 :=
  rfl

@[simp]
theorem length_backward {X Y : B} (f : X ⟶ Y) (hf : W f) :
    length (W := W) (backward W f hf) = 1 :=
  rfl

end Word

/-! ## Raw 2-cell generators -/

/-- Raw 2-cell expressions between parallel marked zigzags. These are the
generators and closure operations consumed by the presented quotient below;
the equations themselves are kept separately in `Presented.Rel`. -/
inductive Cell : ∀ {X Y : B}, Word W X Y → Word W X Y →
    Type max u₁ v₁ w₁ where
  /-- Identity raw 2-cell. -/
  | id {X Y : B} (word : Word W X Y) : Cell word word
  /-- Vertical composition of raw 2-cells. -/
  | vcomp {X Y : B} {first middle last : Word W X Y}
      (α : Cell first middle) (β : Cell middle last) : Cell first last
  /-- An original source 2-cell between forward one-step words. -/
  | original {X Y : B} {f g : X ⟶ Y} (α : f ⟶ g) :
      Cell (Word.forward W f) (Word.forward W g)
  /-- Comparison from the forward source identity to the empty word. -/
  | sourceId {X : B} :
      Cell (Word.forward W (𝟙 X)) (.nil X)
  /-- Formal inverse of the source-identity comparison. -/
  | sourceIdInv {X : B} :
      Cell (.nil X) (Word.forward W (𝟙 X))
  /-- Comparison from the forward source composite to concatenated forward
  words. -/
  | sourceComp {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
      Cell (Word.forward W (f ≫ g))
        (Word.append (W := W) (Word.forward W f) (Word.forward W g))
  /-- Formal inverse of the source-composition comparison. -/
  | sourceCompInv {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
      Cell (Word.append (W := W) (Word.forward W f) (Word.forward W g))
        (Word.forward W (f ≫ g))
  /-- Unit generator for a marked arrow and its formal reverse. -/
  | markedUnit {X Y : B} (f : X ⟶ Y) (hf : W f) :
      Cell (.nil X)
        (Word.append (W := W) (Word.forward W f) (Word.backward W f hf))
  /-- Formal inverse of the marked unit. -/
  | markedUnitInv {X Y : B} (f : X ⟶ Y) (hf : W f) :
      Cell
        (Word.append (W := W) (Word.forward W f) (Word.backward W f hf))
        (.nil X)
  /-- Counit generator for a formal reverse followed by its marked arrow. -/
  | markedCounit {X Y : B} (f : X ⟶ Y) (hf : W f) :
      Cell
        (Word.append (W := W) (Word.backward W f hf) (Word.forward W f))
        (.nil Y)
  /-- Formal inverse of the marked counit. -/
  | markedCounitInv {X Y : B} (f : X ⟶ Y) (hf : W f) :
      Cell (.nil Y)
        (Word.append (W := W) (Word.backward W f hf) (Word.forward W f))
  /-- Left whiskering by a fixed marked zigzag. -/
  | whiskerLeft {X Y Z : B} (preword : Word W X Y)
      {first second : Word W Y Z} (α : Cell first second) :
      Cell (Word.append (W := W) preword first)
        (Word.append (W := W) preword second)
  /-- Right whiskering by a fixed marked zigzag. -/
  | whiskerRight {X Y Z : B} {first second : Word W X Y}
      (α : Cell first second) (postword : Word W Y Z) :
      Cell (Word.append (W := W) first postword)
        (Word.append (W := W) second postword)
  /-- Bicategorical associator generator. -/
  | associator {X Y Z T : B} (first : Word W X Y)
      (second : Word W Y Z) (third : Word W Z T) :
      Cell
        (Word.append (W := W) (Word.append (W := W) first second) third)
        (Word.append (W := W) first (Word.append (W := W) second third))
  /-- Inverse bicategorical associator generator. -/
  | associatorInv {X Y Z T : B} (first : Word W X Y)
      (second : Word W Y Z) (third : Word W Z T) :
      Cell
        (Word.append (W := W) first (Word.append (W := W) second third))
        (Word.append (W := W) (Word.append (W := W) first second) third)
  /-- Bicategorical left-unitor generator. -/
  | leftUnitor {X Y : B} (word : Word W X Y) :
      Cell (Word.append (W := W) (.nil X) word) word
  /-- Inverse bicategorical left-unitor generator. -/
  | leftUnitorInv {X Y : B} (word : Word W X Y) :
      Cell word (Word.append (W := W) (.nil X) word)
  /-- Bicategorical right-unitor generator. -/
  | rightUnitor {X Y : B} (word : Word W X Y) :
      Cell (Word.append (W := W) word (.nil Y)) word
  /-- Inverse bicategorical right-unitor generator. -/
  | rightUnitorInv {X Y : B} (word : Word W X Y) :
      Cell word (Word.append (W := W) word (.nil Y))
  /-- Transport a raw 2-cell along equalities of its source and target words.
  This makes the propositional unit/associativity laws of executable word
  concatenation available to the future quotient presentation. -/
  | transport {X Y : B} {first second first' second' : Word W X Y}
      (source_eq : first = first') (target_eq : second = second')
      (α : Cell first second) : Cell first' second'

namespace Cell

/-- Raw unit generator for a marked forward/reverse pair. -/
def unit {X Y : B} (f : X ⟶ Y) (hf : W f) :
    Cell W (.nil X)
      (Word.append (W := W) (Word.forward W f) (Word.backward W f hf)) :=
  .markedUnit f hf

/-- Raw counit generator for a marked reverse/forward pair. -/
def counit {X Y : B} (f : X ⟶ Y) (hf : W f) :
    Cell W
      (Word.append (W := W) (Word.backward W f hf) (Word.forward W f))
      (.nil Y) :=
  .markedCounit f hf

/-- Turn equality of parallel marked words into a raw structural 2-cell. -/
def ofEq {X Y : B} {first second : Word W X Y}
    (equality : first = second) : Cell W first second :=
  Cell.transport (W := W) rfl equality (Cell.id first)

end Cell

/-! ## Presented local hom-categories -/

namespace Presented

/-- Relations imposed on raw 2-cell expressions at the local-category layer.
They make vertical composition categorical, make original source 2-cells
functorial, make whiskering congruent, make the source identity/compositor and
marked unit/counit generators invertible, impose horizontal bicategory
coherence, and impose both marked adjunction triangle equations. -/
inductive Rel : ∀ {X Y : B} {first second : Word W X Y},
    Cell W first second → Cell W first second → Prop where
  | vcomp_right {X Y : B} {first middle last : Word W X Y}
      (α : Cell W first middle) {β β' : Cell W middle last} :
      Rel β β' → Rel (.vcomp α β) (.vcomp α β')
  | vcomp_left {X Y : B} {first middle last : Word W X Y}
      {α α' : Cell W first middle} (β : Cell W middle last) :
      Rel α α' → Rel (.vcomp α β) (.vcomp α' β)
  | id_vcomp {X Y : B} {first second : Word W X Y}
      (α : Cell W first second) : Rel (.vcomp (.id first) α) α
  | vcomp_id {X Y : B} {first second : Word W X Y}
      (α : Cell W first second) : Rel (.vcomp α (.id second)) α
  | vcomp_assoc {X Y : B} {first second third fourth : Word W X Y}
      (α : Cell W first second) (β : Cell W second third)
      (γ : Cell W third fourth) :
      Rel (.vcomp (.vcomp α β) γ) (.vcomp α (.vcomp β γ))
  | original_id {X Y : B} (f : X ⟶ Y) :
      Rel (.original (𝟙 f)) (.id (Word.forward W f))
  | original_vcomp {X Y : B} {f g h : X ⟶ Y}
      (α : f ⟶ g) (β : g ⟶ h) :
      Rel (.original (α ≫ β)) (.vcomp (.original α) (.original β))
  | whisker_left {X Y Z : B} (preword : Word W X Y)
      {first second : Word W Y Z} {α β : Cell W first second} :
      Rel α β → Rel (.whiskerLeft preword α) (.whiskerLeft preword β)
  | whisker_right {X Y Z : B} {first second : Word W X Y}
      {α β : Cell W first second} (postword : Word W Y Z) :
      Rel α β → Rel (.whiskerRight α postword) (.whiskerRight β postword)
  | whisker_left_id {X Y Z : B} (first : Word W X Y)
      (second : Word W Y Z) :
      Rel (.whiskerLeft first (.id second))
        (.id (Word.append (W := W) first second))
  | whisker_left_vcomp {X Y Z : B} (preword : Word W X Y)
      {first second third : Word W Y Z}
      (α : Cell W first second) (β : Cell W second third) :
      Rel (.whiskerLeft preword (.vcomp α β))
        (.vcomp (.whiskerLeft preword α) (.whiskerLeft preword β))
  | id_whisker_left {X Y : B} {first second : Word W X Y}
      (α : Cell W first second) :
      Rel (.whiskerLeft (.nil X) α)
        (.vcomp (Cell.leftUnitor (W := W) first)
          (.vcomp α (Cell.leftUnitorInv (W := W) second)))
  | comp_whisker_left {X Y Z T : B} (first : Word W X Y)
      (second : Word W Y Z) {third third' : Word W Z T}
      (α : Cell W third third') :
      Rel (.whiskerLeft (Word.append (W := W) first second) α)
        (.vcomp (Cell.associator (W := W) first second third)
          (.vcomp (.whiskerLeft first (.whiskerLeft second α))
            (Cell.associatorInv (W := W) first second third')))
  | whisker_right_id {X Y Z : B} (first : Word W X Y)
      (second : Word W Y Z) :
      Rel (.whiskerRight (.id first) second)
        (.id (Word.append (W := W) first second))
  | whisker_right_vcomp {X Y Z : B}
      {first second third : Word W X Y} (postword : Word W Y Z)
      (α : Cell W first second) (β : Cell W second third) :
      Rel (.whiskerRight (.vcomp α β) postword)
        (.vcomp (.whiskerRight α postword) (.whiskerRight β postword))
  | whisker_right_id_word {X Y : B} {first second : Word W X Y}
      (α : Cell W first second) :
      Rel (.whiskerRight α (.nil Y))
        (.vcomp (Cell.rightUnitor (W := W) first)
          (.vcomp α (Cell.rightUnitorInv (W := W) second)))
  | whisker_right_comp {X Y Z T : B} {first first' : Word W X Y}
      (second : Word W Y Z) (third : Word W Z T)
      (α : Cell W first first') :
      Rel (.whiskerRight α (Word.append (W := W) second third))
        (.vcomp (Cell.associatorInv (W := W) first second third)
          (.vcomp (.whiskerRight (.whiskerRight α second) third)
            (Cell.associator (W := W) first' second third)))
  | whisker_assoc {X Y Z T : B} (first : Word W X Y)
      {second second' : Word W Y Z} (α : Cell W second second')
      (third : Word W Z T) :
      Rel (.whiskerRight (.whiskerLeft first α) third)
        (.vcomp (Cell.associator (W := W) first second third)
          (.vcomp (.whiskerLeft first (.whiskerRight α third))
            (Cell.associatorInv (W := W) first second' third)))
  | whisker_exchange {X Y Z : B} {first first' : Word W X Y}
      {second second' : Word W Y Z}
      (α : Cell W first first') (β : Cell W second second') :
      Rel (.vcomp (.whiskerLeft first β) (.whiskerRight α second'))
        (.vcomp (.whiskerRight α second) (.whiskerLeft first' β))
  | associator_hom_inv {X Y Z T : B} (first : Word W X Y)
      (second : Word W Y Z) (third : Word W Z T) :
      Rel (.vcomp (Cell.associator (W := W) first second third)
        (Cell.associatorInv (W := W) first second third))
        (.id (Word.append (W := W)
          (Word.append (W := W) first second) third))
  | associator_inv_hom {X Y Z T : B} (first : Word W X Y)
      (second : Word W Y Z) (third : Word W Z T) :
      Rel (.vcomp (Cell.associatorInv (W := W) first second third)
        (Cell.associator (W := W) first second third))
        (.id (Word.append (W := W) first
          (Word.append (W := W) second third)))
  | left_unitor_hom_inv {X Y : B} (word : Word W X Y) :
      Rel (.vcomp (Cell.leftUnitor (W := W) word) (Cell.leftUnitorInv (W := W) word))
        (.id (Word.append (W := W) (.nil X) word))
  | left_unitor_inv_hom {X Y : B} (word : Word W X Y) :
      Rel (.vcomp (Cell.leftUnitorInv (W := W) word) (Cell.leftUnitor (W := W) word))
        (.id word)
  | right_unitor_hom_inv {X Y : B} (word : Word W X Y) :
      Rel (.vcomp (Cell.rightUnitor (W := W) word) (Cell.rightUnitorInv (W := W) word))
        (.id (Word.append (W := W) word (.nil Y)))
  | right_unitor_inv_hom {X Y : B} (word : Word W X Y) :
      Rel (.vcomp (Cell.rightUnitorInv (W := W) word) (Cell.rightUnitor (W := W) word))
        (.id word)
  | pentagon {X Y Z T U : B} (first : Word W X Y)
      (second : Word W Y Z) (third : Word W Z T) (fourth : Word W T U) :
      Rel
        (.vcomp (.whiskerRight (Cell.associator (W := W) first second third) fourth)
          (.vcomp (Cell.associator (W := W) first
              (Word.append (W := W) second third) fourth)
            (.whiskerLeft first (Cell.associator (W := W) second third fourth))))
        (.vcomp (Cell.associator (W := W)
            (Word.append (W := W) first second) third fourth)
          (Cell.associator (W := W) first second
            (Word.append (W := W) third fourth)))
  | triangle {X Y Z : B} (first : Word W X Y) (second : Word W Y Z) :
      Rel
        (.vcomp (Cell.associator (W := W) first (.nil Y) second)
          (.whiskerLeft first (Cell.leftUnitor (W := W) second)))
        (.whiskerRight (Cell.rightUnitor (W := W) first) second)
  | original_whisker_left {X Y Z : B} (f : X ⟶ Y)
      {g h : Y ⟶ Z} (α : g ⟶ h) :
      Rel (.original (f ◁ α))
        (.vcomp (.sourceComp (W := W) f g)
          (.vcomp (.whiskerLeft (Word.forward W f) (.original α))
            (.sourceCompInv (W := W) f h)))
  | original_whisker_right {X Y Z : B} {f g : X ⟶ Y}
      (α : f ⟶ g) (h : Y ⟶ Z) :
      Rel (.original (α ▷ h))
        (.vcomp (.sourceComp (W := W) f h)
          (.vcomp (.whiskerRight (.original α) (Word.forward W h))
            (.sourceCompInv (W := W) g h)))
  | original_associator {X Y Z T : B} (f : X ⟶ Y)
      (g : Y ⟶ Z) (h : Z ⟶ T) :
      Rel (.original (α_ f g h).hom)
        (.vcomp (.sourceComp (W := W) (f ≫ g) h)
          (.vcomp (.whiskerRight (.sourceComp (W := W) f g)
              (Word.forward W h))
            (.vcomp (Cell.associator (W := W) (Word.forward W f)
                (Word.forward W g) (Word.forward W h))
              (.vcomp (.whiskerLeft (Word.forward W f)
                  (.sourceCompInv (W := W) g h))
                (.sourceCompInv (W := W) f (g ≫ h))))))
  | original_left_unitor {X Y : B} (f : X ⟶ Y) :
      Rel (.original (λ_ f).hom)
        (.vcomp (.sourceComp (W := W) (𝟙 X) f)
          (.vcomp (.whiskerRight (.sourceId (W := W)) (Word.forward W f))
            (Cell.leftUnitor (W := W) (Word.forward W f))))
  | original_right_unitor {X Y : B} (f : X ⟶ Y) :
      Rel (.original (ρ_ f).hom)
        (.vcomp (.sourceComp (W := W) f (𝟙 Y))
          (.vcomp (.whiskerLeft (Word.forward W f) (.sourceId (W := W)))
            (Cell.rightUnitor (W := W) (Word.forward W f))))
  | transport_refl {X Y : B} {first second : Word W X Y}
      (α : Cell W first second) : Rel (.transport rfl rfl α) α
  | source_id_hom_inv {X : B} :
      Rel (.vcomp (.sourceId (W := W)) (.sourceIdInv (W := W)))
        (.id (Word.forward W (𝟙 X)))
  | source_id_inv_hom {X : B} :
      Rel (.vcomp (.sourceIdInv (W := W)) (.sourceId (W := W)))
        (.id (.nil X))
  | source_comp_hom_inv {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
      Rel (.vcomp (.sourceComp (W := W) f g)
        (.sourceCompInv (W := W) f g))
        (.id (Word.forward W (f ≫ g)))
  | source_comp_inv_hom {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
      Rel (.vcomp (.sourceCompInv (W := W) f g)
        (.sourceComp (W := W) f g))
        (.id (Word.append (W := W) (Word.forward W f) (Word.forward W g)))
  | marked_unit_hom_inv {X Y : B} (f : X ⟶ Y) (hf : W f) :
      Rel (.vcomp (.markedUnit (W := W) f hf)
        (.markedUnitInv (W := W) f hf)) (.id (.nil X))
  | marked_unit_inv_hom {X Y : B} (f : X ⟶ Y) (hf : W f) :
      Rel (.vcomp (.markedUnitInv (W := W) f hf)
        (.markedUnit (W := W) f hf))
        (.id (Word.append (W := W) (Word.forward W f) (Word.backward W f hf)))
  | marked_counit_hom_inv {X Y : B} (f : X ⟶ Y) (hf : W f) :
      Rel (.vcomp (.markedCounit (W := W) f hf)
        (.markedCounitInv (W := W) f hf))
        (.id (Word.append (W := W) (Word.backward W f hf) (Word.forward W f)))
  | marked_counit_inv_hom {X Y : B} (f : X ⟶ Y) (hf : W f) :
      Rel (.vcomp (.markedCounitInv (W := W) f hf)
        (.markedCounit (W := W) f hf)) (.id (.nil Y))
  | marked_left_triangle {X Y : B} (f : X ⟶ Y) (hf : W f) :
      Rel
        (.vcomp
          (.whiskerRight (.markedUnit (W := W) f hf) (Word.forward W f))
          (.vcomp
            (.vcomp
              (.associator (W := W) (Word.forward W f)
                (Word.backward W f hf) (Word.forward W f))
              (.whiskerRight (.id (Word.forward W f))
                (Word.append (W := W) (Word.backward W f hf)
                  (Word.forward W f))))
            (.whiskerLeft (Word.forward W f)
              (.markedCounit (W := W) f hf))))
        (.vcomp (.leftUnitor (W := W) (Word.forward W f))
          (.rightUnitorInv (W := W) (Word.forward W f)))
  | marked_right_triangle {X Y : B} (f : X ⟶ Y) (hf : W f) :
      Rel
        (.vcomp
          (.whiskerLeft (Word.backward W f hf)
            (.markedUnit (W := W) f hf))
          (.vcomp
            (.associatorInv (W := W) (Word.backward W f hf)
              (Word.forward W f) (Word.backward W f hf))
            (.whiskerRight (.markedCounit (W := W) f hf)
              (Word.backward W f hf))))
        (.vcomp (.rightUnitor (W := W) (Word.backward W f hf))
          (.leftUnitorInv (W := W) (Word.backward W f hf)))

/-- Quotient 2-cells between parallel marked zigzags. -/
abbrev Hom {X Y : B} (first second : Word W X Y) :=
  Quot (@Rel B _ W X Y first second)

/-- Embed a raw 2-cell expression into the presented local hom-category. -/
abbrev mk {X Y : B} {first second : Word W X Y}
    (α : Cell W first second) : Hom W first second :=
  Quot.mk _ α

/-- Every pair of source objects now has a genuine category whose objects are
marked zigzags and whose morphisms are quotient 2-cells. -/
instance wordCategory (X Y : B) : Category (Word W X Y) where
  Hom first second := Hom W first second
  id first := mk W (Cell.id first)
  comp := @fun _ _ _ α β =>
    Quot.map₂ Cell.vcomp Rel.vcomp_right
      (fun _ _ postcell relation => Rel.vcomp_left postcell relation) α β
  id_comp := by
    rintro first second ⟨α⟩
    exact Quot.sound (Rel.id_vcomp α)
  comp_id := by
    rintro first second ⟨α⟩
    exact Quot.sound (Rel.vcomp_id α)
  assoc := by
    rintro first second third fourth ⟨α⟩ ⟨β⟩ ⟨γ⟩
    exact Quot.sound (Rel.vcomp_assoc α β γ)

/-- Original source 2-cells define a functor into each presented local
hom-category. -/
def forwardHomFunctor (X Y : B) : (X ⟶ Y) ⥤ Word W X Y where
  obj f := Word.forward W f
  map α := mk W (Cell.original (W := W) α)
  map_id f := Quot.sound (Rel.original_id f)
  map_comp α β := Quot.sound (Rel.original_vcomp α β)

/-- The source identity comparison is an isomorphism in the presented local
category. -/
def sourceIdIso (X : B) :
    Word.forward W (𝟙 X) ≅ (.nil X : Word W X X) where
  hom := mk W (Cell.sourceId (W := W))
  inv := mk W (Cell.sourceIdInv (W := W))
  hom_inv_id := Quot.sound Rel.source_id_hom_inv
  inv_hom_id := Quot.sound Rel.source_id_inv_hom

/-- The source composition comparison is an isomorphism in the presented
local category. -/
def sourceCompIso {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Word.forward W (f ≫ g) ≅
      Word.append (W := W) (Word.forward W f) (Word.forward W g) where
  hom := mk W (Cell.sourceComp (W := W) f g)
  inv := mk W (Cell.sourceCompInv (W := W) f g)
  hom_inv_id := Quot.sound (Rel.source_comp_hom_inv f g)
  inv_hom_id := Quot.sound (Rel.source_comp_inv_hom f g)

/-- The marked unit generator is an isomorphism in the presented local
category. -/
def markedUnitIso {X Y : B} (f : X ⟶ Y) (hf : W f) :
    (.nil X : Word W X X) ≅
      Word.append (W := W) (Word.forward W f) (Word.backward W f hf) where
  hom := mk W (Cell.markedUnit (W := W) f hf)
  inv := mk W (Cell.markedUnitInv (W := W) f hf)
  hom_inv_id := Quot.sound (Rel.marked_unit_hom_inv f hf)
  inv_hom_id := Quot.sound (Rel.marked_unit_inv_hom f hf)

/-- The marked counit generator is an isomorphism in the presented local
category. -/
def markedCounitIso {X Y : B} (f : X ⟶ Y) (hf : W f) :
    Word.append (W := W) (Word.backward W f hf) (Word.forward W f) ≅
      (.nil Y : Word W Y Y) where
  hom := mk W (Cell.markedCounit (W := W) f hf)
  inv := mk W (Cell.markedCounitInv (W := W) f hf)
  hom_inv_id := Quot.sound (Rel.marked_counit_hom_inv f hf)
  inv_hom_id := Quot.sound (Rel.marked_counit_inv_hom f hf)

/-- Left whiskering descends to quotient 2-cells. -/
def whiskerLeftHom {X Y Z : B} (preword : Word W X Y)
    {first second : Word W Y Z} :
    Hom W first second →
      Hom W (Word.append (W := W) preword first)
        (Word.append (W := W) preword second) :=
  Quot.map (Cell.whiskerLeft preword)
    (fun _ _ relation => Rel.whisker_left preword relation)

/-- Right whiskering descends to quotient 2-cells. -/
def whiskerRightHom {X Y Z : B} {first second : Word W X Y}
    (postword : Word W Y Z) :
    Hom W first second →
      Hom W (Word.append (W := W) first postword)
        (Word.append (W := W) second postword) :=
  Quot.map (fun raw => Cell.whiskerRight raw postword)
    (fun _ _ relation => Rel.whisker_right postword relation)

/-- Quotient associator isomorphism for word concatenation. -/
def wordAssociatorIso {X Y Z T : B} (first : Word W X Y)
    (second : Word W Y Z) (third : Word W Z T) :
    Word.append (W := W) (Word.append (W := W) first second) third ≅
      Word.append (W := W) first (Word.append (W := W) second third) where
  hom := mk W (Cell.associator (W := W) first second third)
  inv := mk W (Cell.associatorInv (W := W) first second third)
  hom_inv_id := Quot.sound (Rel.associator_hom_inv first second third)
  inv_hom_id := Quot.sound (Rel.associator_inv_hom first second third)

/-- Quotient left-unitor isomorphism for word concatenation. -/
def wordLeftUnitorIso {X Y : B} (word : Word W X Y) :
    Word.append (W := W) (.nil X) word ≅ word where
  hom := mk W (Cell.leftUnitor (W := W) word)
  inv := mk W (Cell.leftUnitorInv (W := W) word)
  hom_inv_id := Quot.sound (Rel.left_unitor_hom_inv word)
  inv_hom_id := Quot.sound (Rel.left_unitor_inv_hom word)

/-- Quotient right-unitor isomorphism for word concatenation. -/
def wordRightUnitorIso {X Y : B} (word : Word W X Y) :
    Word.append (W := W) word (.nil Y) ≅ word where
  hom := mk W (Cell.rightUnitor (W := W) word)
  inv := mk W (Cell.rightUnitorInv (W := W) word)
  hom_inv_id := Quot.sound (Rel.right_unitor_hom_inv word)
  inv_hom_id := Quot.sound (Rel.right_unitor_inv_hom word)

/-- The presented marked localization has the same objects as the source
bicategory. -/
structure Localization (_marking : Bicategory.MorphismProperty B) where
  /-- Underlying source object. -/
  as : B

/-- Marked words are the 1-cells of the presented localization. -/
instance localizationQuiver : Quiver (Localization W) where
  Hom X Y := Word W X.as Y.as

/-- Empty words and executable concatenation supply identities and
composition of localization 1-cells. -/
instance localizationCategoryStruct : CategoryStruct (Localization W) where
  id X := .nil X.as
  comp := Word.append (W := W)

/-- The quotient local categories and the horizontal coherence relations
assemble into a genuine bicategory of marked zigzags. -/
instance localizationBicategory : Bicategory (Localization W) where
  homCategory := fun X Y => wordCategory W X.as Y.as
  whiskerLeft := @fun _ _ _ first _ _ α =>
    whiskerLeftHom W first α
  whiskerLeft_id := @fun _ _ _ first second =>
    Quot.sound (Rel.whisker_left_id first second)
  whiskerLeft_comp := by
    rintro X Y Z first second third fourth ⟨α⟩ ⟨β⟩
    exact Quot.sound (Rel.whisker_left_vcomp first α β)
  id_whiskerLeft := by
    rintro X Y first second ⟨α⟩
    exact Quot.sound (Rel.id_whisker_left α)
  comp_whiskerLeft := by
    rintro X Y Z T first second third third' ⟨α⟩
    exact Quot.sound (Rel.comp_whisker_left first second α)
  whiskerRight := @fun _ _ _ _ _ α postword =>
    whiskerRightHom W postword α
  id_whiskerRight := @fun _ _ _ first second =>
    Quot.sound (Rel.whisker_right_id first second)
  comp_whiskerRight := by
    rintro X Y Z first second third ⟨α⟩ ⟨β⟩ postword
    exact Quot.sound (Rel.whisker_right_vcomp postword α β)
  whiskerRight_id := by
    rintro X Y first second ⟨α⟩
    exact Quot.sound (Rel.whisker_right_id_word α)
  whiskerRight_comp := by
    rintro X Y Z T first first' ⟨α⟩ second third
    exact Quot.sound (Rel.whisker_right_comp second third α)
  whisker_assoc := by
    rintro X Y Z T first second second' ⟨α⟩ third
    exact Quot.sound (Rel.whisker_assoc first α third)
  whisker_exchange := by
    rintro X Y Z first first' second second' ⟨α⟩ ⟨β⟩
    exact Quot.sound (Rel.whisker_exchange α β)
  associator := @fun _ _ _ _ first second third =>
    wordAssociatorIso W first second third
  leftUnitor := @fun _ _ word => wordLeftUnitorIso W word
  rightUnitor := @fun _ _ word => wordRightUnitorIso W word
  pentagon := @fun _ _ _ _ _ first second third fourth =>
    Quot.sound (Rel.pentagon first second third fourth)
  triangle := @fun _ _ _ first second =>
    Quot.sound (Rel.triangle first second)

/-- The canonical inclusion of the source bicategory into the presented
marked-zigzag bicategory. -/
def inclusion : B ⥤ᵖ Localization W where
  obj X := ⟨X⟩
  map f := Word.forward W f
  map₂ α := mk W (Cell.original (W := W) α)
  map₂_id f := Quot.sound (Rel.original_id f)
  map₂_comp α β := Quot.sound (Rel.original_vcomp α β)
  mapId X := sourceIdIso W X
  mapComp f g := sourceCompIso W f g
  map₂_whisker_left := @fun _ _ _ f _ _ α =>
    Quot.sound (Rel.original_whisker_left f α)
  map₂_whisker_right := @fun _ _ _ _ _ α h =>
    Quot.sound (Rel.original_whisker_right α h)
  map₂_associator := @fun _ _ _ _ f g h =>
    Quot.sound (Rel.original_associator f g h)
  map₂_left_unitor := @fun _ _ f =>
    Quot.sound (Rel.original_left_unitor f)
  map₂_right_unitor := @fun _ _ f =>
    Quot.sound (Rel.original_right_unitor f)

/-- Every marked source arrow has an explicit adjoint-equivalence image in
the presented zigzag bicategory. Its unit and counit are exactly the presented
generators, and the quotient's marked triangle relation supplies adjunction
coherence without changing either generator. -/
noncomputable def markedEquivalence {X Y : B} (f : X ⟶ Y) (hf : W f) :
    (Localization.mk X : Localization W) ≌ Localization.mk Y :=
  { hom := Word.forward W f
    inv := Word.backward W f hf
    unit := markedUnitIso W f hf
    counit := markedCounitIso W f hf
    left_triangle := by
      apply Iso.ext
      dsimp [Bicategory.leftZigzagIso, bicategoricalIsoComp,
        Bicategory.leftZigzag, bicategoricalComp]
      simp only [whiskerRightIso_hom, whiskerLeftIso_hom, Iso.refl_hom]
      change mk W
          (Cell.vcomp
            (Cell.whiskerRight (Cell.markedUnit (W := W) f hf)
              (Word.forward W f))
        (Cell.vcomp
          (Cell.vcomp
            (Cell.associator (W := W) (Word.forward W f)
              (Word.backward W f hf) (Word.forward W f))
            (Cell.whiskerRight (Cell.id (Word.forward W f))
              (Word.append (W := W) (Word.backward W f hf)
                (Word.forward W f))))
          (Cell.whiskerLeft (Word.forward W f)
            (Cell.markedCounit (W := W) f hf)))) =
        mk W (Cell.vcomp
          (Cell.leftUnitor (W := W) (Word.forward W f))
          (Cell.rightUnitorInv (W := W) (Word.forward W f)))
      exact Quot.sound (Rel.marked_left_triangle f hf) }

@[simp]
theorem markedEquivalence_hom {X Y : B} (f : X ⟶ Y) (hf : W f) :
    (markedEquivalence W f hf).hom = Word.forward W f :=
  rfl

@[simp]
theorem markedEquivalence_inv {X Y : B} (f : X ⟶ Y) (hf : W f) :
    (markedEquivalence W f hf).inv = Word.backward W f hf :=
  rfl

/-- The canonical inclusion genuinely inverts every marked source arrow. -/
theorem inclusion_inverts : W.IsInvertedBy (inclusion W) := by
  intro X Y f hf
  change Bicategory.IsEquivalence (B := Localization W) (Word.forward W f)
  exact Bicategory.isEquivalence_hom (markedEquivalence W f hf)

end Presented

variable {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable (Q : B ⥤ᵖ C)

/-- Explicit inversion data for a pseudofunctor: every marked arrow is sent
to a chosen adjoint equivalence whose forward 1-cell is definitionally tied
to the pseudofunctor image by an equality proof.  Supplying this structure
makes word evaluation independent of global choice. -/
structure InversionData where
  /-- Chosen target adjoint equivalence for each marked source arrow. -/
  equivalence : ∀ {X Y : B} (f : X ⟶ Y), W f →
    Bicategory.Equivalence (Q.obj X) (Q.obj Y)
  /-- Its forward arrow is exactly the pseudofunctor image. -/
  hom_eq : ∀ {X Y : B} (f : X ⟶ Y) (hf : W f),
    (equivalence f hf).hom = Q.map f

namespace InversionData

/-- Choose explicit inversion data from the proposition-valued statement
that a pseudofunctor inverts the marking.  This is the sole choice boundary
of the marked-zigzag interpretation. -/
noncomputable def ofIsInvertedBy
    (hQ : W.IsInvertedBy Q) : InversionData W Q where
  equivalence f hf := (Classical.choice (hQ f hf)).1
  hom_eq f hf := (Classical.choice (hQ f hf)).2

variable (inversion : InversionData W Q)

/-- Interpret one oriented marked step in the target bicategory. -/
def evalStep {X Y : B} : Step W X Y → (Q.obj X ⟶ Q.obj Y)
  | .forward f => Q.map f
  | .backward f hf => (inversion.equivalence f hf).inv

/-- The single recursive interpretation of a marked zigzag. -/
def evalWord {X Y : B} : Word W X Y → (Q.obj X ⟶ Q.obj Y)
  | .atom step => evalStep W Q inversion step
  | .nil _ => 𝟙 _
  | .comp first second => evalWord first ≫ evalWord second

@[simp]
theorem evalStep_forward {X Y : B} (f : X ⟶ Y) :
    evalStep W Q inversion (Step.forward (W := W) f) = Q.map f :=
  rfl

@[simp]
theorem evalStep_backward {X Y : B} (f : X ⟶ Y) (hf : W f) :
    evalStep W Q inversion (Step.backward (W := W) f hf) =
      (inversion.equivalence f hf).inv :=
  rfl

@[simp]
theorem evalWord_nil (X : B) :
    evalWord W Q inversion (.nil X) = 𝟙 (Q.obj X) :=
  rfl

@[simp]
theorem evalWord_atom {X Y : B} (step : Step W X Y) :
    evalWord W Q inversion (.atom step) = evalStep W Q inversion step :=
  rfl

@[simp]
theorem evalWord_comp {X Y Z : B} (first : Word W X Y)
    (second : Word W Y Z) :
    evalWord W Q inversion (.comp first second) =
      evalWord W Q inversion first ≫ evalWord W Q inversion second :=
  rfl

/-- Horizontal composition of isomorphisms in the two local categories of a
bicategory. -/
noncomputable def horizontalIso
    {X Y Z : C} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}
    (first : f ≅ f') (second : g ≅ g') : f ≫ g ≅ f' ≫ g' :=
  whiskerRightIso first g ≪≫ whiskerLeftIso f' second

/-- **Sequential representation theorem for marked zigzags.** Interpreting
a concatenated word is canonically isomorphic to composing the two separate
interpretations. -/
noncomputable def evalAppendIso {X Y Z : B}
    (first : Word W X Y) (second : Word W Y Z) :
    evalWord W Q inversion (Word.append (W := W) first second) ≅
      evalWord W Q inversion first ≫ evalWord W Q inversion second :=
  Iso.refl _

@[simp]
theorem evalAppendIso_hom {X Y Z : B} (first : Word W X Y)
    (second : Word W Y Z) :
    (evalAppendIso W Q inversion first second).hom =
      𝟙 (evalWord W Q inversion first ≫ evalWord W Q inversion second) :=
  rfl

@[simp]
theorem evalAppendIso_inv {X Y Z : B} (first : Word W X Y)
    (second : Word W Y Z) :
    (evalAppendIso W Q inversion first second).inv =
      𝟙 (evalWord W Q inversion first ≫ evalWord W Q inversion second) :=
  rfl

/-- A one-step forward word evaluates definitionally to the image of its
source arrow. -/
noncomputable def evalForwardIso {X Y : B} (f : X ⟶ Y) :
    evalWord W Q inversion (Word.forward W f) ≅ Q.map f :=
  Iso.refl _

/-- A one-step reverse word evaluates definitionally to the chosen inverse of
its marked source arrow. -/
noncomputable def evalBackwardIso {X Y : B} (f : X ⟶ Y) (hf : W f) :
    evalWord W Q inversion (Word.backward W f hf) ≅
      (inversion.equivalence f hf).inv :=
  Iso.refl _

/-- Reorient the stored equality so that the pseudofunctor image is
isomorphic to the chosen equivalence's forward 1-cell. -/
noncomputable def imageIsoEquivalenceHom {X Y : B}
    (f : X ⟶ Y) (hf : W f) :
    Q.map f ≅ (inversion.equivalence f hf).hom :=
  eqToIso (inversion.hom_eq f hf).symm

/-- Normalize the chosen adjoint equivalence so that its forward 1-cell is
definitionally the pseudofunctor image. The inverse 1-cell is unchanged. -/
noncomputable def imageEquivalence {X Y : B}
    (f : X ⟶ Y) (hf : W f) : Q.obj X ≌ Q.obj Y :=
  (inversion.equivalence f hf).replaceHom
    (imageIsoEquivalenceHom W Q inversion f hf).symm

@[simp]
theorem imageEquivalence_hom {X Y : B} (f : X ⟶ Y) (hf : W f) :
    (imageEquivalence W Q inversion f hf).hom = Q.map f :=
  rfl

@[simp]
theorem imageEquivalence_inv {X Y : B} (f : X ⟶ Y) (hf : W f) :
    (imageEquivalence W Q inversion f hf).inv =
      (inversion.equivalence f hf).inv :=
  rfl

/-- The forward/reverse word of a marked arrow evaluates to the identity via
the chosen adjoint-equivalence unit. -/
noncomputable def evalForwardBackwardCancellation {X Y : B}
    (f : X ⟶ Y) (hf : W f) :
    evalWord W Q inversion
        (Word.append (W := W) (Word.forward W f)
          (Word.backward W f hf)) ≅
      𝟙 (Q.obj X) :=
  evalAppendIso W Q inversion (Word.forward W f) (Word.backward W f hf) ≪≫
    horizontalIso
      (evalForwardIso W Q inversion f)
      (evalBackwardIso W Q inversion f hf) ≪≫
    (imageEquivalence W Q inversion f hf).unit.symm

/-- The reverse/forward word of a marked arrow evaluates to the identity via
the chosen adjoint-equivalence counit. -/
noncomputable def evalBackwardForwardCancellation {X Y : B}
    (f : X ⟶ Y) (hf : W f) :
    evalWord W Q inversion
        (Word.append (W := W) (Word.backward W f hf)
          (Word.forward W f)) ≅
      𝟙 (Q.obj Y) :=
  evalAppendIso W Q inversion (Word.backward W f hf) (Word.forward W f) ≪≫
    horizontalIso
      (evalBackwardIso W Q inversion f hf)
      (evalForwardIso W Q inversion f) ≪≫
    (imageEquivalence W Q inversion f hf).counit

/-- Interpret every raw 2-cell generator in a marking-inverting target.
Forward source cells use `Q.map₂`; source identity/composition comparisons use
the pseudofunctor constraints; marked unit/counit generators use the chosen
adjoint equivalences; whiskering is conjugated by `evalAppendIso`. -/
noncomputable def evalCell :
    ∀ {X Y : B} {first second : Word W X Y}, Cell W first second →
      (evalWord W Q inversion first ⟶ evalWord W Q inversion second)
  | _, _, _, _, .id _ => 𝟙 _
  | _, _, _, _, .vcomp α β =>
      evalCell α ≫ evalCell β
  | _, _, _, _, .original α =>
      (evalForwardIso W Q inversion _).hom ≫ Q.map₂ α ≫
        (evalForwardIso W Q inversion _).inv
  | _, _, _, _, .sourceId =>
      (evalForwardIso W Q inversion _).hom ≫ (Q.mapId _).hom
  | _, _, _, _, .sourceIdInv =>
      (Q.mapId _).inv ≫ (evalForwardIso W Q inversion _).inv
  | _, _, _, _, .sourceComp f g =>
      (evalForwardIso W Q inversion (f ≫ g)).hom ≫
        (Q.mapComp f g).hom ≫
        (horizontalIso (evalForwardIso W Q inversion f).symm
          (evalForwardIso W Q inversion g).symm).hom ≫
        (evalAppendIso W Q inversion (Word.forward W f) (Word.forward W g)).inv
  | _, _, _, _, .sourceCompInv f g =>
      (evalAppendIso W Q inversion (Word.forward W f) (Word.forward W g)).hom ≫
        (horizontalIso (evalForwardIso W Q inversion f)
          (evalForwardIso W Q inversion g)).hom ≫
        (Q.mapComp f g).inv ≫ (evalForwardIso W Q inversion (f ≫ g)).inv
  | _, _, _, _, .markedUnit f hf =>
      (imageEquivalence W Q inversion f hf).unit.hom
  | _, _, _, _, .markedUnitInv f hf =>
      (imageEquivalence W Q inversion f hf).unit.inv
  | _, _, _, _, .markedCounit f hf =>
      (imageEquivalence W Q inversion f hf).counit.hom
  | _, _, _, _, .markedCounitInv f hf =>
      (imageEquivalence W Q inversion f hf).counit.inv
  | _, _, _, _, .whiskerLeft preword α =>
      (evalAppendIso W Q inversion preword _).hom ≫
        evalWord W Q inversion preword ◁ evalCell α ≫
        (evalAppendIso W Q inversion preword _).inv
  | _, _, _, _, .whiskerRight α postword =>
      (evalAppendIso W Q inversion _ postword).hom ≫
        evalCell α ▷ evalWord W Q inversion postword ≫
        (evalAppendIso W Q inversion _ postword).inv
  | _, _, _, _, .associator first second third =>
      (α_ (evalWord W Q inversion first) (evalWord W Q inversion second)
        (evalWord W Q inversion third)).hom
  | _, _, _, _, .associatorInv first second third =>
      (α_ (evalWord W Q inversion first) (evalWord W Q inversion second)
        (evalWord W Q inversion third)).inv
  | _, _, _, _, .leftUnitor word => (λ_ (evalWord W Q inversion word)).hom
  | _, _, _, _, .leftUnitorInv word => (λ_ (evalWord W Q inversion word)).inv
  | _, _, _, _, .rightUnitor word => (ρ_ (evalWord W Q inversion word)).hom
  | _, _, _, _, .rightUnitorInv word => (ρ_ (evalWord W Q inversion word)).inv
  | _, _, _, _, .transport rfl rfl α => evalCell α

set_option backward.isDefEq.respectTransparency.types false in
attribute [local simp] whisker_exchange in
/-- The raw 2-cell interpretation respects every relation of the presented
marked-zigzag bicategory. -/
theorem evalCell_respects {X Y : B} {first second : Word W X Y}
    {α β : Cell W first second} (relation : Presented.Rel W α β) :
    evalCell (W := W) (Q := Q) (inversion := inversion) α =
      evalCell (W := W) (Q := Q) (inversion := inversion) β := by
  induction relation <;>
    dsimp [evalCell, evalAppendIso, evalForwardIso, evalBackwardIso,
      horizontalIso,
      imageEquivalence,
      evalForwardBackwardCancellation, evalBackwardForwardCancellation,
      evalWord, evalStep, Word.forward, Word.backward, Word.single,
      Word.append] <;>
    (try simp) <;>
    (try cat_disch)
  case marked_left_triangle f hf =>
    have h := (imageEquivalence W Q inversion f hf).left_triangle_hom
    dsimp [Bicategory.leftZigzag, bicategoricalComp] at h
    dsimp [imageEquivalence] at h ⊢
    simpa only [whiskerRightIso_hom, Iso.refl_hom, id_whiskerRight,
      Category.comp_id, Category.id_comp, Category.assoc] using h
  case marked_right_triangle f hf =>
    have h := (imageEquivalence W Q inversion f hf).right_triangle_hom
    dsimp [Bicategory.rightZigzag, bicategoricalComp] at h
    dsimp [imageEquivalence] at h ⊢
    simpa only [whiskerRightIso_hom, Iso.refl_hom, id_whiskerRight,
      Category.comp_id, Category.id_comp, Category.assoc] using h

/-- Descend the raw 2-cell interpretation to quotient 2-cells. -/
noncomputable def evalHom {X Y : B} {first second : Word W X Y} :
    Presented.Hom W first second →
      (evalWord W Q inversion first ⟶ evalWord W Q inversion second) :=
  Quot.lift (evalCell (W := W) (Q := Q) (inversion := inversion))
    (fun _ _ relation => evalCell_respects W Q inversion relation)

/-- The descended interpretation is a functor on every presented local
hom-category. -/
noncomputable def evalHomFunctor (X Y : B) :
    Word W X Y ⥤ (Q.obj X ⟶ Q.obj Y) where
  obj word := evalWord W Q inversion word
  map α := evalHom W Q inversion α
  map_id word := rfl
  map_comp := by
    rintro first second third ⟨α⟩ ⟨β⟩
    rfl

/-- Extend a marking-inverting source pseudofunctor to the presented
marked-zigzag bicategory. -/
noncomputable def lift : Presented.Localization W ⥤ᵖ C where
  obj X := Q.obj X.as
  map word := evalWord W Q inversion word
  map₂ α := evalHom W Q inversion α
  map₂_id word := rfl
  map₂_comp := by
    rintro X Y first second third ⟨α⟩ ⟨β⟩
    rfl
  mapId _ := Iso.refl _
  mapComp first second := evalAppendIso W Q inversion first second
  map₂_whisker_left := by
    rintro X Y Z first second third ⟨α⟩
    rfl
  map₂_whisker_right := by
    rintro X Y Z first second ⟨α⟩ third
    rfl
  map₂_associator := by
    intro a b c d first second third
    change (α_ (evalWord W Q inversion first) (evalWord W Q inversion second)
      (evalWord W Q inversion third)).hom = _
    simp
    bicategory
  map₂_left_unitor := by
    intro a b word
    change (λ_ (evalWord W Q inversion word)).hom = _
    simp
    bicategory
  map₂_right_unitor := by
    intro a b word
    change (ρ_ (evalWord W Q inversion word)).hom = _
    simp
    bicategory

@[simp]
theorem lift_obj_mk (X : B) :
    (lift W Q inversion).obj (Presented.Localization.mk X) = Q.obj X :=
  rfl

@[simp]
theorem lift_map_forward {X Y : B} (f : X ⟶ Y) :
    (lift W Q inversion).map (Word.forward W f) = Q.map f :=
  rfl

@[simp]
theorem lift_map₂_original {X Y : B} {f g : X ⟶ Y} (α : f ⟶ g) :
    (lift W Q inversion).map₂
        ((Presented.inclusion W).map₂ α) = Q.map₂ α := by
  simp [lift, Presented.inclusion, evalHom, evalCell, evalForwardIso,
    evalWord, Word.forward, Word.single, evalStep]
  rfl

/-- Restrict the universal word lift back along the canonical inclusion. -/
noncomputable abbrev restrictedLift : B ⥤ᵖ C :=
  (Presented.inclusion W).comp (lift W Q inversion)

@[simp]
theorem restrictedLift_obj (X : B) :
    (restrictedLift W Q inversion).obj X = Q.obj X :=
  rfl

@[simp]
theorem restrictedLift_map {X Y : B} (f : X ⟶ Y) :
    (restrictedLift W Q inversion).map f = Q.map f :=
  rfl

@[simp]
theorem restrictedLift_map₂ {X Y : B} {f g : X ⟶ Y} (α : f ⟶ g) :
    (restrictedLift W Q inversion).map₂ α = Q.map₂ α :=
  lift_map₂_original W Q inversion α

@[simp]
theorem restrictedLift_mapId (X : B) :
    (restrictedLift W Q inversion).mapId X = Q.mapId X := by
  apply Iso.ext
  change evalCell (W := W) (Q := Q) (inversion := inversion)
      (Cell.sourceId (W := W)) ≫ 𝟙 _ = (Q.mapId X).hom
  dsimp [evalCell, evalForwardIso, evalWord, Word.forward, Word.single,
    evalStep]
  simp

@[simp]
theorem restrictedLift_mapComp {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (restrictedLift W Q inversion).mapComp f g = Q.mapComp f g := by
  apply Iso.ext
  change evalCell (W := W) (Q := Q) (inversion := inversion)
      (Cell.sourceComp (W := W) f g) ≫ 𝟙 _ = (Q.mapComp f g).hom
  dsimp [evalCell, evalAppendIso, evalForwardIso, horizontalIso, evalWord,
    Word.forward, Word.single, evalStep]
  simp

attribute [nolint simpNF] restrictedLift_mapId restrictedLift_mapComp

/-- Forward strong transformation exhibiting that the universal lift
restricts to the original marking-inverting pseudofunctor. -/
noncomputable def factorizationHom : restrictedLift W Q inversion ⟶ Q where
  app X := 𝟙 (Q.obj X)
  naturality f := (ρ_ (Q.map f)) ≪≫ (λ_ (Q.map f)).symm
  naturality_naturality η := by
    simp only [restrictedLift_map₂, restrictedLift_map, restrictedLift_obj]
    convert (Pseudofunctor.StrongTrans.id Q).naturality_naturality η using 1 <;> rfl
  naturality_id X := by
    simp only [restrictedLift_mapId, restrictedLift_map, restrictedLift_obj]
    convert (Pseudofunctor.StrongTrans.id Q).naturality_id X using 1 <;> rfl
  naturality_comp f g := by
    simp only [restrictedLift_mapComp, restrictedLift_map, restrictedLift_obj]
    convert (Pseudofunctor.StrongTrans.id Q).naturality_comp f g using 1 <;> rfl

/-- Reverse strong transformation for the restriction factorization. -/
noncomputable def factorizationInv : Q ⟶ restrictedLift W Q inversion where
  app X := 𝟙 (Q.obj X)
  naturality f := (ρ_ (Q.map f)) ≪≫ (λ_ (Q.map f)).symm
  naturality_naturality η := by
    simp only [restrictedLift_map₂, restrictedLift_map, restrictedLift_obj]
    convert (Pseudofunctor.StrongTrans.id Q).naturality_naturality η using 1 <;> rfl
  naturality_id X := by
    simp only [restrictedLift_mapId, restrictedLift_map, restrictedLift_obj]
    convert (Pseudofunctor.StrongTrans.id Q).naturality_id X using 1 <;> rfl
  naturality_comp f g := by
    simp only [restrictedLift_mapComp, restrictedLift_map, restrictedLift_obj]
    convert (Pseudofunctor.StrongTrans.id Q).naturality_comp f g using 1 <;> rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **Marked-zigzag factorization theorem.** The restriction of the
single-valued word interpreter is adjoint equivalent to the original
marking-inverting pseudofunctor.  The unit and counit modifications are
objectwise unitors; their modification equations are exactly bicategorical
coherence. -/
noncomputable def factorization : restrictedLift W Q inversion ≌ Q :=
  Bicategory.Equivalence.mkOfAdjointifyCounit
    (Pseudofunctor.StrongTrans.isoMk
      (η := 𝟙 (restrictedLift W Q inversion))
      (θ := factorizationHom W Q inversion ≫ factorizationInv W Q inversion)
      (fun X => (ρ_ (𝟙 (Q.obj X))).symm)
      (by
        intro X Y f
        simp only [restrictedLift_map, restrictedLift_obj]
        dsimp [factorizationHom, factorizationInv]
        bicategory))
    (Pseudofunctor.StrongTrans.isoMk
      (η := factorizationInv W Q inversion ≫ factorizationHom W Q inversion)
      (θ := 𝟙 Q)
      (fun X => ρ_ (𝟙 (Q.obj X)))
      (by
        intro X Y f
        dsimp [factorizationHom, factorizationInv]
        bicategory))

/-- Every pseudofunctor that inverts the marking factors through the
presented marked-zigzag localization, up to an explicit adjoint equivalence
of pseudofunctors. -/
theorem factorsThrough (hQ : W.IsInvertedBy Q) :
    (Presented.inclusion W).FactorsThrough Q :=
  let inversion := ofIsInvertedBy W Q hQ
  ⟨lift W Q inversion, ⟨factorization W Q inversion⟩⟩

/-- Machine-facing package for the executable marked-zigzag syntax and its
single-valued interpretation under chosen inversion data. -/
structure InterpretationCore where
  /-- Recursive target interpretation. -/
  eval : ∀ {X Y : B}, Word W X Y → (Q.obj X ⟶ Q.obj Y)
  /-- The packaged interpretation is the canonical recursion. -/
  eval_eq : ∀ {X Y : B} (word : Word W X Y),
    eval word = evalWord W Q inversion word
  /-- Concatenation is represented by target composition up to canonical
  coherence. -/
  appendIso : ∀ {X Y Z : B} (first : Word W X Y) (second : Word W Y Z),
    eval (Word.append (W := W) first second) ≅ eval first ≫ eval second
  /-- Marked forward/reverse cancellation. -/
  forwardBackward : ∀ {X Y : B} (f : X ⟶ Y) (hf : W f),
    eval (Word.append (W := W) (Word.forward W f)
      (Word.backward W f hf)) ≅
      𝟙 (Q.obj X)
  /-- Marked reverse/forward cancellation. -/
  backwardForward : ∀ {X Y : B} (f : X ⟶ Y) (hf : W f),
    eval (Word.append (W := W) (Word.backward W f hf)
      (Word.forward W f)) ≅
      𝟙 (Q.obj Y)

attribute [nolint simpNF] InterpretationCore.mk.injEq

/-- Package the canonical interpretation and both marked cancellation
isomorphisms. -/
noncomputable def interpretationCore : InterpretationCore W Q inversion where
  eval := evalWord W Q inversion
  eval_eq := fun _ => rfl
  appendIso := evalAppendIso W Q inversion
  forwardBackward := evalForwardBackwardCancellation W Q inversion
  backwardForward := evalBackwardForwardCancellation W Q inversion

end InversionData

end CategoryTheory.Bicategory.MarkedZigzag
