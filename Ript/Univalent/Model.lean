import Mathlib.CategoryTheory.Groupoid
import Ript.Univalent.Syntax

/-!
# A quotient groupoid model of the internal universe

An `UniverseModel` assigns a small Lean type to each atomic interface.  Raw
internal equivalences and paths are quotiented by equality of their interpreted
type equivalences.  The quotient is important: it validates the groupoid laws
and the internal univalence computation rules without asserting equality of
the endpoint codes themselves.

The resulting `UniverseModel.Object` type is a genuine Mathlib groupoid.  Its
morphisms are interpreted internal identities, and every morphism is inverted
by path symmetry.
-/

set_option autoImplicit false

namespace Ript.Univalent

open CategoryTheory

universe u

/-- External set-level data interpreting the atoms of the deep universe. -/
structure UniverseModel (Atom : Type u) where
  /-- The small Lean type assigned to each atomic interface code. -/
  atomSemantics : Atom → Type

namespace UniverseModel

variable {Atom : Type u} (M : UniverseModel Atom)
variable {A B C D : Code Atom}

/-- Semantic equality of raw internal equivalence expressions. -/
def equivSetoid (A B : Code Atom) : Setoid (EquivExpr A B) where
  r first second :=
    first.denote M.atomSemantics = second.denote M.atomSemantics
  iseqv := {
    refl := fun _ ↦ rfl
    symm := fun h ↦ h.symm
    trans := fun h₁ h₂ ↦ h₁.trans h₂ }

/-- Semantic equality of raw internal identity expressions. -/
def pathSetoid (A B : Code Atom) : Setoid (PathExpr A B) where
  r first second :=
    first.denote M.atomSemantics = second.denote M.atomSemantics
  iseqv := {
    refl := fun _ ↦ rfl
    symm := fun h ↦ h.symm
    trans := fun h₁ h₂ ↦ h₁.trans h₂ }

/-- Internal structural equivalences modulo equality in the chosen model. -/
abbrev InternalEquiv (A B : Code Atom) : Type u :=
  Quotient (M.equivSetoid A B)

/-- Internal identities modulo equality in the chosen model. -/
abbrev Identity (A B : Code Atom) : Type u :=
  Quotient (M.pathSetoid A B)

namespace InternalEquiv

/-- Embed a raw equivalence expression into its semantic quotient. -/
def mk (equiv : EquivExpr A B) : M.InternalEquiv A B :=
  Quotient.mk (M.equivSetoid A B) equiv

/-- Interpret an internal equivalence as a Lean type equivalence.  This is
well-defined because the quotient relation is semantic equality. -/
def interpret (equiv : M.InternalEquiv A B) :
    Code.denote M.atomSemantics A ≃ Code.denote M.atomSemantics B :=
  Quotient.lift (EquivExpr.denote M.atomSemantics) (fun _ _ h ↦ h) equiv

@[simp]
theorem interpret_mk (equiv : EquivExpr A B) :
    interpret M (mk M equiv) = equiv.denote M.atomSemantics :=
  rfl

/-- Two internal equivalences are equal when their external interpretations
are equal. -/
theorem eq_of_interpret_eq {first second : M.InternalEquiv A B}
    (h : interpret M first = interpret M second) : first = second := by
  induction first using Quotient.inductionOn with
  | _ first =>
      induction second using Quotient.inductionOn with
      | _ second => exact Quotient.sound h

/-- Reflexive internal equivalence. -/
def refl (A : Code Atom) : M.InternalEquiv A A :=
  mk M (.refl A)

/-- Inverse of an internal equivalence. -/
def symm (equiv : M.InternalEquiv A B) : M.InternalEquiv B A :=
  Quotient.map EquivExpr.symm (by
    intro first second h
    change (first.denote M.atomSemantics).symm =
      (second.denote M.atomSemantics).symm
    rw [h]) equiv

/-- Composition of internal equivalences. -/
def trans (first : M.InternalEquiv A B) (second : M.InternalEquiv B C) :
    M.InternalEquiv A C :=
  Quotient.map₂ EquivExpr.trans (by
    intro first first' hFirst second second' hSecond
    change (first.denote M.atomSemantics).trans
        (second.denote M.atomSemantics) =
      (first'.denote M.atomSemantics).trans
        (second'.denote M.atomSemantics)
    rw [hFirst, hSecond]) first second

/-- Internal equivalences are closed under disjoint sum. -/
def sumCongr (left : M.InternalEquiv A B) (right : M.InternalEquiv C D) :
    M.InternalEquiv (.sum A C) (.sum B D) :=
  Quotient.map₂ EquivExpr.sumCongr (by
    intro left left' hLeft right right' hRight
    change Equiv.sumCongr (left.denote M.atomSemantics)
        (right.denote M.atomSemantics) =
      Equiv.sumCongr (left'.denote M.atomSemantics)
        (right'.denote M.atomSemantics)
    rw [hLeft, hRight]) left right

/-- Internal equivalences are closed under parallel tensor. -/
def tensorCongr (left : M.InternalEquiv A B) (right : M.InternalEquiv C D) :
    M.InternalEquiv (.tensor A C) (.tensor B D) :=
  Quotient.map₂ EquivExpr.tensorCongr (by
    intro left left' hLeft right right' hRight
    change Equiv.prodCongr (left.denote M.atomSemantics)
        (right.denote M.atomSemantics) =
      Equiv.prodCongr (left'.denote M.atomSemantics)
        (right'.denote M.atomSemantics)
    rw [hLeft, hRight]) left right

@[simp]
theorem interpret_refl (A : Code Atom) :
    interpret M (refl M A) = Equiv.refl (Code.denote M.atomSemantics A) :=
  rfl

@[simp]
theorem interpret_symm (equiv : M.InternalEquiv A B) :
    interpret M (symm M equiv) = (interpret M equiv).symm := by
  induction equiv using Quotient.inductionOn
  rfl

@[simp]
theorem interpret_trans (first : M.InternalEquiv A B)
    (second : M.InternalEquiv B C) :
    interpret M (trans M first second) =
      (interpret M first).trans (interpret M second) := by
  induction first using Quotient.inductionOn
  induction second using Quotient.inductionOn
  rfl

end InternalEquiv

namespace Identity

/-- Embed a raw internal identity expression into its semantic quotient. -/
def mk (path : PathExpr A B) : M.Identity A B :=
  Quotient.mk (M.pathSetoid A B) path

/-- Interpret an internal identity as a Lean type equivalence.  The endpoint
codes remain distinct Lean values. -/
def interpret (path : M.Identity A B) :
    Code.denote M.atomSemantics A ≃ Code.denote M.atomSemantics B :=
  Quotient.lift (PathExpr.denote M.atomSemantics) (fun _ _ h ↦ h) path

@[simp]
theorem interpret_mk (path : PathExpr A B) :
    interpret M (mk M path) = path.denote M.atomSemantics :=
  rfl

/-- Internal identities are extensionally determined by their model
interpretations. -/
theorem eq_of_interpret_eq {first second : M.Identity A B}
    (h : interpret M first = interpret M second) : first = second := by
  induction first using Quotient.inductionOn with
  | _ first =>
      induction second using Quotient.inductionOn with
      | _ second => exact Quotient.sound h

/-- Reflexive internal identity. -/
def refl (A : Code Atom) : M.Identity A A :=
  mk M (.refl A)

/-- Symmetry of internal identity. -/
def symm (path : M.Identity A B) : M.Identity B A :=
  Quotient.map PathExpr.symm (by
    intro first second h
    change (first.denote M.atomSemantics).symm =
      (second.denote M.atomSemantics).symm
    rw [h]) path

/-- Transitivity of internal identity. -/
def trans (first : M.Identity A B) (second : M.Identity B C) : M.Identity A C :=
  Quotient.map₂ PathExpr.trans (by
    intro first first' hFirst second second' hSecond
    change (first.denote M.atomSemantics).trans
        (second.denote M.atomSemantics) =
      (first'.denote M.atomSemantics).trans
        (second'.denote M.atomSemantics)
    rw [hFirst, hSecond]) first second

/-- Internal identities are closed under disjoint sum. -/
def sumCongr (left : M.Identity A B) (right : M.Identity C D) :
    M.Identity (.sum A C) (.sum B D) :=
  Quotient.map₂ PathExpr.sumCongr (by
    intro left left' hLeft right right' hRight
    change Equiv.sumCongr (left.denote M.atomSemantics)
        (right.denote M.atomSemantics) =
      Equiv.sumCongr (left'.denote M.atomSemantics)
        (right'.denote M.atomSemantics)
    rw [hLeft, hRight]) left right

/-- Internal identities are closed under parallel tensor. -/
def tensorCongr (left : M.Identity A B) (right : M.Identity C D) :
    M.Identity (.tensor A C) (.tensor B D) :=
  Quotient.map₂ PathExpr.tensorCongr (by
    intro left left' hLeft right right' hRight
    change Equiv.prodCongr (left.denote M.atomSemantics)
        (right.denote M.atomSemantics) =
      Equiv.prodCongr (left'.denote M.atomSemantics)
        (right'.denote M.atomSemantics)
    rw [hLeft, hRight]) left right

@[simp]
theorem interpret_refl (A : Code Atom) :
    interpret M (refl M A) = Equiv.refl (Code.denote M.atomSemantics A) :=
  rfl

@[simp]
theorem interpret_symm (path : M.Identity A B) :
    interpret M (symm M path) = (interpret M path).symm := by
  induction path using Quotient.inductionOn
  rfl

@[simp]
theorem interpret_trans (first : M.Identity A B) (second : M.Identity B C) :
    interpret M (trans M first second) =
      (interpret M first).trans (interpret M second) := by
  induction first using Quotient.inductionOn
  induction second using Quotient.inductionOn
  rfl

end Identity

/-- A wrapper making the chosen universe model part of the object type.  This
allows different atom interpretations to carry independent groupoid instances. -/
structure Object (M : UniverseModel Atom) where
  /-- The interface code represented by this groupoid object. -/
  code : Code Atom

namespace Object

/-- Interpret a universe object as its external small type. -/
abbrev denote (X : M.Object) : Type :=
  X.code.denote M.atomSemantics

end Object

/-- The groupoid interpretation of the deeply embedded universe.  Morphisms
are internal identities, composition is path transitivity, and inversion is
path symmetry. -/
instance objectGroupoid : Groupoid (M.Object) where
  Hom X Y := M.Identity X.code Y.code
  id X := Identity.refl M X.code
  comp first second := Identity.trans M first second
  inv path := Identity.symm M path
  id_comp path := by
    apply Identity.eq_of_interpret_eq M
    simp
  comp_id path := by
    apply Identity.eq_of_interpret_eq M
    simp
  assoc first second third := by
    apply Identity.eq_of_interpret_eq M
    simpa using Equiv.trans_assoc (Identity.interpret M first)
      (Identity.interpret M second) (Identity.interpret M third)
  inv_comp path := by
    apply Identity.eq_of_interpret_eq M
    simp
  comp_inv path := by
    apply Identity.eq_of_interpret_eq M
    simp

end UniverseModel

end Ript.Univalent
