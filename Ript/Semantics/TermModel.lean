import Ript.Semantics.Eval
import Ript.Syntax.Derivation

/-!
# The sequential term model

The term model has signature object symbols as objects and formal expressions
modulo explicit derivations as morphisms. Quotients are confined to this proof
layer; executable syntax remains unquotiented.
-/

set_option autoImplicit false

namespace Ript.Semantics

open CategoryTheory
open Ript.Core
open Ript.Syntax

universe u w

/-- The object type of the term model for a signature.  It is a transparent
alias so typed syntax indices and term-model objects elaborate interchangeably. -/
abbrev TermModel {R : Type w} (signature : Signature.{u, w} R) :=
  signature.Obj

namespace TermModel

variable {R : Type w} (signature : Signature.{u, w} R)

/-- The category whose morphisms are expressions modulo formal derivability. -/
instance category : Category.{u} (TermModel signature) where
  Hom X Y := Quotient (derivesSetoid signature X Y)
  id X := ⟦Expr.id X⟧
  comp := Quotient.map₂ Expr.comp fun _ _ hf _ _ hg ↦
    Derives.comp_congr hf hg
  id_comp := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (Derives.id_comp f)
  comp_id := by
    rintro X Y ⟨f⟩
    exact Quotient.sound (Derives.comp_id f)
  assoc := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact Quotient.sound (Derives.assoc f g h)

/-- Embed a raw expression into the quotient term model. -/
def quote {X Y : TermModel signature} (expression : Expr signature X Y) :
    X ⟶ Y :=
  Quotient.mk _ expression

@[simp]
theorem quote_id (X : TermModel signature) :
    quote signature (.id X) = 𝟙 X :=
  rfl

@[simp]
theorem quote_comp {X Y Z : TermModel signature}
    (left : Expr signature X Y) (right : Expr signature Y Z) :
    quote signature (.comp left right) =
      quote signature left ≫ quote signature right :=
  rfl

variable [AddCommMonoid R] [Preorder R]

/-- Cost on a term-model morphism, well-defined because derivations preserve
syntax cost. -/
def cost {X Y : TermModel signature} (f : X ⟶ Y) : R :=
  Quotient.lift Expr.syntaxCost
    (fun _ _ h ↦ Derives.syntaxCost_eq h) f

/-- The term-model process cost is exactly represented syntax cost. -/
instance hasProcessCost : HasProcessCost (TermModel signature) R where
  cost := cost signature
  cost_id _ := rfl
  cost_comp := by
    rintro X Y Z ⟨f⟩ ⟨g⟩
    exact le_rfl

/-- The canonical interpretation of generators into their own term model. -/
def interpretation : Interpretation signature (TermModel signature) where
  obj X := X
  mapGen g := ⟦Expr.gen g⟧
  mapGen_cost _ := le_rfl

/-- Evaluating into the term model returns the derivation class of the original
expression. -/
theorem eval_interpretation {X Y : signature.Obj} (expression : Expr signature X Y) :
    eval (interpretation signature) expression = quote signature expression := by
  induction expression with
  | gen _ => rfl
  | id _ => rfl
  | comp f g ihf ihg =>
      change eval (interpretation signature) f ≫ eval (interpretation signature) g = _
      rw [ihf, ihg]
      rfl

omit [Preorder R] in
/-- Term-model cost agrees exactly with the syntax cost of a representative. -/
theorem cost_mk {X Y : TermModel signature} (expression : Expr signature X Y) :
    cost signature (quote signature expression : X ⟶ Y) = expression.syntaxCost :=
  rfl

end TermModel

end Ript.Semantics
