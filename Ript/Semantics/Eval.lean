import Ript.Resource.Budget
import Ript.Semantics.Interpretation
import Ript.Syntax.Cost

/-!
# Evaluation of sequential expressions

Evaluation is a structurally recursive, executable interpretation of the
stage-1 syntax. The central resource theorem bounds semantic cost by the
computed syntax cost.
-/

set_option autoImplicit false

namespace Ript.Semantics

open CategoryTheory
open Ript.Core
open Ript.Resource
open Ript.Syntax

universe u v w x

section Evaluation

variable {R : Type w} [AddCommMonoid R] [Preorder R]
variable {signature : Signature.{u, w} R}
variable {C : Type x} [Category.{v} C] [HasProcessCost C R]

/-- Recursively evaluate a typed sequential expression. -/
def eval (interpretation : Interpretation signature C) {X Y : signature.Obj}
    (expression : Expr signature X Y) :
    interpretation.obj X ⟶ interpretation.obj Y :=
  match expression with
  | .gen g => interpretation.mapGen g
  | .id _ => 𝟙 _
  | .comp f g => eval interpretation f ≫ eval interpretation g

variable (interpretation : Interpretation signature C)

/-- Evaluation maps syntactic identities to semantic identities. -/
@[simp]
theorem eval_id (X : signature.Obj) :
    eval interpretation (.id X) = 𝟙 (interpretation.obj X) :=
  rfl

/-- Evaluation maps syntactic composition to semantic composition. -/
@[simp]
theorem eval_comp {X Y Z : signature.Obj} (f : Expr signature X Y)
    (g : Expr signature Y Z) :
    eval interpretation (.comp f g) = eval interpretation f ≫ eval interpretation g :=
  rfl

/-- Evaluation maps a generator to its assigned semantic morphism. -/
@[simp]
theorem eval_gen {X Y : signature.Obj} (g : signature.Gen X Y) :
    eval interpretation (.gen g) = interpretation.mapGen g :=
  rfl

end Evaluation

section ResourceBound

variable {R : Type w} [AddCommMonoid R] [PartialOrder R] [ResourceAlgebra R]
variable {signature : Signature.{u, w} R}
variable {C : Type x} [Category.{v} C] [HasProcessCost C R]
variable (interpretation : Interpretation signature C)

/-- The semantic cost of an expression is bounded by its computed syntax cost. -/
theorem eval_cost_le {X Y : signature.Obj} (expression : Expr signature X Y) :
    processCost (R := R) (eval interpretation expression) ≤ expression.syntaxCost := by
  induction expression with
  | gen g => exact interpretation.mapGen_cost g
  | id X => simp
  | comp f g ihf ihg =>
      exact (processCost_comp (eval interpretation f) (eval interpretation g)).trans
        (add_le_add_resources ihf ihg)

/-- A syntactic budget proof yields a checked semantic budget proof. -/
theorem budget_sound {X Y : signature.Obj} {r : R} (expression : Expr signature X Y)
    (h : expression.syntaxCost ≤ r) : WithinBudget r (eval interpretation expression) :=
  (eval_cost_le interpretation expression).trans h

end ResourceBound

end Ript.Semantics
