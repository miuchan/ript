import Ript.Semantics.Soundness
import Ript.Semantics.TermModel

/-!
# Relative completeness via the term model

Equality in the term model is exactly formal derivability. This is the
stage-1 relative completeness theorem and avoids universe-wide quantification
over all semantic models.
-/

set_option autoImplicit false

namespace Ript.Semantics

open Ript.Resource
open Ript.Syntax

universe u w

variable {R : Type w} [AddCommMonoid R] [PartialOrder R] [ResourceAlgebra R]
variable {signature : Signature.{u, w} R}

omit [ResourceAlgebra R] in
/-- Equality under the canonical term-model interpretation implies a formal
derivation. -/
theorem complete_via_term_model {X Y : signature.Obj} {f g : Expr signature X Y}
    (h : eval (TermModel.interpretation signature) f =
      eval (TermModel.interpretation signature) g) : Derives f g := by
  rw [TermModel.eval_interpretation, TermModel.eval_interpretation] at h
  exact Quotient.exact h

omit [ResourceAlgebra R] in
/-- Formal derivability is equivalent to equality in the term model. -/
theorem soundness_iff_term_model {X Y : signature.Obj} {f g : Expr signature X Y} :
    Derives f g ↔
      eval (TermModel.interpretation signature) f =
        eval (TermModel.interpretation signature) g :=
  ⟨soundness (TermModel.interpretation signature), complete_via_term_model⟩

omit [ResourceAlgebra R] in
/-- In the free term model, the syntax budget bound is exact. -/
theorem budget_complete_in_free_model {X Y : signature.Obj}
    (expression : Expr signature X Y) :
    Ript.Core.processCost (R := R)
      (eval (TermModel.interpretation signature) expression) = expression.syntaxCost := by
  rw [TermModel.eval_interpretation]
  exact TermModel.cost_mk signature expression

end Ript.Semantics
