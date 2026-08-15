import Ript.Semantics.MonoidalTermModel

/-!
# Relative completeness for symmetric monoidal syntax

Equality in the canonical symmetric monoidal term model is exactly formal
derivability. This is relative completeness with respect to the explicitly
constructed free quotient model.
-/

set_option autoImplicit false

namespace Ript.Semantics

open Ript.Core
open Ript.Syntax

universe u w

variable {R : Type w} [AddCommMonoid R] [Preorder R]
variable {signature : MonoidalSignature.{u, w} R}

/-- Equality under the canonical monoidal term-model interpretation implies
a formal symmetric monoidal derivation. -/
theorem monoidal_complete_via_term_model {X Y : signature.Obj}
    {f g : MonoidalExpr signature X Y}
    (h : monoidalEval (MonoidalTermModel.interpretation signature) f =
      monoidalEval (MonoidalTermModel.interpretation signature) g) :
    MonoidalDerives f g := by
  rw [MonoidalTermModel.eval_interpretation,
    MonoidalTermModel.eval_interpretation] at h
  exact Quotient.exact (MonoidalTermModel.canonicalQuote_injective signature h)

/-- Formal derivability is equivalent to equality in the canonical symmetric
monoidal term model. -/
theorem monoidal_soundness_iff_term_model {X Y : signature.Obj}
    {f g : MonoidalExpr signature X Y} :
    MonoidalDerives f g ↔
      monoidalEval (MonoidalTermModel.interpretation signature) f =
        monoidalEval (MonoidalTermModel.interpretation signature) g :=
  ⟨monoidal_soundness (MonoidalTermModel.interpretation signature),
    monoidal_complete_via_term_model⟩

/-- The computed syntax budget is exact in the free symmetric monoidal term model. -/
theorem monoidal_budget_complete_in_free_model {X Y : signature.Obj}
    (expression : MonoidalExpr signature X Y) :
    processCost (R := R)
      (monoidalEval (MonoidalTermModel.interpretation signature) expression) =
        expression.syntaxCost := by
  rw [MonoidalTermModel.eval_interpretation]
  exact MonoidalTermModel.cost_canonicalQuote signature expression

end Ript.Semantics
