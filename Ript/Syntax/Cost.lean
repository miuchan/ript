import Mathlib.Algebra.Group.Defs
import Ript.Syntax.Sequential

/-!
# Computable syntax costs

Syntax cost is the declared generator cost added along serial composition.
-/

set_option autoImplicit false

namespace Ript.Syntax

universe u w

namespace Expr

variable {R : Type w} [AddMonoid R]
variable {signature : Signature.{u, w} R} {X Y Z : signature.Obj}

/-- Compute the additive resource upper bound of an expression. -/
def syntaxCost {X Y : signature.Obj} (expression : Expr signature X Y) : R :=
  match expression with
  | .gen g => signature.cost g
  | .id _ => 0
  | .comp f g => syntaxCost f + syntaxCost g

/-- The syntax cost of an identity is zero. -/
@[simp]
theorem syntaxCost_id (X : signature.Obj) : syntaxCost (.id X) = (0 : R) :=
  rfl

/-- Syntax cost is additive under serial composition. -/
@[simp]
theorem syntaxCost_comp (f : Expr signature X Y) (g : Expr signature Y Z) :
    syntaxCost (.comp f g) = syntaxCost f + syntaxCost g :=
  rfl

/-- A generator has its declared signature cost. -/
@[simp]
theorem syntaxCost_gen (g : signature.Gen X Y) :
    syntaxCost (.gen g) = signature.cost g :=
  rfl

end Expr

end Ript.Syntax
