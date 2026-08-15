import Mathlib.Algebra.Group.Defs
import Ript.Syntax.Monoidal

/-!
# Computable costs for monoidal expressions

Primitive costs add under both sequential and parallel composition. All
coherence and symmetry morphisms are structural and therefore have zero
syntax cost.
-/

set_option autoImplicit false

namespace Ript.Syntax

universe u w

namespace MonoidalExpr

variable {R : Type w} [AddMonoid R]
variable {signature : MonoidalSignature.{u, w} R}

/-- Compute the resource upper bound of a monoidal process expression. -/
def syntaxCost {X Y : signature.Obj} (expression : MonoidalExpr signature X Y) : R :=
  match expression with
  | .gen g => signature.cost g
  | .id _ => 0
  | .comp f g => syntaxCost f + syntaxCost g
  | .tensor f g => syntaxCost f + syntaxCost g
  | .associator _ _ _ => 0
  | .associatorInv _ _ _ => 0
  | .leftUnitor _ => 0
  | .leftUnitorInv _ => 0
  | .rightUnitor _ => 0
  | .rightUnitorInv _ => 0
  | .braid _ _ => 0

/-- Identity expressions have zero syntax cost. -/
@[simp]
theorem syntaxCost_id (X : signature.Obj) : syntaxCost (.id X) = (0 : R) :=
  rfl

/-- Sequential syntax costs add. -/
@[simp]
theorem syntaxCost_comp {X Y Z : signature.Obj} (f : MonoidalExpr signature X Y)
    (g : MonoidalExpr signature Y Z) :
    syntaxCost (.comp f g) = syntaxCost f + syntaxCost g :=
  rfl

/-- Parallel syntax costs add. -/
@[simp]
theorem syntaxCost_tensor {X₁ Y₁ X₂ Y₂ : signature.Obj}
    (f : MonoidalExpr signature X₁ Y₁) (g : MonoidalExpr signature X₂ Y₂) :
    syntaxCost (.tensor f g) = syntaxCost f + syntaxCost g :=
  rfl

/-- Symmetry is a zero-cost structural expression. -/
@[simp]
theorem syntaxCost_braid (X Y : signature.Obj) :
    syntaxCost (.braid X Y) = (0 : R) :=
  rfl

end MonoidalExpr

end Ript.Syntax
