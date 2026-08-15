import Mathlib.Tactic.CategoryTheory.Coherence
import Ript.Semantics.MonoidalEval
import Ript.Syntax.MonoidalDerivation

/-!
# Soundness of symmetric monoidal derivations

Every explicit category, tensor, coherence, and symmetry derivation is
respected by every symmetric monoidal interpretation.
-/

set_option autoImplicit false

namespace Ript.Semantics

open CategoryTheory
open MonoidalCategory
open Ript.Core
open Ript.Syntax

universe u v w x

variable {R : Type w} [AddCommMonoid R] [Preorder R]
variable {signature : MonoidalSignature.{u, w} R}
variable {C : Type x} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [HasProcessCost C R]
variable (interpretation : MonoidalInterpretation signature C)

/-- Formal symmetric monoidal derivability implies equality in every
interpretation. -/
theorem monoidal_soundness {X Y : signature.Obj}
    {f g : MonoidalExpr signature X Y} (derivation : MonoidalDerives f g) :
    monoidalEval interpretation f = monoidalEval interpretation g := by
  induction derivation with
  | hexagon_forward X Y Z =>
      simpa only [monoidalEval, monoidalObjEval_tensor,
        MonoidalCategory.tensorHom_id,
        MonoidalCategory.id_tensorHom] using
        (BraidedCategory.hexagon_forward
          (monoidalObjEval interpretation.wire X)
          (monoidalObjEval interpretation.wire Y)
          (monoidalObjEval interpretation.wire Z))
  | hexagon_reverse X Y Z =>
      simpa only [monoidalEval, monoidalObjEval_tensor,
        MonoidalCategory.tensorHom_id,
        MonoidalCategory.id_tensorHom] using
        (BraidedCategory.hexagon_reverse
          (monoidalObjEval interpretation.wire X)
          (monoidalObjEval interpretation.wire Y)
          (monoidalObjEval interpretation.wire Z))
  | _ => simp_all [monoidalEval]

end Ript.Semantics
