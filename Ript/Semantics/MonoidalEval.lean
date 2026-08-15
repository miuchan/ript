import Ript.Semantics.MonoidalInterpretation
import Ript.Resource.Basic
import Ript.Syntax.MonoidalCost

/-!
# Evaluation of monoidal expressions

Every syntax constructor maps to its corresponding categorical operation. The
resource theorem combines sequential subadditivity, parallel subadditivity,
and zero-cost structural rewiring.
-/

set_option autoImplicit false

namespace Ript.Semantics

open CategoryTheory
open MonoidalCategory
open Ript.Core
open Ript.Resource
open Ript.Syntax

universe u v w x

section Evaluation

variable {R : Type w} [AddCommMonoid R] [Preorder R]
variable {signature : MonoidalSignature.{u, w} R}
variable {C : Type x} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [HasProcessCost C R]

/-- Evaluate a symmetric monoidal process expression. -/
def monoidalEval (interpretation : MonoidalInterpretation signature C)
    {X Y : signature.Obj} (expression : MonoidalExpr signature X Y) :
    monoidalObjEval interpretation.wire X ⟶ monoidalObjEval interpretation.wire Y :=
  match expression with
  | .gen g => interpretation.mapGen g
  | .id _ => 𝟙 _
  | .comp f g => monoidalEval interpretation f ≫ monoidalEval interpretation g
  | .tensor f g => monoidalEval interpretation f ⊗ₘ monoidalEval interpretation g
  | .associator _ _ _ => (α_ _ _ _).hom
  | .associatorInv _ _ _ => (α_ _ _ _).inv
  | .leftUnitor _ => (λ_ _).hom
  | .leftUnitorInv _ => (λ_ _).inv
  | .rightUnitor _ => (ρ_ _).hom
  | .rightUnitorInv _ => (ρ_ _).inv
  | .braid _ _ => (β_ _ _).hom

variable (interpretation : MonoidalInterpretation signature C)

/-- Monoidal evaluation preserves identities. -/
@[simp]
theorem monoidalEval_id (X : signature.Obj) :
    monoidalEval interpretation (.id X) = 𝟙 (monoidalObjEval interpretation.wire X) :=
  rfl

/-- Monoidal evaluation preserves sequential composition. -/
@[simp]
theorem monoidalEval_comp {X Y Z : signature.Obj}
    (f : MonoidalExpr signature X Y) (g : MonoidalExpr signature Y Z) :
    monoidalEval interpretation (.comp f g) =
      monoidalEval interpretation f ≫ monoidalEval interpretation g :=
  rfl

/-- Monoidal evaluation preserves tensor products. -/
@[simp]
theorem monoidalEval_tensor {X₁ Y₁ X₂ Y₂ : signature.Obj}
    (f : MonoidalExpr signature X₁ Y₁) (g : MonoidalExpr signature X₂ Y₂) :
    monoidalEval interpretation (.tensor f g) =
      monoidalEval interpretation f ⊗ₘ monoidalEval interpretation g :=
  rfl

end Evaluation

section ResourceBound

variable {R : Type w} [AddCommMonoid R] [PartialOrder R] [ResourceAlgebra R]
variable {signature : MonoidalSignature.{u, w} R}
variable {C : Type x} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable [HasProcessCost C R] [HasParallelProcessCost C R]
variable [HasFreeStructuralCost C R]
variable (interpretation : MonoidalInterpretation signature C)

/-- Semantic monoidal evaluation is bounded by the computed syntax cost. -/
theorem monoidalEval_cost_le {X Y : signature.Obj}
    (expression : MonoidalExpr signature X Y) :
    processCost (R := R) (monoidalEval interpretation expression) ≤ expression.syntaxCost := by
  induction expression with
  | gen g => exact interpretation.mapGen_cost g
  | id X => simp
  | comp f g ihf ihg =>
      exact (processCost_comp (monoidalEval interpretation f)
        (monoidalEval interpretation g)).trans (add_le_add_resources ihf ihg)
  | tensor f g ihf ihg =>
      exact (processCost_tensor (monoidalEval interpretation f)
        (monoidalEval interpretation g)).trans (add_le_add_resources ihf ihg)
  | associator X Y Z =>
      change processCost (R := R) (α_ _ _ _).hom ≤ 0
      exact le_of_eq (processCost_associator _ _ _)
  | associatorInv X Y Z =>
      change processCost (R := R) (α_ _ _ _).inv ≤ 0
      exact le_of_eq (processCost_associator_inv _ _ _)
  | leftUnitor X =>
      change processCost (R := R) (λ_ _).hom ≤ 0
      exact le_of_eq (processCost_leftUnitor _)
  | leftUnitorInv X =>
      change processCost (R := R) (λ_ _).inv ≤ 0
      exact le_of_eq (processCost_leftUnitor_inv _)
  | rightUnitor X =>
      change processCost (R := R) (ρ_ _).hom ≤ 0
      exact le_of_eq (processCost_rightUnitor _)
  | rightUnitorInv X =>
      change processCost (R := R) (ρ_ _).inv ≤ 0
      exact le_of_eq (processCost_rightUnitor_inv _)
  | braid X Y =>
      change processCost (R := R) (β_ _ _).hom ≤ 0
      exact le_of_eq (processCost_braiding _ _)

end ResourceBound

end Ript.Semantics
