import Ript.Core.StructuralCost
import Ript.Syntax.MonoidalSignature

/-!
# Interpretations of monoidal signatures

A monoidal interpretation assigns semantic objects to primitive wires and
cost-respecting semantic morphisms to primitive processes. Object trees are
evaluated recursively using the target tensor and unit.
-/

set_option autoImplicit false

namespace Ript.Semantics

open CategoryTheory
open MonoidalCategory
open Ript.Core
open Ript.Syntax

universe u v w x

/-- Interpret a free monoidal object tree in a target monoidal category.
Object evaluation depends only on the primitive wire type, not on the
signature's resource algebra. -/
def monoidalObjEval {Wire : Type u} {C : Type x}
    [Category.{v} C] [MonoidalCategory C]
    (wire : Wire → C) : FreeMonoidalCategory Wire → C
  | .of X => wire X
  | .unit => 𝟙_ C
  | .tensor X Y => monoidalObjEval wire X ⊗ monoidalObjEval wire Y

/-- Object evaluation maps a primitive wire to its assigned semantic object. -/
@[simp]
theorem monoidalObjEval_of {R : Type w} {signature : MonoidalSignature.{u, w} R}
    {C : Type x} [Category.{v} C] [MonoidalCategory C]
    (wire : signature.Wire → C) (X : signature.Wire) :
    monoidalObjEval wire (.of X) = wire X :=
  rfl

/-- Object evaluation maps the formal unit to the semantic tensor unit. -/
@[simp]
theorem monoidalObjEval_unit {R : Type w} {signature : MonoidalSignature.{u, w} R}
    {C : Type x} [Category.{v} C] [MonoidalCategory C]
    (wire : signature.Wire → C) :
    monoidalObjEval wire (.unit : signature.Obj) = 𝟙_ C :=
  rfl

/-- Object evaluation maps formal tensor to semantic tensor. -/
@[simp]
theorem monoidalObjEval_tensor {R : Type w} {signature : MonoidalSignature.{u, w} R}
    {C : Type x} [Category.{v} C] [MonoidalCategory C]
    (wire : signature.Wire → C) (X Y : signature.Obj) :
    monoidalObjEval wire (.tensor X Y) = monoidalObjEval wire X ⊗ monoidalObjEval wire Y :=
  rfl

/-- Object evaluation respects the tensor-object notation of the free monoidal category. -/
@[simp]
theorem monoidalObjEval_tensorObj {R : Type w}
    {signature : MonoidalSignature.{u, w} R}
    {C : Type x} [Category.{v} C] [MonoidalCategory C]
    (wire : signature.Wire → C) (X Y : signature.Obj) :
    monoidalObjEval wire (X ⊗ Y) = monoidalObjEval wire X ⊗ monoidalObjEval wire Y :=
  rfl

/-- Object evaluation respects the tensor-unit notation of the free monoidal category. -/
@[simp]
theorem monoidalObjEval_tensorUnit {R : Type w}
    {signature : MonoidalSignature.{u, w} R}
    {C : Type x} [Category.{v} C] [MonoidalCategory C]
    (wire : signature.Wire → C) :
    monoidalObjEval wire (𝟙_ (FreeMonoidalCategory signature.Wire)) = 𝟙_ C :=
  rfl

/-- A cost-respecting interpretation of a monoidal process signature. -/
structure MonoidalInterpretation {R : Type w} [AddCommMonoid R] [Preorder R]
    (signature : MonoidalSignature.{u, w} R) (C : Type x) [Category.{v} C]
    [MonoidalCategory C] [HasProcessCost C R] where
  /-- Interpret each primitive wire as a semantic object. -/
  wire : signature.Wire → C
  /-- Interpret each primitive process as a semantic morphism. -/
  mapGen : {X Y : signature.Obj} → signature.Gen X Y →
    (monoidalObjEval wire X ⟶ monoidalObjEval wire Y)
  /-- Semantic generator cost is bounded by the declared generator cost. -/
  mapGen_cost : ∀ {X Y : signature.Obj} (g : signature.Gen X Y),
    processCost (R := R) (mapGen g) ≤ signature.cost g

end Ript.Semantics
