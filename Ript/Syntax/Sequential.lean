import Ript.Syntax.Signature

/-!
# Typed sequential process expressions

The first executable syntax contains only generators, identities, and serial
composition. Its indices make ill-typed compositions unrepresentable.
-/

set_option autoImplicit false

namespace Ript.Syntax

universe u w

/-- Well-typed sequential process expressions over a signature. -/
inductive Expr {R : Type w} (signature : Signature.{u, w} R) :
    signature.Obj → signature.Obj → Type u where
  /-- Embed a primitive generator. -/
  | gen {X Y : signature.Obj} (g : signature.Gen X Y) : Expr signature X Y
  /-- The identity expression at an object symbol. -/
  | id (X : signature.Obj) : Expr signature X X
  /-- Serially compose two expressions with a matching interface. -/
  | comp {X Y Z : signature.Obj} (f : Expr signature X Y)
      (g : Expr signature Y Z) : Expr signature X Z

namespace Expr

/-- The number of primitive generators occurring in an expression. -/
def generatorCount {R : Type w} {signature : Signature.{u, w} R}
    {X Y : signature.Obj} : Expr signature X Y → Nat
  | .gen _ => 1
  | .id _ => 0
  | .comp f g => generatorCount f + generatorCount g

end Expr

end Ript.Syntax
