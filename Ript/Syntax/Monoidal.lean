import Mathlib.CategoryTheory.Monoidal.Free.Basic
import Ript.Syntax.MonoidalSignature

/-!
# Typed monoidal process expressions

This syntax extends the sequential core with tensor, associators, unitors, and
symmetry. Structural morphisms are explicit so evaluation can target a general
symmetric monoidal category rather than assuming definitional strictness.
-/

set_option autoImplicit false

namespace Ript.Syntax

open CategoryTheory

universe u w

/-- Well-typed symmetric monoidal process expressions over a signature. -/
inductive MonoidalExpr {R : Type w} (signature : MonoidalSignature.{u, w} R) :
    signature.Obj → signature.Obj → Type u where
  /-- Embed a primitive process generator. -/
  | gen {X Y : signature.Obj} (g : signature.Gen X Y) : MonoidalExpr signature X Y
  /-- Identity expression. -/
  | id (X : signature.Obj) : MonoidalExpr signature X X
  /-- Sequential composition. -/
  | comp {X Y Z : signature.Obj} (f : MonoidalExpr signature X Y)
      (g : MonoidalExpr signature Y Z) : MonoidalExpr signature X Z
  /-- Parallel tensor product. -/
  | tensor {X₁ Y₁ X₂ Y₂ : signature.Obj}
      (f : MonoidalExpr signature X₁ Y₁) (g : MonoidalExpr signature X₂ Y₂) :
      MonoidalExpr signature (.tensor X₁ X₂) (.tensor Y₁ Y₂)
  /-- Forward associator. -/
  | associator (X Y Z : signature.Obj) :
      MonoidalExpr signature (.tensor (.tensor X Y) Z) (.tensor X (.tensor Y Z))
  /-- Inverse associator. -/
  | associatorInv (X Y Z : signature.Obj) :
      MonoidalExpr signature (.tensor X (.tensor Y Z)) (.tensor (.tensor X Y) Z)
  /-- Forward left unitor. -/
  | leftUnitor (X : signature.Obj) :
      MonoidalExpr signature (.tensor .unit X) X
  /-- Inverse left unitor. -/
  | leftUnitorInv (X : signature.Obj) :
      MonoidalExpr signature X (.tensor .unit X)
  /-- Forward right unitor. -/
  | rightUnitor (X : signature.Obj) :
      MonoidalExpr signature (.tensor X .unit) X
  /-- Inverse right unitor. -/
  | rightUnitorInv (X : signature.Obj) :
      MonoidalExpr signature X (.tensor X .unit)
  /-- Symmetry exchanging two tensor factors. -/
  | braid (X Y : signature.Obj) :
      MonoidalExpr signature (.tensor X Y) (.tensor Y X)

end Ript.Syntax
