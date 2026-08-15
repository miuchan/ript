import Ript.Core.CostedProcess
import Ript.Syntax.Signature

/-!
# Interpretations of typed signatures

An interpretation assigns a semantic object to every object symbol and a
cost-respecting semantic morphism to every process generator.
-/

set_option autoImplicit false

namespace Ript.Semantics

open CategoryTheory
open Ript.Core
open Ript.Syntax

universe u v w x

/-- A cost-respecting interpretation of a process signature in a category. -/
structure Interpretation {R : Type w} [AddCommMonoid R] [Preorder R]
    (signature : Signature.{u, w} R) (C : Type x) [Category.{v} C]
    [HasProcessCost C R] where
  /-- Interpret each object symbol as a semantic object. -/
  obj : signature.Obj → C
  /-- Interpret each primitive process as a semantic morphism. -/
  mapGen : {X Y : signature.Obj} →
    signature.Gen X Y → (obj X ⟶ obj Y)
  /-- A generator's semantic cost does not exceed its declared cost. -/
  mapGen_cost : ∀ {X Y : signature.Obj} (g : signature.Gen X Y),
    processCost (R := R) (mapGen g) ≤ signature.cost g

end Ript.Semantics
