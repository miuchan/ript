import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Basic
import Ript.Higher.Equivalence
import Ript.Semantics.MonoidalTermModel

/-!
# A concrete object of the model bicategory

This example packages the free symmetric monoidal bit-process term model as a
`ProcessModel Nat`.  It then instantiates the cost-exact identity equivalence
and checks that its forward morphism preserves both exact costs and budget
feasibility.
-/

set_option autoImplicit false

namespace Ript.Examples.HigherModels

open CategoryTheory
open Ript.Core
open Ript.Higher
open Ript.Semantics
open Ript.Syntax

/-- The primitive wire of the monoidal example. -/
inductive Wire where
  /-- A classical bit interface. -/
  | bit
  deriving DecidableEq, Repr

/-- The sole primitive process is bit negation. -/
inductive Generator : FreeMonoidalCategory Wire → FreeMonoidalCategory Wire → Type where
  /-- Negation consumes one abstract resource unit. -/
  | not : Generator (.of .bit) (.of .bit)

/-- Symmetric monoidal bit-process signature with unit-cost negation. -/
def signature : MonoidalSignature Nat where
  Wire := Wire
  Gen := Generator
  cost
    | .not => 1

/-- The canonical free term model, packaged as an object of Ript's model
bicategory. -/
def termProcessModel : ProcessModel Nat where
  Carrier := MonoidalTermModel signature
  category := inferInstance
  monoidal := inferInstance
  symmetric := inferInstance
  costed := inferInstance
  parallelCost := inferInstance
  structuralCost := inferInstance

/-- The identity adjoint equivalence of the concrete bit-process model, with
explicit cost reflection in both directions. -/
def identityEquivalence :
    CostExactModelEquivalence termProcessModel termProcessModel :=
  CostExactModelEquivalence.id termProcessModel

/-- The concrete equivalence preserves the exact cost of every term-model
process. -/
example {X Y : termProcessModel} (f : X ⟶ Y) :
    processCost (R := Nat)
        (identityEquivalence.toEquivalence.hom.toFunctor.map f) =
      processCost (R := Nat) f :=
  identityEquivalence.hom_map_cost_eq f

/-- Consequently, every resource budget is preserved and reflected. -/
example {X Y : termProcessModel} (f : X ⟶ Y) (budget : Nat) :
    processCost (R := Nat)
        (identityEquivalence.toEquivalence.hom.toFunctor.map f) ≤ budget ↔
      processCost (R := Nat) f ≤ budget :=
  identityEquivalence.toEquivalence.hom.map_cost_le_iff f budget

end Ript.Examples.HigherModels
