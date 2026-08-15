import Ript.Models.FiniteFunction
import Ript.Semantics.Eval

/-!
# Executable bit-process example

This example interprets a typed one-bit signature in both the zero-cost finite
function model and the explicitly metered finite function model.
-/

set_option autoImplicit false

namespace Ript.Examples.BitProcesses

open Ript.Core
open Ript.Models
open Ript.Semantics
open Ript.Syntax

/-- The sole object symbol in the bit-process example. -/
inductive BitObject where
  /-- A classical one-bit wire. -/
  | bit
  deriving DecidableEq, Repr

/-- Primitive typed operations on the bit wire. -/
inductive BitGenerator : BitObject → BitObject → Type where
  /-- Boolean negation. -/
  | not : BitGenerator .bit .bit

/-- A one-bit signature in which negation costs one abstract unit. -/
def signature : Signature Nat where
  Obj := BitObject
  Gen := BitGenerator
  cost
    | .not => 1

/-- Interpret the bit signature as zero-cost functions in `FintypeCat`. -/
def zeroCostInterpretation : Interpretation signature FintypeCat where
  obj
    | .bit => FintypeCat.of Bool
  mapGen
    | .not => FintypeCat.homMk Bool.not
  mapGen_cost
    | .not => Nat.zero_le 1

/-- Interpret the bit signature as finite functions carrying explicit costs. -/
def meteredInterpretation :
    Interpretation signature FiniteFunction.Metered where
  obj
    | .bit => FiniteFunction.Metered.of Bool
  mapGen
    | .not => FiniteFunction.Metered.homMk Bool.not 1
  mapGen_cost
    | .not => le_rfl

/-- Negation followed by negation. -/
def notNot : Expr signature .bit .bit :=
  .comp (.gen .not) (.gen .not)

/-- Execute a bit expression in the metered finite function model. -/
def runMetered (expression : Expr signature .bit .bit) (input : Bool) : Bool :=
  FiniteFunction.Metered.apply (eval meteredInterpretation expression) input

/-- The computed syntax budget for two negations is two units. -/
example : notNot.syntaxCost = 2 := by decide

/-- The semantic metered cost for two negations is also two units. -/
example : processCost (R := Nat) (eval meteredInterpretation notNot) = 2 := by decide

-- Executable normalization result for double negation.
#eval runMetered notNot true

-- Executable budget check for double negation.
#eval decide (notNot.syntaxCost ≤ 2)

-- Executable result equality check on a finite input.
#eval decide (runMetered notNot false = false)

end Ript.Examples.BitProcesses
