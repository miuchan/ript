import Mathlib.Tactic.NormNum
import Ript.Models.FiniteStochastic
import Ript.Semantics.Eval

/-!
# Executable finite stochastic examples

This file checks exact rational probabilities for a fair coin, a noisy Boolean
negation channel, independent tensor composition, and copying. Every result is
computed by Lean from `ℚ≥0` data; no floating-point approximation is involved.
-/

set_option autoImplicit false

namespace Ript.Examples.StochasticBits

open Ript.Models.FiniteStochastic
open Ript.Models.FiniteStochastic.FinStoch
open Ript.Semantics
open Ript.Syntax

/-- The one-bit finite stochastic object. -/
abbrev bit : Object :=
  Object.of Bool

/-- An exact fair coin channel from the tensor unit to one bit. -/
def fairCoin : FinStoch Object.unit bit where
  prob _ _ := (1 : ℚ≥0) / 2
  normalized input := by
    cases input
    change (∑ output : Bool, (1 : ℚ≥0) / 2) = 1
    rw [Fintype.sum_bool]
    norm_num

/-- Boolean negation with probability `3/4`, and an unchanged output with
probability `1/4`. -/
def noisyNot : FinStoch bit bit where
  prob := fun (input output : Bool) ↦
    if output = !input then (3 : ℚ≥0) / 4 else (1 : ℚ≥0) / 4
  normalized input := by
    change Bool at input
    cases input with
    | false =>
        change (∑ output : Bool,
          if output = !Bool.false then (3 : ℚ≥0) / 4 else (1 : ℚ≥0) / 4) = 1
        rw [Fintype.sum_bool]
        norm_num
    | true =>
        change (∑ output : Bool,
          if output = !Bool.true then (3 : ℚ≥0) / 4 else (1 : ℚ≥0) / 4) = 1
        rw [Fintype.sum_bool]
        norm_num

/-- Exact Dirac channel for deterministic Boolean negation. -/
def deterministicNot : FinStoch bit bit :=
  dirac Bool.not

/-- Object symbols for a small stochastic signature. -/
inductive StochasticObject where
  /-- No input value. -/
  | unit
  /-- One classical bit. -/
  | bit
  deriving DecidableEq, Repr

/-- Primitive channels in the stochastic example. -/
inductive StochasticGenerator : StochasticObject → StochasticObject → Type where
  /-- Prepare a fair bit. -/
  | fairCoin : StochasticGenerator .unit .bit
  /-- Apply noisy negation. -/
  | noisyNot : StochasticGenerator .bit .bit

/-- Typed stochastic signature with one abstract unit of cost per primitive. -/
def signature : Signature Nat where
  Obj := StochasticObject
  Gen := StochasticGenerator
  cost
    | .fairCoin => 1
    | .noisyNot => 1

/-- Execute the stochastic signature in the exact finite stochastic category. -/
def interpretation : Interpretation signature Object where
  obj
    | .unit => Object.unit
    | .bit => bit
  mapGen
    | .fairCoin => fairCoin
    | .noisyNot => noisyNot
  mapGen_cost
    | .fairCoin => Nat.zero_le 1
    | .noisyNot => Nat.zero_le 1

/-- Prepare a fair coin, then apply noisy negation. -/
def coinThenNoisy : Expr signature .unit .bit :=
  .comp (.gen .fairCoin) (.gen .noisyNot)

/-- Read one exact output probability from the generic typed evaluator. -/
def runCoinThenNoisy (output : Bool) : ℚ≥0 :=
  (eval interpretation coinThenNoisy).prob PUnit.unit output

/-- A noisy negation preserves the uniform distribution. -/
theorem noisyNot_preserves_fair :
    comp fairCoin noisyNot = fairCoin := by
  apply FinStoch.ext
  intro input output
  cases input
  change Bool at output
  cases output with
  | false =>
      change (∑ middle : Bool, (1 : ℚ≥0) / 2 *
        (if Bool.false = !middle then (3 : ℚ≥0) / 4 else (1 : ℚ≥0) / 4)) = 1 / 2
      rw [Fintype.sum_bool]
      norm_num
  | true =>
      change (∑ middle : Bool, (1 : ℚ≥0) / 2 *
        (if Bool.true = !middle then (3 : ℚ≥0) / 4 else (1 : ℚ≥0) / 4)) = 1 / 2
      rw [Fintype.sum_bool]
      norm_num

/-- Two independent fair coins assign probability `1/4` to each pair. -/
theorem fair_pair_probability (output : Bool × Bool) :
    (tensor fairCoin fairCoin).prob (PUnit.unit, PUnit.unit) output =
      (1 : ℚ≥0) / 4 := by
  cases output with
  | mk left right =>
      cases left <;> cases right <;>
        norm_num [tensor, fairCoin, bit, Object.of]

-- Exact fair-coin probability.
#eval decide (fairCoin.prob PUnit.unit false = (1 : ℚ≥0) / 2)

-- Exact probability after Chapman--Kolmogorov composition.
#eval decide ((comp fairCoin noisyNot).prob PUnit.unit true = (1 : ℚ≥0) / 2)

-- Exact probability of an independent two-bit outcome.
#eval decide ((tensor fairCoin fairCoin).prob (PUnit.unit, PUnit.unit) (false, true) =
  (1 : ℚ≥0) / 4)

-- Copying is a deterministic Dirac channel.
#eval decide ((copy bit).prob true (true, true) = 1)

-- The generic typed interpreter executes the finite stochastic model.
#eval decide (runCoinThenNoisy true = (1 : ℚ≥0) / 2)

end Ript.Examples.StochasticBits
