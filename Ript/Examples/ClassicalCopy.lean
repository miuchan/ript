import Ript.Models.FiniteFunction.Monoidal

/-!
# Executable classical copy and discard

This example evaluates the cartesian tensor, diagonal copy, and causal discard
laws on finite Boolean functions.  The general laws are kernel proofs in the
finite-function model; the `#eval` commands only expose their computational
content on concrete inputs.
-/

set_option autoImplicit false

namespace Ript.Examples.ClassicalCopy

open CategoryTheory
open MonoidalCategory
open ComonObj
open Ript.Core
open Ript.Models.FiniteFunction

/-- The finite Boolean system. -/
abbrev Bit : FintypeCat := FintypeCat.of Bool

/-- Boolean negation as a finite deterministic process. -/
def negate : Bit ⟶ Bit :=
  FintypeCat.homMk Bool.not

/-- Copying after negation agrees with negating both copied outputs. -/
theorem negate_copy_natural :
    negate ≫ Δ[Bit] = Δ[Bit] ≫ (negate ⊗ₘ negate) :=
  Ript.Models.FiniteFunction.copy_natural negate

/-- Boolean negation is causal because it preserves discard. -/
theorem negate_causal : CausalProcess negate :=
  Ript.Models.FiniteFunction.causal negate

/-- Copy duplicates a concrete Boolean value. -/
theorem copy_false : Δ[Bit] false = (false, false) :=
  rfl

/-- Tensor applies two Boolean functions independently. -/
theorem tensor_negate_false_true :
    (negate ⊗ₘ negate) (false, true) = (true, false) :=
  rfl

/-- Discard after negation returns the unique tensor-unit point. -/
theorem discard_negate_false :
    (negate ≫ ε[Bit]) false = PUnit.unit :=
  rfl

/-- Concrete output used by the executable copy contract. -/
def copiedFalse : Bool × Bool :=
  Δ[Bit] false

/-- Concrete output used by the executable tensor contract. -/
def independentlyNegated : Bool × Bool :=
  (negate ⊗ₘ negate) (false, true)

/-- Concrete output used by the executable discard contract. -/
def discardedNegation : PUnit :=
  (negate ≫ ε[Bit]) false

-- Executable diagonal-copy check.
#eval copiedFalse == (false, false)

-- Executable independent-tensor check.
#eval independentlyNegated == (true, false)

-- Executable causal-discard check.
#eval match discardedNegation with | .unit => true

end Ript.Examples.ClassicalCopy
