import Mathlib.Tactic.NormNum
import Ript.Models.Quantum.Discard

/-!
# Exact one-qubit Kraus example

The Boolean basis indexes a two-dimensional quantum system.  The Pauli-X
permutation matrix is proved unitary, packaged as a one-operator Kraus
channel, and proved to exchange the two computational-basis density matrices.
The final Boolean checks exercise the corresponding discrete basis action in
the kernel; arbitrary complex matrix evaluation is intentionally kept in the
proof layer because real-number equality is not computationally decidable.
-/

set_option autoImplicit false

namespace Ript.Examples.QubitChannel

open Matrix
open Ript.Models.Quantum
open scoped BigOperators ComplexConjugate ComplexOrder

/-- The two-dimensional quantum object with computational basis `Bool`. -/
abbrev qubit : Object :=
  ⟨Bool, inferInstance, inferInstance⟩

/-- Pauli-X in the Boolean computational basis. -/
def bitFlipOperator : Matrix qubit qubit ℂ :=
  fun row column ↦ if row = !column then 1 else 0

/-- Pauli-X satisfies `XᴴX = I`. -/
theorem bitFlipOperator_complete :
    bitFlipOperatorᴴ * bitFlipOperator = 1 := by
  ext row column
  change Bool at row column
  cases row <;> cases column <;>
    simp [bitFlipOperator, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The Pauli-X one-operator Kraus channel. -/
def bitFlip : KrausChannel qubit qubit :=
  KrausChannel.ofOperators (I := PUnit) (fun _ ↦ bitFlipOperator) (by
    simpa using bitFlipOperator_complete)

/-- Computational-basis pure state `|value⟩⟨value|`. -/
def basisDensity (value : Bool) : DensityMatrix qubit where
  matrix := Matrix.diagonal fun basis ↦ if basis = value then 1 else 0
  posSemidef := Matrix.PosSemidef.diagonal (by
    intro basis
    by_cases h : basis = value <;> simp [h])
  trace_one := by
    rw [Matrix.trace_diagonal]
    cases value <;> simp

/-- Pauli-X exchanges the two computational-basis density matrices. -/
theorem bitFlip_basisDensity (value : Bool) :
    bitFlip.applyDensity (basisDensity value) = basisDensity (!value) := by
  apply DensityMatrix.ext
  ext row column
  change Bool at value row column
  cases value <;> cases row <;> cases column <;>
    simp [bitFlip, KrausChannel.ofOperators, bitFlipOperator,
      basisDensity, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply]

/-- Two independent Pauli-X channels exchange both computational-basis bits. -/
theorem bitFlip_tensor_basisDensity (left right : Bool) :
    (KrausChannel.tensor bitFlip bitFlip).applyDensity
        ((basisDensity left).tensor (basisDensity right)) =
      (basisDensity (!left)).tensor (basisDensity (!right)) := by
  rw [KrausChannel.tensor_applyDensity, bitFlip_basisDensity,
    bitFlip_basisDensity]

/-- Discarding either computational-basis state returns its unit trace. -/
theorem discard_basisDensity (value : Bool) :
    (KrausChannel.discard qubit).map (basisDensity value).matrix
        PUnit.unit PUnit.unit = 1 := by
  rw [KrausChannel.discard_map_entry, (basisDensity value).trace_one]

/-- Executable action of Pauli-X on computational-basis labels. -/
def bitFlipBasisLabel (value : Bool) : Bool :=
  !value

-- Pauli-X maps `|0⟩` to `|1⟩` at the basis-label level.
#eval decide (bitFlipBasisLabel false = true)

-- Pauli-X maps `|1⟩` to `|0⟩` at the basis-label level.
#eval decide (bitFlipBasisLabel true = false)

end Ript.Examples.QubitChannel
