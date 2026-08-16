import Mathlib.Analysis.Matrix.Order

/-!
# Finite quantum systems and density matrices

This file introduces a quantum object independently of Ript's classical
finite-stochastic objects.  A state on `X` is a complex square matrix that is
positive semidefinite and has trace one.  Positivity uses Mathlib's
`Matrix.PosSemidef` under the scoped order on `ℂ`; it is not an entrywise
nonnegativity condition.
-/

set_option autoImplicit false

namespace Ript.Models.Quantum

open Matrix
open scoped ComplexOrder

universe u

/-- A finite-dimensional quantum system with executable basis enumeration and
equality.  The carrier indexes a chosen orthonormal basis. -/
structure Object where
  /-- Basis labels for the finite-dimensional Hilbert space. -/
  carrier : Type u
  /-- Executable enumeration of the chosen basis. -/
  fintype : Fintype carrier
  /-- Executable equality on basis labels. -/
  decEq : DecidableEq carrier

namespace Object

instance : CoeSort Object (Type u) :=
  ⟨Object.carrier⟩

attribute [instance] Object.fintype Object.decEq

/-- Bundle a finite type as a finite-dimensional quantum object. -/
def of (α : Type u) [Fintype α] [DecidableEq α] : Object :=
  ⟨α, inferInstance, inferInstance⟩

/-- The one-dimensional quantum system. -/
abbrev unit : Object :=
  ⟨PUnit, inferInstance, inferInstance⟩

/-- The tensor product of finite quantum systems, represented in the product
basis. -/
abbrev tensor (X Y : Object.{u}) : Object :=
  ⟨X × Y, inferInstance, inferInstance⟩

end Object

/-- A finite density matrix: a positive-semidefinite complex matrix with unit
trace. -/
structure DensityMatrix (X : Object.{u}) where
  /-- Matrix entries in the basis carried by `X`. -/
  matrix : Matrix X X ℂ
  /-- Operator positivity, expressed by nonnegative quadratic forms. -/
  posSemidef : matrix.PosSemidef
  /-- Quantum-state normalization. -/
  trace_one : matrix.trace = 1

namespace DensityMatrix

variable {X : Object.{u}}

/-- Density matrices are equal when their underlying matrices agree. -/
@[ext]
theorem ext (ρ σ : DensityMatrix X) (h : ρ.matrix = σ.matrix) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

end DensityMatrix

end Ript.Models.Quantum
