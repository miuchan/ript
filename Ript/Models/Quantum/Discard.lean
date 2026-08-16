import Ript.Models.Quantum.Tensor

/-!
# Discarding finite quantum systems

Discarding is the trace channel into the one-dimensional quantum system.  A
finite family of basis bras gives its Kraus certificate.  Trace preservation
then proves the causal law: every channel followed by discard is discard, and
the trace channel is the unique channel into the unit system.
-/

set_option autoImplicit false

namespace Ript.Models.Quantum

open Matrix
open scoped BigOperators ComplexConjugate

universe u

namespace KrausChannel

variable {X Y : Object.{u}}

/-- The basis bra `⟨i|`, represented as a one-row matrix. -/
def basisBra (X : Object.{u}) (i : X) : Matrix (Object.unit) X ℂ :=
  fun _ j ↦ if i = j then 1 else 0

/-- Basis bras satisfy the Kraus completeness equation. -/
theorem basisBra_complete (X : Object.{u}) :
    ∑ i, (basisBra X i)ᴴ * basisBra X i = 1 := by
  ext j k
  simp [Matrix.sum_apply, basisBra, Matrix.mul_apply, Matrix.one_apply, eq_comm]

/-- The trace-preserving discard channel into the one-dimensional system. -/
def discard (X : Object.{u}) : KrausChannel X Object.unit :=
  ofOperators (basisBra X) (basisBra_complete X)

/-- The sole entry of a discarded matrix is its trace. -/
theorem discard_map_entry (X : Object.{u}) (ρ : Matrix X X ℂ) :
    (discard X).map ρ PUnit.unit PUnit.unit = ρ.trace := by
  have h := (discard X).map_trace ρ
  simpa [Matrix.trace] using h

/-- Discard is operationally the trace map. -/
theorem discard_map (X : Object.{u}) (ρ : Matrix X X ℂ) :
    (discard X).map ρ = fun _ _ ↦ ρ.trace := by
  ext i j
  cases i
  cases j
  exact discard_map_entry X ρ

/-- The trace channel is the unique Kraus channel into the one-dimensional
quantum system. -/
theorem eq_discard (f : KrausChannel X Object.unit) : f = discard X := by
  apply ext
  funext ρ
  ext i j
  cases i
  cases j
  have h := (f.map_trace ρ).trans ((discard X).map_trace ρ).symm
  simpa [Matrix.trace] using h

/-- Every finite Kraus channel is causal: following it by discard is the
source discard channel. -/
theorem comp_discard (f : KrausChannel X Y) :
    comp f (discard Y) = discard X :=
  eq_discard (comp f (discard Y))

end KrausChannel

end Ript.Models.Quantum
