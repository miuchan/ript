import Mathlib.Data.Matrix.PEquiv
import Mathlib.LinearAlgebra.Matrix.Reindex
import Ript.Models.Quantum.Kraus

/-!
# Quantum channels induced by finite basis equivalences

Every equivalence between two finite bases determines a unitary permutation
matrix and hence a one-operator Kraus channel.  We define its operational
action directly as matrix reindexing, then retain the permutation matrix as an
explicit Kraus certificate.  Extensional channel equality makes the identity
and composition laws reduce to the corresponding laws for `Matrix.reindex`.
-/

set_option autoImplicit false

namespace Ript.Models.Quantum

open Matrix
open scoped BigOperators ComplexConjugate

universe u

namespace KrausChannel

variable {X Y Z : Object.{u}}

/-- The permutation matrix carrying column vectors from basis `X` to basis
`Y` along `equivalence`. -/
def equivalenceOperator (equivalence : X ≃ Y) : Matrix Y X ℂ :=
  equivalence.symm.toPEquiv.toMatrix

/-- Conjugate transposition reverses the basis equivalence. -/
@[simp]
theorem equivalenceOperator_conjTranspose (equivalence : X ≃ Y) :
    (equivalenceOperator equivalence)ᴴ =
      equivalence.toPEquiv.toMatrix := by
  change (equivalence.symm.toPEquiv.toMatrixᵀ.map star) =
    equivalence.toPEquiv.toMatrix
  rw [Matrix.transpose_map]
  have map_star :
      equivalence.symm.toPEquiv.toMatrix.map star =
        (equivalence.symm.toPEquiv.toMatrix : Matrix Y X ℂ) := by
    ext y x
    simp [PEquiv.toMatrix_apply]
  rw [map_star]
  exact (PEquiv.toMatrix_symm (f := equivalence.symm.toPEquiv)).symm

/-- The single permutation Kraus operator is complete. -/
theorem equivalenceOperator_complete (equivalence : X ≃ Y) :
    (equivalenceOperator equivalence)ᴴ * equivalenceOperator equivalence = 1 := by
  rw [equivalenceOperator_conjTranspose, equivalenceOperator]
  rw [← PEquiv.toMatrix_trans]
  rw [← Equiv.toPEquiv_trans]
  simp

/-- A finite basis equivalence as a trace-preserving one-operator Kraus
channel.  Its operational action is conjugation by the corresponding
permutation matrix, equivalently simultaneous row and column reindexing. -/
def ofEquiv (equivalence : X ≃ Y) : KrausChannel X Y where
  map ρ := Matrix.reindex equivalence equivalence ρ
  has_representation := ⟨
    { index := PUnit
      fintype := inferInstance
      operators := fun _ ↦ equivalenceOperator equivalence
      map_eq := by
        intro ρ
        simp only [Fintype.sum_unique]
        rw [equivalenceOperator_conjTranspose, equivalenceOperator,
          PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
        rfl
      completeness := by
        simpa only [Fintype.sum_unique] using
          equivalenceOperator_complete equivalence }⟩

/-- A basis-equivalence channel acts by simultaneous matrix reindexing. -/
@[simp]
theorem ofEquiv_map (equivalence : X ≃ Y) (ρ : Matrix X X ℂ) :
    (ofEquiv equivalence).map ρ = Matrix.reindex equivalence equivalence ρ :=
  rfl

/-- The identity basis equivalence induces the identity quantum channel. -/
@[simp]
theorem ofEquiv_refl (X : Object.{u}) :
    ofEquiv (Equiv.refl X) = identity X := by
  apply ext
  funext ρ
  simp

/-- Serial composition of basis-equivalence channels is composition of the
basis equivalences. -/
@[simp]
theorem ofEquiv_comp (first : X ≃ Y) (second : Y ≃ Z) :
    comp (ofEquiv first) (ofEquiv second) = ofEquiv (first.trans second) := by
  apply ext
  funext ρ
  simp

end KrausChannel

end Ript.Models.Quantum
