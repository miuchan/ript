import Ript.Models.Quantum.Tensor

/-!
# Finite quantum operations

A quantum operation is a completely positive finite Kraus sum without the
trace-preservation equation required of a channel.  Operations are the
individual outcome branches of a quantum instrument.  Their equality is
extensional in the operational matrix map, while finite Kraus families remain
proof-only certificates.
-/

set_option autoImplicit false

namespace Ript.Models.Quantum

open Matrix TensorProduct
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker TensorProduct

universe u

/-- An explicit finite Kraus representation of a not-necessarily
trace-preserving matrix operation. -/
structure KrausOperationRepresentation (X Y : Object.{u})
    (map : Matrix X X ℂ → Matrix Y Y ℂ) where
  /-- Finite labels for the branch Kraus operators. -/
  index : Type u
  /-- Executable enumeration of the Kraus labels. -/
  fintype : Fintype index
  /-- Kraus operators from the source basis to the target basis. -/
  operators : index → Matrix Y X ℂ
  /-- The operation is exactly the finite Kraus sum. -/
  map_eq : ∀ ρ, map ρ = ∑ i, operators i * ρ * (operators i)ᴴ

namespace KrausOperationRepresentation

attribute [instance] KrausOperationRepresentation.fintype

variable {X Y : Object.{u}} {map : Matrix X X ℂ → Matrix Y Y ℂ}

theorem map_posSemidef (rep : KrausOperationRepresentation X Y map)
    {ρ : Matrix X X ℂ} (hρ : ρ.PosSemidef) : (map ρ).PosSemidef := by
  rw [rep.map_eq]
  apply Matrix.posSemidef_sum Finset.univ
  intro i _
  exact hρ.mul_mul_conjTranspose_same (rep.operators i)

theorem map_add (rep : KrausOperationRepresentation X Y map)
    (ρ σ : Matrix X X ℂ) : map (ρ + σ) = map ρ + map σ := by
  rw [rep.map_eq, rep.map_eq, rep.map_eq]
  simp_rw [Matrix.mul_add, Matrix.add_mul]
  exact Finset.sum_add_distrib

theorem map_zero (rep : KrausOperationRepresentation X Y map) : map 0 = 0 := by
  rw [rep.map_eq]
  simp

theorem map_smul (rep : KrausOperationRepresentation X Y map) (c : ℂ)
    (ρ : Matrix X X ℂ) : map (c • ρ) = c • map ρ := by
  rw [rep.map_eq, rep.map_eq]
  simp_rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [← Finset.smul_sum]

end KrausOperationRepresentation

/-- A finite completely positive operation.  Unlike `KrausChannel`, no
individual trace-preservation equation is required. -/
structure KrausOperation (X Y : Object.{u}) where
  /-- Operational action on arbitrary source matrices. -/
  map : Matrix X X ℂ → Matrix Y Y ℂ
  /-- Mere existence of a finite Kraus certificate. -/
  has_representation :
    Nonempty (KrausOperationRepresentation X Y map)

namespace KrausOperation

variable {V W X Y Z T : Object.{u}}

/-- Build an operation from an explicit finite Kraus family. -/
def ofOperators {I : Type u} [Fintype I]
    (operators : I → Matrix Y X ℂ) : KrausOperation X Y where
  map ρ := ∑ i, operators i * ρ * (operators i)ᴴ
  has_representation := ⟨
    { index := I
      fintype := inferInstance
      operators := operators
      map_eq := fun _ ↦ rfl }⟩

/-- Operations are equal exactly when their operational maps are equal. -/
@[ext]
theorem ext (first second : KrausOperation X Y)
    (map_eq : first.map = second.map) : first = second := by
  cases first
  cases second
  cases map_eq
  rfl

theorem map_posSemidef (operation : KrausOperation X Y)
    { ρ : Matrix X X ℂ } (hρ : ρ.PosSemidef) :
    (operation.map ρ).PosSemidef :=
  operation.has_representation.elim fun rep ↦ rep.map_posSemidef hρ

theorem map_add (operation : KrausOperation X Y) (ρ σ : Matrix X X ℂ) :
    operation.map (ρ + σ) = operation.map ρ + operation.map σ :=
  operation.has_representation.elim fun rep ↦ rep.map_add ρ σ

theorem map_zero (operation : KrausOperation X Y) : operation.map 0 = 0 :=
  operation.has_representation.elim fun rep ↦ rep.map_zero

theorem map_smul (operation : KrausOperation X Y) (c : ℂ)
    (ρ : Matrix X X ℂ) : operation.map (c • ρ) = c • operation.map ρ :=
  operation.has_representation.elim fun rep ↦ rep.map_smul c ρ

/-- Quantum operations also commute with real scalar multiplication through
the canonical real action on complex matrices. -/
theorem map_real_smul (operation : KrausOperation X Y) (r : ℝ)
    (ρ : Matrix X X ℂ) : operation.map (r • ρ) = r • operation.map ρ :=
  operation.has_representation.elim fun rep ↦ by
    rw [rep.map_eq, rep.map_eq]
    simp_rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [← Finset.smul_sum]

/-- Canonical complex-linear map underlying an operation. -/
def toLinearMap (operation : KrausOperation X Y) :
    Matrix X X ℂ →ₗ[ℂ] Matrix Y Y ℂ where
  toFun := operation.map
  map_add' := operation.map_add
  map_smul' := operation.map_smul

@[simp]
theorem toLinearMap_apply (operation : KrausOperation X Y)
    (ρ : Matrix X X ℂ) : operation.toLinearMap ρ = operation.map ρ := rfl

/-- Every trace-preserving channel has an underlying quantum operation. -/
def ofChannel (channel : KrausChannel X Y) : KrausOperation X Y where
  map := channel.map
  has_representation := channel.has_representation.elim fun rep ↦ ⟨
    { index := rep.index
      fintype := inferInstance
      operators := rep.operators
      map_eq := rep.map_eq }⟩

@[simp]
theorem ofChannel_map (channel : KrausChannel X Y) (ρ : Matrix X X ℂ) :
    (ofChannel channel).map ρ = channel.map ρ := rfl

/-- Serial composition of quantum operations. -/
def comp (first : KrausOperation X Y) (second : KrausOperation Y Z) :
    KrausOperation X Z where
  map ρ := second.map (first.map ρ)
  has_representation := first.has_representation.elim fun firstRep ↦
    second.has_representation.elim fun secondRep ↦ ⟨
      { index := secondRep.index × firstRep.index
        fintype := inferInstance
        operators := fun pair ↦
          secondRep.operators pair.1 * firstRep.operators pair.2
        map_eq := fun ρ ↦ by
          rw [secondRep.map_eq, firstRep.map_eq, Fintype.sum_prod_type]
          apply Fintype.sum_congr
          intro j
          rw [Matrix.mul_sum, Matrix.sum_mul]
          apply Fintype.sum_congr
          intro i
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc] }⟩

@[simp]
theorem comp_map (first : KrausOperation X Y) (second : KrausOperation Y Z)
    (ρ : Matrix X X ℂ) :
    (comp first second).map ρ = second.map (first.map ρ) := rfl

/-- Pairwise Kraus operators realize the canonical tensor map on every
matrix. -/
private theorem tensorLinearMap_eq_sum
    (first : KrausOperation V W) (second : KrausOperation X Y)
    (firstRep : KrausOperationRepresentation V W first.map)
    (secondRep : KrausOperationRepresentation X Y second.map)
    (τ : Matrix (V × X) (V × X) ℂ) :
    KrausChannel.tensorLinearMap first.toLinearMap second.toLinearMap τ =
      ∑ pair : firstRep.index × secondRep.index,
        (firstRep.operators pair.1 ⊗ₖ secondRep.operators pair.2) * τ *
          (firstRep.operators pair.1 ⊗ₖ secondRep.operators pair.2)ᴴ := by
  let equivalence : Matrix V V ℂ ⊗[ℂ] Matrix X X ℂ ≃ₗ[ℂ]
      Matrix (V × X) (V × X) ℂ :=
    kroneckerLinearEquiv V V X X ℂ
  rw [← equivalence.apply_symm_apply τ]
  induction equivalence.symm τ using TensorProduct.induction_on with
  | zero => simp [KrausChannel.tensorLinearMap]
  | tmul ρ σ =>
      simp only [equivalence, kroneckerLinearEquiv_tmul,
        KrausChannel.tensorLinearMap_kronecker]
      rw [Fintype.sum_prod_type]
      simp_rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
      rw [← KrausChannel.sum_kronecker_sum, ← firstRep.map_eq,
        ← secondRep.map_eq]
      rfl
  | add left right hleft hright =>
      rw [equivalence.map_add,
        (KrausChannel.tensorLinearMap first.toLinearMap second.toLinearMap).map_add]
      simp_rw [Matrix.mul_add, Matrix.add_mul]
      rw [Finset.sum_add_distrib, hleft, hright]

/-- Independent tensor product of quantum operations. -/
def tensor (first : KrausOperation V W) (second : KrausOperation X Y) :
    KrausOperation (Object.tensor V X) (Object.tensor W Y) where
  map := KrausChannel.tensorLinearMap first.toLinearMap second.toLinearMap
  has_representation := first.has_representation.elim fun firstRep ↦
    second.has_representation.elim fun secondRep ↦ ⟨
      { index := firstRep.index × secondRep.index
        fintype := inferInstance
        operators := fun pair ↦
          firstRep.operators pair.1 ⊗ₖ secondRep.operators pair.2
        map_eq := tensorLinearMap_eq_sum first second firstRep secondRep }⟩

@[simp]
theorem tensor_map_kronecker (first : KrausOperation V W)
    (second : KrausOperation X Y) (ρ : Matrix V V ℂ) (σ : Matrix X X ℂ) :
    (tensor first second).map (ρ ⊗ₖ σ) =
      first.map ρ ⊗ₖ second.map σ := by
  simp [tensor]

end KrausOperation

end Ript.Models.Quantum
