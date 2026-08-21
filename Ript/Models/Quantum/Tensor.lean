import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.RingTheory.MatrixAlgebra
import Ript.Models.Quantum.Kraus

/-!
# Tensor products of finite quantum channels

Quantum systems use product bases, states use the matrix Kronecker product,
and channel tensor is defined extensionally through the canonical tensor
product of the channels' complex-linear operational maps.  Explicit pairwise
Kraus operators certify that this canonical map is again a trace-preserving
Kraus channel.
-/

set_option autoImplicit false

namespace Ript.Models.Quantum

open Matrix TensorProduct
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker TensorProduct

universe u

namespace DensityMatrix

variable {X Y : Object.{u}}

/-- Tensor two density matrices using the product basis. -/
def tensor (ρ : DensityMatrix X) (σ : DensityMatrix Y) :
    DensityMatrix (Object.tensor X Y) where
  matrix := ρ.matrix ⊗ₖ σ.matrix
  posSemidef := ρ.posSemidef.kronecker σ.posSemidef
  trace_one := by
    rw [Matrix.trace_kronecker, ρ.trace_one, σ.trace_one, one_mul]

/-- The matrix of a tensor-product state is the Kronecker product. -/
@[simp]
theorem tensor_matrix (ρ : DensityMatrix X) (σ : DensityMatrix Y) :
    (ρ.tensor σ).matrix = ρ.matrix ⊗ₖ σ.matrix := rfl

end DensityMatrix

namespace KrausChannel

variable {V W X Y Z T : Object.{u}}

/-- Canonical tensor product of operational matrix maps, transported through
Mathlib's matrix/tensor-product linear equivalence. -/
def tensorLinearMap
    (f : Matrix V V ℂ →ₗ[ℂ] Matrix W W ℂ)
    (g : Matrix X X ℂ →ₗ[ℂ] Matrix Y Y ℂ) :
    Matrix (V × X) (V × X) ℂ →ₗ[ℂ] Matrix (W × Y) (W × Y) ℂ :=
  (kroneckerLinearEquiv W W Y Y ℂ).toLinearMap.comp
    ((TensorProduct.map f g).comp
      (kroneckerLinearEquiv V V X X ℂ).symm.toLinearMap)

/-- The canonical tensor map acts componentwise on Kronecker products. -/
@[simp]
theorem tensorLinearMap_kronecker
    (f : Matrix V V ℂ →ₗ[ℂ] Matrix W W ℂ)
    (g : Matrix X X ℂ →ₗ[ℂ] Matrix Y Y ℂ)
    (ρ : Matrix V V ℂ) (σ : Matrix X X ℂ) :
    tensorLinearMap f g (ρ ⊗ₖ σ) = f ρ ⊗ₖ g σ := by
  simp [tensorLinearMap]

/-- A Kronecker product distributes over two finite sums. -/
theorem sum_kronecker_sum {I J : Type u} [Fintype I] [Fintype J]
    (a : I → Matrix V V ℂ) (b : J → Matrix X X ℂ) :
    (∑ i, a i) ⊗ₖ (∑ j, b j) = ∑ i, ∑ j, a i ⊗ₖ b j := by
  ext ⟨v, x⟩ ⟨v', x'⟩
  simp only [Matrix.kronecker_apply, Matrix.sum_apply]
  exact Fintype.sum_mul_sum (fun i ↦ a i v v') (fun j ↦ b j x x')

/-- Pairwise tensor products of two Kraus families act componentwise on
Kronecker-product matrices. -/
private theorem tensorKrausSum_kronecker
    {fmap : Matrix V V ℂ → Matrix W W ℂ}
    {gmap : Matrix X X ℂ → Matrix Y Y ℂ}
    (frep : KrausRepresentation V W fmap)
    (grep : KrausRepresentation X Y gmap)
    (ρ : Matrix V V ℂ) (σ : Matrix X X ℂ) :
    (∑ pair : frep.index × grep.index,
        (frep.operators pair.1 ⊗ₖ grep.operators pair.2) * (ρ ⊗ₖ σ) *
          (frep.operators pair.1 ⊗ₖ grep.operators pair.2)ᴴ) =
      fmap ρ ⊗ₖ gmap σ := by
  rw [Fintype.sum_prod_type]
  simp_rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  rw [← sum_kronecker_sum]
  rw [← frep.map_eq, ← grep.map_eq]

/-- The pairwise Kraus sum realizes the canonical tensor product on every
matrix, not only on decomposable matrices. -/
private theorem tensorLinearMap_eq_krausSum
    (f : KrausChannel V W) (g : KrausChannel X Y)
    (frep : KrausRepresentation V W f.map)
    (grep : KrausRepresentation X Y g.map)
    (τ : Matrix (V × X) (V × X) ℂ) :
    tensorLinearMap f.toLinearMap g.toLinearMap τ =
      ∑ pair : frep.index × grep.index,
        (frep.operators pair.1 ⊗ₖ grep.operators pair.2) * τ *
          (frep.operators pair.1 ⊗ₖ grep.operators pair.2)ᴴ := by
  let e : Matrix V V ℂ ⊗[ℂ] Matrix X X ℂ ≃ₗ[ℂ]
      Matrix (V × X) (V × X) ℂ := kroneckerLinearEquiv V V X X ℂ
  rw [← e.apply_symm_apply τ]
  induction e.symm τ using TensorProduct.induction_on with
  | zero => simp [tensorLinearMap]
  | tmul ρ σ =>
      simp only [e, kroneckerLinearEquiv_tmul, tensorLinearMap_kronecker]
      exact (tensorKrausSum_kronecker frep grep ρ σ).symm
  | add a b ha hb =>
      rw [e.map_add, (tensorLinearMap f.toLinearMap g.toLinearMap).map_add]
      simp_rw [Matrix.mul_add, Matrix.add_mul]
      rw [Finset.sum_add_distrib, ha, hb]

/-- Linear maps on product-indexed matrices agree when they agree on every
Kronecker product.  This is the reusable extensionality principle for tensor
coherence proofs. -/
theorem linearMap_ext_kronecker
    {f g : Matrix (V × X) (V × X) ℂ →ₗ[ℂ] Matrix Z Z ℂ}
    (h : ∀ (ρ : Matrix V V ℂ) (σ : Matrix X X ℂ),
      f (ρ ⊗ₖ σ) = g (ρ ⊗ₖ σ)) : f = g := by
  apply LinearMap.ext
  intro τ
  let e : Matrix V V ℂ ⊗[ℂ] Matrix X X ℂ ≃ₗ[ℂ]
      Matrix (V × X) (V × X) ℂ := kroneckerLinearEquiv V V X X ℂ
  rw [← e.apply_symm_apply τ]
  induction e.symm τ using TensorProduct.induction_on with
  | zero => simp
  | tmul ρ σ =>
      simp only [e, kroneckerLinearEquiv_tmul]
      exact h ρ σ
  | add a b ha hb => rw [e.map_add, f.map_add, g.map_add, ha, hb]

/-- Linear maps out of a left-associated triple product agree when they agree
on all left-associated triple Kronecker products. -/
theorem linearMap_ext_kronecker₃_left
    {f g : Matrix ((V × X) × Z) ((V × X) × Z) ℂ →ₗ[ℂ]
      Matrix T T ℂ}
    (h : ∀ (ρ : Matrix V V ℂ) (σ : Matrix X X ℂ)
      (τ : Matrix Z Z ℂ),
      f ((ρ ⊗ₖ σ) ⊗ₖ τ) = g ((ρ ⊗ₖ σ) ⊗ₖ τ)) : f = g := by
  apply LinearMap.ext
  intro ω
  let outer : Matrix (V × X) (V × X) ℂ ⊗[ℂ] Matrix Z Z ℂ ≃ₗ[ℂ]
      Matrix ((V × X) × Z) ((V × X) × Z) ℂ :=
    kroneckerLinearEquiv (V × X) (V × X) Z Z ℂ
  rw [← outer.apply_symm_apply ω]
  induction outer.symm ω using TensorProduct.induction_on with
  | zero => simp
  | tmul ρσ τ =>
      simp only [outer, kroneckerLinearEquiv_tmul]
      let inner : Matrix V V ℂ ⊗[ℂ] Matrix X X ℂ ≃ₗ[ℂ]
          Matrix (V × X) (V × X) ℂ :=
        kroneckerLinearEquiv V V X X ℂ
      rw [← inner.apply_symm_apply ρσ]
      induction inner.symm ρσ using TensorProduct.induction_on with
      | zero => simp
      | tmul ρ σ =>
          simp only [inner, kroneckerLinearEquiv_tmul]
          exact h ρ σ τ
      | add a b ha hb =>
          rw [inner.map_add, Matrix.add_kronecker, f.map_add, g.map_add,
            ha, hb]
  | add a b ha hb => rw [outer.map_add, f.map_add, g.map_add, ha, hb]

/-- Tensor product of two finite Kraus channels.  Its operational action is
the canonical tensor of linear maps; pairwise tensor products of Kraus
operators provide the certificate. -/
def tensor (f : KrausChannel V W) (g : KrausChannel X Y) :
    KrausChannel (Object.tensor V X) (Object.tensor W Y) where
  map := tensorLinearMap f.toLinearMap g.toLinearMap
  has_representation := f.has_representation.elim fun frep ↦
    g.has_representation.elim fun grep ↦ ⟨
      { index := frep.index × grep.index
        fintype := inferInstance
        operators := fun pair ↦
          frep.operators pair.1 ⊗ₖ grep.operators pair.2
        map_eq := tensorLinearMap_eq_krausSum f g frep grep
        completeness := by
          rw [Fintype.sum_prod_type]
          simp_rw [Matrix.conjTranspose_kronecker,
            ← Matrix.mul_kronecker_mul]
          rw [← sum_kronecker_sum]
          rw [frep.completeness, grep.completeness,
            Matrix.one_kronecker_one] }⟩

/-- Tensor channels act componentwise on Kronecker-product matrices. -/
@[simp]
theorem tensor_map_kronecker (f : KrausChannel V W)
    (g : KrausChannel X Y) (ρ : Matrix V V ℂ) (σ : Matrix X X ℂ) :
    (tensor f g).map (ρ ⊗ₖ σ) = f.map ρ ⊗ₖ g.map σ := by
  simp [tensor]

/-- Applying a tensor channel to a tensor-product state is componentwise. -/
@[simp]
theorem tensor_applyDensity (f : KrausChannel V W)
    (g : KrausChannel X Y) (ρ : DensityMatrix V) (σ : DensityMatrix X) :
    (tensor f g).applyDensity (ρ.tensor σ) =
      (f.applyDensity ρ).tensor (g.applyDensity σ) := by
  apply DensityMatrix.ext
  simp

/-- Tensoring two identity channels gives the identity on the product
system. -/
theorem tensor_identity (V X : Object.{u}) :
    tensor (identity V) (identity X) = identity (Object.tensor V X) := by
  apply ext
  funext τ
  have h : (tensor (identity V) (identity X)).toLinearMap =
      (identity (Object.tensor V X)).toLinearMap := by
    apply linearMap_ext_kronecker
    intro ρ σ
    change (tensor (identity V) (identity X)).map (ρ ⊗ₖ σ) =
      (identity (Object.tensor V X)).map (ρ ⊗ₖ σ)
    rw [tensor_map_kronecker, identity_map, identity_map, identity_map]
  exact congrArg (fun linear ↦ linear τ) h

/-- Tensor product satisfies the interchange law with serial channel
composition. -/
theorem tensor_comp (f : KrausChannel V W) (f' : KrausChannel W Z)
    (g : KrausChannel X Y) (g' : KrausChannel Y T) :
    tensor (comp f f') (comp g g') =
      comp (tensor f g) (tensor f' g') := by
  apply ext
  funext τ
  have h : (tensor (comp f f') (comp g g')).toLinearMap =
      (comp (tensor f g) (tensor f' g')).toLinearMap := by
    apply linearMap_ext_kronecker
    intro ρ σ
    change (tensor (comp f f') (comp g g')).map (ρ ⊗ₖ σ) =
      (comp (tensor f g) (tensor f' g')).map (ρ ⊗ₖ σ)
    rw [tensor_map_kronecker, comp_map, comp_map, comp_map,
      tensor_map_kronecker, tensor_map_kronecker]
  exact congrArg (fun linear ↦ linear τ) h

end KrausChannel

end Ript.Models.Quantum
