import Ript.Models.Quantum.Tensor

/-!
# Complete positivity of finite Kraus channels

This file makes the complete-positivity content of the Kraus construction
explicit.  A complex-linear matrix map is completely positive when every
finite identity amplification preserves positive semidefiniteness.  The
amplification uses the same product-basis tensor map as the finite quantum
channel model.

Mathlib also provides `CompletelyPositiveMap` for general C-star algebras via
`CStarMatrix`.  The predicate below is the finite ordinary-matrix formulation
native to Ript's current quantum layer; no analytic C-star-algebra bridge is
claimed here.
-/

set_option autoImplicit false

namespace Ript.Models.Quantum

open Matrix
open scoped ComplexOrder Kronecker

universe u

/-- Amplify a complex-linear matrix map by the identity action on an arbitrary
finite auxiliary quantum system. -/
def amplification {X Y : Object.{u}} (A : Object.{u})
    (f : Matrix X X ℂ →ₗ[ℂ] Matrix Y Y ℂ) :
    Matrix (A × X) (A × X) ℂ →ₗ[ℂ] Matrix (A × Y) (A × Y) ℂ :=
  KrausChannel.tensorLinearMap LinearMap.id f

/-- A finite-dimensional matrix map is completely positive when every finite
identity amplification preserves positive semidefiniteness. -/
def IsCompletelyPositive {X Y : Object.{u}}
    (f : Matrix X X ℂ →ₗ[ℂ] Matrix Y Y ℂ) : Prop :=
  ∀ (A : Object.{u}) (τ : Matrix (A × X) (A × X) ℂ),
    τ.PosSemidef → (amplification A f τ).PosSemidef

/-- Identity amplification acts componentwise on Kronecker-product matrices. -/
@[simp]
theorem amplification_kronecker {X Y A : Object.{u}}
    (f : Matrix X X ℂ →ₗ[ℂ] Matrix Y Y ℂ)
    (σ : Matrix A A ℂ) (ρ : Matrix X X ℂ) :
    amplification A f (σ ⊗ₖ ρ) = σ ⊗ₖ f ρ := by
  simp [amplification]

namespace KrausChannel

variable {X Y : Object.{u}}

/-- The canonical amplification of a Kraus channel is the linear map of its
tensor product with the auxiliary identity channel. -/
theorem amplification_eq_tensor_identity (channel : KrausChannel X Y)
    (A : Object.{u}) :
    amplification A channel.toLinearMap =
      (tensor (identity A) channel).toLinearMap := by
  apply LinearMap.ext
  intro τ
  change amplification A channel.toLinearMap τ =
    (tensor (identity A) channel).map τ
  simp [amplification, tensor]

/-- Every finite trace-preserving Kraus channel is completely positive: for
every finite auxiliary system, its identity amplification preserves positive
semidefiniteness on arbitrary joint matrices. -/
theorem toLinearMap_isCompletelyPositive (channel : KrausChannel X Y) :
    IsCompletelyPositive channel.toLinearMap := by
  intro A τ hτ
  rw [amplification_eq_tensor_identity]
  exact (tensor (identity A) channel).map_posSemidef hτ

end KrausChannel

end Ript.Models.Quantum
