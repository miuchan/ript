import Mathlib.Algebra.Order.Monoid.Defs

/-!
# Resource algebras

The stage-1 resource interface is exactly an ordered additive commutative
monoid. It deliberately reuses mathlib's algebraic hierarchy instead of
introducing a stronger bundled structure.
-/

set_option autoImplicit false

namespace Ript.Resource

universe u

/-- A `ResourceAlgebra R` instance says that addition on the partially ordered
commutative monoid `R` is monotone in both arguments. -/
abbrev ResourceAlgebra (R : Type u) [AddCommMonoid R] [PartialOrder R] : Prop :=
  IsOrderedAddMonoid R

/-- Resource bounds can be added componentwise. -/
theorem add_le_add_resources {R : Type u} [AddCommMonoid R] [PartialOrder R]
    [ResourceAlgebra R] {r₁ r₂ s₁ s₂ : R} (h₁ : r₁ ≤ s₁) (h₂ : r₂ ≤ s₂) :
    r₁ + r₂ ≤ s₁ + s₂ :=
  add_le_add h₁ h₂

end Ript.Resource
