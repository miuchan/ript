import Mathlib.Algebra.Order.Hom.Monoid

/-!
# Typed process signatures

A stage-1 signature supplies object symbols, typed process generators, and the
resource cost of each generator. Capability labels are deferred until their
first concrete consumer.
-/

set_option autoImplicit false

namespace Ript.Syntax

universe u w

/-- A typed collection of primitive processes carrying generator costs. -/
structure Signature (R : Type w) where
  /-- Symbols for the input and output types of processes. -/
  Obj : Type u
  /-- Primitive process symbols indexed by their source and target. -/
  Gen : Obj → Obj → Type u
  /-- The declared resource cost of a primitive process. -/
  cost : {X Y : Obj} → Gen X Y → R

namespace Signature

/-- Push a sequential signature's declared generator costs through an ordered
additive resource translation without changing its objects or generators. -/
def mapCost {R S : Type w} [AddCommMonoid R] [Preorder R]
    [AddCommMonoid S] [Preorder S] (signature : Signature.{u, w} R)
    (φ : R →+o S) : Signature.{u, w} S where
  Obj := signature.Obj
  Gen := signature.Gen
  cost g := φ (signature.cost g)

/-- Sequential generator costs translate pointwise. -/
@[simp]
theorem mapCost_cost {R S : Type w} [AddCommMonoid R] [Preorder R]
    [AddCommMonoid S] [Preorder S] (signature : Signature.{u, w} R)
    (φ : R →+o S) {X Y : (signature.mapCost φ).Obj}
    (g : (signature.mapCost φ).Gen X Y) :
    (signature.mapCost φ).cost g = φ (signature.cost g) :=
  rfl

/-- Successive sequential cost translations compose definitionally. -/
@[simp]
theorem mapCost_comp {R S T : Type w}
    [AddCommMonoid R] [Preorder R] [AddCommMonoid S] [Preorder S]
    [AddCommMonoid T] [Preorder T] (signature : Signature.{u, w} R)
    (φ : R →+o S) (ψ : S →+o T) :
    (signature.mapCost φ).mapCost ψ = signature.mapCost (ψ.comp φ) :=
  rfl

end Signature

end Ript.Syntax
