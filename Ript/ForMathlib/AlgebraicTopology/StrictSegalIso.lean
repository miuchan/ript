import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal

/-!
# Strict Segal simplicial sets and isomorphisms

This file supplies the small transport API needed to compare strict Segal
simplicial sets through a natural isomorphism.  It is kept under
`Ript.ForMathlib` because the constructions are independent of Ript's process
models and are suitable candidates for upstreaming.
-/

set_option autoImplicit false

open CategoryTheory
open Opposite
open Simplicial

universe u

namespace SSet.Path

variable {X Y : SSet.{u}} {n : ℕ}

/-- An isomorphism of simplicial sets induces an equivalence of paths of every
fixed length. -/
def mapIso (e : X ≅ Y) : X.Path n ≃ Y.Path n where
  toFun p := p.map e.hom
  invFun p := p.map e.inv
  left_inv p := by
    ext i
    · simp
    · simp
  right_inv p := by
    ext i
    · simp
    · simp

/-- Mapping the spine of a simplex through an isomorphism is the spine of the
mapped simplex. -/
@[simp]
theorem mapIso_spine (e : X ≅ Y) (n : ℕ) (x : X _⦋n⦌) :
    mapIso e (X.spine n x) = Y.spine n (e.hom.app _ x) := by
  ext i
  · change e.hom.app (op ⦋0⦌)
        (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op x) =
      Y.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op (e.hom.app _ x)
    exact e.hom.naturality_apply
      (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op x
  · change e.hom.app (op ⦋1⦌) (X.map (SimplexCategory.mkOfSucc i).op x) =
      Y.map (SimplexCategory.mkOfSucc i).op (e.hom.app _ x)
    exact e.hom.naturality_apply (SimplexCategory.mkOfSucc i).op x

end SSet.Path

namespace SSet.StrictSegal

variable {X Y : SSet.{u}}

/-- Strict Segal structure transports backward along an isomorphism of
simplicial sets. -/
def ofIso (e : X ≅ Y) (sy : StrictSegal Y) : StrictSegal X where
  spineToSimplex {n} p :=
    e.inv.app _ (sy.spineToSimplex (SSet.Path.mapIso e p))
  spine_spineToSimplex n := by
    funext p
    apply (SSet.Path.mapIso e).injective
    simp
  spineToSimplex_spine n := by
    funext x
    simp

end SSet.StrictSegal
