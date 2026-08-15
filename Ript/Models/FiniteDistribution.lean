import Ript.Models.FiniteStochastic

/-!
# Exact finite probability distributions

`FinDist X` is an exact probability distribution on an executable finite
carrier `X`. Probabilities are nonnegative rationals, and normalization is a
finite sum. The operations `pure` and `bind` are executable and satisfy the
three monad laws.

The carrier of all rational distributions on a nonempty finite type is usually
infinite. Consequently, `FinDist X` is not itself an object of the finite-type
category used by `FinStoch`. The restricted Kleisli category on finite source
and target carriers is constructed separately in
`Ript.Models.FiniteStochastic.Kleisli`.
-/

set_option autoImplicit false

namespace Ript.Models.FiniteDistribution

open scoped BigOperators

open Ript.Models.FiniteStochastic

universe u

/-- An exact normalized probability distribution on an executable finite
carrier. -/
structure FinDist (X : Object.{u}) where
  /-- Probability mass at a finite outcome. -/
  prob : X → ℚ≥0
  /-- Total probability mass is one. -/
  normalized : ∑ x, prob x = 1

namespace FinDist

variable {W X Y Z : Object.{u}}

/-- Probability distributions are equal when every outcome has the same
probability. -/
@[ext]
theorem ext (p q : FinDist X) (h : ∀ x, p.prob x = q.prob x) : p = q := by
  cases p with
  | mk pProb pNormalized =>
    cases q with
    | mk qProb qNormalized =>
      have hProb : pProb = qProb := by
        funext x
        exact h x
      cases hProb
      rfl

/-- The point distribution concentrated at one outcome. -/
def pure (x : X) : FinDist X where
  prob y := if x = y then 1 else 0
  normalized := by simp

/-- Monadic substitution of exact finite distributions. -/
def bind (p : FinDist X) (f : X → FinDist Y) : FinDist Y where
  prob y := ∑ x, p.prob x * (f x).prob y
  normalized := by
    calc
      ∑ y, ∑ x, p.prob x * (f x).prob y =
          ∑ x, ∑ y, p.prob x * (f x).prob y := Finset.sum_comm
      _ = ∑ x, p.prob x * (∑ y, (f x).prob y) := by
        apply Fintype.sum_congr
        intro x
        rw [Finset.mul_sum]
      _ = 1 := by simp [FinDist.normalized, p.normalized]

/-- Entrywise formula for a point distribution. -/
@[simp]
theorem pure_apply (x y : X) : (pure x).prob y = if x = y then 1 else 0 :=
  rfl

/-- Entrywise formula for monadic substitution. -/
@[simp]
theorem bind_apply (p : FinDist X) (f : X → FinDist Y) (y : Y) :
    (bind p f).prob y = ∑ x, p.prob x * (f x).prob y :=
  rfl

/-- Left unit law for exact finite-distribution substitution. -/
@[simp]
theorem pure_bind (x : X) (f : X → FinDist Y) : bind (pure x) f = f x := by
  apply ext
  intro y
  simp [bind, pure]

/-- Right unit law for exact finite-distribution substitution. -/
@[simp]
theorem bind_pure (p : FinDist X) : bind p pure = p := by
  apply ext
  intro x
  simp [bind, pure]

/-- Associativity law for exact finite-distribution substitution. -/
theorem bind_assoc (p : FinDist W) (f : W → FinDist X) (g : X → FinDist Y) :
    bind (bind p f) g = bind p (fun w ↦ bind (f w) g) := by
  apply ext
  intro y
  simp only [bind_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [mul_assoc]

/-- Push an exact finite distribution forward along a deterministic function. -/
def map (f : X → Y) (p : FinDist X) : FinDist Y :=
  bind p (fun x ↦ pure (f x))

/-- Mapping by the identity function does not change a distribution. -/
@[simp]
theorem map_id (p : FinDist X) : map (fun x ↦ x) p = p :=
  bind_pure p

/-- Pushforward respects deterministic function composition. -/
theorem map_comp (f : X → Y) (g : Y → Z) (p : FinDist X) :
    map (fun x ↦ g (f x)) p = map g (map f p) := by
  rw [map, map, map, bind_assoc]
  apply ext
  intro z
  simp

end FinDist

end Ript.Models.FiniteDistribution
