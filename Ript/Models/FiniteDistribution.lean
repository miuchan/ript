import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.NNRat.BigOperators
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

/-- Every normalized finite distribution has a nonempty carrier. -/
theorem carrier_nonempty (p : FinDist X) : Nonempty X := by
  by_contra h
  let _ : IsEmpty X := not_nonempty_iff.mp h
  have hnormalized := p.normalized
  simp at hnormalized

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

/-- Point distributions faithfully encode their supporting outcomes. -/
theorem pure_injective : Function.Injective (pure : X → FinDist X) := by
  intro x y equal
  by_contra different
  have atX := congrArg (fun distribution ↦ distribution.prob x) equal
  simp [pure_apply, Ne.symm different] at atX

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

/-- Entrywise formula for deterministic pushforward. -/
@[simp]
theorem map_apply (f : X → Y) (p : FinDist X) (y : Y) :
    (map f p).prob y =
      ∑ x, p.prob x * (if f x = y then 1 else 0) :=
  rfl

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

/-- Evolve an exact finite distribution through a stochastic channel. -/
def push (p : FinDist X) (channel : FinStoch X Y) : FinDist Y :=
  bind p fun x ↦
    { prob := channel.prob x
      normalized := channel.normalized x }

/-- Entrywise formula for stochastic evolution of a finite distribution. -/
@[simp]
theorem push_apply (p : FinDist X) (channel : FinStoch X Y) (y : Y) :
    (p.push channel).prob y = ∑ x, p.prob x * channel.prob x y :=
  rfl

/-- Pushing through a deterministic equivalence reindexes the distribution
without changing any probability mass. -/
theorem push_diracEquiv_apply (p : FinDist X) (equivalence : X ≃ Y)
    (output : Y) :
    (p.push (FinStoch.dirac equivalence)).prob output =
      p.prob (equivalence.symm output) := by
  simp [FinStoch.dirac, ← equivalence.eq_symm_apply]

/-- Evolving through the identity channel leaves a distribution unchanged. -/
@[simp]
theorem push_identity (p : FinDist X) :
    p.push (FinStoch.identity X) = p := by
  apply ext
  intro y
  simp [push, FinStoch.identity]

/-- Stochastic evolution respects Chapman--Kolmogorov composition. -/
theorem push_comp (p : FinDist X) (f : FinStoch X Y) (g : FinStoch Y Z) :
    p.push (FinStoch.comp f g) = (p.push f).push g := by
  apply ext
  intro z
  change (∑ x, p.prob x * (∑ y, f.prob x y * g.prob y z)) =
    ∑ y, (∑ x, p.prob x * f.prob x y) * g.prob y z
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [mul_assoc]

/-- Independent product of two exact finite distributions. -/
def tensor (p : FinDist X) (q : FinDist Y) :
    FinDist (Object.tensor X Y) where
  prob outcome := p.prob outcome.1 * q.prob outcome.2
  normalized := by
    change (∑ outcome : X × Y, p.prob outcome.1 * q.prob outcome.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    simp [p.normalized, q.normalized]

/-- Entrywise formula for an independent product distribution. -/
@[simp]
theorem tensor_apply (p : FinDist X) (q : FinDist Y) (outcome : X × Y) :
    (p.tensor q).prob outcome = p.prob outcome.1 * q.prob outcome.2 :=
  rfl

/-- Left marginal of an exact joint distribution. -/
def leftMarginal (joint : FinDist (Object.tensor X Y)) : FinDist X :=
  map Prod.fst joint

/-- Right marginal of an exact joint distribution. -/
def rightMarginal (joint : FinDist (Object.tensor X Y)) : FinDist Y :=
  map Prod.snd joint

/-- The left marginal sums over the right coordinate. -/
@[simp]
theorem leftMarginal_apply (joint : FinDist (Object.tensor X Y)) (x : X) :
    joint.leftMarginal.prob x = ∑ y : Y, joint.prob (x, y) := by
  change (∑ outcome : X × Y,
    joint.prob outcome * (if outcome.1 = x then 1 else 0)) =
      ∑ y : Y, joint.prob (x, y)
  rw [Fintype.sum_prod_type]
  simp

/-- The right marginal sums over the left coordinate. -/
@[simp]
theorem rightMarginal_apply (joint : FinDist (Object.tensor X Y)) (y : Y) :
    joint.rightMarginal.prob y = ∑ x : X, joint.prob (x, y) := by
  change (∑ outcome : X × Y,
    joint.prob outcome * (if outcome.2 = y then 1 else 0)) =
      ∑ x : X, joint.prob (x, y)
  rw [Fintype.sum_prod_type]
  simp

/-- The left marginal of an independent product is its left factor. -/
@[simp]
theorem leftMarginal_tensor (p : FinDist X) (q : FinDist Y) :
    (p.tensor q).leftMarginal = p := by
  apply ext
  intro x
  rw [leftMarginal_apply]
  simp_rw [tensor_apply]
  rw [← Finset.mul_sum, q.normalized, mul_one]

/-- The right marginal of an independent product is its right factor. -/
@[simp]
theorem rightMarginal_tensor (p : FinDist X) (q : FinDist Y) :
    (p.tensor q).rightMarginal = q := by
  apply ext
  intro y
  rw [rightMarginal_apply]
  simp_rw [tensor_apply]
  rw [← Finset.sum_mul, p.normalized, one_mul]

/-- A zero left-marginal mass forces every joint mass above it to vanish. -/
theorem joint_prob_eq_zero_of_leftMarginal_eq_zero
    (joint : FinDist (Object.tensor X Y)) (x : X) (y : Y)
    (hzero : joint.leftMarginal.prob x = 0) :
    joint.prob (x, y) = 0 := by
  rw [leftMarginal_apply] at hzero
  apply NNRat.cast_injective (α := ℚ)
  apply le_antisymm
  · calc
      (joint.prob (x, y) : ℚ) ≤
          ∑ y' : Y, (joint.prob (x, y') : ℚ) :=
        Finset.single_le_sum (fun y' _ ↦ (joint.prob (x, y')).coe_nonneg)
          (Finset.mem_univ y)
      _ = 0 := by
        rw [← NNRat.cast_sum, hzero, NNRat.cast_zero]
  · exact (joint.prob (x, y)).coe_nonneg

/-- A zero right-marginal mass forces every joint mass above it to vanish. -/
theorem joint_prob_eq_zero_of_rightMarginal_eq_zero
    (joint : FinDist (Object.tensor X Y)) (x : X) (y : Y)
    (hzero : joint.rightMarginal.prob y = 0) :
    joint.prob (x, y) = 0 := by
  rw [rightMarginal_apply] at hzero
  apply NNRat.cast_injective (α := ℚ)
  apply le_antisymm
  · calc
      (joint.prob (x, y) : ℚ) ≤
          ∑ x' : X, (joint.prob (x', y) : ℚ) :=
        Finset.single_le_sum (fun x' _ ↦ (joint.prob (x', y)).coe_nonneg)
          (Finset.mem_univ x)
      _ = 0 := by
        rw [← NNRat.cast_sum, hzero, NNRat.cast_zero]
  · exact (joint.prob (x, y)).coe_nonneg

/-- Every exact joint distribution is supported inside the product of its
marginals. -/
theorem support_tensor_marginals (joint : FinDist (Object.tensor X Y)) :
    ∀ outcome,
      (joint.leftMarginal.tensor joint.rightMarginal).prob outcome = 0 →
        joint.prob outcome = 0 := by
  rintro ⟨x, y⟩ hzero
  rw [tensor_apply] at hzero
  rcases mul_eq_zero.mp hzero with hleft | hright
  · exact joint_prob_eq_zero_of_leftMarginal_eq_zero joint x y hleft
  · exact joint_prob_eq_zero_of_rightMarginal_eq_zero joint x y hright

/-- Independent stochastic evolution commutes with product distributions. -/
theorem push_tensor (p : FinDist W) (q : FinDist Y)
    (f : FinStoch W X) (g : FinStoch Y Z) :
    (p.tensor q).push (FinStoch.tensor f g) =
      (p.push f).tensor (q.push g) := by
  apply ext
  intro output
  change X × Z at output
  rcases output with ⟨x, z⟩
  change (∑ input : W × Y,
      (p.prob input.1 * q.prob input.2) *
        (f.prob input.1 x * g.prob input.2 z)) =
    (∑ w, p.prob w * f.prob w x) *
      ∑ y, q.prob y * g.prob y z
  rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]
  apply Fintype.sum_congr
  intro w
  apply Fintype.sum_congr
  intro y
  ac_rfl

/-- Regard a normalized finite distribution as a stochastic state from the
tensor unit. -/
def toState (p : FinDist X) : FinStoch Object.unit X where
  prob _ x := p.prob x
  normalized _ := p.normalized

/-- A stochastic state exposes the probability mass of its distribution. -/
@[simp]
theorem toState_apply (p : FinDist X) (input : Object.unit) (x : X) :
    p.toState.prob input x = p.prob x :=
  rfl

/-- Preparing a distribution from the unique unit state produces that
distribution. -/
@[simp]
theorem pure_unit_push_toState (p : FinDist X) :
    (pure PUnit.unit).push p.toState = p := by
  apply ext
  intro x
  change (∑ input : PUnit,
    (if PUnit.unit = input then 1 else 0) * p.prob x) = p.prob x
  rw [Fintype.sum_unique]
  simp

end FinDist

end Ript.Models.FiniteDistribution
