import Ript.Core.Convex
import Ript.Models.FiniteStochastic

/-!
# Exact convex mixing of finite stochastic channels

Finite stochastic channels support pointwise convex mixing over exact
nonnegative rationals.  Normalization follows from the weight equation, and
mixing distributes over Chapman--Kolmogorov composition and independent
tensoring.  This file supplies the optional `ConvexProcess` capability without
adding it to models that do not support random choice.
-/

set_option autoImplicit false

namespace Ript.Models.FiniteStochastic.FinStoch

open scoped BigOperators
open CategoryTheory
open Ript.Core

universe u

variable {V W X Y Z : Object.{u}}

/-- Pointwise exact convex mixing of two finite stochastic channels. -/
def mix (weight : ConvexWeight ℚ≥0) (f g : FinStoch X Y) : FinStoch X Y where
  prob x y := weight.left * f.prob x y + weight.right * g.prob x y
  normalized x := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [f.normalized, g.normalized, mul_one, mul_one]
    exact weight.total

/-- Entrywise formula for exact convex mixing. -/
@[simp]
theorem mix_apply (weight : ConvexWeight ℚ≥0) (f g : FinStoch X Y)
    (x : X) (y : Y) :
    (mix weight f g).prob x y =
      weight.left * f.prob x y + weight.right * g.prob x y :=
  rfl

/-- Full weight on the first channel selects it. -/
@[simp]
theorem mix_leftOnly (f g : FinStoch X Y) :
    mix ConvexWeight.leftOnly f g = f := by
  apply ext
  intro x y
  simp [mix, ConvexWeight.leftOnly]

/-- Full weight on the second channel selects it. -/
@[simp]
theorem mix_rightOnly (f g : FinStoch X Y) :
    mix ConvexWeight.rightOnly f g = g := by
  apply ext
  intro x y
  simp [mix, ConvexWeight.rightOnly]

/-- Mixing a channel with itself leaves it unchanged. -/
@[simp]
theorem mix_idem (weight : ConvexWeight ℚ≥0) (f : FinStoch X Y) :
    mix weight f f = f := by
  apply ext
  intro x y
  change weight.left * f.prob x y + weight.right * f.prob x y = f.prob x y
  rw [← add_mul, weight.total, one_mul]

/-- Swapping both weights and branches preserves the mixture. -/
theorem mix_swap (weight : ConvexWeight ℚ≥0) (f g : FinStoch X Y) :
    mix weight.swap f g = mix weight g f := by
  apply ext
  intro x y
  change weight.right * f.prob x y + weight.left * g.prob x y =
    weight.left * g.prob x y + weight.right * f.prob x y
  ac_rfl

/-- Postcomposition distributes over exact convex mixing. -/
theorem mix_postcomp (weight : ConvexWeight ℚ≥0)
    (f g : FinStoch X Y) (h : FinStoch Y Z) :
    comp (mix weight f g) h = mix weight (comp f h) (comp g h) := by
  apply ext
  intro x z
  change (∑ y, (weight.left * f.prob x y + weight.right * g.prob x y) *
      h.prob y z) =
    weight.left * (∑ y, f.prob x y * h.prob y z) +
      weight.right * (∑ y, g.prob x y * h.prob y z)
  simp only [add_mul]
  rw [Finset.sum_add_distrib]
  congr 1 <;> rw [Finset.mul_sum] <;>
    apply Fintype.sum_congr <;> intro y <;> ac_rfl

/-- Precomposition distributes over exact convex mixing. -/
theorem mix_precomp (weight : ConvexWeight ℚ≥0)
    (h : FinStoch W X) (f g : FinStoch X Y) :
    comp h (mix weight f g) = mix weight (comp h f) (comp h g) := by
  apply ext
  intro w y
  change (∑ x, h.prob w x *
      (weight.left * f.prob x y + weight.right * g.prob x y)) =
    weight.left * (∑ x, h.prob w x * f.prob x y) +
      weight.right * (∑ x, h.prob w x * g.prob x y)
  simp only [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1 <;> rw [Finset.mul_sum] <;>
    apply Fintype.sum_congr <;> intro x <;> ac_rfl

/-- Mixing in the left tensor factor distributes over independent tensor. -/
theorem mix_tensor_left (weight : ConvexWeight ℚ≥0)
    (f g : FinStoch V W) (h : FinStoch X Y) :
    tensor (mix weight f g) h =
      mix weight (tensor f h) (tensor g h) := by
  apply ext
  intro input output
  simp only [tensor_apply, mix_apply]
  rw [add_mul]
  congr 1 <;> ac_rfl

/-- Mixing in the right tensor factor distributes over independent tensor. -/
theorem mix_tensor_right (weight : ConvexWeight ℚ≥0)
    (h : FinStoch V W) (f g : FinStoch X Y) :
    tensor h (mix weight f g) =
      mix weight (tensor h f) (tensor h g) := by
  apply ext
  intro input output
  simp only [tensor_apply, mix_apply]
  rw [mul_add]
  congr 1 <;> ac_rfl

/-- Exact finite stochastic channels implement the independent convex-process
capability over nonnegative rationals. -/
instance convexProcess : ConvexProcess Object ℚ≥0 where
  mix := mix
  mix_leftOnly := mix_leftOnly
  mix_rightOnly := mix_rightOnly
  mix_idem := mix_idem
  mix_swap := mix_swap
  mix_postcomp := mix_postcomp
  mix_precomp := mix_precomp

end Ript.Models.FiniteStochastic.FinStoch
