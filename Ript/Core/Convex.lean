import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.CategoryTheory.Category.Basic

/-!
# Convex process capability

Convex mixing is an optional process-theoretic capability: deterministic,
quantum, or resource-sensitive models need not provide it.  The interface is
coefficient-generic and records both coefficients explicitly, avoiding any
subtraction or approximation.  Instantiating it with `ℚ≥0` therefore gives
exact, executable rational mixtures.

The laws expose the binary convex structure needed by Ript: endpoint,
idempotence, symmetry, and compatibility with composition on either side.
-/

set_option autoImplicit false

namespace Ript.Core

open CategoryTheory

universe u v w

/-- Two nonnegative coefficients whose exact sum is one.  Recording both
coefficients avoids defining the second as a potentially truncated `1 - p`.-/
structure ConvexWeight (S : Type w) [AddCommMonoid S] [PartialOrder S]
    [One S] [ZeroLEOneClass S] where
  /-- Coefficient of the first process. -/
  left : S
  /-- Coefficient of the second process. -/
  right : S
  /-- The first coefficient is nonnegative. -/
  left_nonnegative : 0 ≤ left
  /-- The second coefficient is nonnegative. -/
  right_nonnegative : 0 ≤ right
  /-- The coefficients form an exact partition of unit mass. -/
  total : left + right = 1

namespace ConvexWeight

variable {S : Type w} [AddCommMonoid S] [PartialOrder S]
  [One S] [ZeroLEOneClass S]

/-- Select only the first branch. -/
def leftOnly : ConvexWeight S where
  left := 1
  right := 0
  left_nonnegative := zero_le_one
  right_nonnegative := le_rfl
  total := add_zero 1

/-- Select only the second branch. -/
def rightOnly : ConvexWeight S where
  left := 0
  right := 1
  left_nonnegative := le_rfl
  right_nonnegative := zero_le_one
  total := zero_add 1

/-- Exchange the two branch coefficients. -/
def swap (weight : ConvexWeight S) : ConvexWeight S where
  left := weight.right
  right := weight.left
  left_nonnegative := weight.right_nonnegative
  right_nonnegative := weight.left_nonnegative
  total := by rw [add_comm]; exact weight.total

@[simp] theorem swap_left (weight : ConvexWeight S) : weight.swap.left = weight.right := rfl
@[simp] theorem swap_right (weight : ConvexWeight S) : weight.swap.right = weight.left := rfl

end ConvexWeight

/-- Optional binary convex mixing for a category of processes.  It is kept
independent of copying, discarding, monoidal structure, and costs. -/
class ConvexProcess (C : Type u) (S : Type w) [Category.{v} C]
    [AddCommMonoid S] [PartialOrder S] [One S] [ZeroLEOneClass S] where
  /-- Mix two parallel processes with exact normalized coefficients. -/
  mix : {X Y : C} → ConvexWeight S → (X ⟶ Y) → (X ⟶ Y) → (X ⟶ Y)
  /-- Unit weight on the first process selects that process. -/
  mix_leftOnly : ∀ {X Y : C} (f g : X ⟶ Y),
    mix ConvexWeight.leftOnly f g = f
  /-- Unit weight on the second process selects that process. -/
  mix_rightOnly : ∀ {X Y : C} (f g : X ⟶ Y),
    mix ConvexWeight.rightOnly f g = g
  /-- Mixing a process with itself does not change it. -/
  mix_idem : ∀ {X Y : C} (weight : ConvexWeight S) (f : X ⟶ Y),
    mix weight f f = f
  /-- Swapping branches together with their coefficients preserves a mix. -/
  mix_swap : ∀ {X Y : C} (weight : ConvexWeight S) (f g : X ⟶ Y),
    mix weight.swap f g = mix weight g f
  /-- Postcomposition distributes over mixing. -/
  mix_postcomp : ∀ {X Y Z : C} (weight : ConvexWeight S)
      (f g : X ⟶ Y) (h : Y ⟶ Z),
    mix weight f g ≫ h = mix weight (f ≫ h) (g ≫ h)
  /-- Precomposition distributes over mixing. -/
  mix_precomp : ∀ {W X Y : C} (weight : ConvexWeight S)
      (h : W ⟶ X) (f g : X ⟶ Y),
    h ≫ mix weight f g = mix weight (h ≫ f) (h ≫ g)

/-- Invoke the convex-mixing capability without exposing its implementation. -/
def convexMix {C : Type u} {S : Type w} [Category.{v} C]
    [AddCommMonoid S] [PartialOrder S] [One S] [ZeroLEOneClass S]
    [ConvexProcess C S] {X Y : C} (weight : ConvexWeight S)
    (f g : X ⟶ Y) : X ⟶ Y :=
  ConvexProcess.mix weight f g

end Ript.Core
