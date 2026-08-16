import Ript.Models.Decision.Separation

/-!
# Exact finite garbling simplex

Every stochastic post-processing matrix on finite carriers is an exact convex
mixture of deterministic post-processings.  This module makes that elementary
polytope representation executable over `ℚ≥0`.

For a channel `κ : X ⟶ Y`, `independentGarblingLaw κ` samples an entire
deterministic function `d : X → Y` by drawing each value `d x` independently
from row `κ x`.  Its marginal at every input is exactly `κ`.  Conversely, any
exact distribution over deterministic functions induces a stochastic channel
by taking those marginals.

The resulting equivalence turns Blackwell dominance into feasibility over a
finite rational simplex.  It is the algebraic finite-polytope boundary needed
before applying a separation or linear-programming duality theorem.
-/

set_option autoImplicit false

namespace Ript.Models.Decision.GarblingPolytope

open scoped BigOperators

open Ript.Models.Decision.Blackwell
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic

universe u

variable {Θ X Y : Object.{u}}

/-- Finite executable carrier of all deterministic post-processings from `X`
to `Y`. -/
abbrev deterministicGarblingObject (X Y : Object.{u}) : Object.{u} :=
  Object.of (X.carrier → Y.carrier)

/-- Exact law on deterministic post-processings obtained by independently
sampling one output from every row of a stochastic channel. -/
def independentGarblingLaw (κ : FinStoch X Y) :
    FinDist (deterministicGarblingObject X Y) where
  prob decision := ∏ x, κ.prob x (decision x)
  normalized := by
    change (∑ decision : X.carrier → Y.carrier,
      ∏ x, κ.prob x (decision x)) = 1
    calc
      _ = ∏ x : X.carrier, ∑ y : Y.carrier, κ.prob x y := by
        simpa using
          (Finset.sum_prod_piFinset (R := ℚ≥0)
            (Finset.univ : Finset Y) (fun x y ↦ κ.prob x y))
      _ = 1 := by simp [κ.normalized]

/-- A distribution over deterministic post-processings induces the
corresponding exact stochastic channel by taking its one-input marginals. -/
def mixedGarbling
    (weights : FinDist (deterministicGarblingObject X Y)) : FinStoch X Y where
  prob x y :=
    ∑ decision, weights.prob decision *
      if decision x = y then 1 else 0
  normalized x := by
    calc
      ∑ y, ∑ decision, weights.prob decision *
          (if decision x = y then 1 else 0) =
          ∑ decision, ∑ y, weights.prob decision *
            (if decision x = y then 1 else 0) := Finset.sum_comm
      _ = ∑ decision, weights.prob decision *
          (∑ y, if decision x = y then 1 else 0) := by
        apply Fintype.sum_congr
        intro decision
        rw [Finset.mul_sum]
      _ = 1 := by simp [weights.normalized]

/-- Entrywise form of a mixed deterministic garbling. -/
@[simp]
theorem mixedGarbling_apply
    (weights : FinDist (deterministicGarblingObject X Y))
    (x : X.carrier) (y : Y.carrier) :
    (mixedGarbling weights).prob x y =
      ∑ decision, weights.prob decision *
        if decision x = y then 1 else 0 :=
  rfl

/-- The mixed channel induced by the independent law of a stochastic channel
recovers every original row exactly. -/
theorem mixedGarbling_independentGarblingLaw (κ : FinStoch X Y) :
    mixedGarbling (independentGarblingLaw κ) = κ := by
  apply FinStoch.ext
  intro x y
  rw [mixedGarbling_apply]
  change (∑ decision : X.carrier → Y.carrier,
      (∏ input, κ.prob input (decision input)) *
        (if decision x = y then 1 else 0)) = κ.prob x y
  calc
    _ = ∑ decision : X.carrier → Y.carrier,
        ∏ input, κ.prob input (decision input) *
          (if input = x then
            if decision input = y then 1 else 0
          else 1) := by
      apply Fintype.sum_congr
      intro decision
      by_cases hdecision : decision x = y
      · rw [if_pos hdecision, mul_one]
        apply Fintype.prod_congr
        intro input
        by_cases hinput : input = x
        · subst input
          simp [hdecision]
        · simp [hinput]
      · rw [if_neg hdecision, mul_zero]
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ x)
        simp [hdecision]
    _ = ∏ input : X.carrier, ∑ output : Y.carrier,
        κ.prob input output *
          (if input = x then
            if output = y then 1 else 0
          else 1) := by
      simpa using
        (Finset.sum_prod_piFinset (R := ℚ≥0)
          (Finset.univ : Finset Y)
          (fun input output ↦
            κ.prob input output *
              (if input = x then
                if output = y then 1 else 0
              else 1)))
    _ = κ.prob x y := by
      calc
        _ = ∏ input : X.carrier,
            if input = x then κ.prob input y else 1 := by
          apply Fintype.prod_congr
          intro input
          by_cases hinput : input = x
          · subst input
            simp
          · simp [hinput, κ.normalized]
        _ = κ.prob x y := by simp

/-- A point mass on one deterministic post-processing recovers its Dirac
stochastic channel. -/
@[simp]
theorem mixedGarbling_pure (decision : X.carrier → Y.carrier) :
    mixedGarbling (FinDist.pure decision) = FinStoch.dirac decision := by
  apply FinStoch.ext
  intro x y
  rw [mixedGarbling_apply]
  change (∑ candidate, (if decision = candidate then 1 else 0) *
      (if candidate x = y then 1 else 0)) =
    if decision x = y then 1 else 0
  rw [Fintype.sum_eq_single decision]
  · simp
  · intro candidate hne
    simp [Ne.symm hne]

/-- One vertex of the garbling polytope: post-process `P` by a deterministic
function. -/
def deterministicPostprocessing (P : FinStoch Θ X)
    (decision : X.carrier → Y.carrier) :
    FinStoch Θ Y :=
  FinStoch.comp P (FinStoch.dirac decision)

/-- Composing with a mixed garbling is entrywise the same finite rational
convex combination of deterministic post-processing vertices. -/
theorem comp_mixedGarbling_apply (P : FinStoch Θ X)
    (weights : FinDist (deterministicGarblingObject X Y))
    (θ : Θ.carrier) (y : Y.carrier) :
    (FinStoch.comp P (mixedGarbling weights)).prob θ y =
      ∑ decision, weights.prob decision *
        (deterministicPostprocessing P decision).prob θ y := by
  change (∑ x, P.prob θ x *
      (∑ decision, weights.prob decision *
        (if decision x = y then 1 else 0))) =
    ∑ decision, weights.prob decision *
      (∑ x, P.prob θ x *
        (if decision x = y then 1 else 0))
  calc
    _ = ∑ x, ∑ decision,
        P.prob θ x *
          (weights.prob decision *
            (if decision x = y then 1 else 0)) := by
      apply Fintype.sum_congr
      intro x
      rw [Finset.mul_sum]
    _ = ∑ decision, ∑ x,
        P.prob θ x *
          (weights.prob decision *
            (if decision x = y then 1 else 0)) := Finset.sum_comm
    _ = ∑ decision, ∑ x,
        weights.prob decision *
          (P.prob θ x *
            (if decision x = y then 1 else 0)) := by
      apply Fintype.sum_congr
      intro decision
      apply Fintype.sum_congr
      intro x
      ac_rfl
    _ = ∑ decision, weights.prob decision *
        (∑ x, P.prob θ x *
          (if decision x = y then 1 else 0)) := by
      apply Fintype.sum_congr
      intro decision
      rw [Finset.mul_sum]

/-- Feasibility formulation of Blackwell dominance over the finite rational
simplex of deterministic post-processings. -/
def DeterministicMixtureDominates
    (P : FinStoch Θ X) (Q : FinStoch Θ Y) : Prop :=
  ∃ weights : FinDist (deterministicGarblingObject X Y),
    FinStoch.comp P (mixedGarbling weights) = Q

/-- **Exact garbling-polytope representation.** Blackwell dominance is
equivalent to membership in the rational simplex image generated by all
deterministic post-processings. -/
theorem deterministicMixtureDominates_iff
    (P : FinStoch Θ X) (Q : FinStoch Θ Y) :
    DeterministicMixtureDominates P Q ↔ BlackwellDominates P Q := by
  constructor
  · rintro ⟨weights, hweights⟩
    exact ⟨mixedGarbling weights, hweights⟩
  · rintro ⟨κ, hκ⟩
    refine ⟨independentGarblingLaw κ, ?_⟩
    rw [mixedGarbling_independentGarblingLaw]
    exact hκ

end Ript.Models.Decision.GarblingPolytope
