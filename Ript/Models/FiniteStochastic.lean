import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.Data.Fintype.BigOperators
import Ript.Core.CostedProcess

/-!
# Executable finite stochastic channels

`FinStoch X Y` is an exact row-stochastic matrix over nonnegative rational
numbers. Objects bundle a finite carrier together with executable enumeration
and equality, so channel application, composition, tensor, and small examples
reduce in the kernel without floating-point arithmetic or classical choice.
-/

set_option autoImplicit false

namespace Ript.Models.FiniteStochastic

open scoped BigOperators
open CategoryTheory
open Ript.Core

universe u

/-- A finite type with computational `Fintype` and `DecidableEq` data. -/
structure Object where
  /-- Underlying finite carrier. -/
  carrier : Type u
  /-- Executable enumeration of the carrier. -/
  fintype : Fintype carrier
  /-- Executable equality on the carrier. -/
  decEq : DecidableEq carrier

namespace Object

instance : CoeSort Object (Type u) :=
  ⟨Object.carrier⟩

attribute [instance] Object.fintype Object.decEq

/-- Bundle a type with its computational finite structure. -/
def of (α : Type u) [Fintype α] [DecidableEq α] : Object :=
  ⟨α, inferInstance, inferInstance⟩

/-- Tensor unit for finite stochastic objects. -/
def unit : Object :=
  of PUnit

/-- Cartesian product of finite stochastic objects. -/
abbrev tensor (X Y : Object) : Object :=
  ⟨X × Y, inferInstance, inferInstance⟩

end Object

/-- An exact finite stochastic channel, represented by a normalized
nonnegative-rational row for every input. -/
structure FinStoch (X Y : Object.{u}) where
  /-- Conditional probability `P(y | x)`. -/
  prob : X → Y → ℚ≥0
  /-- Every conditional row has total mass one. -/
  normalized : ∀ x, ∑ y, prob x y = 1

namespace FinStoch

variable {W X Y Z : Object.{u}}

/-- Two finite stochastic channels are equal when all matrix entries agree. -/
@[ext]
theorem ext (f g : FinStoch X Y) (h : ∀ x y, f.prob x y = g.prob x y) : f = g := by
  cases f with
  | mk fProb fNormalized =>
    cases g with
    | mk gProb gNormalized =>
      have hProb : fProb = gProb := by
        funext x y
        exact h x y
      cases hProb
      rfl

/-- Identity stochastic matrix. -/
def identity (X : Object.{u}) : FinStoch X X where
  prob x y := if x = y then 1 else 0
  normalized x := by simp

/-- Chapman--Kolmogorov composition of finite stochastic channels. -/
def comp (f : FinStoch X Y) (g : FinStoch Y Z) : FinStoch X Z where
  prob x z := ∑ y, f.prob x y * g.prob y z
  normalized x := by
    calc
      ∑ z, ∑ y, f.prob x y * g.prob y z =
          ∑ y, ∑ z, f.prob x y * g.prob y z := Finset.sum_comm
      _ = ∑ y, f.prob x y * (∑ z, g.prob y z) := by
        apply Fintype.sum_congr
        intro y
        rw [Finset.mul_sum]
      _ = 1 := by simp [g.normalized, f.normalized]

/-- Finite stochastic objects and channels form a category. -/
instance category : Category.{u} Object where
  Hom := FinStoch
  id := identity
  comp := comp
  id_comp := by
    intro X Y f
    apply ext
    intro x y
    simp [identity, comp]
  comp_id := by
    intro X Y f
    apply ext
    intro x y
    simp [identity, comp]
  assoc := by
    intro V W X Y f g h
    apply ext
    intro v y
    simp only [comp]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp [mul_assoc]

/-- Entrywise form of the identity channel. -/
@[simp]
theorem id_apply (X : Object.{u}) (x y : X) :
    (𝟙 X : X ⟶ X).prob x y = if x = y then 1 else 0 :=
  rfl

/-- Entrywise Chapman--Kolmogorov formula. -/
@[simp]
theorem comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (z : Z) :
    (f ≫ g).prob x z = ∑ y, f.prob x y * g.prob y z :=
  rfl

/-- Parallel composition of independent finite stochastic channels. -/
def tensor (f : FinStoch W X) (g : FinStoch Y Z) :
    FinStoch (Object.tensor W Y) (Object.tensor X Z) where
  prob input output := f.prob input.1 output.1 * g.prob input.2 output.2
  normalized input := by
    change W × Y at input
    change (∑ output : X × Z,
      f.prob input.1 output.1 * g.prob input.2 output.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    simp [g.normalized, f.normalized]

/-- Entrywise tensor formula. -/
@[simp]
theorem tensor_apply (f : FinStoch W X) (g : FinStoch Y Z)
    (input : W × Y) (output : X × Z) :
    (tensor f g).prob input output =
      f.prob input.1 output.1 * g.prob input.2 output.2 :=
  rfl

/-- Embed a deterministic finite function as its Dirac stochastic channel. -/
def dirac (f : X → Y) : FinStoch X Y where
  prob x y := if f x = y then 1 else 0
  normalized x := by simp

/-- Entrywise Dirac formula. -/
@[simp]
theorem dirac_apply (f : X → Y) (x : X) (y : Y) :
    (dirac f).prob x y = if f x = y then 1 else 0 :=
  rfl

/-- Dirac embedding preserves deterministic composition. -/
theorem dirac_comp (f : X → Y) (g : Y → Z) :
    dirac (fun x ↦ g (f x)) =
      comp (dirac f) (dirac g) := by
  apply ext
  intro x z
  change (if g (f x) = z then 1 else 0) =
    ∑ y, (if f x = y then 1 else 0) * (if g y = z then 1 else 0)
  symm
  calc
    ∑ y, (if f x = y then (1 : ℚ≥0) else 0) *
          (if g y = z then 1 else 0) =
        ∑ y, if f x = y then (if g y = z then (1 : ℚ≥0) else 0) else 0 := by
      apply Fintype.sum_congr
      intro y
      by_cases h : f x = y <;> simp [h]
    _ = if g (f x) = z then (1 : ℚ≥0) else 0 := Fintype.sum_ite_eq _ _

/-- Dirac embedding preserves deterministic identities. -/
theorem dirac_id (X : Object.{u}) :
    dirac (fun x : X ↦ x) = identity X := by
  apply ext
  intro x y
  rfl

/-- The Dirac embedding is faithful on deterministic functions. -/
theorem dirac_faithful {f g : X → Y} (h : dirac f = dirac g) : f = g := by
  funext x
  by_contra hne
  have entryEquality := congrArg (fun channel ↦ channel.prob x (f x)) h
  simp only [dirac_apply, if_neg (Ne.symm hne)] at entryEquality
  exact one_ne_zero entryEquality

/-- Tensoring Dirac channels gives the Dirac channel of the product function. -/
theorem dirac_tensor (f : W → X) (g : Y → Z) :
    tensor (dirac f) (dirac g) =
      dirac (fun input : W × Y ↦ (f input.1, g input.2)) := by
  apply ext
  intro input output
  rcases input with ⟨w, y⟩
  rcases output with ⟨x, z⟩
  change (if f w = x then 1 else 0) * (if g y = z then 1 else 0) =
    if (f w, g y) = (x, z) then 1 else 0
  by_cases hf : f w = x <;> by_cases hg : g y = z <;> simp [hf, hg]

/-- Tensor preserves stochastic identity channels. -/
theorem tensor_id (X Y : Object.{u}) :
    tensor (identity X) (identity Y) = identity (Object.tensor X Y) := by
  apply ext
  intro input output
  change X × Y at input
  change X × Y at output
  rcases input with ⟨x, y⟩
  rcases output with ⟨x', y'⟩
  change (if x = x' then 1 else 0) * (if y = y' then 1 else 0) =
    if (x, y) = (x', y') then 1 else 0
  by_cases hx : x = x' <;> by_cases hy : y = y' <;> simp [hx, hy]

/-- Tensor satisfies the interchange law with Chapman--Kolmogorov
composition. -/
theorem tensor_comp
    {A B C D E F : Object.{u}}
    (f : FinStoch A B) (f' : FinStoch B C)
    (g : FinStoch D E) (g' : FinStoch E F) :
    tensor (comp f f') (comp g g') =
      comp (tensor f g) (tensor f' g') := by
  apply ext
  intro input output
  change A × D at input
  change C × F at output
  rcases input with ⟨a, d⟩
  rcases output with ⟨c, outputF⟩
  change (∑ b, f.prob a b * f'.prob b c) *
      (∑ e, g.prob d e * g'.prob e outputF) =
    ∑ middle : B × E,
      (f.prob a middle.1 * g.prob d middle.2) *
        (f'.prob middle.1 c * g'.prob middle.2 outputF)
  rw [Fintype.sum_mul_sum, Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro b
  apply Fintype.sum_congr
  intro e
  ac_rfl

/-- Independent parallel composition is a bifunctor on the finite stochastic
category. -/
def tensorFunctor : Object.{u} × Object.{u} ⥤ Object.{u} where
  obj pair := Object.tensor pair.1 pair.2
  map pair := tensor pair.1 pair.2
  map_id pair := tensor_id pair.1 pair.2
  map_comp f g := tensor_comp f.1 g.1 f.2 g.2

/-- Copy a classical finite value. -/
def copy (X : Object.{u}) : FinStoch X (Object.tensor X X) :=
  dirac fun x ↦ (x, x)

/-- Discard a classical finite value. -/
def discard (X : Object.{u}) : FinStoch X Object.unit :=
  dirac fun _ ↦ PUnit.unit

/-- Discarding has probability one for the unique output. -/
@[simp]
theorem discard_apply (X : Object.{u}) (x : X) (output : Object.unit) :
    (discard X).prob x output = 1 := by
  cases output
  rfl

/-- Every normalized finite stochastic channel is causal: following it by
discarding is the same as discarding immediately. -/
theorem comp_discard (f : FinStoch X Y) :
    comp f (discard Y) = discard X := by
  apply ext
  intro x output
  cases output
  change (∑ y, f.prob x y * 1) = 1
  simpa using f.normalized x

/-- Apply a channel to a fixed input and read an exact output probability. -/
def apply (f : FinStoch X Y) (x : X) (y : Y) : ℚ≥0 :=
  f.prob x y

/-- The baseline finite stochastic model assigns zero abstract resource cost
to every channel. -/
instance zeroCost : HasProcessCost Object Nat where
  cost _ := 0
  cost_id _ := rfl
  cost_comp _ _ := Nat.zero_le 0

end FinStoch

/-- Object wrapper for deterministic finite functions on the same executable
finite carriers used by `FinStoch`. -/
structure Deterministic where
  /-- Underlying executable finite object. -/
  object : Object.{u}

namespace Deterministic

/-- Deterministic functions form the source category for the Dirac embedding. -/
instance category : Category.{u} Deterministic where
  Hom X Y := X.object → Y.object
  id _ := id
  comp f g := g ∘ f

/-- Bundle an executable finite object as a deterministic object. -/
def of (X : Object.{u}) : Deterministic :=
  ⟨X⟩

/-- Deterministic finite functions embed into exact finite stochastic channels
by Dirac distributions. -/
def diracFunctor : CategoryTheory.Functor Deterministic Object where
  obj X := X.object
  map f := FinStoch.dirac f
  map_id X := FinStoch.dirac_id X.object
  map_comp f g := FinStoch.dirac_comp f g

/-- The deterministic-to-stochastic Dirac functor is faithful. -/
instance diracFunctorFaithful : diracFunctor.Faithful where
  map_injective h := FinStoch.dirac_faithful h

end Deterministic

end Ript.Models.FiniteStochastic
