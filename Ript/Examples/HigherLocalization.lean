import Mathlib.Algebra.Group.PUnit
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Ript.Higher.Localization

/-!
# A genuinely noninvertible cost-exact model morphism

The canonical model localization is not merely re-inverting known
bicategorical equivalences.  This file gives a concrete marked arrow that is
not invertible in the model homotopy category.

Both source and target are zero-cost discrete symmetric monoidal models.  The
source is the one-element additive monoid viewed multiplicatively; the target
is the additive monoid of natural numbers viewed multiplicatively.  The
unique monoid homomorphism sends the source object to `0`, so the target object
`1` is not in its essential image.  Nevertheless all process costs are zero,
hence the induced strong
braided model morphism reflects costs exactly and is marked for localization.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Ript.Examples.HigherLocalization

open CategoryTheory
open Ript.Core
open Ript.Higher

universe u

variable (A : Type u) [CommMonoid A]

section DiscreteModel

/-- The symmetry on a discrete category induced by a commutative monoid. -/
@[nolint docBlame]
local instance discreteSymmetric : SymmetricCategory (Discrete A) where
  symmetry _ _ := Subsingleton.elim _ _

/-- The constantly-zero serial cost on a discrete monoidal category. -/
@[instance_reducible]
def discreteZeroProcessCost : HasProcessCost (Discrete A) Nat where
  cost _ := 0
  cost_id _ := rfl
  cost_comp _ _ := by simp

/-- The local serial-cost instance used by the discrete zero-cost model. -/
@[nolint docBlame]
local instance : HasProcessCost (Discrete A) Nat :=
  discreteZeroProcessCost A

/-- Parallel composition also has zero cost. -/
theorem discreteZeroParallelCost : HasParallelProcessCost (Discrete A) Nat where
  cost_tensor _ _ := by
    change 0 ≤ 0 + 0
    simp

local instance : HasParallelProcessCost (Discrete A) Nat :=
  discreteZeroParallelCost A

/-- All structural rewiring in the discrete model has zero cost. -/
theorem discreteZeroStructuralCost : HasFreeStructuralCost (Discrete A) Nat where
  cost_associator _ _ _ := rfl
  cost_associator_inv _ _ _ := rfl
  cost_leftUnitor _ := rfl
  cost_leftUnitor_inv _ := rfl
  cost_rightUnitor _ := rfl
  cost_rightUnitor_inv _ := rfl
  cost_braiding _ _ := rfl

local instance : HasFreeStructuralCost (Discrete A) Nat :=
  discreteZeroStructuralCost A

/-- A discrete symmetric monoidal process model in which every process has
zero natural-number cost. -/
def discreteZeroCostModel : ProcessModel Nat where
  Carrier := Discrete A
  category := inferInstance
  monoidal := inferInstance
  symmetric := inferInstance
  costed := discreteZeroProcessCost A
  parallelCost := discreteZeroParallelCost A
  structuralCost := discreteZeroStructuralCost A

end DiscreteModel

/-- The unique multiplicative map from the one-element source sends its
object to additive zero in the target. -/
def unitToNat : Multiplicative PUnit.{1} →* Multiplicative Nat where
  toFun _ := Multiplicative.ofAdd 0
  map_one' := rfl
  map_mul' _ _ := by simp

/-- The discrete symmetric structure on the one-object source model. -/
@[nolint docBlame]
local instance unitSourceSymmetric :
    SymmetricCategory (Discrete (Multiplicative PUnit.{1})) :=
  discreteSymmetric (Multiplicative PUnit.{1})

/-- The discrete symmetric structure on the natural-number target model. -/
@[nolint docBlame]
local instance unitTargetSymmetric :
    SymmetricCategory (Discrete (Multiplicative Nat)) :=
  discreteSymmetric (Multiplicative Nat)

/-- The induced strong braided morphism of zero-cost process models. -/
def unitToNatModelHom :
    ModelHom (discreteZeroCostModel (Multiplicative PUnit.{1}))
      (discreteZeroCostModel (Multiplicative Nat)) where
  toLaxBraided :=
    { toFunctor := Discrete.monoidalFunctor unitToNat
      laxBraided := by
        change (Discrete.monoidalFunctor unitToNat).LaxBraided
        infer_instance }
  unit_isIso := by
    change IsIso (Discrete.eqToHom unitToNat.map_one.symm)
    infer_instance
  tensor_isIso := by
    intro X Y
    change IsIso (Discrete.eqToHom (unitToNat.map_mul X.as Y.as).symm)
    infer_instance
  map_cost_le _ := by
    change 0 ≤ 0
    exact le_rfl

/-- The discrete embedding reflects costs because both sides assign zero. -/
instance unitToNatModelHom_costReflecting : CostReflecting unitToNatModelHom where
  map_cost_ge _ := by
    change 0 ≤ 0
    exact le_rfl

/-- The discrete embedding is one of the arrows formally inverted by the
cost-exact localization. -/
theorem unitToNatModelHom_mem :
    costExactMorphisms Nat
      (CategoryTheory.Bicategory.HomotopyCategory.homMk
        (B := ProcessModel.{0, 0, 0} Nat) unitToNatModelHom) :=
  costExactMorphisms_homMk unitToNatModelHom

private theorem equivalence_hom_essSurj
    {M N : ProcessModel Nat} (e : CategoryTheory.Bicategory.Equivalence M N) :
    e.hom.toFunctor.EssSurj where
  mem_essImage Y :=
    ⟨e.inv.toFunctor.obj Y,
      ⟨(ModelTransformation.toNatIso e.counit).app Y⟩⟩

/-- The marked embedding is not invertible in the model homotopy category:
additive `1 : Nat` cannot be isomorphic to the sole image object `0`. -/
theorem unitToNatModelHom_not_isIso :
    ¬ IsIso (CategoryTheory.Bicategory.HomotopyCategory.homMk
      (B := ProcessModel.{0, 0, 0} Nat) unitToNatModelHom) := by
  intro h
  let _ : IsIso
      (CategoryTheory.Bicategory.HomotopyCategory.homMk
        (B := ProcessModel.{0, 0, 0} Nat) unitToNatModelHom) := h
  let e := CategoryTheory.Bicategory.HomotopyCategory.equivalenceOfIsIso
    (B := ProcessModel.{0, 0, 0} Nat) unitToNatModelHom
  let _ : e.hom.toFunctor.EssSurj := equivalence_hom_essSurj e
  obtain ⟨X, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage e.hom.toFunctor
    (Discrete.mk (Multiplicative.ofAdd 1))
  have hEq := Discrete.eq_of_hom i.hom
  have ehom : e.hom = unitToNatModelHom := by
    simp [e]
  rw [ehom] at hEq
  change Multiplicative.ofAdd 0 = Multiplicative.ofAdd 1 at hEq
  have h01 : (0 : Nat) = 1 := congrArg Multiplicative.toAdd hEq
  exact Nat.zero_ne_one h01

/-- The marked discrete embedding is not an adjoint equivalence in the model
bicategory.  Otherwise its forward arrow would already be invertible in the
homotopy category, contradicting the explicit essential-surjectivity
obstruction above. -/
theorem unitToNatModelHom_not_isEquivalence :
    ¬ CategoryTheory.Bicategory.IsEquivalence
      (B := ProcessModel.{0, 0, 0} Nat) unitToNatModelHom := by
  rintro ⟨⟨e, he⟩⟩
  apply unitToNatModelHom_not_isIso
  rw [← he]
  exact (CategoryTheory.Bicategory.HomotopyCategory.isoOfEquivalence e).isIso_hom

/-- The identity pseudofunctor on the full model bicategory is not the
cost-exact bicategorical localization.  The higher construction must really
adjoin an inverse to `unitToNatModelHom`; it cannot satisfy the universal
property merely by reusing the source bicategory unchanged. -/
theorem costExactIdentity_not_isBicategoricalLocalization :
    ¬ IsCostExactBicategoricalLocalization
      (Pseudofunctor.id (ProcessModel.{0, 0, 0} Nat)) := by
  intro h
  apply unitToNatModelHom_not_isEquivalence
  exact h.map_costReflecting_isEquivalence unitToNatModelHom (by
    change CostReflecting unitToNatModelHom
    infer_instance)

attribute [nolint docBlame] discreteSymmetric instHasProcessCostDiscreteNat
  unitSourceSymmetric unitTargetSymmetric

end Ript.Examples.HigherLocalization
