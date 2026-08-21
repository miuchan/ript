import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Ript.Core.ParallelCost
import Ript.Core.StructuralCost
import Ript.Models.FiniteStochastic

/-!
# Symmetric monoidal finite stochastic channels

The tensor product is the ordinary product of finite carriers and independent
product of stochastic matrices.  Associators, unitors, and braidings are
deterministic Dirac channels, so all coherence maps remain executable.
-/

set_option autoImplicit false

namespace Ript.Models.FiniteStochastic

open CategoryTheory
open MonoidalCategory
open Ript.Core

universe u

namespace FinStoch

/-- Rebracketing equivalence of three product carriers. -/
def associatorEquiv (X Y Z : Object.{u}) : ((X × Y) × Z) ≃ (X × (Y × Z)) where
  toFun input := (input.1.1, (input.1.2, input.2))
  invFun input := ((input.1, input.2.1), input.2.2)
  left_inv input := by rcases input with ⟨⟨x, y⟩, z⟩; rfl
  right_inv input := by rcases input with ⟨x, y, z⟩; rfl

/-- Left-unit equivalence of product carriers. -/
def leftUnitorEquiv (X : Object.{u}) : (PUnit × X) ≃ X where
  toFun input := input.2
  invFun input := (PUnit.unit, input)
  left_inv input := by rcases input with ⟨unitValue, x⟩; cases unitValue; rfl
  right_inv _ := rfl

/-- Right-unit equivalence of product carriers. -/
def rightUnitorEquiv (X : Object.{u}) : (X × PUnit) ≃ X where
  toFun input := input.1
  invFun input := (input, PUnit.unit)
  left_inv input := by rcases input with ⟨x, unitValue⟩; cases unitValue; rfl
  right_inv _ := rfl

/-- Swap equivalence of two product carriers. -/
def braidEquiv (X Y : Object.{u}) : (X × Y) ≃ (Y × X) where
  toFun input := (input.2, input.1)
  invFun input := (input.2, input.1)
  left_inv input := by rcases input with ⟨x, y⟩; rfl
  right_inv input := by rcases input with ⟨y, x⟩; rfl

/-- Postcomposition by a deterministic equivalence simply reindexes the
output of a stochastic channel. -/
@[simp]
theorem comp_diracEquiv_apply {X Y Z : Object.{u}} (channel : X ⟶ Y)
    (equivalence : Y ≃ Z) (input : X) (output : Z) :
    (comp channel (dirac equivalence)).prob input output =
      channel.prob input (equivalence.symm output) := by
  simp [comp, dirac, ← equivalence.eq_symm_apply]

/-- Precomposition by a deterministic equivalence reindexes the input. -/
@[simp]
theorem diracEquiv_comp_apply {X Y Z : Object.{u}} (equivalence : X ≃ Y)
    (channel : Y ⟶ Z) (input : X) (output : Z) :
    (comp (dirac equivalence) channel).prob input output =
      channel.prob (equivalence input) output := by
  simp [comp, dirac]

/-- Deterministic rebracketing of three finite carriers. -/
def associatorHom (X Y Z : Object.{u}) :
    Object.tensor (Object.tensor X Y) Z ⟶
      Object.tensor X (Object.tensor Y Z) :=
  dirac (associatorEquiv X Y Z)

/-- Inverse deterministic rebracketing. -/
def associatorInv (X Y Z : Object.{u}) :
    Object.tensor X (Object.tensor Y Z) ⟶
      Object.tensor (Object.tensor X Y) Z :=
  dirac (associatorEquiv X Y Z).symm

/-- Deterministic removal of the left tensor unit. -/
def leftUnitorHom (X : Object.{u}) : Object.tensor Object.unit X ⟶ X :=
  dirac (leftUnitorEquiv X)

/-- Deterministic insertion of the left tensor unit. -/
def leftUnitorInv (X : Object.{u}) : X ⟶ Object.tensor Object.unit X :=
  dirac (leftUnitorEquiv X).symm

/-- Deterministic removal of the right tensor unit. -/
def rightUnitorHom (X : Object.{u}) : Object.tensor X Object.unit ⟶ X :=
  dirac (rightUnitorEquiv X)

/-- Deterministic insertion of the right tensor unit. -/
def rightUnitorInv (X : Object.{u}) : X ⟶ Object.tensor X Object.unit :=
  dirac (rightUnitorEquiv X).symm

/-- Deterministic swap of two finite carriers. -/
def braidHom (X Y : Object.{u}) : Object.tensor X Y ⟶ Object.tensor Y X :=
  dirac (braidEquiv X Y)

/-- The independent product tensor and deterministic coherence maps. -/
instance monoidalCategoryStruct : MonoidalCategoryStruct Object.{u} where
  tensorObj := Object.tensor
  tensorUnit := Object.unit
  whiskerLeft X _ _ morphism := tensor (𝟙 X) morphism
  whiskerRight morphism Y := tensor morphism (𝟙 Y)
  tensorHom := tensor
  associator X Y Z :=
    { hom := associatorHom X Y Z
      inv := associatorInv X Y Z
      hom_inv_id := by
        change comp (dirac _) (dirac _) = identity _
        rw [← dirac_comp, ← dirac_id]
        congr
      inv_hom_id := by
        change comp (dirac _) (dirac _) = identity _
        rw [← dirac_comp, ← dirac_id]
        congr }
  leftUnitor X :=
    { hom := leftUnitorHom X
      inv := leftUnitorInv X
      hom_inv_id := by
        change comp (dirac _) (dirac _) = identity _
        rw [← dirac_comp, ← dirac_id]
        congr
      inv_hom_id := by
        change comp (dirac _) (dirac _) = identity _
        rw [← dirac_comp, ← dirac_id]
        congr }
  rightUnitor X :=
    { hom := rightUnitorHom X
      inv := rightUnitorInv X
      hom_inv_id := by
        change comp (dirac _) (dirac _) = identity _
        rw [← dirac_comp, ← dirac_id]
        congr
      inv_hom_id := by
        change comp (dirac _) (dirac _) = identity _
        rw [← dirac_comp, ← dirac_id]
        congr }

@[simp]
theorem tensorHom_eq {W X Y Z : Object.{u}}
    (left : W ⟶ X) (right : Y ⟶ Z) :
    left ⊗ₘ right = tensor left right :=
  rfl

@[simp]
theorem associator_hom_eq (X Y Z : Object.{u}) :
    (α_ X Y Z).hom = associatorHom X Y Z :=
  rfl

@[simp]
theorem associator_inv_eq (X Y Z : Object.{u}) :
    (α_ X Y Z).inv = associatorInv X Y Z :=
  rfl

@[simp]
theorem leftUnitor_hom_eq (X : Object.{u}) :
    (λ_ X).hom = leftUnitorHom X :=
  rfl

@[simp]
theorem leftUnitor_inv_eq (X : Object.{u}) :
    (λ_ X).inv = leftUnitorInv X :=
  rfl

@[simp]
theorem rightUnitor_hom_eq (X : Object.{u}) :
    (ρ_ X).hom = rightUnitorHom X :=
  rfl

@[simp]
theorem rightUnitor_inv_eq (X : Object.{u}) :
    (ρ_ X).inv = rightUnitorInv X :=
  rfl

@[simp]
theorem tensorUnit_eq : (𝟙_ Object.{u}) = Object.unit :=
  rfl

@[simp]
theorem tensorObj_eq (X Y : Object.{u}) : X ⊗ Y = Object.tensor X Y :=
  rfl

@[simp]
theorem whiskerLeft_eq {X Y Z : Object.{u}} (morphism : Y ⟶ Z) :
    X ◁ morphism = tensor (𝟙 X) morphism :=
  rfl

@[simp]
theorem whiskerRight_eq {X Y Z : Object.{u}} (morphism : X ⟶ Y) :
    morphism ▷ Z = tensor morphism (𝟙 Z) :=
  rfl

theorem categoryId_eq (X : Object.{u}) : (𝟙 X : X ⟶ X) = identity X :=
  rfl

theorem categoryComp_eq {X Y Z : Object.{u}} (left : X ⟶ Y)
    (right : Y ⟶ Z) : left ≫ right = comp left right :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Independent finite stochastic channels form a monoidal category. -/
instance monoidalCategory : MonoidalCategory Object.{u} :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := tensor_id)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := by
      intro X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂
      exact (tensor_comp f₁ g₁ f₂ g₂).symm)
    (associator_naturality := by
      intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
      change
        comp (tensor (tensor f₁ f₂) f₃)
            (dirac (associatorEquiv Y₁ Y₂ Y₃)) =
          comp (dirac (associatorEquiv X₁ X₂ X₃))
            (tensor f₁ (tensor f₂ f₃))
      apply ext
      intro input output
      rcases input with ⟨⟨x₁, x₂⟩, x₃⟩
      rcases output with ⟨y₁, y₂, y₃⟩
      rw [comp_diracEquiv_apply, diracEquiv_comp_apply]
      simp [associatorEquiv, tensor, mul_assoc])
    (leftUnitor_naturality := by
      intro X Y morphism
      change
        comp (tensor (identity Object.unit) morphism)
            (dirac (leftUnitorEquiv Y)) =
          comp (dirac (leftUnitorEquiv X)) morphism
      apply ext
      intro input output
      rcases input with ⟨unitValue, x⟩
      cases unitValue
      rw [comp_diracEquiv_apply, diracEquiv_comp_apply]
      simp [identity, tensor, leftUnitorEquiv])
    (rightUnitor_naturality := by
      intro X Y morphism
      change
        comp (tensor morphism (identity Object.unit))
            (dirac (rightUnitorEquiv Y)) =
          comp (dirac (rightUnitorEquiv X)) morphism
      apply ext
      intro input output
      rcases input with ⟨x, unitValue⟩
      cases unitValue
      rw [comp_diracEquiv_apply, diracEquiv_comp_apply]
      simp [identity, tensor, rightUnitorEquiv])
    (pentagon := by
      intro W X Y Z
      simp only [tensorHom_eq, associator_hom_eq]
      change
        comp (tensor (dirac _) (identity Z))
            (comp (dirac _) (tensor (identity W) (dirac _))) =
          comp (dirac _) (dirac _)
      rw [← dirac_id Z, ← dirac_id W, dirac_tensor, dirac_tensor,
        ← dirac_comp, ← dirac_comp, ← dirac_comp]
      rfl)
    (triangle := by
      intro X Y
      simp only [tensorHom_eq, associator_hom_eq, leftUnitor_hom_eq,
        rightUnitor_hom_eq]
      change
        comp (dirac _) (tensor (identity X) (dirac _)) =
          tensor (dirac _) (identity Y)
      rw [← dirac_id X, ← dirac_id Y, dirac_tensor, dirac_tensor,
        ← dirac_comp]
      rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The product tensor is symmetric via deterministic swapping. -/
instance symmetricCategory : SymmetricCategory Object.{u} where
  braiding X Y :=
    { hom := braidHom X Y
      inv := braidHom Y X
      hom_inv_id := by
        change comp (dirac _) (dirac _) = identity _
        rw [← dirac_comp, ← dirac_id]
        congr
      inv_hom_id := by
        change comp (dirac _) (dirac _) = identity _
        rw [← dirac_comp, ← dirac_id]
        congr }
  braiding_naturality_right X := by
    intro Y Z morphism
    change
      comp (tensor (identity X) morphism) (dirac (braidEquiv X Z)) =
        comp (dirac (braidEquiv X Y)) (tensor morphism (identity X))
    apply ext
    intro input output
    rcases input with ⟨x, y⟩
    rcases output with ⟨z, x'⟩
    rw [comp_diracEquiv_apply, diracEquiv_comp_apply]
    simp [identity, tensor, braidEquiv, mul_comm]
  braiding_naturality_left := by
    intro X Y morphism Z
    change
      comp (tensor morphism (identity Z)) (dirac (braidEquiv Y Z)) =
        comp (dirac (braidEquiv X Z)) (tensor (identity Z) morphism)
    apply ext
    intro input output
    rcases input with ⟨x, z⟩
    rcases output with ⟨z', y⟩
    rw [comp_diracEquiv_apply, diracEquiv_comp_apply]
    simp [identity, tensor, braidEquiv, mul_comm]
  hexagon_forward X Y Z := by
    simp only [associator_hom_eq]
    change
      comp (dirac _) (comp (dirac _) (dirac _)) =
        comp (tensor (dirac _) (identity Z))
          (comp (dirac _) (tensor (identity Y) (dirac _)))
    rw [← dirac_id Z, ← dirac_id Y, dirac_tensor, dirac_tensor,
      ← dirac_comp, ← dirac_comp, ← dirac_comp, ← dirac_comp]
    rfl
  hexagon_reverse X Y Z := by
    simp only [associator_inv_eq]
    change
      comp (dirac _) (comp (dirac _) (dirac _)) =
        comp (tensor (identity X) (dirac _))
          (comp (dirac _) (tensor (dirac _) (identity Y)))
    rw [← dirac_id X, ← dirac_id Y, dirac_tensor, dirac_tensor,
      ← dirac_comp, ← dirac_comp, ← dirac_comp, ← dirac_comp]
    rfl
  symmetry X Y := by
    change comp (dirac _) (dirac _) = identity _
    rw [← dirac_comp, ← dirac_id]
    congr

@[simp]
theorem braiding_hom_eq (X Y : Object.{u}) :
    (β_ X Y).hom = braidHom X Y :=
  rfl

/-- Tensoring zero-cost stochastic channels remains zero-cost. -/
instance zeroParallelCost : HasParallelProcessCost Object.{u} Nat where
  cost_tensor _ _ := Nat.zero_le 0

/-- Deterministic coherence maps have zero abstract stochastic cost. -/
instance zeroStructuralCost : HasFreeStructuralCost Object.{u} Nat where
  cost_associator _ _ _ := rfl
  cost_associator_inv _ _ _ := rfl
  cost_leftUnitor _ := rfl
  cost_leftUnitor_inv _ := rfl
  cost_rightUnitor _ := rfl
  cost_rightUnitor_inv _ := rfl
  cost_braiding _ _ := rfl

@[simp]
theorem tensorHom_apply {W X Y Z : Object.{u}}
    (left : W ⟶ X) (right : Y ⟶ Z) (input : W × Y) (output : X × Z) :
    (left ⊗ₘ right).prob input output =
      left.prob input.1 output.1 * right.prob input.2 output.2 :=
  rfl

end FinStoch

end Ript.Models.FiniteStochastic
