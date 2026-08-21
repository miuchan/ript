import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Ript.Core.ParallelCost
import Ript.Core.StructuralCost
import Ript.Models.Computation.Total

/-!
# Symmetric monoidal total computations

Independent execution is the tensor product.  It acts componentwise on values
and adds all four resource coordinates exactly.  Coherence maps are executable
zero-cost rebracketing, unit, and swap computations.
-/

set_option autoImplicit false

namespace Ript.Models.Computation.Total

open CategoryTheory
open MonoidalCategory
open Ript.Core

universe u

/-- Rebracket a triple of executable values at zero resource cost. -/
def associatorHom (X Y Z : Object.{u}) :
    Object.tensor (Object.tensor X Y) Z ⟶
      Object.tensor X (Object.tensor Y Z) :=
  ⟨fun input ↦ (input.1.1, (input.1.2, input.2)), 0⟩

/-- Inverse zero-cost rebracketing. -/
def associatorInv (X Y Z : Object.{u}) :
    Object.tensor X (Object.tensor Y Z) ⟶
      Object.tensor (Object.tensor X Y) Z :=
  ⟨fun input ↦ ((input.1, input.2.1), input.2.2), 0⟩

/-- Remove the left unit at zero cost. -/
def leftUnitorHom (X : Object.{u}) : Object.tensor Object.unit X ⟶ X :=
  ⟨fun input ↦ input.2, 0⟩

/-- Insert the left unit at zero cost. -/
def leftUnitorInv (X : Object.{u}) : X ⟶ Object.tensor Object.unit X :=
  ⟨fun input ↦ (PUnit.unit, input), 0⟩

/-- Remove the right unit at zero cost. -/
def rightUnitorHom (X : Object.{u}) : Object.tensor X Object.unit ⟶ X :=
  ⟨fun input ↦ input.1, 0⟩

/-- Insert the right unit at zero cost. -/
def rightUnitorInv (X : Object.{u}) : X ⟶ Object.tensor X Object.unit :=
  ⟨fun input ↦ (input, PUnit.unit), 0⟩

/-- Swap two executable values at zero cost. -/
def braidHom (X Y : Object.{u}) : Object.tensor X Y ⟶ Object.tensor Y X :=
  ⟨fun input ↦ (input.2, input.1), 0⟩

/-- Product objects, independent execution, and executable coherence maps. -/
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
        apply Hom.ext
        · funext input; rfl
        · simp [associatorHom, associatorInv]
      inv_hom_id := by
        apply Hom.ext
        · funext input; rfl
        · simp [associatorHom, associatorInv] }
  leftUnitor X :=
    { hom := leftUnitorHom X
      inv := leftUnitorInv X
      hom_inv_id := by
        apply Hom.ext
        · funext input
          rcases input with ⟨unitValue, x⟩
          cases unitValue
          rfl
        · simp [leftUnitorHom, leftUnitorInv]
      inv_hom_id := by
        apply Hom.ext
        · funext input; rfl
        · simp [leftUnitorHom, leftUnitorInv] }
  rightUnitor X :=
    { hom := rightUnitorHom X
      inv := rightUnitorInv X
      hom_inv_id := by
        apply Hom.ext
        · funext input
          rcases input with ⟨x, unitValue⟩
          cases unitValue
          rfl
        · simp [rightUnitorHom, rightUnitorInv]
      inv_hom_id := by
        apply Hom.ext
        · funext input; rfl
        · simp [rightUnitorHom, rightUnitorInv] }

@[simp]
theorem tensorHom_eq {W X Y Z : Object.{u}}
    (left : W ⟶ X) (right : Y ⟶ Z) :
    left ⊗ₘ right = tensor left right :=
  rfl

@[simp]
theorem whiskerLeft_resource {X Y Z : Object.{u}} (morphism : Y ⟶ Z) :
    (X ◁ morphism).resource = morphism.resource := by
  change (0 : ComputationResource) + morphism.resource = morphism.resource
  simp

@[simp]
theorem whiskerRight_resource {X Y Z : Object.{u}} (morphism : X ⟶ Y) :
    (morphism ▷ Z).resource = morphism.resource := by
  change morphism.resource + (0 : ComputationResource) = morphism.resource
  simp

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
theorem rightUnitor_hom_eq (X : Object.{u}) :
    (ρ_ X).hom = rightUnitorHom X :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Total computations form a monoidal category under independent execution. -/
instance monoidalCategory : MonoidalCategory Object.{u} :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := tensor_id)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := by
      intro X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂
      exact (tensor_comp f₁ g₁ f₂ g₂).symm)
    (associator_naturality := by
      intros
      apply Hom.ext
      · funext input; rfl
      · simp [associatorHom, tensor, add_assoc])
    (leftUnitor_naturality := by
      intros
      apply Hom.ext
      · funext input
        rcases input with ⟨unitValue, value⟩
        cases unitValue
        rfl
      · simp [leftUnitorHom, tensor])
    (rightUnitor_naturality := by
      intros
      apply Hom.ext
      · funext input
        rcases input with ⟨value, unitValue⟩
        cases unitValue
        rfl
      · simp [rightUnitorHom, tensor])
    (pentagon := by
      intros
      apply Hom.ext
      · funext input; rfl
      · simp [associatorHom, tensor])
    (triangle := by
      intros
      apply Hom.ext
      · funext input
        rcases input with ⟨⟨value, unitValue⟩, right⟩
        cases unitValue
        rfl
      · simp [associatorHom, leftUnitorHom, rightUnitorHom, tensor])

set_option backward.isDefEq.respectTransparency false in
/-- Independent execution is symmetric via zero-cost swapping. -/
instance symmetricCategory : SymmetricCategory Object.{u} where
  braiding X Y :=
    { hom := braidHom X Y
      inv := braidHom Y X
      hom_inv_id := by
        apply Hom.ext
        · funext input; rfl
        · simp [braidHom]
      inv_hom_id := by
        apply Hom.ext
        · funext input; rfl
        · simp [braidHom] }
  braiding_naturality_right X := by
    intros
    apply Hom.ext
    · funext input; rfl
    · simp [braidHom]
  braiding_naturality_left := by
    intros
    apply Hom.ext
    · funext input; rfl
    · simp [braidHom]
  hexagon_forward X Y Z := by
    apply Hom.ext
    · funext input; rfl
    · simp [associatorHom, braidHom]
  hexagon_reverse X Y Z := by
    apply Hom.ext
    · funext input; rfl
    · simp [associatorInv, braidHom]
  symmetry X Y := by
    apply Hom.ext
    · funext input; rfl
    · simp [braidHom]

/-- Independent execution adds the exact stored resource vectors. -/
instance parallelCost : HasParallelProcessCost Object.{u} ComputationResource where
  cost_tensor _ _ := le_rfl

/-- All coherence computations have zero resource cost. -/
instance freeStructuralCost :
    HasFreeStructuralCost Object.{u} ComputationResource where
  cost_associator _ _ _ := rfl
  cost_associator_inv _ _ _ := rfl
  cost_leftUnitor _ := rfl
  cost_leftUnitor_inv _ := rfl
  cost_rightUnitor _ := rfl
  cost_rightUnitor_inv _ := rfl
  cost_braiding _ _ := rfl

@[simp]
theorem tensorHom_run {W X Y Z : Object.{u}}
    (left : W ⟶ X) (right : Y ⟶ Z) (input : W × Y) :
    (left ⊗ₘ right).run input =
      (left.run input.1, right.run input.2) :=
  rfl

@[simp]
theorem tensorHom_resource {W X Y Z : Object.{u}}
    (left : W ⟶ X) (right : Y ⟶ Z) :
    (left ⊗ₘ right).resource = left.resource + right.resource :=
  rfl

end Ript.Models.Computation.Total
