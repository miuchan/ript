import Ript.Core.ParallelCost
import Ript.Core.StructuralCost
import Ript.Models.Computation.Randomized
import Ript.Models.FiniteStochastic.Monoidal

/-!
# Symmetric monoidal randomized computations

Independent stochastic execution tensors exact kernels and adds all four
resource coordinates.  Associator, unitors, and swapping are deterministic
zero-resource programs inherited from finite stochastic channels.
-/

set_option autoImplicit false

namespace Ript.Models.Computation.Randomized

open CategoryTheory
open MonoidalCategory
open Ript.Core
open Ript.Models.FiniteStochastic

universe u

/-- Zero-resource product reassociation. -/
def associatorHom (X Y Z : Object.{u}) :
    Object.tensor (Object.tensor X Y) Z ⟶
      Object.tensor X (Object.tensor Y Z) :=
  ⟨FinStoch.associatorHom X.classical Y.classical Z.classical, 0⟩

/-- Inverse zero-resource reassociation. -/
def associatorInv (X Y Z : Object.{u}) :
    Object.tensor X (Object.tensor Y Z) ⟶
      Object.tensor (Object.tensor X Y) Z :=
  ⟨FinStoch.associatorInv X.classical Y.classical Z.classical, 0⟩

/-- Remove the left unit. -/
def leftUnitorHom (X : Object.{u}) : Object.tensor Object.unit X ⟶ X :=
  ⟨FinStoch.leftUnitorHom X.classical, 0⟩

/-- Insert the left unit. -/
def leftUnitorInv (X : Object.{u}) : X ⟶ Object.tensor Object.unit X :=
  ⟨FinStoch.leftUnitorInv X.classical, 0⟩

/-- Remove the right unit. -/
def rightUnitorHom (X : Object.{u}) : Object.tensor X Object.unit ⟶ X :=
  ⟨FinStoch.rightUnitorHom X.classical, 0⟩

/-- Insert the right unit. -/
def rightUnitorInv (X : Object.{u}) : X ⟶ Object.tensor X Object.unit :=
  ⟨FinStoch.rightUnitorInv X.classical, 0⟩

/-- Swap independent randomized interfaces. -/
def braidHom (X Y : Object.{u}) : Object.tensor X Y ⟶ Object.tensor Y X :=
  ⟨FinStoch.braidHom X.classical Y.classical, 0⟩

instance monoidalCategoryStruct : MonoidalCategoryStruct Object.{u} where
  tensorObj := Object.tensor
  tensorUnit := Object.unit
  whiskerLeft X _ _ program := tensor (𝟙 X) program
  whiskerRight program Y := tensor program (𝟙 Y)
  tensorHom := tensor
  associator X Y Z :=
    { hom := associatorHom X Y Z
      inv := associatorInv X Y Z
      hom_inv_id := by
        apply Hom.ext
        · exact (FinStoch.monoidalCategoryStruct.associator
            X.classical Y.classical Z.classical).hom_inv_id
        · simp [associatorHom, associatorInv]
      inv_hom_id := by
        apply Hom.ext
        · exact (FinStoch.monoidalCategoryStruct.associator
            X.classical Y.classical Z.classical).inv_hom_id
        · simp [associatorHom, associatorInv] }
  leftUnitor X :=
    { hom := leftUnitorHom X
      inv := leftUnitorInv X
      hom_inv_id := by
        apply Hom.ext
        · exact (FinStoch.monoidalCategoryStruct.leftUnitor
            X.classical).hom_inv_id
        · simp [leftUnitorHom, leftUnitorInv]
      inv_hom_id := by
        apply Hom.ext
        · exact (FinStoch.monoidalCategoryStruct.leftUnitor
            X.classical).inv_hom_id
        · simp [leftUnitorHom, leftUnitorInv] }
  rightUnitor X :=
    { hom := rightUnitorHom X
      inv := rightUnitorInv X
      hom_inv_id := by
        apply Hom.ext
        · exact (FinStoch.monoidalCategoryStruct.rightUnitor
            X.classical).hom_inv_id
        · simp [rightUnitorHom, rightUnitorInv]
      inv_hom_id := by
        apply Hom.ext
        · exact (FinStoch.monoidalCategoryStruct.rightUnitor
            X.classical).inv_hom_id
        · simp [rightUnitorHom, rightUnitorInv] }

@[simp]
theorem tensorHom_eq {V W X Y : Object.{u}} (first : V ⟶ W)
    (second : X ⟶ Y) : first ⊗ₘ second = tensor first second := rfl

@[simp]
theorem associator_hom_eq (X Y Z : Object.{u}) :
    (α_ X Y Z).hom = associatorHom X Y Z := rfl

@[simp]
theorem associator_inv_eq (X Y Z : Object.{u}) :
    (α_ X Y Z).inv = associatorInv X Y Z := rfl

@[simp]
theorem leftUnitor_hom_eq (X : Object.{u}) :
    (λ_ X).hom = leftUnitorHom X := rfl

@[simp]
theorem rightUnitor_hom_eq (X : Object.{u}) :
    (ρ_ X).hom = rightUnitorHom X := rfl

@[simp]
theorem tensorObj_classical (X Y : Object.{u}) :
    (X ⊗ Y).classical =
      FiniteStochastic.Object.tensor X.classical Y.classical := rfl

@[simp]
theorem tensorUnit_classical :
    (𝟙_ Object.{u}).classical = FiniteStochastic.Object.unit := rfl

@[simp]
theorem tensorHom_channel {V W X Y : Object.{u}}
    (first : V ⟶ W) (second : X ⟶ Y) :
    (first ⊗ₘ second).channel =
      FinStoch.tensor first.channel second.channel := rfl

@[simp]
theorem associator_hom_channel (X Y Z : Object.{u}) :
    (associatorHom X Y Z).channel =
      FinStoch.associatorHom X.classical Y.classical Z.classical := rfl

@[simp]
theorem associator_inv_channel (X Y Z : Object.{u}) :
    (associatorInv X Y Z).channel =
      FinStoch.associatorInv X.classical Y.classical Z.classical := rfl

@[simp]
theorem leftUnitor_hom_channel (X : Object.{u}) :
    (leftUnitorHom X).channel = FinStoch.leftUnitorHom X.classical := rfl

@[simp]
theorem rightUnitor_hom_channel (X : Object.{u}) :
    (rightUnitorHom X).channel = FinStoch.rightUnitorHom X.classical := rfl

@[simp]
theorem whiskerLeft_channel {X Y Z : Object.{u}} (program : Y ⟶ Z) :
    (X ◁ program).channel =
      FinStoch.tensor (FinStoch.identity X.classical) program.channel := rfl

@[simp]
theorem whiskerRight_channel {X Y Z : Object.{u}} (program : X ⟶ Y) :
    (program ▷ Z).channel =
      FinStoch.tensor program.channel (FinStoch.identity Z.classical) := rfl

@[simp]
theorem whiskerLeft_resource {X Y Z : Object.{u}} (program : Y ⟶ Z) :
    (X ◁ program).resource = program.resource := by
  change (0 : ComputationResource) + program.resource = program.resource
  simp

@[simp]
theorem whiskerRight_resource {X Y Z : Object.{u}} (program : X ⟶ Y) :
    (program ▷ Z).resource = program.resource := by
  change program.resource + (0 : ComputationResource) = program.resource
  simp

set_option backward.isDefEq.respectTransparency false in
instance monoidalCategory : MonoidalCategory Object.{u} :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := tensor_id)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := by
      intros
      exact (tensor_comp _ _ _ _).symm)
    (associator_naturality := by
      intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
      apply Hom.ext
      · simpa only [channel_comp, tensorHom_channel, associator_hom_eq,
          associator_hom_channel, tensorObj_classical,
          FinStoch.categoryComp_eq, FinStoch.tensorHom_eq,
          FinStoch.associator_hom_eq, FinStoch.tensorObj_eq] using
          FinStoch.monoidalCategory.associator_naturality
            f₁.channel f₂.channel f₃.channel
      · simp [associatorHom, tensor, add_assoc])
    (leftUnitor_naturality := by
      intro X Y program
      apply Hom.ext
      · simpa only [channel_comp, tensorHom_channel, channel_id,
          leftUnitor_hom_eq,
          leftUnitor_hom_channel, tensorObj_classical, tensorUnit_classical,
          FinStoch.categoryComp_eq, FinStoch.tensorHom_eq,
          FinStoch.categoryId_eq, FinStoch.leftUnitor_hom_eq,
          FinStoch.tensorObj_eq, FinStoch.tensorUnit_eq,
          FinStoch.whiskerLeft_eq] using
          FinStoch.monoidalCategory.leftUnitor_naturality program.channel
      · simp [leftUnitorHom])
    (rightUnitor_naturality := by
      intro X Y program
      apply Hom.ext
      · simpa only [channel_comp, tensorHom_channel, channel_id,
          rightUnitor_hom_eq,
          rightUnitor_hom_channel, tensorObj_classical, tensorUnit_classical,
          FinStoch.categoryComp_eq, FinStoch.tensorHom_eq,
          FinStoch.categoryId_eq, FinStoch.rightUnitor_hom_eq,
          FinStoch.tensorObj_eq, FinStoch.tensorUnit_eq,
          FinStoch.whiskerRight_eq] using
          FinStoch.monoidalCategory.rightUnitor_naturality program.channel
      · simp [rightUnitorHom])
    (pentagon := by
      intro W X Y Z
      apply Hom.ext
      · simpa only [channel_comp, tensorHom_channel, channel_id,
          associator_hom_eq,
          associator_hom_channel, tensorObj_classical,
          FinStoch.categoryComp_eq, FinStoch.tensorHom_eq,
          FinStoch.categoryId_eq, FinStoch.associator_hom_eq,
          FinStoch.tensorObj_eq, FinStoch.whiskerLeft_eq,
          FinStoch.whiskerRight_eq] using
          FinStoch.monoidalCategory.pentagon
            W.classical X.classical Y.classical Z.classical
      · simp [associatorHom])
    (triangle := by
      intro X Y
      apply Hom.ext
      · simpa only [channel_comp, tensorHom_channel, channel_id,
          associator_hom_eq, leftUnitor_hom_eq, rightUnitor_hom_eq,
          associator_hom_channel, leftUnitor_hom_channel,
          rightUnitor_hom_channel, tensorObj_classical, tensorUnit_classical,
          FinStoch.categoryComp_eq, FinStoch.tensorHom_eq,
          FinStoch.categoryId_eq, FinStoch.associator_hom_eq,
          FinStoch.leftUnitor_hom_eq, FinStoch.rightUnitor_hom_eq,
          FinStoch.tensorObj_eq, FinStoch.tensorUnit_eq,
          FinStoch.whiskerLeft_eq, FinStoch.whiskerRight_eq] using
          FinStoch.monoidalCategory.triangle X.classical Y.classical
      · simp [associatorHom, leftUnitorHom, rightUnitorHom])

set_option backward.isDefEq.respectTransparency false in
instance symmetricCategory : SymmetricCategory Object.{u} where
  braiding X Y :=
    { hom := braidHom X Y
      inv := braidHom Y X
      hom_inv_id := by
        apply Hom.ext
        · exact (FinStoch.symmetricCategory.braiding
            X.classical Y.classical).hom_inv_id
        · simp [braidHom]
      inv_hom_id := by
        apply Hom.ext
        · exact (FinStoch.symmetricCategory.braiding
            X.classical Y.classical).inv_hom_id
        · simp [braidHom] }
  braiding_naturality_right X := by
    intro Y Z program
    apply Hom.ext
    · simpa only [channel_comp, whiskerLeft_channel,
        whiskerRight_channel, braidHom, tensorObj_classical,
        FinStoch.categoryComp_eq, FinStoch.categoryId_eq,
        FinStoch.whiskerLeft_eq, FinStoch.whiskerRight_eq,
        FinStoch.braiding_hom_eq, FinStoch.tensorObj_eq] using
        FinStoch.symmetricCategory.braiding_naturality_right
          X.classical program.channel
    · simp [braidHom]
  braiding_naturality_left := by
    intro X Y program Z
    apply Hom.ext
    · simpa only [channel_comp, whiskerLeft_channel,
        whiskerRight_channel, braidHom, tensorObj_classical,
        FinStoch.categoryComp_eq, FinStoch.categoryId_eq,
        FinStoch.whiskerLeft_eq, FinStoch.whiskerRight_eq,
        FinStoch.braiding_hom_eq, FinStoch.tensorObj_eq] using
        FinStoch.symmetricCategory.braiding_naturality_left
          program.channel Z.classical
    · simp [braidHom]
  hexagon_forward X Y Z := by
    apply Hom.ext
    · simpa only [channel_comp, whiskerLeft_channel,
        whiskerRight_channel, associator_hom_eq, associator_hom_channel, braidHom,
        tensorObj_classical, FinStoch.categoryComp_eq,
        FinStoch.categoryId_eq, FinStoch.whiskerLeft_eq,
        FinStoch.whiskerRight_eq, FinStoch.associator_hom_eq,
        FinStoch.braiding_hom_eq, FinStoch.tensorObj_eq] using
        FinStoch.symmetricCategory.hexagon_forward
          X.classical Y.classical Z.classical
    · simp [associatorHom, braidHom]
  hexagon_reverse X Y Z := by
    apply Hom.ext
    · simpa only [channel_comp, whiskerLeft_channel,
        whiskerRight_channel, associator_inv_eq, associator_inv_channel, braidHom,
        tensorObj_classical, FinStoch.categoryComp_eq,
        FinStoch.categoryId_eq, FinStoch.whiskerLeft_eq,
        FinStoch.whiskerRight_eq, FinStoch.associator_inv_eq,
        FinStoch.braiding_hom_eq, FinStoch.tensorObj_eq] using
        FinStoch.symmetricCategory.hexagon_reverse
          X.classical Y.classical Z.classical
    · simp [associatorInv, braidHom]
  symmetry X Y := by
    apply Hom.ext
    · simpa only [channel_comp, channel_id, braidHom,
        tensorObj_classical, FinStoch.categoryComp_eq,
        FinStoch.categoryId_eq, FinStoch.braiding_hom_eq,
        FinStoch.tensorObj_eq] using
        FinStoch.symmetricCategory.symmetry X.classical Y.classical
    · simp [braidHom]

instance parallelCost : HasParallelProcessCost Object ComputationResource where
  cost_tensor _ _ := le_rfl

instance structuralCost : HasFreeStructuralCost Object ComputationResource where
  cost_associator _ _ _ := rfl
  cost_associator_inv _ _ _ := rfl
  cost_leftUnitor _ := rfl
  cost_leftUnitor_inv _ := rfl
  cost_rightUnitor _ := rfl
  cost_rightUnitor_inv _ := rfl
  cost_braiding _ _ := rfl

@[simp]
theorem tensorHom_probability {V W X Y : Object.{u}}
    (first : V ⟶ W) (second : X ⟶ Y)
    (input : V × X) (output : W × Y) :
    probability (first ⊗ₘ second) input output =
      probability first input.1 output.1 *
        probability second input.2 output.2 :=
  rfl

end Ript.Models.Computation.Randomized
