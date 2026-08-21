import Ript.Core.ParallelCost
import Ript.Core.StructuralCost
import Ript.Models.FiniteStochastic.Monoidal
import Ript.Models.Quantum.ClassicalEmbedding

/-!
# A symmetric monoidal classical quantum image

This category is a distinct quantum realization of exact finite stochastic
channels.  Every morphism stores its exact stochastic matrix and denotes the
corresponding measurement--preparation Kraus channel.  The faithful functor to
the dephasing-idempotent quantum category proves that no stochastic morphism is
identified by the quantum realization.
-/

set_option autoImplicit false

namespace Ript.Models.Quantum.ClassicalMonoidal

open CategoryTheory
open MonoidalCategory
open Ript.Core
open Ript.Models.FiniteStochastic
open Ript.Models.Quantum.ClassicalEmbedding

universe u

/-- A finite basis regarded as an object of the classical quantum image. -/
structure Object where
  /-- Exact finite classical basis underlying the quantum image object. -/
  classical : FiniteStochastic.Object.{u}

/-- A morphism whose quantum denotation is measurement--preparation. -/
structure Channel (X Y : Object.{u}) where
  /-- Exact stochastic channel whose measurement--preparation image is used. -/
  stochastic : FinStoch X.classical Y.classical

namespace Channel

variable {W X Y Z : Object.{u}}

@[ext]
theorem ext (left right : Channel X Y)
    (stochastic_eq : left.stochastic = right.stochastic) : left = right := by
  cases left
  cases right
  cases stochastic_eq
  rfl

/-- Ambient Kraus denotation of an image-channel morphism. -/
noncomputable def toKraus (channel : Channel X Y) :
    KrausChannel (classicalObject X.classical) (classicalObject Y.classical) :=
  measurementPreparation channel.stochastic

end Channel

/-- Categorical identity in the classical quantum image. -/
def identity (X : Object.{u}) : Channel X X :=
  ⟨FinStoch.identity X.classical⟩

/-- Serial composition in the classical quantum image. -/
def comp {X Y Z : Object.{u}} (left : Channel X Y) (right : Channel Y Z) :
    Channel X Z :=
  ⟨FinStoch.comp left.stochastic right.stochastic⟩

/-- The image channels form a category. -/
instance category : Category.{u} Object.{u} where
  Hom := Channel
  id := identity
  comp := comp
  id_comp := by
    intro X Y morphism
    apply Channel.ext
    exact FinStoch.category.id_comp morphism.stochastic
  comp_id := by
    intro X Y morphism
    apply Channel.ext
    exact FinStoch.category.comp_id morphism.stochastic
  assoc := by
    intro W X Y Z first second third
    apply Channel.ext
    exact FinStoch.category.assoc first.stochastic second.stochastic
      third.stochastic

/-- Tensor unit basis. -/
abbrev Object.unit : Object.{u} :=
  ⟨FiniteStochastic.Object.unit⟩

/-- Product basis. -/
abbrev Object.tensor (X Y : Object.{u}) : Object.{u} :=
  ⟨FiniteStochastic.Object.tensor X.classical Y.classical⟩

/-- Independent tensor of image channels. -/
def tensor {W X Y Z : Object.{u}} (left : W ⟶ X) (right : Y ⟶ Z) :
    Object.tensor W Y ⟶ Object.tensor X Z :=
  ⟨FinStoch.tensor left.stochastic right.stochastic⟩

/-- Rebracketing image channel. -/
def associatorHom (X Y Z : Object.{u}) :
    Object.tensor (Object.tensor X Y) Z ⟶
      Object.tensor X (Object.tensor Y Z) :=
  ⟨FinStoch.associatorHom X.classical Y.classical Z.classical⟩

/-- Inverse product-basis rebracketing channel. -/
def associatorInv (X Y Z : Object.{u}) :
    Object.tensor X (Object.tensor Y Z) ⟶
      Object.tensor (Object.tensor X Y) Z :=
  ⟨FinStoch.associatorInv X.classical Y.classical Z.classical⟩

/-- Remove the left product-basis unit. -/
def leftUnitorHom (X : Object.{u}) : Object.tensor Object.unit X ⟶ X :=
  ⟨FinStoch.leftUnitorHom X.classical⟩

/-- Insert the left product-basis unit. -/
def leftUnitorInv (X : Object.{u}) : X ⟶ Object.tensor Object.unit X :=
  ⟨FinStoch.leftUnitorInv X.classical⟩

/-- Remove the right product-basis unit. -/
def rightUnitorHom (X : Object.{u}) : Object.tensor X Object.unit ⟶ X :=
  ⟨FinStoch.rightUnitorHom X.classical⟩

/-- Insert the right product-basis unit. -/
def rightUnitorInv (X : Object.{u}) : X ⟶ Object.tensor X Object.unit :=
  ⟨FinStoch.rightUnitorInv X.classical⟩

/-- Swap two product-basis factors. -/
def braidHom (X Y : Object.{u}) : Object.tensor X Y ⟶ Object.tensor Y X :=
  ⟨FinStoch.braidHom X.classical Y.classical⟩

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
        apply Channel.ext
        exact (FinStoch.monoidalCategoryStruct.associator
          X.classical Y.classical Z.classical).hom_inv_id
      inv_hom_id := by
        apply Channel.ext
        exact (FinStoch.monoidalCategoryStruct.associator
          X.classical Y.classical Z.classical).inv_hom_id }
  leftUnitor X :=
    { hom := leftUnitorHom X
      inv := leftUnitorInv X
      hom_inv_id := by
        apply Channel.ext
        exact (FinStoch.monoidalCategoryStruct.leftUnitor X.classical).hom_inv_id
      inv_hom_id := by
        apply Channel.ext
        exact (FinStoch.monoidalCategoryStruct.leftUnitor X.classical).inv_hom_id }
  rightUnitor X :=
    { hom := rightUnitorHom X
      inv := rightUnitorInv X
      hom_inv_id := by
        apply Channel.ext
        exact (FinStoch.monoidalCategoryStruct.rightUnitor X.classical).hom_inv_id
      inv_hom_id := by
        apply Channel.ext
        exact (FinStoch.monoidalCategoryStruct.rightUnitor X.classical).inv_hom_id }

@[simp]
theorem tensorObj_classical (X Y : Object.{u}) :
    (X ⊗ Y).classical = FiniteStochastic.Object.tensor X.classical Y.classical :=
  rfl

@[simp]
theorem tensorUnit_classical :
    (𝟙_ Object.{u}).classical = FiniteStochastic.Object.unit :=
  rfl

@[simp]
theorem categoryId_stochastic (X : Object.{u}) :
    (𝟙 X : X ⟶ X).stochastic = FinStoch.identity X.classical :=
  rfl

@[simp]
theorem categoryComp_stochastic {X Y Z : Object.{u}}
    (left : X ⟶ Y) (right : Y ⟶ Z) :
    (left ≫ right).stochastic =
      FinStoch.comp left.stochastic right.stochastic :=
  rfl

@[simp]
theorem tensorHom_stochastic {W X Y Z : Object.{u}}
    (left : W ⟶ X) (right : Y ⟶ Z) :
    (left ⊗ₘ right).stochastic =
      FinStoch.tensor left.stochastic right.stochastic :=
  rfl

@[simp]
theorem associator_hom_stochastic (X Y Z : Object.{u}) :
    (α_ X Y Z).hom.stochastic =
      FinStoch.associatorHom X.classical Y.classical Z.classical :=
  rfl

@[simp]
theorem associator_inv_stochastic (X Y Z : Object.{u}) :
    (α_ X Y Z).inv.stochastic =
      FinStoch.associatorInv X.classical Y.classical Z.classical :=
  rfl

@[simp]
theorem leftUnitor_hom_stochastic (X : Object.{u}) :
    (λ_ X).hom.stochastic = FinStoch.leftUnitorHom X.classical :=
  rfl

@[simp]
theorem rightUnitor_hom_stochastic (X : Object.{u}) :
    (ρ_ X).hom.stochastic = FinStoch.rightUnitorHom X.classical :=
  rfl

@[simp]
theorem whiskerLeft_stochastic {X Y Z : Object.{u}} (morphism : Y ⟶ Z) :
    (X ◁ morphism).stochastic =
      FinStoch.tensor (FinStoch.identity X.classical) morphism.stochastic :=
  rfl

@[simp]
theorem whiskerRight_stochastic {X Y Z : Object.{u}} (morphism : X ⟶ Y) :
    (morphism ▷ Z).stochastic =
      FinStoch.tensor morphism.stochastic (FinStoch.identity Z.classical) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
instance monoidalCategory : MonoidalCategory Object.{u} :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := by intros; apply Channel.ext; exact FinStoch.tensor_id _ _)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := by
      intros
      apply Channel.ext
      exact (FinStoch.tensor_comp _ _ _ _).symm)
    (associator_naturality := by
      intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
      apply Channel.ext
      simpa only [categoryComp_stochastic, tensorHom_stochastic,
        associator_hom_stochastic, tensorObj_classical,
        FinStoch.categoryComp_eq, FinStoch.tensorHom_eq,
        FinStoch.associator_hom_eq, FinStoch.tensorObj_eq] using
        FinStoch.monoidalCategory.associator_naturality
          f₁.stochastic f₂.stochastic f₃.stochastic)
    (leftUnitor_naturality := by
      intro X Y morphism
      apply Channel.ext
      simpa only [categoryComp_stochastic, tensorHom_stochastic,
        categoryId_stochastic, leftUnitor_hom_stochastic,
        tensorObj_classical, tensorUnit_classical,
        FinStoch.categoryComp_eq, FinStoch.tensorHom_eq,
        FinStoch.categoryId_eq, FinStoch.leftUnitor_hom_eq,
        FinStoch.tensorObj_eq, FinStoch.tensorUnit_eq,
        FinStoch.whiskerLeft_eq] using
        FinStoch.monoidalCategory.leftUnitor_naturality morphism.stochastic)
    (rightUnitor_naturality := by
      intro X Y morphism
      apply Channel.ext
      simpa only [categoryComp_stochastic, tensorHom_stochastic,
        categoryId_stochastic, rightUnitor_hom_stochastic,
        tensorObj_classical, tensorUnit_classical,
        FinStoch.categoryComp_eq, FinStoch.tensorHom_eq,
        FinStoch.categoryId_eq, FinStoch.rightUnitor_hom_eq,
        FinStoch.tensorObj_eq, FinStoch.tensorUnit_eq,
        FinStoch.whiskerRight_eq] using
        FinStoch.monoidalCategory.rightUnitor_naturality morphism.stochastic)
    (pentagon := by
      intro W X Y Z
      apply Channel.ext
      simpa only [categoryComp_stochastic, tensorHom_stochastic,
        categoryId_stochastic, associator_hom_stochastic,
        tensorObj_classical, FinStoch.categoryComp_eq,
        FinStoch.tensorHom_eq, FinStoch.categoryId_eq,
        FinStoch.associator_hom_eq, FinStoch.tensorObj_eq,
        FinStoch.whiskerLeft_eq, FinStoch.whiskerRight_eq] using
        FinStoch.monoidalCategory.pentagon
          W.classical X.classical Y.classical Z.classical)
    (triangle := by
      intro X Y
      apply Channel.ext
      simpa only [categoryComp_stochastic, tensorHom_stochastic,
        categoryId_stochastic, associator_hom_stochastic,
        leftUnitor_hom_stochastic, rightUnitor_hom_stochastic,
        tensorObj_classical, tensorUnit_classical,
        FinStoch.categoryComp_eq, FinStoch.tensorHom_eq,
        FinStoch.categoryId_eq, FinStoch.associator_hom_eq,
        FinStoch.leftUnitor_hom_eq, FinStoch.rightUnitor_hom_eq,
        FinStoch.tensorObj_eq, FinStoch.tensorUnit_eq,
        FinStoch.whiskerLeft_eq, FinStoch.whiskerRight_eq] using
        FinStoch.monoidalCategory.triangle X.classical Y.classical)

set_option backward.isDefEq.respectTransparency false in
instance symmetricCategory : SymmetricCategory Object.{u} where
  braiding X Y :=
    { hom := braidHom X Y
      inv := braidHom Y X
      hom_inv_id := by
        apply Channel.ext
        exact (FinStoch.symmetricCategory.braiding
          X.classical Y.classical).hom_inv_id
      inv_hom_id := by
        apply Channel.ext
        exact (FinStoch.symmetricCategory.braiding
          X.classical Y.classical).inv_hom_id }
  braiding_naturality_right X := by
    intro Y Z morphism
    apply Channel.ext
    simpa only [categoryComp_stochastic, whiskerLeft_stochastic,
      whiskerRight_stochastic, braidHom, tensorObj_classical,
      FinStoch.categoryComp_eq, FinStoch.categoryId_eq,
      FinStoch.whiskerLeft_eq, FinStoch.whiskerRight_eq,
      FinStoch.braiding_hom_eq, FinStoch.tensorObj_eq] using
      FinStoch.symmetricCategory.braiding_naturality_right
        X.classical morphism.stochastic
  braiding_naturality_left := by
    intro X Y morphism Z
    apply Channel.ext
    simpa only [categoryComp_stochastic, whiskerLeft_stochastic,
      whiskerRight_stochastic, braidHom, tensorObj_classical,
      FinStoch.categoryComp_eq, FinStoch.categoryId_eq,
      FinStoch.whiskerLeft_eq, FinStoch.whiskerRight_eq,
      FinStoch.braiding_hom_eq, FinStoch.tensorObj_eq] using
      FinStoch.symmetricCategory.braiding_naturality_left
        morphism.stochastic Z.classical
  hexagon_forward X Y Z := by
    apply Channel.ext
    simpa only [categoryComp_stochastic, whiskerLeft_stochastic,
      whiskerRight_stochastic, associator_hom_stochastic, braidHom,
      tensorObj_classical, FinStoch.categoryComp_eq,
      FinStoch.categoryId_eq, FinStoch.whiskerLeft_eq,
      FinStoch.whiskerRight_eq, FinStoch.associator_hom_eq,
      FinStoch.braiding_hom_eq, FinStoch.tensorObj_eq] using
      FinStoch.symmetricCategory.hexagon_forward
        X.classical Y.classical Z.classical
  hexagon_reverse X Y Z := by
    apply Channel.ext
    simpa only [categoryComp_stochastic, whiskerLeft_stochastic,
      whiskerRight_stochastic, associator_inv_stochastic, braidHom,
      tensorObj_classical, FinStoch.categoryComp_eq,
      FinStoch.categoryId_eq, FinStoch.whiskerLeft_eq,
      FinStoch.whiskerRight_eq, FinStoch.associator_inv_eq,
      FinStoch.braiding_hom_eq, FinStoch.tensorObj_eq] using
      FinStoch.symmetricCategory.hexagon_reverse
        X.classical Y.classical Z.classical
  symmetry X Y := by
    apply Channel.ext
    simpa only [categoryComp_stochastic, categoryId_stochastic, braidHom,
      tensorObj_classical, FinStoch.categoryComp_eq,
      FinStoch.categoryId_eq, FinStoch.braiding_hom_eq,
      FinStoch.tensorObj_eq] using
      FinStoch.symmetricCategory.symmetry X.classical Y.classical

/-- Faithful quantum realization into the dephasing-idempotent Kraus category. -/
noncomputable def quantumEmbedding :
    Object.{u} ⥤ ClassicalQuantum.Object.{u} where
  obj X := ClassicalQuantum.ofClassical X.classical
  map channel := ClassicalQuantum.ofChannel channel.stochastic
  map_id X := by apply ClassicalQuantum.Channel.ext; rfl
  map_comp left right := by
    apply ClassicalQuantum.Channel.ext
    exact measurementPreparation_comp left.stochastic right.stochastic

instance quantumEmbedding_faithful : quantumEmbedding.Faithful where
  map_injective equality := by
    apply Channel.ext
    exact measurementPreparation_faithful
      (congrArg ClassicalQuantum.Channel.toKraus equality)

instance zeroCost : HasProcessCost Object.{u} Nat where
  cost _ := 0
  cost_id _ := rfl
  cost_comp _ _ := Nat.zero_le 0

instance zeroParallelCost : HasParallelProcessCost Object.{u} Nat where
  cost_tensor _ _ := Nat.zero_le 0

instance zeroStructuralCost : HasFreeStructuralCost Object.{u} Nat where
  cost_associator _ _ _ := rfl
  cost_associator_inv _ _ _ := rfl
  cost_leftUnitor _ := rfl
  cost_leftUnitor_inv _ := rfl
  cost_rightUnitor _ := rfl
  cost_rightUnitor_inv _ := rfl
  cost_braiding _ _ := rfl

end Ript.Models.Quantum.ClassicalMonoidal
