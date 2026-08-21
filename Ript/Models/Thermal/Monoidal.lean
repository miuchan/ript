import Ript.Core.ParallelCost
import Ript.Core.StructuralCost
import Ript.Models.FiniteStochastic.Monoidal
import Ript.Models.Thermal.GibbsPreserving

/-!
# Symmetric monoidal Gibbs-preserving processes

Independent thermal composition uses product equilibrium states.  The
associator, unitors, and braiding are deterministic reindexing channels, and
their equilibrium-preservation proofs account for the factorization of product
equilibria explicitly.
-/

set_option autoImplicit false

namespace Ript.Models.Thermal

open CategoryTheory
open MonoidalCategory
open Ript.Core
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic

universe u

namespace GibbsPreserving

/-- Thermal associator induced by deterministic product rebracketing. -/
def associatorHom (X Y Z : ThermalObject.{u}) :
    ThermalObject.tensor (ThermalObject.tensor X Y) Z ⟶
      ThermalObject.tensor X (ThermalObject.tensor Y Z) where
  channel := FinStoch.associatorHom X.system Y.system Z.system
  preserves_equilibrium := by
    apply FinDist.ext
    intro output
    rcases output with ⟨x, y, z⟩
    change
      (((X.equilibrium.tensor Y.equilibrium).tensor Z.equilibrium).push
        (FinStoch.dirac
          (X := Object.tensor (Object.tensor X.system Y.system) Z.system)
          (Y := Object.tensor X.system (Object.tensor Y.system Z.system))
          (FinStoch.associatorEquiv X.system Y.system Z.system))).prob
            (x, y, z) = _
    rw [FinDist.push_diracEquiv_apply]
    exact mul_assoc _ _ _

/-- Inverse thermal associator. -/
def associatorInv (X Y Z : ThermalObject.{u}) :
    ThermalObject.tensor X (ThermalObject.tensor Y Z) ⟶
      ThermalObject.tensor (ThermalObject.tensor X Y) Z where
  channel := FinStoch.associatorInv X.system Y.system Z.system
  preserves_equilibrium := by
    apply FinDist.ext
    intro output
    rcases output with ⟨⟨x, y⟩, z⟩
    change
      ((X.equilibrium.tensor (Y.equilibrium.tensor Z.equilibrium)).push
        (FinStoch.dirac
          (X := Object.tensor X.system (Object.tensor Y.system Z.system))
          (Y := Object.tensor (Object.tensor X.system Y.system) Z.system)
          (FinStoch.associatorEquiv X.system Y.system Z.system).symm)).prob
            ((x, y), z) = _
    rw [FinDist.push_diracEquiv_apply]
    exact (mul_assoc _ _ _).symm

/-- Thermal left unitor. -/
def leftUnitorHom (X : ThermalObject.{u}) :
    ThermalObject.tensor ThermalObject.unit X ⟶ X where
  channel := FinStoch.leftUnitorHom X.system
  preserves_equilibrium := by
    apply FinDist.ext
    intro output
    change
      (((FinDist.pure PUnit.unit).tensor X.equilibrium).push
        (FinStoch.dirac
          (X := Object.tensor Object.unit X.system) (Y := X.system)
          (FinStoch.leftUnitorEquiv X.system))).prob output = _
    rw [FinDist.push_diracEquiv_apply]
    simp [FinStoch.leftUnitorEquiv]

/-- Inverse thermal left unitor. -/
def leftUnitorInv (X : ThermalObject.{u}) :
    X ⟶ ThermalObject.tensor ThermalObject.unit X where
  channel := FinStoch.leftUnitorInv X.system
  preserves_equilibrium := by
    apply FinDist.ext
    intro output
    rcases output with ⟨unitValue, x⟩
    cases unitValue
    change
      (X.equilibrium.push
        (FinStoch.dirac
          (X := X.system) (Y := Object.tensor Object.unit X.system)
          (FinStoch.leftUnitorEquiv X.system).symm)).prob
          (PUnit.unit, x) = _
    rw [FinDist.push_diracEquiv_apply]
    simp [FinStoch.leftUnitorEquiv]

/-- Thermal right unitor. -/
def rightUnitorHom (X : ThermalObject.{u}) :
    ThermalObject.tensor X ThermalObject.unit ⟶ X where
  channel := FinStoch.rightUnitorHom X.system
  preserves_equilibrium := by
    apply FinDist.ext
    intro output
    change
      ((X.equilibrium.tensor (FinDist.pure PUnit.unit)).push
        (FinStoch.dirac
          (X := Object.tensor X.system Object.unit) (Y := X.system)
          (FinStoch.rightUnitorEquiv X.system))).prob output = _
    rw [FinDist.push_diracEquiv_apply]
    simp [FinStoch.rightUnitorEquiv]

/-- Inverse thermal right unitor. -/
def rightUnitorInv (X : ThermalObject.{u}) :
    X ⟶ ThermalObject.tensor X ThermalObject.unit where
  channel := FinStoch.rightUnitorInv X.system
  preserves_equilibrium := by
    apply FinDist.ext
    intro output
    rcases output with ⟨x, unitValue⟩
    cases unitValue
    change
      (X.equilibrium.push
        (FinStoch.dirac
          (X := X.system) (Y := Object.tensor X.system Object.unit)
          (FinStoch.rightUnitorEquiv X.system).symm)).prob
          (x, PUnit.unit) = _
    rw [FinDist.push_diracEquiv_apply]
    simp [FinStoch.rightUnitorEquiv]

/-- Thermal braiding induced by deterministic swapping. -/
def braidHom (X Y : ThermalObject.{u}) :
    ThermalObject.tensor X Y ⟶ ThermalObject.tensor Y X where
  channel := FinStoch.braidHom X.system Y.system
  preserves_equilibrium := by
    apply FinDist.ext
    intro output
    rcases output with ⟨y, x⟩
    change
      ((X.equilibrium.tensor Y.equilibrium).push
        (FinStoch.dirac
          (X := Object.tensor X.system Y.system)
          (Y := Object.tensor Y.system X.system)
          (FinStoch.braidEquiv X.system Y.system))).prob
          (y, x) = _
    rw [FinDist.push_diracEquiv_apply]
    simp [FinStoch.braidEquiv, mul_comm]

/-- Product thermal systems and Gibbs-preserving independent composition. -/
instance monoidalCategoryStruct : MonoidalCategoryStruct ThermalObject.{u} where
  tensorObj := ThermalObject.tensor
  tensorUnit := ThermalObject.unit
  whiskerLeft X _ _ morphism := tensor (𝟙 X) morphism
  whiskerRight morphism Y := tensor morphism (𝟙 Y)
  tensorHom := tensor
  associator X Y Z :=
    { hom := associatorHom X Y Z
      inv := GibbsPreserving.associatorInv X Y Z
      hom_inv_id := by
        apply ext
        exact (FinStoch.monoidalCategoryStruct.associator
          X.system Y.system Z.system).hom_inv_id
      inv_hom_id := by
        apply ext
        exact (FinStoch.monoidalCategoryStruct.associator
          X.system Y.system Z.system).inv_hom_id }
  leftUnitor X :=
    { hom := leftUnitorHom X
      inv := leftUnitorInv X
      hom_inv_id := by
        apply ext
        exact (FinStoch.monoidalCategoryStruct.leftUnitor X.system).hom_inv_id
      inv_hom_id := by
        apply ext
        exact (FinStoch.monoidalCategoryStruct.leftUnitor X.system).inv_hom_id }
  rightUnitor X :=
    { hom := rightUnitorHom X
      inv := rightUnitorInv X
      hom_inv_id := by
        apply ext
        exact (FinStoch.monoidalCategoryStruct.rightUnitor X.system).hom_inv_id
      inv_hom_id := by
        apply ext
        exact (FinStoch.monoidalCategoryStruct.rightUnitor X.system).inv_hom_id }

@[simp]
theorem tensorObj_system (X Y : ThermalObject.{u}) :
    (X ⊗ Y).system = Object.tensor X.system Y.system :=
  rfl

@[simp]
theorem tensorUnit_system :
    (𝟙_ ThermalObject.{u}).system = Object.unit :=
  rfl

@[simp]
theorem tensorHom_channel {V W X Y : ThermalObject.{u}}
    (left : V ⟶ W) (right : X ⟶ Y) :
    (left ⊗ₘ right).channel = FinStoch.tensor left.channel right.channel :=
  rfl

@[simp]
theorem associator_hom_channel (X Y Z : ThermalObject.{u}) :
    (α_ X Y Z).hom.channel =
      FinStoch.associatorHom X.system Y.system Z.system :=
  rfl

@[simp]
theorem associator_inv_channel (X Y Z : ThermalObject.{u}) :
    (α_ X Y Z).inv.channel =
      FinStoch.associatorInv X.system Y.system Z.system :=
  rfl

@[simp]
theorem leftUnitor_hom_channel (X : ThermalObject.{u}) :
    (λ_ X).hom.channel = FinStoch.leftUnitorHom X.system :=
  rfl

@[simp]
theorem rightUnitor_hom_channel (X : ThermalObject.{u}) :
    (ρ_ X).hom.channel = FinStoch.rightUnitorHom X.system :=
  rfl

@[simp]
theorem whiskerLeft_channel {X Y Z : ThermalObject.{u}} (morphism : Y ⟶ Z) :
    (X ◁ morphism).channel =
      FinStoch.tensor (FinStoch.identity X.system) morphism.channel :=
  rfl

@[simp]
theorem whiskerRight_channel {X Y Z : ThermalObject.{u}} (morphism : X ⟶ Y) :
    (morphism ▷ Z).channel =
      FinStoch.tensor morphism.channel (FinStoch.identity Z.system) :=
  rfl

@[simp]
theorem categoryId_channel (X : ThermalObject.{u}) :
    (𝟙 X : X ⟶ X).channel = FinStoch.identity X.system :=
  rfl

@[simp]
theorem categoryComp_channel {X Y Z : ThermalObject.{u}}
    (left : X ⟶ Y) (right : Y ⟶ Z) :
    (left ≫ right).channel = FinStoch.comp left.channel right.channel :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Gibbs-preserving processes form a monoidal category. -/
instance monoidalCategory : MonoidalCategory ThermalObject.{u} :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := tensor_id)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := by
      intro X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂
      exact (tensor_comp f₁ g₁ f₂ g₂).symm)
    (associator_naturality := by
      intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
      apply ext
      simpa only [categoryComp_channel, tensorHom_channel,
        associator_hom_channel, tensorObj_system,
        FinStoch.categoryComp_eq, FinStoch.tensorHom_eq,
        FinStoch.associator_hom_eq, FinStoch.tensorObj_eq]
        using FinStoch.monoidalCategory.associator_naturality
        f₁.channel f₂.channel f₃.channel)
    (leftUnitor_naturality := by
      intro X Y morphism
      apply ext
      simpa only [categoryComp_channel, whiskerLeft_channel,
        tensorHom_channel, categoryId_channel, leftUnitor_hom_channel,
        tensorObj_system, tensorUnit_system,
        FinStoch.categoryComp_eq, FinStoch.categoryId_eq,
        FinStoch.whiskerLeft_eq, FinStoch.leftUnitor_hom_eq,
        FinStoch.tensorHom_eq, FinStoch.tensorObj_eq, FinStoch.tensorUnit_eq]
        using FinStoch.monoidalCategory.leftUnitor_naturality
        morphism.channel)
    (rightUnitor_naturality := by
      intro X Y morphism
      apply ext
      simpa only [categoryComp_channel, whiskerRight_channel,
        tensorHom_channel, categoryId_channel, rightUnitor_hom_channel,
        tensorObj_system, tensorUnit_system,
        FinStoch.categoryComp_eq, FinStoch.categoryId_eq,
        FinStoch.whiskerRight_eq, FinStoch.rightUnitor_hom_eq,
        FinStoch.tensorHom_eq, FinStoch.tensorObj_eq, FinStoch.tensorUnit_eq]
        using FinStoch.monoidalCategory.rightUnitor_naturality
        morphism.channel)
    (pentagon := by
      intro W X Y Z
      apply ext
      simpa only [categoryComp_channel, tensorHom_channel,
        associator_hom_channel, categoryId_channel,
        tensorObj_system, FinStoch.tensorHom_eq,
        FinStoch.associator_hom_eq, FinStoch.categoryId_eq,
        FinStoch.categoryComp_eq, FinStoch.whiskerLeft_eq,
        FinStoch.whiskerRight_eq, FinStoch.tensorObj_eq] using
        FinStoch.monoidalCategory.pentagon
        W.system X.system Y.system Z.system)
    (triangle := by
      intro X Y
      apply ext
      simpa only [categoryComp_channel, tensorHom_channel,
        associator_hom_channel, leftUnitor_hom_channel,
        rightUnitor_hom_channel, categoryId_channel,
        tensorObj_system, tensorUnit_system,
        FinStoch.tensorHom_eq, FinStoch.associator_hom_eq,
        FinStoch.leftUnitor_hom_eq, FinStoch.rightUnitor_hom_eq,
        FinStoch.categoryId_eq, FinStoch.categoryComp_eq,
        FinStoch.whiskerLeft_eq, FinStoch.whiskerRight_eq,
        FinStoch.tensorObj_eq, FinStoch.tensorUnit_eq] using
        FinStoch.monoidalCategory.triangle X.system Y.system)

set_option backward.isDefEq.respectTransparency false in
/-- Gibbs-preserving independent composition is symmetric. -/
instance symmetricCategory : SymmetricCategory ThermalObject.{u} where
  braiding X Y :=
    { hom := braidHom X Y
      inv := braidHom Y X
      hom_inv_id := by
        apply ext
        exact (FinStoch.symmetricCategory.braiding X.system Y.system).hom_inv_id
      inv_hom_id := by
        apply ext
        exact (FinStoch.symmetricCategory.braiding X.system Y.system).inv_hom_id }
  braiding_naturality_right X := by
    intro Y Z morphism
    apply ext
    simpa only [categoryComp_channel, whiskerLeft_channel,
      whiskerRight_channel, braidHom, tensorObj_system,
      FinStoch.categoryComp_eq, FinStoch.categoryId_eq,
      FinStoch.whiskerLeft_eq,
      FinStoch.whiskerRight_eq, FinStoch.braiding_hom_eq,
      FinStoch.tensorObj_eq] using
      FinStoch.symmetricCategory.braiding_naturality_right
      X.system morphism.channel
  braiding_naturality_left := by
    intro X Y morphism Z
    apply ext
    simpa only [categoryComp_channel, whiskerLeft_channel,
      whiskerRight_channel, braidHom, tensorObj_system,
      FinStoch.categoryComp_eq, FinStoch.categoryId_eq,
      FinStoch.whiskerLeft_eq,
      FinStoch.whiskerRight_eq, FinStoch.braiding_hom_eq,
      FinStoch.tensorObj_eq] using
      FinStoch.symmetricCategory.braiding_naturality_left
      morphism.channel Z.system
  hexagon_forward X Y Z := by
    apply ext
    simpa only [categoryComp_channel, whiskerLeft_channel,
      whiskerRight_channel, associator_hom_channel, braidHom,
      tensorObj_system, FinStoch.categoryComp_eq, FinStoch.categoryId_eq,
      FinStoch.whiskerLeft_eq, FinStoch.whiskerRight_eq,
      FinStoch.associator_hom_eq, FinStoch.braiding_hom_eq,
      FinStoch.tensorObj_eq] using
      FinStoch.symmetricCategory.hexagon_forward
      X.system Y.system Z.system
  hexagon_reverse X Y Z := by
    apply ext
    simpa only [categoryComp_channel, whiskerLeft_channel,
      whiskerRight_channel, associator_inv_channel, braidHom,
      tensorObj_system, FinStoch.categoryComp_eq, FinStoch.categoryId_eq,
      FinStoch.whiskerLeft_eq, FinStoch.whiskerRight_eq,
      FinStoch.associator_inv_eq, FinStoch.braiding_hom_eq,
      FinStoch.tensorObj_eq] using
      FinStoch.symmetricCategory.hexagon_reverse
      X.system Y.system Z.system
  symmetry X Y := by
    apply ext
    simpa only [categoryComp_channel, braidHom, categoryId_channel,
      tensorObj_system, FinStoch.categoryComp_eq,
      FinStoch.categoryId_eq, FinStoch.braiding_hom_eq,
      FinStoch.tensorObj_eq] using
      FinStoch.symmetricCategory.symmetry X.system Y.system

/-- The abstract thermal process slice uses zero scalar category cost; physical
work and free-energy observables remain separate proved quantities. -/
instance zeroCost : HasProcessCost ThermalObject.{u} Nat where
  cost _ := 0
  cost_id _ := rfl
  cost_comp _ _ := Nat.zero_le 0

instance zeroParallelCost : HasParallelProcessCost ThermalObject.{u} Nat where
  cost_tensor _ _ := Nat.zero_le 0

instance zeroStructuralCost : HasFreeStructuralCost ThermalObject.{u} Nat where
  cost_associator _ _ _ := rfl
  cost_associator_inv _ _ _ := rfl
  cost_leftUnitor _ := rfl
  cost_leftUnitor_inv _ := rfl
  cost_rightUnitor _ := rfl
  cost_rightUnitor_inv _ := rfl
  cost_braiding _ _ := rfl

end GibbsPreserving

end Ript.Models.Thermal
