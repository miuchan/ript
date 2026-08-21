import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Ript.Core.ParallelCost
import Ript.Core.StructuralCost
import Ript.Models.Quantum.Equivalence
import Ript.Models.Quantum.Tensor

/-!
# Symmetric monoidal finite Kraus channels

The tensor product is the product of finite bases and the canonical tensor of
the channels' complex-linear matrix maps.  Product reassociation, unit
removal, and swapping are implemented by the reversible one-operator Kraus
channels induced by the corresponding finite-basis equivalences.

Unlike the classical measurement--preparation image, this structure is placed
on the full category of finite trace-preserving Kraus channels.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Ript.Models.Quantum

open CategoryTheory
open MonoidalCategory
open Matrix
open Ript.Core
open scoped Kronecker

universe u

namespace KrausChannel

/-- Rebracketing equivalence of three product bases. -/
def associatorEquiv (X Y Z : Object.{u}) : ((X × Y) × Z) ≃ (X × (Y × Z)) where
  toFun input := (input.1.1, (input.1.2, input.2))
  invFun input := ((input.1, input.2.1), input.2.2)
  left_inv input := by rcases input with ⟨⟨x, y⟩, z⟩; rfl
  right_inv input := by rcases input with ⟨x, y, z⟩; rfl

/-- Left-unit equivalence of product bases. -/
def leftUnitorEquiv (X : Object.{u}) : (Object.unit × X) ≃ X where
  toFun input := input.2
  invFun input := (PUnit.unit, input)
  left_inv input := by rcases input with ⟨unitValue, x⟩; cases unitValue; rfl
  right_inv _ := rfl

/-- Right-unit equivalence of product bases. -/
def rightUnitorEquiv (X : Object.{u}) : (X × Object.unit) ≃ X where
  toFun input := input.1
  invFun input := (input, PUnit.unit)
  left_inv input := by rcases input with ⟨x, unitValue⟩; cases unitValue; rfl
  right_inv _ := rfl

/-- Swap equivalence of two product bases. -/
def braidEquiv (X Y : Object.{u}) : (X × Y) ≃ (Y × X) where
  toFun input := (input.2, input.1)
  invFun input := (input.2, input.1)
  left_inv input := by rcases input with ⟨x, y⟩; rfl
  right_inv input := by rcases input with ⟨y, x⟩; rfl

/-- Swapping two product bases twice is the identity equivalence. -/
@[simp]
theorem braidEquiv_trans (X Y : Object.{u}) :
    (braidEquiv X Y).trans (braidEquiv Y X) = Equiv.refl (X × Y) := by
  apply Equiv.ext
  intro input
  rcases input with ⟨x, y⟩
  rfl

/-- Tensoring reversible basis-change channels is the basis change induced by
the product equivalence. -/
@[simp]
theorem tensor_ofEquiv {V W X Y : Object.{u}} (first : V ≃ W)
    (second : X ≃ Y) :
    tensor (ofEquiv first) (ofEquiv second) =
      ofEquiv (first.prodCongr second) := by
  apply ext
  funext τ
  have maps_equal :
      (tensor (ofEquiv first) (ofEquiv second)).toLinearMap =
        (ofEquiv (first.prodCongr second)).toLinearMap := by
    apply linearMap_ext_kronecker
    intro ρ σ
    change (tensor (ofEquiv first) (ofEquiv second)).map (ρ ⊗ₖ σ) =
      (ofEquiv (X := Object.tensor V X) (Y := Object.tensor W Y)
        (first.prodCongr second)).map (ρ ⊗ₖ σ)
    rw [tensor_map_kronecker, ofEquiv_map, ofEquiv_map, ofEquiv_map]
    change
      Matrix.reindex first first ρ ⊗ₖ Matrix.reindex second second σ =
        Matrix.reindex (first.prodCongr second) (first.prodCongr second)
          (ρ ⊗ₖ σ)
    exact Matrix.kroneckerMap_reindex _ _ _ _ _ _ _
  exact congrArg (fun linear ↦ linear τ) maps_equal

/-- Reindexing a Kronecker product along the left unitor extracts the unique
unit-basis matrix entry as a scalar. -/
theorem reindex_leftUnitor_kronecker (X : Object.{u})
    (unitMatrix : Matrix Object.unit Object.unit ℂ)
    (matrix : Matrix X X ℂ) :
    Matrix.reindex (leftUnitorEquiv X) (leftUnitorEquiv X)
        (unitMatrix ⊗ₖ matrix) =
      unitMatrix PUnit.unit PUnit.unit • matrix := by
  ext x y
  rfl

/-- Reindexing a Kronecker product along the right unitor extracts the unique
unit-basis matrix entry as a scalar. -/
theorem reindex_rightUnitor_kronecker (X : Object.{u})
    (matrix : Matrix X X ℂ)
    (unitMatrix : Matrix Object.unit Object.unit ℂ) :
    Matrix.reindex (rightUnitorEquiv X) (rightUnitorEquiv X)
        (matrix ⊗ₖ unitMatrix) =
      unitMatrix PUnit.unit PUnit.unit • matrix := by
  ext x y
  change matrix x y * unitMatrix PUnit.unit PUnit.unit =
    unitMatrix PUnit.unit PUnit.unit * matrix x y
  rw [mul_comm]

/-- Reindexing along product swap exchanges Kronecker factors. -/
theorem reindex_braid_kronecker (X Y : Object.{u})
    (first : Matrix X X ℂ) (second : Matrix Y Y ℂ) :
    Matrix.reindex (braidEquiv X Y) (braidEquiv X Y)
        (first ⊗ₖ second) = second ⊗ₖ first := by
  ext ⟨y, x⟩ ⟨y', x'⟩
  change first x x' * second y y' = second y y' * first x x'
  rw [mul_comm]

/-- Reindexing along the chosen associator turns a left-associated triple
Kronecker product into the corresponding right-associated product. -/
theorem reindex_associator_kronecker (X Y Z : Object.{u})
    (first : Matrix X X ℂ) (second : Matrix Y Y ℂ)
    (third : Matrix Z Z ℂ) :
    Matrix.reindex (associatorEquiv X Y Z) (associatorEquiv X Y Z)
        ((first ⊗ₖ second) ⊗ₖ third) =
      first ⊗ₖ (second ⊗ₖ third) := by
  ext ⟨x, y, z⟩ ⟨x', y', z'⟩
  change (first x x' * second y y') * third z z' =
    first x x' * (second y y' * third z z')
  rw [mul_assoc]

/-- Rebracketing quantum channel. -/
def associatorHom (X Y Z : Object.{u}) :
    Object.tensor (Object.tensor X Y) Z ⟶
      Object.tensor X (Object.tensor Y Z) :=
  ofEquiv (associatorEquiv X Y Z)

/-- Inverse product-basis rebracketing channel. -/
def associatorInv (X Y Z : Object.{u}) :
    Object.tensor X (Object.tensor Y Z) ⟶
      Object.tensor (Object.tensor X Y) Z :=
  ofEquiv (associatorEquiv X Y Z).symm

/-- Remove the left product-basis unit. -/
def leftUnitorHom (X : Object.{u}) : Object.tensor Object.unit X ⟶ X :=
  ofEquiv (leftUnitorEquiv X)

/-- Insert the left product-basis unit. -/
def leftUnitorInv (X : Object.{u}) : X ⟶ Object.tensor Object.unit X :=
  ofEquiv (leftUnitorEquiv X).symm

/-- Remove the right product-basis unit. -/
def rightUnitorHom (X : Object.{u}) : Object.tensor X Object.unit ⟶ X :=
  ofEquiv (rightUnitorEquiv X)

/-- Insert the right product-basis unit. -/
def rightUnitorInv (X : Object.{u}) : X ⟶ Object.tensor X Object.unit :=
  ofEquiv (rightUnitorEquiv X).symm

/-- Swap two product-basis factors. -/
def braidHom (X Y : Object.{u}) : Object.tensor X Y ⟶ Object.tensor Y X :=
  ofEquiv (braidEquiv X Y)

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
        change comp (ofEquiv (associatorEquiv X Y Z))
          (ofEquiv (X := Object.tensor X (Object.tensor Y Z))
            (Y := Object.tensor (Object.tensor X Y) Z)
            (associatorEquiv X Y Z).symm) = identity _
        rw [ofEquiv_comp]
        exact ofEquiv_refl (Object.tensor (Object.tensor X Y) Z)
      inv_hom_id := by
        change comp
          (ofEquiv (X := Object.tensor X (Object.tensor Y Z))
            (Y := Object.tensor (Object.tensor X Y) Z)
            (associatorEquiv X Y Z).symm)
          (ofEquiv (X := Object.tensor (Object.tensor X Y) Z)
            (Y := Object.tensor X (Object.tensor Y Z))
            (associatorEquiv X Y Z)) = identity _
        rw [ofEquiv_comp]
        exact ofEquiv_refl (Object.tensor X (Object.tensor Y Z)) }
  leftUnitor X :=
    { hom := leftUnitorHom X
      inv := leftUnitorInv X
      hom_inv_id := by
        change comp (ofEquiv (leftUnitorEquiv X))
          (ofEquiv (X := X) (Y := Object.tensor Object.unit X)
            (leftUnitorEquiv X).symm) = identity _
        rw [ofEquiv_comp]
        exact ofEquiv_refl (Object.tensor Object.unit X)
      inv_hom_id := by
        change comp
          (ofEquiv (X := X) (Y := Object.tensor Object.unit X)
            (leftUnitorEquiv X).symm)
          (ofEquiv (X := Object.tensor Object.unit X) (Y := X)
            (leftUnitorEquiv X)) = identity _
        rw [ofEquiv_comp]
        simp }
  rightUnitor X :=
    { hom := rightUnitorHom X
      inv := rightUnitorInv X
      hom_inv_id := by
        change comp (ofEquiv (rightUnitorEquiv X))
          (ofEquiv (X := X) (Y := Object.tensor X Object.unit)
            (rightUnitorEquiv X).symm) = identity _
        rw [ofEquiv_comp]
        exact ofEquiv_refl (Object.tensor X Object.unit)
      inv_hom_id := by
        change comp
          (ofEquiv (X := X) (Y := Object.tensor X Object.unit)
            (rightUnitorEquiv X).symm)
          (ofEquiv (X := Object.tensor X Object.unit) (Y := X)
            (rightUnitorEquiv X)) = identity _
        rw [ofEquiv_comp]
        simp }

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
theorem leftUnitor_inv_eq (X : Object.{u}) :
    (λ_ X).inv = leftUnitorInv X := rfl

@[simp]
theorem rightUnitor_hom_eq (X : Object.{u}) :
    (ρ_ X).hom = rightUnitorHom X := rfl

@[simp]
theorem rightUnitor_inv_eq (X : Object.{u}) :
    (ρ_ X).inv = rightUnitorInv X := rfl

@[simp]
theorem tensorUnit_eq : (𝟙_ Object.{u}) = Object.unit := rfl

@[simp]
theorem tensorObj_eq (X Y : Object.{u}) : X ⊗ Y = Object.tensor X Y := rfl

@[simp]
theorem whiskerLeft_eq {X Y Z : Object.{u}} (morphism : Y ⟶ Z) :
    X ◁ morphism = tensor (𝟙 X) morphism := rfl

@[simp]
theorem whiskerRight_eq {X Y Z : Object.{u}} (morphism : X ⟶ Y) :
    morphism ▷ Z = tensor morphism (𝟙 Z) := rfl

theorem categoryId_eq (X : Object.{u}) : (𝟙 X : X ⟶ X) = identity X := rfl

theorem categoryComp_eq {X Y Z : Object.{u}} (first : X ⟶ Y)
    (second : Y ⟶ Z) : first ≫ second = comp first second := rfl

set_option backward.isDefEq.respectTransparency false in
/-- All finite trace-preserving Kraus channels form a monoidal category. -/
instance monoidalCategory : MonoidalCategory Object.{u} :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := tensor_identity)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := by
      intros
      exact (tensor_comp _ _ _ _).symm)
    (associator_naturality := by
      intro X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃
      change
        comp (tensor (tensor f₁ f₂) f₃)
            (associatorHom Y₁ Y₂ Y₃) =
          comp (associatorHom X₁ X₂ X₃)
            (tensor f₁ (tensor f₂ f₃))
      apply ext
      funext ω
      have maps_equal :
          (comp (tensor (tensor f₁ f₂) f₃)
              (associatorHom Y₁ Y₂ Y₃)).toLinearMap =
            (comp (associatorHom X₁ X₂ X₃)
              (tensor f₁ (tensor f₂ f₃))).toLinearMap := by
        apply linearMap_ext_kronecker₃_left
        intro ρ σ τ
        change
          (comp (tensor (tensor f₁ f₂) f₃)
            (associatorHom Y₁ Y₂ Y₃)).map
              ((ρ ⊗ₖ σ) ⊗ₖ τ) =
          (comp (associatorHom X₁ X₂ X₃)
            (tensor f₁ (tensor f₂ f₃))).map ((ρ ⊗ₖ σ) ⊗ₖ τ)
        rw [comp_map, tensor_map_kronecker, tensor_map_kronecker,
          associatorHom, ofEquiv_map, reindex_associator_kronecker,
          comp_map, associatorHom, ofEquiv_map,
          reindex_associator_kronecker, tensor_map_kronecker,
          tensor_map_kronecker]
      exact congrArg (fun linear ↦ linear ω) maps_equal)
    (leftUnitor_naturality := by
      intro X Y morphism
      change
        comp (tensor (identity Object.unit) morphism)
            (leftUnitorHom Y) =
          comp (leftUnitorHom X) morphism
      apply ext
      funext ω
      have maps_equal :
          (comp (tensor (identity Object.unit) morphism)
              (leftUnitorHom Y)).toLinearMap =
            (comp (leftUnitorHom X) morphism).toLinearMap := by
        apply linearMap_ext_kronecker
        intro unitMatrix matrix
        change
          (comp (tensor (identity Object.unit) morphism)
            (leftUnitorHom Y)).map (unitMatrix ⊗ₖ matrix) =
          (comp (leftUnitorHom X) morphism).map
            (unitMatrix ⊗ₖ matrix)
        rw [comp_map, tensor_map_kronecker, identity_map, leftUnitorHom,
          ofEquiv_map, comp_map, leftUnitorHom, ofEquiv_map]
        change
          Matrix.reindex (leftUnitorEquiv Y) (leftUnitorEquiv Y)
              (unitMatrix ⊗ₖ morphism.map matrix) =
            morphism.map (Matrix.reindex (leftUnitorEquiv X)
              (leftUnitorEquiv X) (unitMatrix ⊗ₖ matrix))
        rw [reindex_leftUnitor_kronecker,
          reindex_leftUnitor_kronecker, morphism.map_smul]
      exact congrArg (fun linear ↦ linear ω) maps_equal)
    (rightUnitor_naturality := by
      intro X Y morphism
      change
        comp (tensor morphism (identity Object.unit))
            (rightUnitorHom Y) =
          comp (rightUnitorHom X) morphism
      apply ext
      funext ω
      have maps_equal :
          (comp (tensor morphism (identity Object.unit))
              (rightUnitorHom Y)).toLinearMap =
            (comp (rightUnitorHom X) morphism).toLinearMap := by
        apply linearMap_ext_kronecker
        intro matrix unitMatrix
        change
          (comp (tensor morphism (identity Object.unit))
            (rightUnitorHom Y)).map (matrix ⊗ₖ unitMatrix) =
          (comp (rightUnitorHom X) morphism).map
            (matrix ⊗ₖ unitMatrix)
        rw [comp_map, tensor_map_kronecker, identity_map, rightUnitorHom,
          ofEquiv_map, comp_map, rightUnitorHom, ofEquiv_map]
        change
          Matrix.reindex (rightUnitorEquiv Y) (rightUnitorEquiv Y)
              (morphism.map matrix ⊗ₖ unitMatrix) =
            morphism.map (Matrix.reindex (rightUnitorEquiv X)
              (rightUnitorEquiv X) (matrix ⊗ₖ unitMatrix))
        rw [reindex_rightUnitor_kronecker,
          reindex_rightUnitor_kronecker, morphism.map_smul]
      exact congrArg (fun linear ↦ linear ω) maps_equal)
    (pentagon := by
      intro W X Y Z
      simp only [tensorHom_eq, associator_hom_eq]
      change
        comp (tensor (ofEquiv _) (identity Z))
            (comp (ofEquiv _) (tensor (identity W) (ofEquiv _))) =
          comp (ofEquiv _) (ofEquiv _)
      rw [← ofEquiv_refl Z, ← ofEquiv_refl W, tensor_ofEquiv,
        tensor_ofEquiv, ofEquiv_comp, ofEquiv_comp, ofEquiv_comp]
      rfl)
    (triangle := by
      intro X Y
      simp only [tensorHom_eq, associator_hom_eq, leftUnitor_hom_eq,
        rightUnitor_hom_eq]
      change
        comp (ofEquiv _) (tensor (identity X) (ofEquiv _)) =
          tensor (ofEquiv _) (identity Y)
      rw [← ofEquiv_refl X, ← ofEquiv_refl Y, tensor_ofEquiv,
        tensor_ofEquiv, ofEquiv_comp]
      rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The full finite Kraus category is symmetric via reversible product-basis
swapping. -/
instance symmetricCategory : SymmetricCategory Object.{u} where
  braiding X Y :=
    { hom := braidHom X Y
      inv := braidHom Y X
      hom_inv_id := by
        change comp (braidHom X Y) (braidHom Y X) = identity _
        unfold braidHom
        rw [ofEquiv_comp]
        rw [braidEquiv_trans]
        exact ofEquiv_refl (Object.tensor X Y)
      inv_hom_id := by
        change comp (braidHom Y X) (braidHom X Y) = identity _
        unfold braidHom
        rw [ofEquiv_comp]
        rw [braidEquiv_trans]
        exact ofEquiv_refl (Object.tensor Y X) }
  braiding_naturality_right X := by
    intro Y Z morphism
    change
      comp (tensor (identity X) morphism) (braidHom X Z) =
        comp (braidHom X Y) (tensor morphism (identity X))
    apply ext
    funext ω
    have maps_equal :
        (comp (tensor (identity X) morphism)
            (braidHom X Z)).toLinearMap =
          (comp (braidHom X Y)
            (tensor morphism (identity X))).toLinearMap := by
      apply linearMap_ext_kronecker
      intro first second
      change
        (comp (tensor (identity X) morphism)
          (braidHom X Z)).map (first ⊗ₖ second) =
        (comp (braidHom X Y)
          (tensor morphism (identity X))).map (first ⊗ₖ second)
      rw [comp_map, tensor_map_kronecker, identity_map, braidHom, ofEquiv_map,
        reindex_braid_kronecker, comp_map, braidHom, ofEquiv_map,
        reindex_braid_kronecker, tensor_map_kronecker, identity_map]
    exact congrArg (fun linear ↦ linear ω) maps_equal
  braiding_naturality_left := by
    intro X Y morphism Z
    change
      comp (tensor morphism (identity Z)) (braidHom Y Z) =
        comp (braidHom X Z) (tensor (identity Z) morphism)
    apply ext
    funext ω
    have maps_equal :
        (comp (tensor morphism (identity Z))
            (braidHom Y Z)).toLinearMap =
          (comp (braidHom X Z)
            (tensor (identity Z) morphism)).toLinearMap := by
      apply linearMap_ext_kronecker
      intro first second
      change
        (comp (tensor morphism (identity Z))
          (braidHom Y Z)).map (first ⊗ₖ second) =
        (comp (braidHom X Z)
          (tensor (identity Z) morphism)).map (first ⊗ₖ second)
      rw [comp_map, tensor_map_kronecker, identity_map, braidHom, ofEquiv_map,
        reindex_braid_kronecker, comp_map, braidHom, ofEquiv_map,
        reindex_braid_kronecker, tensor_map_kronecker, identity_map]
    exact congrArg (fun linear ↦ linear ω) maps_equal
  hexagon_forward X Y Z := by
    simp only [associator_hom_eq]
    change
      comp (ofEquiv _) (comp (ofEquiv _) (ofEquiv _)) =
        comp (tensor (ofEquiv _) (identity Z))
          (comp (ofEquiv _) (tensor (identity Y) (ofEquiv _)))
    rw [← ofEquiv_refl Z, ← ofEquiv_refl Y, tensor_ofEquiv,
      tensor_ofEquiv, ofEquiv_comp, ofEquiv_comp, ofEquiv_comp,
      ofEquiv_comp]
    rfl
  hexagon_reverse X Y Z := by
    simp only [associator_inv_eq]
    change
      comp (ofEquiv _) (comp (ofEquiv _) (ofEquiv _)) =
        comp (tensor (identity X) (ofEquiv _))
          (comp (ofEquiv _) (tensor (ofEquiv _) (identity Y)))
    rw [← ofEquiv_refl X, ← ofEquiv_refl Y, tensor_ofEquiv,
      tensor_ofEquiv, ofEquiv_comp, ofEquiv_comp, ofEquiv_comp,
      ofEquiv_comp]
    rfl
  symmetry X Y := by
    change comp (braidHom X Y) (braidHom Y X) = identity _
    unfold braidHom
    rw [ofEquiv_comp]
    rw [braidEquiv_trans]
    exact ofEquiv_refl (Object.tensor X Y)

@[simp]
theorem braiding_hom_eq (X Y : Object.{u}) :
    (β_ X Y).hom = braidHom X Y := rfl

/-- The baseline resource account assigns zero abstract cost to every quantum
channel; nontrivial physical costs can be supplied by heterogeneous resource
maps without changing the process category. -/
instance zeroCost : HasProcessCost Object.{u} Nat where
  cost _ := 0
  cost_id _ := rfl
  cost_comp _ _ := Nat.zero_le 0

/-- Tensoring zero-cost quantum channels remains zero-cost. -/
instance zeroParallelCost : HasParallelProcessCost Object.{u} Nat where
  cost_tensor _ _ := Nat.zero_le 0

/-- Reversible basis coherence maps have zero baseline resource cost. -/
instance zeroStructuralCost : HasFreeStructuralCost Object.{u} Nat where
  cost_associator _ _ _ := rfl
  cost_associator_inv _ _ _ := rfl
  cost_leftUnitor _ := rfl
  cost_leftUnitor_inv _ := rfl
  cost_rightUnitor _ := rfl
  cost_rightUnitor_inv _ := rfl
  cost_braiding _ _ := rfl

end KrausChannel

end Ript.Models.Quantum
