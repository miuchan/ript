import Ript.Examples.ParallelBitRealizations
import Ript.Higher.TotalModelCoherence

/-!
# Six parallel realizations as one-cells of the total model bicategory

The common free symmetric monoidal bit theory is packaged as a resource model.
Each of its six concrete interpretations becomes a heterogeneous strong
braided one-cell to a bundled target model.  Thus the realizations live inside
Ript's higher category of models rather than only as unrelated evaluation
functions.
-/

set_option autoImplicit false

namespace Ript.Examples.ParallelBitHigherModels

open CategoryTheory
open MonoidalCategory
open Ript.Core
open Ript.Higher
open Ript.Models.Computation
open Ript.Semantics
open Ript.Syntax

/-! ## Bundled process models -/

/-- Object-universe lift of the free syntax.  Objects live in `Type 1`, while
morphisms remain the original `Type 0` quotient expressions. -/
structure LiftedSyntax : Type 1 where
  /-- Underlying free term-model object. -/
  down : MonoidalTermModel Ript.Examples.ParallelBitRealizations.signature

namespace LiftedSyntax

/-- Original unlifted free term-model carrier. -/
abbrev Underlying :=
  MonoidalTermModel Ript.Examples.ParallelBitRealizations.signature

instance category : Category.{0} LiftedSyntax where
  Hom X Y := X.down ⟶ Y.down
  id X := 𝟙 X.down
  comp left right := left ≫ right
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

instance monoidalCategoryStruct : MonoidalCategoryStruct LiftedSyntax where
  tensorObj X Y := ⟨X.down ⊗ Y.down⟩
  tensorUnit := ⟨𝟙_ (MonoidalTermModel
    Ript.Examples.ParallelBitRealizations.signature)⟩
  whiskerLeft X Y Z morphism :=
    (𝟙 X.down) ⊗ₘ (show Y.down ⟶ Z.down from morphism)
  whiskerRight {X Y} morphism Z :=
    (show X.down ⟶ Y.down from morphism) ⊗ₘ 𝟙 Z.down
  tensorHom {X₁ Y₁ X₂ Y₂} left right :=
    (show X₁.down ⟶ Y₁.down from left) ⊗ₘ
      (show X₂.down ⟶ Y₂.down from right)
  associator X Y Z :=
    { hom := (α_ X.down Y.down Z.down).hom
      inv := (α_ X.down Y.down Z.down).inv
      hom_inv_id := (α_ X.down Y.down Z.down).hom_inv_id
      inv_hom_id := (α_ X.down Y.down Z.down).inv_hom_id }
  leftUnitor X :=
    { hom := (λ_ X.down).hom
      inv := (λ_ X.down).inv
      hom_inv_id := (λ_ X.down).hom_inv_id
      inv_hom_id := (λ_ X.down).inv_hom_id }
  rightUnitor X :=
    { hom := (ρ_ X.down).hom
      inv := (ρ_ X.down).inv
      hom_inv_id := (ρ_ X.down).hom_inv_id
      inv_hom_id := (ρ_ X.down).inv_hom_id }

instance monoidalCategory : MonoidalCategory LiftedSyntax :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := by
      intro X Y
      change (𝟙 X.down ⊗ₘ 𝟙 Y.down) = 𝟙 (X.down ⊗ Y.down)
      exact Quotient.sound
        (MonoidalDerives.tensor_id X.down.object Y.down.object))
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := by
      rintro X₁ Y₁ Z₁ X₂ Y₂ Z₂ ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩
      exact Quotient.sound (MonoidalDerives.interchange f₁ f₂ g₁ g₂))
    (associator_naturality := by
      rintro X₁ X₂ X₃ Y₁ Y₂ Y₃ ⟨f₁⟩ ⟨f₂⟩ ⟨f₃⟩
      exact Quotient.sound
        (MonoidalDerives.associator_naturality f₁ f₂ f₃))
    (leftUnitor_naturality := by
      rintro X Y ⟨f⟩
      exact Quotient.sound (MonoidalDerives.leftUnitor_naturality f))
    (rightUnitor_naturality := by
      rintro X Y ⟨f⟩
      exact Quotient.sound (MonoidalDerives.rightUnitor_naturality f))
    (pentagon := by
      intro W X Y Z
      exact Quotient.sound (MonoidalDerives.pentagon
        W.down.object X.down.object Y.down.object Z.down.object))
    (triangle := by
      intro X Y
      exact Quotient.sound
        (MonoidalDerives.triangle X.down.object Y.down.object))

instance symmetricCategory : SymmetricCategory LiftedSyntax where
  braiding X Y :=
    { hom := (β_ X.down Y.down).hom
      inv := (β_ X.down Y.down).inv
      hom_inv_id := (β_ X.down Y.down).hom_inv_id
      inv_hom_id := (β_ X.down Y.down).inv_hom_id }
  braiding_naturality_right X := by
    rintro Y Z ⟨f⟩
    exact Quotient.sound
      (MonoidalDerives.braid_naturality_right X.down.object f)
  braiding_naturality_left := by
    rintro X Y ⟨f⟩ Z
    exact Quotient.sound
      (MonoidalDerives.braid_naturality_left f Z.down.object)
  hexagon_forward X Y Z := by
    exact Quotient.sound (MonoidalDerives.hexagon_forward
      X.down.object Y.down.object Z.down.object)
  hexagon_reverse X Y Z := by
    exact Quotient.sound (MonoidalDerives.hexagon_reverse
      X.down.object Y.down.object Z.down.object)
  symmetry X Y := by
    exact Quotient.sound
      (MonoidalDerives.braid_symmetry X.down.object Y.down.object)

instance processCost : HasProcessCost LiftedSyntax Nat where
  cost morphism := Ript.Core.processCost
    (C := MonoidalTermModel Ript.Examples.ParallelBitRealizations.signature)
    (R := Nat) morphism
  cost_id X := Ript.Core.processCost_id
    (C := MonoidalTermModel Ript.Examples.ParallelBitRealizations.signature)
    (R := Nat) X.down
  cost_comp left right := Ript.Core.processCost_comp
    (C := MonoidalTermModel Ript.Examples.ParallelBitRealizations.signature)
    (R := Nat) left right

instance parallelCost : HasParallelProcessCost LiftedSyntax Nat where
  cost_tensor left right := by
    rcases left with ⟨left⟩
    rcases right with ⟨right⟩
    exact le_rfl

instance structuralCost : HasFreeStructuralCost LiftedSyntax Nat where
  cost_associator _ _ _ := rfl
  cost_associator_inv _ _ _ := rfl
  cost_leftUnitor _ := rfl
  cost_leftUnitor_inv _ := rfl
  cost_rightUnitor _ := rfl
  cost_rightUnitor_inv _ := rfl
  cost_braiding _ _ := rfl

/-- Forget the object-universe wrapper. -/
def downFunctor :
    LiftedSyntax ⥤
      MonoidalTermModel Ript.Examples.ParallelBitRealizations.signature where
  obj X := X.down
  map morphism := morphism
  map_id _ := rfl
  map_comp _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
instance downFunctorMonoidal : downFunctor.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _
      μIso_hom_natural_left := by
        intro A B morphism X
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
        change (show A.down ⟶ B.down from morphism) ▷ X.down =
          (show A.down ⟶ B.down from morphism) ⊗ₘ 𝟙 X.down
        exact (MonoidalCategory.tensorHom_id
          (C := Underlying) morphism X.down).symm
      μIso_hom_natural_right := by
        intro X Y X' morphism
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
        change X'.down ◁ (show X.down ⟶ Y.down from morphism) =
          𝟙 X'.down ⊗ₘ (show X.down ⟶ Y.down from morphism)
        exact (MonoidalCategory.id_tensorHom
          (C := Underlying) X'.down morphism).symm
      associativity := by
        intros
        simp only [Iso.refl_hom, MonoidalCategory.id_whiskerRight,
          MonoidalCategory.whiskerLeft_id, Category.id_comp,
          Category.comp_id]
        rfl
      left_unitality := by
        intros
        simp only [Iso.refl_hom, MonoidalCategory.id_whiskerRight,
          Category.id_comp]
        rfl
      right_unitality := by
        intros
        simp only [Iso.refl_hom, MonoidalCategory.whiskerLeft_id,
          Category.id_comp]
        rfl }

instance downFunctorBraided : downFunctor.Braided where
  braided X Y := by
    change 𝟙 _ ≫ (β_ X.down Y.down).hom = (β_ X.down Y.down).hom ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]

/-- Quote a raw expression into the lifted syntax category. -/
def quote {X Y : Ript.Examples.ParallelBitRealizations.signature.Obj}
    (expression : MonoidalExpr
      Ript.Examples.ParallelBitRealizations.signature X Y) :
    (⟨⟨X⟩⟩ : LiftedSyntax) ⟶ ⟨⟨Y⟩⟩ :=
  MonoidalTermModel.quote _ expression

end LiftedSyntax

/-- Free common syntax as a fixed-resource process model. -/
def syntaxProcessModel : ProcessModel.{1, 0, 0} Nat where
  Carrier := LiftedSyntax
  category := inferInstance
  monoidal := inferInstance
  symmetric := inferInstance
  costed := inferInstance
  parallelCost := inferInstance
  structuralCost := inferInstance

/-- Exact finite stochastic probability model. -/
def probabilityProcessModel : ProcessModel.{1, 0, 0} Nat where
  Carrier := Ript.Models.FiniteStochastic.Object
  category := inferInstance
  monoidal := inferInstance
  symmetric := inferInstance
  costed := inferInstance
  parallelCost := inferInstance
  structuralCost := inferInstance

/-- Finite causal mechanisms use the same exact stochastic process carrier,
with their distinct interpretation supplied by the one-cell below. -/
def causalProcessModel : ProcessModel.{1, 0, 0} Nat :=
  probabilityProcessModel

/-- Semantic experiments use the exact stochastic process carrier with a
task-specific generator interpretation. -/
def semanticProcessModel : ProcessModel.{1, 0, 0} Nat :=
  probabilityProcessModel

/-- Full finite trace-preserving Kraus quantum model. -/
def quantumProcessModel : ProcessModel.{1, 0, 0} Nat where
  Carrier := Ript.Models.Quantum.Object
  category := inferInstance
  monoidal := inferInstance
  symmetric := inferInstance
  costed := inferInstance
  parallelCost := inferInstance
  structuralCost := inferInstance

/-- Four-coordinate total-computation process model. -/
def computationProcessModel : ProcessModel.{1, 0, 0} ComputationResource where
  Carrier := Ript.Models.Computation.Total.Object
  category := inferInstance
  monoidal := inferInstance
  symmetric := inferInstance
  costed := inferInstance
  parallelCost := inferInstance
  structuralCost := inferInstance

/-- Gibbs-preserving thermal process model. -/
def thermalProcessModel : ProcessModel.{1, 0, 0} Nat where
  Carrier := Ript.Models.Thermal.ThermalObject
  category := inferInstance
  monoidal := inferInstance
  symmetric := inferInstance
  costed := inferInstance
  parallelCost := inferInstance
  structuralCost := inferInstance

/-! ## Heterogeneous strong braided model morphisms -/

/-- Ordinary functor underlying the probability realization. -/
def probabilityFunctor :
    LiftedSyntax ⥤ Ript.Models.FiniteStochastic.Object :=
  LiftedSyntax.downFunctor ⋙
    ResourceChangingMonoidalFree.liftFunctor
      Ript.Examples.ParallelBitRealizations.probabilityInterpretation

/-- Ordinary functor underlying the full-Kraus quantum realization. -/
def quantumFunctor :
    LiftedSyntax ⥤ Ript.Models.Quantum.Object :=
  LiftedSyntax.downFunctor ⋙
    ResourceChangingMonoidalFree.liftFunctor
      Ript.Examples.ParallelBitRealizations.quantumInterpretation

/-- Ordinary functor underlying the causal realization. -/
def causalFunctor :
    LiftedSyntax ⥤ Ript.Models.FiniteStochastic.Object :=
  LiftedSyntax.downFunctor ⋙
    ResourceChangingMonoidalFree.liftFunctor
      Ript.Examples.ParallelBitRealizations.causalInterpretation

/-- Ordinary functor underlying the computation realization. -/
def computationFunctor :
    LiftedSyntax ⥤ Ript.Models.Computation.Total.Object :=
  LiftedSyntax.downFunctor ⋙
    ResourceChangingMonoidalFree.liftFunctor
      Ript.Examples.ParallelBitRealizations.computationInterpretation

/-- Ordinary functor underlying the semantic-information realization. -/
def semanticFunctor :
    LiftedSyntax ⥤ Ript.Models.FiniteStochastic.Object :=
  LiftedSyntax.downFunctor ⋙
    ResourceChangingMonoidalFree.liftFunctor
      Ript.Examples.ParallelBitRealizations.semanticInterpretation

/-- Ordinary functor underlying the thermal realization. -/
def thermalFunctor : LiftedSyntax ⥤ Ript.Models.Thermal.ThermalObject :=
  LiftedSyntax.downFunctor ⋙
    ResourceChangingMonoidalFree.liftFunctor
      Ript.Examples.ParallelBitRealizations.thermalInterpretation

instance probabilityFunctorMonoidal : probabilityFunctor.Monoidal := by
  dsimp [probabilityFunctor]
  infer_instance

instance probabilityFunctorBraided : probabilityFunctor.Braided := by
  dsimp [probabilityFunctor]
  infer_instance

instance quantumFunctorMonoidal : quantumFunctor.Monoidal := by
  dsimp [quantumFunctor]
  infer_instance

instance quantumFunctorBraided : quantumFunctor.Braided := by
  dsimp [quantumFunctor]
  infer_instance

instance causalFunctorMonoidal : causalFunctor.Monoidal := by
  dsimp [causalFunctor]
  infer_instance

instance causalFunctorBraided : causalFunctor.Braided := by
  dsimp [causalFunctor]
  infer_instance

instance computationFunctorMonoidal : computationFunctor.Monoidal := by
  dsimp [computationFunctor]
  infer_instance

instance computationFunctorBraided : computationFunctor.Braided := by
  dsimp [computationFunctor]
  infer_instance

instance semanticFunctorMonoidal : semanticFunctor.Monoidal := by
  dsimp [semanticFunctor]
  infer_instance

instance semanticFunctorBraided : semanticFunctor.Braided := by
  dsimp [semanticFunctor]
  infer_instance

instance thermalFunctorMonoidal : thermalFunctor.Monoidal := by
  dsimp [thermalFunctor]
  infer_instance

instance thermalFunctorBraided : thermalFunctor.Braided := by
  dsimp [thermalFunctor]
  infer_instance

/-- Upgrade a heterogeneous monoidal free lift to a higher model morphism. -/
def probabilityModelMap :
    ResourceChangeModelHom (OrderAddMonoidHom.id Nat)
      syntaxProcessModel probabilityProcessModel := by
  dsimp [syntaxProcessModel, probabilityProcessModel]
  exact
    { toLaxBraided := LaxBraidedFunctor.of probabilityFunctor
      unit_isIso := by
        change IsIso (Functor.LaxMonoidal.ε probabilityFunctor)
        infer_instance
      tensor_isIso := by
        intros
        change IsIso (Functor.LaxMonoidal.μ probabilityFunctor _ _)
        infer_instance
      map_cost_le :=
        (ResourceChangingMonoidalFree.lift Ript.Examples.ParallelBitRealizations.probabilityInterpretation).map_cost_le }

/-- Full-Kraus quantum higher model morphism. -/
def quantumModelMap :
    ResourceChangeModelHom (OrderAddMonoidHom.id Nat)
      syntaxProcessModel quantumProcessModel := by
  dsimp [syntaxProcessModel, quantumProcessModel]
  exact
    { toLaxBraided := LaxBraidedFunctor.of quantumFunctor
      unit_isIso := by
        change IsIso (Functor.LaxMonoidal.ε quantumFunctor)
        infer_instance
      tensor_isIso := by
        intros
        change IsIso (Functor.LaxMonoidal.μ quantumFunctor _ _)
        infer_instance
      map_cost_le :=
        (ResourceChangingMonoidalFree.lift Ript.Examples.ParallelBitRealizations.quantumInterpretation).map_cost_le }

/-- Causal higher model morphism. -/
def causalModelMap :
    ResourceChangeModelHom (OrderAddMonoidHom.id Nat)
      syntaxProcessModel causalProcessModel := by
  dsimp [syntaxProcessModel, causalProcessModel, probabilityProcessModel]
  exact
    { toLaxBraided := LaxBraidedFunctor.of causalFunctor
      unit_isIso := by
        change IsIso (Functor.LaxMonoidal.ε causalFunctor)
        infer_instance
      tensor_isIso := by
        intros
        change IsIso (Functor.LaxMonoidal.μ causalFunctor _ _)
        infer_instance
      map_cost_le :=
        (ResourceChangingMonoidalFree.lift Ript.Examples.ParallelBitRealizations.causalInterpretation).map_cost_le }

/-- Computation higher model morphism over the scalar-to-vector resource map. -/
def computationModelMap :
    ResourceChangeModelHom
      Ript.Examples.CommonBitRealizations.computationResourceMap
      syntaxProcessModel computationProcessModel := by
  dsimp [syntaxProcessModel, computationProcessModel]
  exact
    { toLaxBraided := LaxBraidedFunctor.of computationFunctor
      unit_isIso := by
        change IsIso (Functor.LaxMonoidal.ε computationFunctor)
        infer_instance
      tensor_isIso := by
        intros
        change IsIso (Functor.LaxMonoidal.μ computationFunctor _ _)
        infer_instance
      map_cost_le :=
        (ResourceChangingMonoidalFree.lift Ript.Examples.ParallelBitRealizations.computationInterpretation).map_cost_le }

/-- Semantic-information higher model morphism. -/
def semanticModelMap :
    ResourceChangeModelHom (OrderAddMonoidHom.id Nat)
      syntaxProcessModel semanticProcessModel := by
  dsimp [syntaxProcessModel, semanticProcessModel, probabilityProcessModel]
  exact
    { toLaxBraided := LaxBraidedFunctor.of semanticFunctor
      unit_isIso := by
        change IsIso (Functor.LaxMonoidal.ε semanticFunctor)
        infer_instance
      tensor_isIso := by
        intros
        change IsIso (Functor.LaxMonoidal.μ semanticFunctor _ _)
        infer_instance
      map_cost_le :=
        (ResourceChangingMonoidalFree.lift Ript.Examples.ParallelBitRealizations.semanticInterpretation).map_cost_le }

/-- Thermal higher model morphism. -/
def thermalModelMap :
    ResourceChangeModelHom (OrderAddMonoidHom.id Nat)
      syntaxProcessModel thermalProcessModel := by
  dsimp [syntaxProcessModel, thermalProcessModel]
  exact
    { toLaxBraided := LaxBraidedFunctor.of thermalFunctor
      unit_isIso := by
        change IsIso (Functor.LaxMonoidal.ε thermalFunctor)
        infer_instance
      tensor_isIso := by
        intros
        change IsIso (Functor.LaxMonoidal.μ thermalFunctor _ _)
        infer_instance
      map_cost_le :=
        (ResourceChangingMonoidalFree.lift Ript.Examples.ParallelBitRealizations.thermalInterpretation).map_cost_le }

/-! ## Objects and one-cells of the total bicategory -/

/-- Common free syntax as an object of the total resource-model bicategory. -/
def syntaxModel : ResourceModel.{1, 0, 0} where
  Resource := Nat
  addCommMonoid := inferInstance
  partialOrder := inferInstance
  model := syntaxProcessModel

/-- Bundled probability resource model. -/
def probabilityModel : ResourceModel.{1, 0, 0} where
  Resource := Nat
  addCommMonoid := inferInstance
  partialOrder := inferInstance
  model := probabilityProcessModel

/-- Bundled full-Kraus quantum resource model. -/
def quantumModel : ResourceModel.{1, 0, 0} where
  Resource := Nat
  addCommMonoid := inferInstance
  partialOrder := inferInstance
  model := quantumProcessModel

/-- Bundled finite causal resource model. -/
def causalModel : ResourceModel.{1, 0, 0} where
  Resource := Nat
  addCommMonoid := inferInstance
  partialOrder := inferInstance
  model := causalProcessModel

/-- Bundled four-coordinate computation resource model. -/
def computationModel : ResourceModel.{1, 0, 0} where
  Resource := ComputationResource
  addCommMonoid := inferInstance
  partialOrder := inferInstance
  model := computationProcessModel

/-- Bundled semantic-experiment resource model. -/
def semanticModel : ResourceModel.{1, 0, 0} where
  Resource := Nat
  addCommMonoid := inferInstance
  partialOrder := inferInstance
  model := semanticProcessModel

/-- Bundled Gibbs-preserving thermal resource model. -/
def thermalModel : ResourceModel.{1, 0, 0} where
  Resource := Nat
  addCommMonoid := inferInstance
  partialOrder := inferInstance
  model := thermalProcessModel

/-- Probability realization as a total-bicategory one-cell. -/
def probabilityOneCell : syntaxModel ⟶ probabilityModel where
  resourceMap := OrderAddMonoidHom.id Nat
  modelMap := probabilityModelMap

/-- Full-Kraus quantum realization as a total-bicategory one-cell. -/
def quantumOneCell : syntaxModel ⟶ quantumModel where
  resourceMap := OrderAddMonoidHom.id Nat
  modelMap := quantumModelMap

/-- Causal realization as a total-bicategory one-cell. -/
def causalOneCell : syntaxModel ⟶ causalModel where
  resourceMap := OrderAddMonoidHom.id Nat
  modelMap := causalModelMap

/-- Computation realization as a heterogeneous total-bicategory one-cell. -/
def computationOneCell : syntaxModel ⟶ computationModel where
  resourceMap := Ript.Examples.CommonBitRealizations.computationResourceMap
  modelMap := computationModelMap

/-- Semantic-information realization as a total-bicategory one-cell. -/
def semanticOneCell : syntaxModel ⟶ semanticModel where
  resourceMap := OrderAddMonoidHom.id Nat
  modelMap := semanticModelMap

/-- Thermal realization as a total-bicategory one-cell. -/
def thermalOneCell : syntaxModel ⟶ thermalModel where
  resourceMap := OrderAddMonoidHom.id Nat
  modelMap := thermalModelMap

/-! ## Higher-level preservation theorems -/

/-- The six one-cells retain their advertised resource translations. -/
theorem sixModelResourceMaps :
    probabilityOneCell.resourceMap = OrderAddMonoidHom.id Nat ∧
    quantumOneCell.resourceMap = OrderAddMonoidHom.id Nat ∧
    causalOneCell.resourceMap = OrderAddMonoidHom.id Nat ∧
    computationOneCell.resourceMap =
      Ript.Examples.CommonBitRealizations.computationResourceMap ∧
    semanticOneCell.resourceMap = OrderAddMonoidHom.id Nat ∧
    thermalOneCell.resourceMap = OrderAddMonoidHom.id Nat :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Mapping the shared primitive through each total-bicategory one-cell agrees
with the corresponding concrete generator interpretation. -/
theorem sixModelOneCellsOnGenerator :
    probabilityOneCell.toFunctor.map
        (LiftedSyntax.quote (.gen .flip)) =
      Ript.Examples.ParallelBitRealizations.probabilityInterpretation.mapGen .flip ∧
    quantumOneCell.toFunctor.map
        (LiftedSyntax.quote (.gen .flip)) =
      Ript.Examples.ParallelBitRealizations.quantumInterpretation.mapGen .flip ∧
    causalOneCell.toFunctor.map
        (LiftedSyntax.quote (.gen .flip)) =
      Ript.Examples.ParallelBitRealizations.causalInterpretation.mapGen .flip ∧
    computationOneCell.toFunctor.map
        (LiftedSyntax.quote (.gen .flip)) =
      Ript.Examples.ParallelBitRealizations.computationInterpretation.mapGen .flip ∧
    semanticOneCell.toFunctor.map
        (LiftedSyntax.quote (.gen .flip)) =
      Ript.Examples.ParallelBitRealizations.semanticInterpretation.mapGen .flip ∧
    thermalOneCell.toFunctor.map
        (LiftedSyntax.quote (.gen .flip)) =
      Ript.Examples.ParallelBitRealizations.thermalInterpretation.mapGen .flip :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The higher computation one-cell transports the exact two-unit source
budget into the native four-coordinate computation resource. -/
theorem computationOneCell_parallel_cost :
    computationProcessModel.costed.cost
        (computationOneCell.toFunctor.map
          (LiftedSyntax.quote
            Ript.Examples.ParallelBitRealizations.parallelFlipExpr)) =
      Ript.Examples.CommonBitRealizations.computationResourceMap 2 :=
  Ript.Examples.ParallelBitRealizations.computation_parallel_cost

end Ript.Examples.ParallelBitHigherModels
