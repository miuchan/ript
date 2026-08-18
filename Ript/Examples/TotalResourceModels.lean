import Ript.Higher.TotalModelCoherence
import Ript.Models.Computation.Resource
import Ript.Semantics.MonoidalTermModel

/-!
# A model morphism from vector resources to scalar resources

This example realizes a genuinely heterogeneous one-cell in the total model
bicategory.  A free symmetric monoidal computation model first records four
resource coordinates.  Its target model measures only formal evaluation
steps, obtained by reindexing along the ordered additive projection
`ComputationResource.stepsHom`.  The identity process functor, paired with
that projection, is then a total-model one-cell and transports checked vector
budgets to checked scalar budgets.
-/

set_option autoImplicit false

namespace Ript.Examples.TotalResourceModels

open CategoryTheory
open Ript.Core
open Ript.Higher
open Ript.Models.Computation
open Ript.Resource
open Ript.Semantics
open Ript.Syntax

/-- The single wire carried by the example model. -/
inductive Wire where
  /-- A Boolean information interface. -/
  | bit
  deriving DecidableEq, Repr

/-- A primitive reversible Boolean gate. -/
inductive Generator : FreeMonoidalCategory Wire → FreeMonoidalCategory Wire → Type where
  /-- Negation declares three steps and one circuit gate. -/
  | not : Generator (.of .bit) (.of .bit)

/-- A vector-valued symmetric monoidal signature. -/
def signature : MonoidalSignature ComputationResource where
  Wire := Wire
  Gen := Generator
  cost
    | .not => ComputationResource.of 3 0 0 1

/-- The source process model retains all four computation-resource
coordinates. -/
def vectorProcessModel : ProcessModel ComputationResource where
  Carrier := MonoidalTermModel signature
  category := inferInstance
  monoidal := inferInstance
  symmetric := inferInstance
  costed := inferInstance
  parallelCost := inferInstance
  structuralCost := inferInstance

/-- The target process model measures the same processes only by their formal
step count. -/
def stepProcessModel : ProcessModel Nat :=
  vectorProcessModel.reindex ComputationResource.stepsHom

/-- The vector-valued model as an object of the total bicategory. -/
def vectorModel : ResourceModel.{0, 0, 0} where
  Resource := ComputationResource
  addCommMonoid := inferInstance
  partialOrder := inferInstance
  model := vectorProcessModel

/-- The scalar step-count model as an object of the total bicategory. -/
def stepModel : ResourceModel.{0, 0, 0} where
  Resource := Nat
  addCommMonoid := inferInstance
  partialOrder := inferInstance
  model := stepProcessModel

-- Concrete local instances keep the two cost interpretations distinguishable
-- even though both bundled models have the same underlying process carrier.
/-- The original vector-valued cost interpretation on the shared carrier. -/
local instance vectorCost : HasProcessCost vectorModel ComputationResource :=
  vectorProcessModel.costed

/-- The reindexed step-valued cost interpretation on the shared carrier. -/
local instance stepCost : HasProcessCost stepModel Nat :=
  stepProcessModel.costed

/-- Forget auxiliary resource coordinates while retaining the exact step
cost.  This is a one-cell between two objects with different resource types. -/
def projectToSteps : vectorModel ⟶ stepModel where
  resourceMap := ComputationResource.stepsHom
  modelMap := ResourceChangeModelHom.toReindex
    ComputationResource.stepsHom vectorProcessModel

@[simp]
theorem projectToSteps_resourceMap :
    projectToSteps.resourceMap = ComputationResource.stepsHom :=
  rfl

/-- The heterogeneous model morphism is cost-exact for this reindexed target,
not merely cost-nonincreasing. -/
theorem projectToSteps_cost_exact {X Y : vectorProcessModel} (f : X ⟶ Y) :
    processCost (C := stepModel) (R := Nat)
        (projectToSteps.toFunctor.map f) =
      ComputationResource.stepsHom
        (processCost (C := vectorModel) (R := ComputationResource) f) :=
  rfl

/-- Raw syntax for the declared three-step negation. -/
def notExpr : MonoidalExpr signature (.of .bit) (.of .bit) :=
  .gen .not

/-- Its resource-vector cost remains executable before quotienting into the
proof model. -/
def notVectorCost : ComputationResource :=
  notExpr.syntaxCost

/-- Applying the resource map is an executable scalar observation. -/
def notStepCost : Nat :=
  projectToSteps.resourceMap notVectorCost

example : notStepCost = 3 :=
  rfl

/-- The quoted process with its exact vector-valued budget certificate. -/
def vectorBudgetedNot :
    BudgetedHom (R := ComputationResource)
      (ComputationResource.of 3 0 0 1)
      (⟨.of .bit⟩ : MonoidalTermModel signature)
      (⟨.of .bit⟩ : MonoidalTermModel signature) :=
  ⟨MonoidalTermModel.quote signature notExpr, le_rfl⟩

/-- The total-model one-cell transports the same process to an exact scalar
step budget. -/
def stepBudgetedNot :
    BudgetedHom (R := Nat) 3
      (projectToSteps.toFunctor.obj
        (⟨.of .bit⟩ : MonoidalTermModel signature))
      (projectToSteps.toFunctor.obj
        (⟨.of .bit⟩ : MonoidalTermModel signature)) :=
  projectToSteps.modelMap.mapBudgetedHom vectorBudgetedNot

@[simp]
theorem stepBudgetedNot_cost :
    processCost (C := stepModel) (R := Nat) stepBudgetedNot.hom = 3 :=
  rfl

#eval notStepCost

end Ript.Examples.TotalResourceModels
