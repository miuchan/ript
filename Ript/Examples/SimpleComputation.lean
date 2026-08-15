import Ript.Models.Computation.Partial
import Ript.Semantics.Eval

/-!
# Executable total and partial computation example

One typed program performs a formal query, flips a bit, and checks that the
result is true.  The total interpretation treats the check as an identity;
the `Option` interpretation can fail.  Both interpreters receive the same
syntax-derived four-coordinate resource bound, which is checked by executable
Boolean predicates and connected back to the generic proof-level budget API.
-/

set_option autoImplicit false

namespace Ript.Examples.SimpleComputation

open CategoryTheory
open Ript.Core
open Ript.Models.Computation
open Ript.Semantics
open Ript.Syntax

/-- The single wire type in the example computation language. -/
inductive ComputationObject where
  | bit

/-- Primitive total/partial operations on a Boolean wire. -/
inductive ComputationGenerator :
    ComputationObject → ComputationObject → Type where
  /-- Account for one abstract oracle query. -/
  | query : ComputationGenerator .bit .bit
  /-- Boolean negation, counted as one formal gate. -/
  | not : ComputationGenerator .bit .bit
  /-- A guard that may fail in the partial interpretation. -/
  | requireTrue : ComputationGenerator .bit .bit

/-- Declared multidimensional resource use of each primitive. -/
def generatorResource {X Y : ComputationObject}
    (generator : ComputationGenerator X Y) : ComputationResource :=
  match generator with
  | .query => ComputationResource.of 1 1 0 0
  | .not => ComputationResource.of 1 0 0 1
  | .requireTrue => ComputationResource.of 1 0 0 0

/-- Typed signature shared by the total and partial interpreters. -/
def signature : Signature ComputationResource where
  Obj := ComputationObject
  Gen := ComputationGenerator
  cost := generatorResource

/-- Query, negate, then require the resulting bit to be true. -/
def pipeline : Expr signature .bit .bit :=
  .comp (.gen .query) (.comp (.gen .not) (.gen .requireTrue))

/-- Semantic Boolean object in the total-computation category. -/
abbrev totalBit : Total.Object :=
  ⟨Bool⟩

/-- Total query primitive. -/
def totalQuery : totalBit ⟶ totalBit :=
  Total.mk id (generatorResource .query)

/-- Total Boolean-negation primitive. -/
def totalNot : totalBit ⟶ totalBit :=
  Total.mk (!·) (generatorResource .not)

/-- Total guard primitive, interpreted as an identity. -/
def totalRequireTrue : totalBit ⟶ totalBit :=
  Total.mk id (generatorResource .requireTrue)

/-- Total interpretation: the guard is an identity and cannot fail. -/
abbrev totalInterpretation : Interpretation signature Total.Object where
  obj
    | .bit => totalBit
  mapGen
    | .query => totalQuery
    | .not => totalNot
    | .requireTrue => totalRequireTrue
  mapGen_cost generator := by
    cases generator <;> exact le_rfl

/-- Semantic Boolean object in the partial-computation category. -/
abbrev partialBit : Partial.Object :=
  ⟨Bool⟩

/-- Always-successful query primitive in the partial model. -/
def partialQuery : partialBit ⟶ partialBit :=
  Partial.mk some (generatorResource .query)

/-- Always-successful Boolean negation in the partial model. -/
def partialNot : partialBit ⟶ partialBit :=
  Partial.mk (fun bit ↦ some (!bit)) (generatorResource .not)

/-- Partial guard primitive, failing exactly when its input is false. -/
def partialRequireTrue : partialBit ⟶ partialBit :=
  Partial.mk (fun bit ↦ if bit then some true else none)
    (generatorResource .requireTrue)

/-- Partial interpretation: the guard fails exactly on `false`. -/
abbrev partialInterpretation : Interpretation signature Partial.Object where
  obj
    | .bit => partialBit
  mapGen
    | .query => partialQuery
    | .not => partialNot
    | .requireTrue => partialRequireTrue
  mapGen_cost generator := by
    cases generator <;> exact le_rfl

/-- The program's syntax computes one query, one gate, and three steps. -/
theorem pipeline_syntaxCost :
    pipeline.syntaxCost = ComputationResource.of 3 1 0 1 := by
  decide

/-- The total interpreter executes the expected Boolean function. -/
theorem total_pipeline_result (input : Bool) :
    (eval totalInterpretation pipeline).run input = !input :=
  rfl

/-- The partial interpreter succeeds on `false` because negation produces
`true` before the guard. -/
theorem partial_pipeline_success :
    (eval partialInterpretation pipeline).run false = some true :=
  rfl

/-- The partial interpreter fails on `true` because negation produces `false`
before the guard. -/
theorem partial_pipeline_failure :
    (eval partialInterpretation pipeline).run true = none :=
  rfl

/-- The total executor stores exactly the cost computed by syntax. -/
theorem total_pipeline_resource :
    (eval totalInterpretation pipeline).resource = pipeline.syntaxCost := by
  decide

/-- The partial executor stores exactly the same syntax-derived resource. -/
theorem partial_pipeline_resource :
    (eval partialInterpretation pipeline).resource = pipeline.syntaxCost := by
  decide

/-- Generic interpretation soundness applies to the concrete total executor. -/
theorem total_interpreter_cost_sound :
    processCost (R := ComputationResource)
      (eval totalInterpretation pipeline) ≤ pipeline.syntaxCost :=
  eval_cost_le totalInterpretation pipeline

/-- Generic interpretation soundness applies to the concrete partial executor. -/
theorem partial_interpreter_cost_sound :
    processCost (R := ComputationResource)
      (eval partialInterpretation pipeline) ≤ pipeline.syntaxCost :=
  eval_cost_le partialInterpretation pipeline

/-- The executable total-model budget checker proves a generic budget
judgment at the exact syntax-computed resource vector. -/
theorem total_budget_checker_sound :
    Ript.Resource.WithinBudget pipeline.syntaxCost
      (eval totalInterpretation pipeline) := by
  apply Total.withinBudget_sound
  rw [Total.withinBudget, total_pipeline_resource]
  simp [ComputationResource.within]

/-- The executable partial-model budget checker proves the corresponding
generic budget judgment. -/
theorem partial_budget_checker_sound :
    Ript.Resource.WithinBudget pipeline.syntaxCost
      (eval partialInterpretation pipeline) := by
  apply Partial.withinBudget_sound
  rw [Partial.withinBudget, partial_pipeline_resource]
  simp [ComputationResource.within]

#eval decide (pipeline.syntaxCost = ComputationResource.of 3 1 0 1)
#eval decide ((eval totalInterpretation pipeline).run false = true)
#eval decide ((eval totalInterpretation pipeline).run true = false)
#eval decide ((eval partialInterpretation pipeline).run false = some true)
#eval decide ((eval partialInterpretation pipeline).run true = none)
#eval decide
  (Total.withinBudget pipeline.syntaxCost (eval totalInterpretation pipeline))
#eval decide
  (Partial.withinBudget pipeline.syntaxCost (eval partialInterpretation pipeline))

end Ript.Examples.SimpleComputation
