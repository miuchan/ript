import Ript.Examples.QubitInstrument
import Ript.Models.Quantum.Monoidal
import Ript.Semantics.ResourceChangingMonoidalInitiality

/-!
# Resource-bounded syntax for a finite quantum instrument

The computational-basis instrument is represented as an ordinary channel from
a qubit to a classical Boolean record tensored with the residual qubit.  This
makes a genuine branching measurement available to the common resource-aware
symmetric monoidal syntax and hence to its soundness, completeness, and free
lift theorems.
-/

set_option autoImplicit false

namespace Ript.Examples.InstrumentSyntax

open CategoryTheory
open Ript.Core
open Ript.Models.Quantum
open Ript.Semantics
open Ript.Syntax
open scoped Kronecker

/-- Quantum-system and classical-record wire sorts. -/
inductive Wire where
  | quantum
  | classical
  | treeClassical
  deriving DecidableEq, Repr

/-- One measurement generator exposes a classical result while retaining the
posterior quantum system. -/
inductive Generator : FreeMonoidalCategory Wire → FreeMonoidalCategory Wire → Type where
  | measure : Generator (.of .quantum) (.tensor (.of .classical) (.of .quantum))
  | measureCorrect :
      Generator (.of .quantum) (.tensor (.of .classical) (.of .quantum))
  | measureTree :
      Generator (.of .quantum)
        (.tensor (.of .treeClassical) (.of .quantum))

/-- Measurement has one declared abstract resource unit. -/
def signature : MonoidalSignature Nat where
  Wire := Wire
  Gen := Generator
  cost
    | .measure => 1
    | .measureCorrect => 2
    | .measureTree => 2

/-- One recorded measurement. -/
def measureExpr : MonoidalExpr signature (.of .quantum)
    (.tensor (.of .classical) (.of .quantum)) :=
  .gen .measure

/-- Recorded measurement followed by outcome-controlled correction. -/
def measureCorrectExpr : MonoidalExpr signature (.of .quantum)
    (.tensor (.of .classical) (.of .quantum)) :=
  .gen .measureCorrect

/-- Two-round dependent-outcome measurement tree. -/
def measureTreeExpr : MonoidalExpr signature (.of .quantum)
    (.tensor (.of .treeClassical) (.of .quantum)) :=
  .gen .measureTree

/-- Two independent recorded measurements. -/
def parallelMeasureExpr :
    MonoidalExpr signature
      (.tensor (.of .quantum) (.of .quantum))
      (.tensor
        (.tensor (.of .classical) (.of .quantum))
        (.tensor (.of .classical) (.of .quantum))) :=
  .tensor (.gen .measure) (.gen .measure)

@[simp]
theorem measureExpr_cost : measureExpr.syntaxCost = 1 := rfl

@[simp]
theorem measureCorrectExpr_cost : measureCorrectExpr.syntaxCost = 2 := rfl

@[simp]
theorem measureTreeExpr_cost : measureTreeExpr.syntaxCost = 2 := rfl

@[simp]
theorem parallelMeasureExpr_cost : parallelMeasureExpr.syntaxCost = 2 := rfl

/-- Full-Kraus interpretation of the instrument syntax. -/
noncomputable def interpretation :
    ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := Object)
      (OrderAddMonoidHom.id Nat) where
  wire
    | .quantum => QubitChannel.qubit
    | .classical => KrausInstrument.outcomeObject Bool
    | .treeClassical => KrausInstrument.outcomeObject
        QubitInstrument.recursiveTree.History
  mapGen
    | .measure => QubitInstrument.computationalMeasurement.recordedChannel
    | .measureCorrect => QubitInstrument.correctedMeasurement.recordedChannel
    | .measureTree => QubitInstrument.recursiveTree.eval.recordedChannel
  mapGen_cost
    | .measure => Nat.zero_le 1
    | .measureCorrect => Nat.zero_le 2
    | .measureTree => Nat.zero_le 2

/-- Evaluating the generator is exactly the classical-record channel
representation of the instrument. -/
theorem eval_measure :
    ResourceChangingMonoidalInterpretation.eval interpretation measureExpr =
      QubitInstrument.computationalMeasurement.recordedChannel :=
  rfl

/-- The adaptive generator is exactly the recorded channel of the
classically controlled measurement-and-correction instrument. -/
theorem eval_measureCorrect :
    ResourceChangingMonoidalInterpretation.eval interpretation
        measureCorrectExpr =
      QubitInstrument.correctedMeasurement.recordedChannel :=
  rfl

/-- The dependent-tree generator is exactly its classical-record channel
representation. -/
theorem eval_measureTree :
    ResourceChangingMonoidalInterpretation.eval interpretation
        measureTreeExpr =
      QubitInstrument.recursiveTree.eval.recordedChannel :=
  rfl

/-- Every diagonal classical-result block of the interpreted channel is the
corresponding instrument branch, and every off-diagonal block vanishes. -/
theorem eval_measure_block (ρ : Matrix QubitChannel.qubit QubitChannel.qubit ℂ)
    (outcome outcome' : Bool) (row column : Bool) :
    (ResourceChangingMonoidalInterpretation.eval interpretation measureExpr).map ρ
        (outcome, row) (outcome', column) =
      if outcome = outcome' then
        (QubitInstrument.computationalMeasurement.branch outcome).map ρ
          row column else 0 := by
  rw [eval_measure]
  exact KrausInstrument.recordedChannel_map_apply _ _ _ _ _ _

/-- Parallel syntax evaluates to the tensor of the two recorded instrument
channels. -/
theorem eval_parallelMeasure :
    ResourceChangingMonoidalInterpretation.eval interpretation
        parallelMeasureExpr =
      KrausChannel.tensor
        QubitInstrument.computationalMeasurement.recordedChannel
        QubitInstrument.computationalMeasurement.recordedChannel :=
  rfl

/-- The resource soundness theorem bounds the represented instrument channel
by its one-unit syntax declaration. -/
theorem measure_cost_bound :
    processCost (R := Nat)
        (ResourceChangingMonoidalInterpretation.eval interpretation measureExpr) ≤
      1 :=
  ResourceChangingMonoidalInterpretation.eval_cost_le interpretation measureExpr

/-- Adaptive measurement and feedback is bounded by its two-unit syntax
declaration. -/
theorem measureCorrect_cost_bound :
    processCost (R := Nat)
        (ResourceChangingMonoidalInterpretation.eval interpretation
          measureCorrectExpr) ≤ 2 :=
  ResourceChangingMonoidalInterpretation.eval_cost_le interpretation
    measureCorrectExpr

/-- The two-round dependent tree is bounded by two declared units. -/
theorem measureTree_cost_bound :
    processCost (R := Nat)
        (ResourceChangingMonoidalInterpretation.eval interpretation
          measureTreeExpr) ≤ 2 :=
  ResourceChangingMonoidalInterpretation.eval_cost_le interpretation
    measureTreeExpr

/-- The two-measurement tensor is bounded by the exact two-unit syntax
budget. -/
theorem parallel_measure_cost_bound :
    processCost (R := Nat)
        (ResourceChangingMonoidalInterpretation.eval interpretation
          parallelMeasureExpr) ≤ 2 :=
  ResourceChangingMonoidalInterpretation.eval_cost_le interpretation
    parallelMeasureExpr

/-- Canonical strong symmetric resource-changing lift of the instrument
interpretation from the free term model. -/
noncomputable def freeLift :
    ResourceChangeFunctor (MonoidalTermModel signature) Object Nat Nat
      (OrderAddMonoidHom.id Nat) :=
  ResourceChangingMonoidalFree.lift interpretation

theorem freeLift_on_measure :
    freeLift.toFunctor.map
        (MonoidalTermModel.quote signature (.gen .measure)) =
      interpretation.mapGen .measure :=
  rfl

theorem freeLift_on_measureCorrect :
    freeLift.toFunctor.map
        (MonoidalTermModel.quote signature (.gen .measureCorrect)) =
      interpretation.mapGen .measureCorrect :=
  rfl

theorem freeLift_on_measureTree :
    freeLift.toFunctor.map
        (MonoidalTermModel.quote signature (.gen .measureTree)) =
      interpretation.mapGen .measureTree :=
  rfl

end Ript.Examples.InstrumentSyntax
