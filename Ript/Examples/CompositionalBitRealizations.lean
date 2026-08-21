import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Ript.Examples.CommonBitRealizations

/-!
# A compositional process language realized in six models

The one-generator common slice is extended here to three interfaces and two
composable Boolean flips.  Each model must interpret the whole typed pipeline,
not only one isolated primitive.  The resulting comparison exposes six
different composition mechanisms while proving one shared observable law:
two flips restore the input.
-/

set_option autoImplicit false

namespace Ript.Examples.CompositionalBitRealizations

open CategoryTheory
open Ript.Core
open Ript.Models.Causal
open Ript.Models.Computation
open Ript.Models.Decision.Blackwell
open Ript.Models.Decision.SemanticValue
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic
open Ript.Models.FiniteStochastic.FinStoch
open Ript.Models.Quantum
open Ript.Models.Thermal
open Ript.Semantics
open Ript.Syntax

namespace OneStep

open Ript.Examples.CommonBitRealizations

end OneStep

/-- Three interfaces make the common syntax genuinely compositional. -/
inductive Interface where
  | input
  | middle
  | output
  deriving DecidableEq, Repr

/-- Two typed generators represent the two stages of the common process. -/
inductive Generator : Interface → Interface → Type where
  | firstFlip : Generator .input .middle
  | secondFlip : Generator .middle .output

/-- Each primitive declares one scalar resource unit. -/
def signature : Signature Nat where
  Obj := Interface
  Gen := Generator
  cost
    | .firstFlip => 1
    | .secondFlip => 1

/-- The shared two-stage process. -/
def doubleFlipExpr : Expr signature .input .output :=
  .comp (.gen .firstFlip) (.gen .secondFlip)

/-- Composition computes two units before choosing any model. -/
@[simp]
theorem doubleFlipExpr_syntaxCost : doubleFlipExpr.syntaxCost = 2 :=
  rfl

/-! ## Probability -/

/-- Both stochastic stages are exact deterministic negation. -/
def probabilityInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.FiniteStochastic.Object)
      (OrderAddMonoidHom.id Nat) where
  obj _ := Ript.Examples.StochasticBits.bit
  mapGen
    | .firstFlip => Ript.Examples.StochasticBits.deterministicNot
    | .secondFlip => Ript.Examples.StochasticBits.deterministicNot
  mapGen_cost generator := by
    cases generator <;> exact Nat.zero_le 1

/-! ## Quantum processes -/

/-- Zero abstract scalar cost used only for the quantum channel slice. -/
local instance quantumZeroCost :
    HasProcessCost Ript.Models.Quantum.Object Nat :=
  Ript.Examples.CommonBitRealizations.quantumZeroCost

/-- Both quantum stages are Pauli-X. -/
def quantumInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.Quantum.Object)
      (OrderAddMonoidHom.id Nat) where
  obj _ := Ript.Examples.QubitChannel.qubit
  mapGen
    | .firstFlip => Ript.Examples.QubitChannel.bitFlip
    | .secondFlip => Ript.Examples.QubitChannel.bitFlip
  mapGen_cost generator := by
    cases generator <;> exact Nat.zero_le 1

/-! ## A three-node causal chain -/

/-- Root input node in topological position zero. -/
def inputNode : Fin 3 := 0

/-- First child node in topological position one. -/
def middleNode : Fin 3 := 1

/-- Output child node in topological position two. -/
def outputNode : Fin 3 := 2

@[simp]
theorem assignment_zero (input middle output : Bool) :
    ![input, middle, output] (0 : Fin 3) = input :=
  rfl

@[simp]
theorem assignment_one (input middle output : Bool) :
    ![input, middle, output] (1 : Fin 3) = middle :=
  rfl

@[simp]
theorem assignment_two (input middle output : Bool) :
    ![input, middle, output] (2 : Fin 3) = output :=
  rfl

/-- The certified chain `input → middle → output`. -/
def negatingChainDAG : FiniteDAG 3 where
  parents child :=
    if child = middleNode then {inputNode}
    else if child = outputNode then {middleNode}
    else ∅
  parent_before child parent hparent := by
    fin_cases child <;> fin_cases parent <;>
      simp [inputNode, middleNode, outputNode] at hparent ⊢

/-- Exact fair root distribution. -/
def fairBitDistribution : FinDist (Ript.Models.FiniteStochastic.Object.of Bool) where
  prob _ := (1 : ℚ≥0) / 2
  normalized := by
    change (∑ _ : Bool, (1 : ℚ≥0) / 2) = 1
    rw [Fintype.sum_bool]
    norm_num

/-- First child negates the input node. -/
def firstFlipMechanism : Mechanism negatingChainDAG Bool middleNode where
  run parents := FinDist.pure
    (!(parents ⟨inputNode, by
      simp [negatingChainDAG, inputNode, middleNode, outputNode]⟩))

/-- Second child negates the middle node. -/
def secondFlipMechanism : Mechanism negatingChainDAG Bool outputNode where
  run parents := FinDist.pure
    (!(parents ⟨middleNode, by
      simp [negatingChainDAG, inputNode, middleNode, outputNode]⟩))

/-- The full normalized finite causal model containing both mechanisms. -/
def rootMechanism : Mechanism negatingChainDAG Bool inputNode where
  run _ := fairBitDistribution

/-- The full normalized finite causal model containing both mechanisms. -/
def negatingChainModel : FiniteCausalModel 3 Bool where
  dag := negatingChainDAG
  mechanism := Fin.cases rootMechanism
    (Fin.cases firstFlipMechanism (fun node ↦ by
      have hnode : node = 0 := Fin.eq_zero node
      subst node
      exact secondFlipMechanism))

@[simp]
theorem negatingChainModel_input
    (parents : negatingChainModel.dag.ParentAssignment Bool inputNode) :
    (negatingChainModel.mechanism inputNode).run parents =
      rootMechanism.run parents :=
  rfl

@[simp]
theorem negatingChainModel_middle
    (parents : negatingChainModel.dag.ParentAssignment Bool middleNode) :
    (negatingChainModel.mechanism middleNode).run parents =
      firstFlipMechanism.run parents :=
  rfl

@[simp]
theorem negatingChainModel_output
    (parents : negatingChainModel.dag.ParentAssignment Bool outputNode) :
    (negatingChainModel.mechanism outputNode).run parents =
      secondFlipMechanism.run parents :=
  rfl

@[simp]
theorem negatingChainModel_zero
    (parents : negatingChainModel.dag.ParentAssignment Bool (0 : Fin 3)) :
    (negatingChainModel.mechanism 0).run parents =
      rootMechanism.run parents :=
  rfl

@[simp]
theorem negatingChainModel_one
    (parents : negatingChainModel.dag.ParentAssignment Bool (1 : Fin 3)) :
    (negatingChainModel.mechanism 1).run parents =
      firstFlipMechanism.run parents :=
  rfl

@[simp]
theorem negatingChainModel_two
    (parents : negatingChainModel.dag.ParentAssignment Bool (2 : Fin 3)) :
    (negatingChainModel.mechanism 2).run parents =
      secondFlipMechanism.run parents :=
  rfl

@[simp]
theorem negatingChainModel_succ_zero
    (parents : negatingChainModel.dag.ParentAssignment Bool
      (Fin.succ (0 : Fin 2))) :
    (negatingChainModel.mechanism (Fin.succ (0 : Fin 2))).run parents =
      firstFlipMechanism.run parents :=
  rfl

@[simp]
theorem negatingChainModel_succ_succ_zero
    (parents : negatingChainModel.dag.ParentAssignment Bool
      (Fin.succ (Fin.succ (0 : Fin 1)))) :
    (negatingChainModel.mechanism
      (Fin.succ (Fin.succ (0 : Fin 1)))).run parents =
      secondFlipMechanism.run parents :=
  rfl

/-- Encode one Boolean as the unique parent assignment of the middle node. -/
def firstParentAssignment (value : Bool) :
    negatingChainDAG.ParentAssignment Bool middleNode :=
  fun _ ↦ value

/-- Encode one Boolean as the unique parent assignment of the output node. -/
def secondParentAssignment (value : Bool) :
    negatingChainDAG.ParentAssignment Bool outputNode :=
  fun _ ↦ value

/-- First local causal mechanism exposed on the common Boolean boundary. -/
def firstCausalChannel :
    FinStoch Ript.Examples.StochasticBits.bit Ript.Examples.StochasticBits.bit :=
  FinStoch.dirac Bool.not

/-- Second local causal mechanism exposed on the same boundary. -/
def secondCausalChannel :
    FinStoch Ript.Examples.StochasticBits.bit Ript.Examples.StochasticBits.bit :=
  FinStoch.dirac Bool.not

/-- The first common-boundary channel is exactly the first local mechanism
after encoding its unique parent value. -/
theorem firstCausalChannel_representsMechanism (input output : Bool) :
    firstCausalChannel.prob input output =
      firstFlipMechanism.toFinStoch.prob
        (firstParentAssignment input) output := by
  change (if (!input) = output then (1 : ℚ≥0) else 0) =
    if (!input) = output then 1 else 0
  rfl

/-- The second boundary channel represents the second local mechanism. -/
theorem secondCausalChannel_representsMechanism (input output : Bool) :
    secondCausalChannel.prob input output =
      secondFlipMechanism.toFinStoch.prob
        (secondParentAssignment input) output := by
  change (if (!input) = output then (1 : ℚ≥0) else 0) =
    if (!input) = output then 1 else 0
  rfl

/-- The common causal interpretation is derived from the two declared local
mechanisms of one three-node model. -/
def causalInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.FiniteStochastic.Object)
      (OrderAddMonoidHom.id Nat) where
  obj _ := Ript.Examples.StochasticBits.bit
  mapGen
    | .firstFlip => firstCausalChannel
    | .secondFlip => secondCausalChannel
  mapGen_cost generator := by
    cases generator <;> exact Nat.zero_le 1

/-! ## Computation -/

/-- Two total gates retain the four-coordinate computation resource. -/
def computationInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.Computation.Total.Object)
      Ript.Examples.CommonBitRealizations.computationResourceMap where
  obj _ := Ript.Examples.SimpleComputation.totalBit
  mapGen
    | .firstFlip => Ript.Examples.SimpleComputation.totalNot
    | .secondFlip => Ript.Examples.SimpleComputation.totalNot
  mapGen_cost generator := by
    cases generator <;> exact le_rfl

/-! ## Task-relative semantic information -/

/-- First flip is an informative experiment; the second is reversible
post-processing of its observation. -/
def semanticInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.FiniteStochastic.Object)
      (OrderAddMonoidHom.id Nat) where
  obj _ := Ript.Examples.SimpleDecision.decisionBit
  mapGen
    | .firstFlip => Ript.Examples.CommonBitRealizations.semanticFlipExperiment
    | .secondFlip => Ript.Examples.CommonBitRealizations.semanticFlipExperiment
  mapGen_cost generator := by
    cases generator <;> exact Nat.zero_le 1

/-! ## Thermodynamics -/

/-- Zero abstract scalar cost used only for the thermal process slice. -/
local instance thermalZeroCost : HasProcessCost ThermalObject Nat :=
  Ript.Examples.CommonBitRealizations.thermalZeroCost

/-- Two free thermal flips form the common thermal interpretation. -/
def thermalInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := ThermalObject)
      (OrderAddMonoidHom.id Nat) where
  obj _ := Ript.Examples.SimpleThermalModel.thermalBit
  mapGen
    | .firstFlip => Ript.Examples.SimpleThermalModel.thermalFlip
    | .secondFlip => Ript.Examples.SimpleThermalModel.thermalFlip
  mapGen_cost generator := by
    cases generator <;> exact Nat.zero_le 1

/-! ## Model-specific composition theorems -/

/-- Chapman--Kolmogorov composition restores the stochastic identity. -/
theorem probability_doubleFlip :
    ResourceChangingInterpretation.eval probabilityInterpretation
        doubleFlipExpr =
      FinStoch.identity Ript.Examples.StochasticBits.bit := by
  apply FinStoch.ext
  intro input output
  change Bool at input output
  change (∑ middle : Bool,
    (if (!input) = middle then (1 : ℚ≥0) else 0) *
      (if (!middle) = output then 1 else 0)) =
    if input = output then 1 else 0
  cases input <;> cases output <;>
    rw [Fintype.sum_bool] <;> norm_num

/-- Two Pauli-X stages restore every computational-basis density matrix. -/
theorem quantum_doubleFlip (value : Bool) :
    (ResourceChangingInterpretation.eval quantumInterpretation
      doubleFlipExpr).applyDensity
        (Ript.Examples.QubitChannel.basisDensity value) =
      Ript.Examples.QubitChannel.basisDensity value := by
  change Ript.Examples.QubitChannel.bitFlip.applyDensity
      (Ript.Examples.QubitChannel.bitFlip.applyDensity
        (Ript.Examples.QubitChannel.basisDensity value)) = _
  rw [Ript.Examples.QubitChannel.bitFlip_basisDensity,
    Ript.Examples.QubitChannel.bitFlip_basisDensity]
  simp

/-- The two local mechanisms of the normalized three-node model first negate
the root and then restore it at the output. -/
theorem causal_mechanisms_doubleFlip (value : Bool) :
    ((negatingChainModel.mechanism middleNode).run
          (firstParentAssignment value)).prob (!value) = 1 ∧
      ((negatingChainModel.mechanism outputNode).run
          (secondParentAssignment (!value))).prob value = 1 := by
  constructor
  · change (firstFlipMechanism.run
      (firstParentAssignment value)).prob (!value) = 1
    change (if (!value) = !value then (1 : ℚ≥0) else 0) = 1
    cases value <;> norm_num
  · change (secondFlipMechanism.run
      (secondParentAssignment (!value))).prob value = 1
    change (if (!(!value)) = value then (1 : ℚ≥0) else 0) = 1
    cases value <;> norm_num

/-- Composition of the two mechanism-derived boundary channels is identity. -/
theorem causal_doubleFlip :
    ResourceChangingInterpretation.eval causalInterpretation doubleFlipExpr =
      FinStoch.identity Ript.Examples.StochasticBits.bit := by
  apply FinStoch.ext
  intro input output
  change Bool at input output
  simp only [ResourceChangingInterpretation.eval,
    ResourceChangingInterpretation.toMappedCost, Ript.Semantics.eval,
    Expr.mapCost, doubleFlipExpr, causalInterpretation,
    firstCausalChannel, secondCausalChannel]
  change (∑ middle : Bool,
    (if (!input) = middle then (1 : ℚ≥0) else 0) *
      (if (!middle) = output then 1 else 0)) =
    if input = output then 1 else 0
  cases input <;> cases output <;>
    rw [Fintype.sum_bool] <;> norm_num

/-- The total program restores its Boolean input. -/
theorem computation_doubleFlip (value : Bool) :
    (ResourceChangingInterpretation.eval computationInterpretation
      doubleFlipExpr).run value = value := by
  simp [ResourceChangingInterpretation.eval,
    ResourceChangingInterpretation.toMappedCost, Ript.Semantics.eval,
    Expr.mapCost, doubleFlipExpr, computationInterpretation,
    Ript.Examples.SimpleComputation.totalNot,
    Ript.Models.Computation.Total.mk]

/-- The two-stage program stores exactly two steps and two gates. -/
theorem computation_doubleFlip_cost :
    processCost (R := ComputationResource)
        (ResourceChangingInterpretation.eval computationInterpretation
          doubleFlipExpr) =
      ComputationResource.of 2 0 0 2 := by
  change ComputationResource.of 1 0 0 1 +
      ComputationResource.of 1 0 0 1 = ComputationResource.of 2 0 0 2
  funext kind
  fin_cases kind <;> rfl

/-- The semantic pipeline is exactly perfect observation after reversible
post-processing. -/
theorem semantic_doubleFlip :
    ResourceChangingInterpretation.eval semanticInterpretation doubleFlipExpr =
      Ript.Examples.SimpleDecision.perfectExperiment := by
  change FinStoch.comp
      Ript.Examples.CommonBitRealizations.semanticFlipExperiment
      Ript.Examples.CommonBitRealizations.semanticFlipExperiment =
    Ript.Examples.SimpleDecision.perfectExperiment
  exact Ript.Examples.CommonBitRealizations.semanticFlip_involutive

/-- Consequently the composed experiment retains exact guessing value
`1/2`. -/
theorem semantic_doubleFlip_value :
    semanticValue Ript.Examples.SimpleDecision.bitGuessing
        Ript.Examples.SimpleDecision.uninformativeExperiment
        (ResourceChangingInterpretation.eval semanticInterpretation
          doubleFlipExpr) = (1 : ℚ≥0) / 2 := by
  rw [semantic_doubleFlip]
  exact Ript.Examples.SimpleDecision.perfect_guessing_semantic_value

/-- The two-step thermal process is exactly the Gibbs-preserving identity. -/
theorem thermal_doubleFlip :
    ResourceChangingInterpretation.eval thermalInterpretation doubleFlipExpr =
      GibbsPreserving.identity Ript.Examples.SimpleThermalModel.thermalBit :=
  Ript.Examples.SimpleThermalModel.thermalFlip_involutive

/-- The two free steps form a closed protocol whose denotation is identity. -/
theorem thermal_protocol_doubleFlip :
    Ript.Examples.SimpleThermalModel.thermalFlipCycle.process =
      GibbsPreserving.identity Ript.Examples.SimpleThermalModel.thermalBit :=
  Ript.Examples.SimpleThermalModel.thermalFlipCycle_process

/-- The six model-specific composition laws packaged without identifying the
models or their proof obligations. -/
structure SixModelCompositionAgreement : Prop where
  probability :
    ResourceChangingInterpretation.eval probabilityInterpretation
        doubleFlipExpr = FinStoch.identity Ript.Examples.StochasticBits.bit
  quantum : ∀ value : Bool,
    (ResourceChangingInterpretation.eval quantumInterpretation
      doubleFlipExpr).applyDensity
        (Ript.Examples.QubitChannel.basisDensity value) =
      Ript.Examples.QubitChannel.basisDensity value
  causalBoundary :
    ResourceChangingInterpretation.eval causalInterpretation doubleFlipExpr =
      FinStoch.identity Ript.Examples.StochasticBits.bit
  causalMechanisms : ∀ value : Bool,
    ((negatingChainModel.mechanism middleNode).run
          (firstParentAssignment value)).prob (!value) = 1 ∧
      ((negatingChainModel.mechanism outputNode).run
          (secondParentAssignment (!value))).prob value = 1
  computation : ∀ value : Bool,
    (ResourceChangingInterpretation.eval computationInterpretation
      doubleFlipExpr).run value = value
  computationCost :
    processCost (R := ComputationResource)
        (ResourceChangingInterpretation.eval computationInterpretation
          doubleFlipExpr) = ComputationResource.of 2 0 0 2
  semantic :
    semanticValue Ript.Examples.SimpleDecision.bitGuessing
        Ript.Examples.SimpleDecision.uninformativeExperiment
        (ResourceChangingInterpretation.eval semanticInterpretation
          doubleFlipExpr) = (1 : ℚ≥0) / 2
  thermal :
    ResourceChangingInterpretation.eval thermalInterpretation doubleFlipExpr =
      GibbsPreserving.identity Ript.Examples.SimpleThermalModel.thermalBit

/-- **Six-model compositional agreement theorem.** -/
theorem sixModelCompositionAgreement : SixModelCompositionAgreement where
  probability := probability_doubleFlip
  quantum := quantum_doubleFlip
  causalBoundary := causal_doubleFlip
  causalMechanisms := causal_mechanisms_doubleFlip
  computation := computation_doubleFlip
  computationCost := computation_doubleFlip_cost
  semantic := semantic_doubleFlip_value
  thermal := thermal_doubleFlip

end Ript.Examples.CompositionalBitRealizations
