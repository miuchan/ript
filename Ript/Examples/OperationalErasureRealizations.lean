import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Ript.Examples.CompositionalBitRealizations
import Ript.Examples.ExactWorkErasure
import Ript.Models.Quantum.ClassicalEmbedding

/-!
# Operational erasure in six information models

This common typed pipeline has two distinct resource coordinates: exposing
information and erasing it.  It then interprets `expose ≫ erase` in all six
model families.  The thermal interpretation is deliberately not a free
fixed-output map on one degenerate bit: it is the compiled Gibbs-preserving joint
memory--work-battery process that pays the exact Landauer cost.
-/

set_option autoImplicit false

namespace Ript.Examples.OperationalErasureRealizations

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
open Ript.Models.Quantum.ClassicalEmbedding
open Ript.Models.Thermal
open Ript.Semantics
open Ript.Syntax

/-! ## Common syntax and resources -/

/-- Exposure and erasure are tracked independently. -/
abbrev OperationKind := Fin 2

namespace OperationKind

/-- Coordinate zero records information exposure. -/
def exposure : OperationKind := 0

/-- Coordinate one records irreversible erasure. -/
def erasure : OperationKind := 1

end OperationKind

/-- Two-coordinate resource algebra of the common operational language. -/
abbrev OperationResource := OperationKind → Nat

/-- Construct an exposure/erasure resource vector. -/
def OperationResource.of (exposure erasure : Nat) : OperationResource :=
  ![exposure, erasure]

/-- Forget the distinction while retaining the total number of declared
operations. -/
def scalarResourceMap : OperationResource →+o Nat where
  toFun resource := resource OperationKind.exposure +
    resource OperationKind.erasure
  map_zero' := rfl
  map_add' left right := by
    simp [OperationKind.exposure, OperationKind.erasure]
    omega
  monotone' left right h :=
    Nat.add_le_add (h OperationKind.exposure) (h OperationKind.erasure)

/-- Map exposure to one step and query, and erasure to one step and gate. -/
def computationResourceMap : OperationResource →+o ComputationResource where
  toFun resource := ComputationResource.of
    (resource OperationKind.exposure + resource OperationKind.erasure)
    (resource OperationKind.exposure) 0 (resource OperationKind.erasure)
  map_zero' := by
    funext kind
    fin_cases kind <;> rfl
  map_add' left right := by
    funext kind
    fin_cases kind <;>
      simp [ComputationResource.of, OperationKind.exposure,
        OperationKind.erasure, add_assoc, add_left_comm, add_comm]
  monotone' left right h kind := by
    fin_cases kind
    · exact Nat.add_le_add (h OperationKind.exposure)
        (h OperationKind.erasure)
    · exact h OperationKind.exposure
    · exact le_rfl
    · exact h OperationKind.erasure

/-- Source, exposed, and erased interfaces of the common pipeline. -/
inductive Interface where
  | source
  | exposed
  | erased
  deriving DecidableEq, Repr

/-- Expose information, then erase the exposed representation. -/
inductive Generator : Interface → Interface → Type where
  | expose : Generator .source .exposed
  | erase : Generator .exposed .erased

/-- Common signature with independent exposure and erasure budgets. -/
def signature : Signature OperationResource where
  Obj := Interface
  Gen := Generator
  cost
    | .expose => OperationResource.of 1 0
    | .erase => OperationResource.of 0 1

/-- The common operational erasure pipeline. -/
def erasurePipeline : Expr signature .source .erased :=
  .comp (.gen .expose) (.gen .erase)

/-- The syntax records exactly one exposure and one erasure. -/
@[simp]
theorem erasurePipeline_syntaxCost :
    erasurePipeline.syntaxCost = OperationResource.of 1 1 := by
  funext kind
  fin_cases kind <;> rfl

/-! ## Shared exact classical erasure -/

/-- Deterministically replace a Boolean value by `false`. -/
def eraseBitChannel :
    FinStoch Ript.Examples.StochasticBits.bit Ript.Examples.StochasticBits.bit :=
  FinStoch.dirac (fun _ : Bool ↦ false)

/-! ## Classical probability -/

/-- Perfect exposure followed by deterministic erasure. -/
def probabilityInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.FiniteStochastic.Object)
      scalarResourceMap where
  obj _ := Ript.Examples.StochasticBits.bit
  mapGen
    | .expose => FinStoch.identity Ript.Examples.StochasticBits.bit
    | .erase => eraseBitChannel
  mapGen_cost generator := by
    cases generator <;> exact Nat.zero_le _

/-! ## Quantum reset -/

/-- Zero abstract scalar cost used only by the quantum erasure slice. -/
local instance quantumZeroCost :
    HasProcessCost Ript.Models.Quantum.Object Nat :=
  Ript.Examples.CommonBitRealizations.quantumZeroCost

/-- Quantum system with the same distinguished Boolean classical basis. -/
abbrev classicalQubit : Ript.Models.Quantum.Object :=
  classicalObject Ript.Examples.StochasticBits.bit

/-- CPTP reset obtained from the faithful classical measurement--preparation
embedding of the deterministic erasure channel. -/
noncomputable def quantumReset : KrausChannel classicalQubit classicalQubit :=
  measurementPreparation eraseBitChannel

/-- Ambient quantum identity followed by the reset channel. -/
noncomputable def quantumInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.Quantum.Object)
      scalarResourceMap where
  obj _ := classicalQubit
  mapGen
    | .expose => KrausChannel.identity classicalQubit
    | .erase => quantumReset
  mapGen_cost generator := by
    cases generator <;> exact Nat.zero_le _

/-! ## Causal mechanism replacement -/

/-- Parent-assignment input of the child mechanism in the existing chain. -/
abbrev causalSource : Ript.Models.FiniteStochastic.Object :=
  Ript.Models.FiniteStochastic.Object.of
    (Ript.Examples.SimpleCausalModel.chainModel.dag.ParentAssignment Bool
      Ript.Examples.SimpleCausalModel.effect)

/-- Hard intervention setting the effect node to `false`. -/
def forceEffectFalse : Intervention 2 Bool :=
  Intervention.doAt Ript.Examples.SimpleCausalModel.effect false

/-- Expose the child's ordinary local mechanism and then erase its output. -/
def causalInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.FiniteStochastic.Object)
      scalarResourceMap where
  obj
    | .source => causalSource
    | .exposed => Ript.Examples.StochasticBits.bit
    | .erased => Ript.Examples.StochasticBits.bit
  mapGen
    | .expose =>
        (Ript.Examples.SimpleCausalModel.chainModel.mechanism
          Ript.Examples.SimpleCausalModel.effect).toFinStoch
    | .erase => eraseBitChannel
  mapGen_cost generator := by
    cases generator <;> exact Nat.zero_le _

/-- Encode the single parent value of the child mechanism. -/
def causalParentInput (value : Bool) : causalSource :=
  fun _ ↦ value

/-! ## Computation -/

/-- Constant-false total program with one step and one gate. -/
def computationErase :
    Ript.Examples.SimpleComputation.totalBit ⟶
      Ript.Examples.SimpleComputation.totalBit :=
  Ript.Models.Computation.Total.mk (fun _ ↦ false)
    (ComputationResource.of 1 0 0 1)

/-- Query/expose the bit, then erase it by a constant program. -/
def computationInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.Computation.Total.Object)
      computationResourceMap where
  obj _ := Ript.Examples.SimpleComputation.totalBit
  mapGen
    | .expose => Ript.Examples.SimpleComputation.totalQuery
    | .erase => computationErase
  mapGen_cost
    | .expose => by
        intro kind
        fin_cases kind <;> decide
    | .erase => by
        intro kind
        fin_cases kind <;> decide

/-! ## Task-relative semantic information -/

/-- Constant observation obtained after discarding the exposed bit. -/
def constantExperiment :
    FinStoch Ript.Examples.SimpleDecision.decisionBit
      Ript.Examples.SimpleDecision.decisionBit :=
  FinStoch.dirac (fun _ : Bool ↦ false)

/-- Perfect observation followed by information-erasing post-processing. -/
def semanticInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.FiniteStochastic.Object)
      scalarResourceMap where
  obj _ := Ript.Examples.SimpleDecision.decisionBit
  mapGen
    | .expose => Ript.Examples.SimpleDecision.perfectExperiment
    | .erase => constantExperiment
  mapGen_cost generator := by
    cases generator <;> exact Nat.zero_le _

/-! ## Work-assisted thermodynamic erasure -/

/-- Zero abstract scalar cost used only by the thermal erasure slice. -/
local instance thermalZeroCost : HasProcessCost ThermalObject Nat :=
  Ript.Examples.CommonBitRealizations.thermalZeroCost

/-- Joint memory--battery object on which exact erasure is Gibbs preserving. -/
abbrev thermalMemoryBattery : ThermalObject :=
  ThermalObject.tensor Ript.Examples.SimpleThermalModel.thermalBit
    Ript.Examples.ExactWorkErasure.workBatteryThermal

/-- Identity exposure followed by the exact work-erasure process. -/
def thermalInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := ThermalObject) scalarResourceMap where
  obj _ := thermalMemoryBattery
  mapGen
    | .expose => GibbsPreserving.identity thermalMemoryBattery
    | .erase => Ript.Examples.ExactWorkErasure.exactWorkErasureProcess
  mapGen_cost generator := by
    cases generator <;> exact Nat.zero_le _

/-! ## Evaluation reductions -/

@[simp]
theorem probability_pipeline_eval :
    ResourceChangingInterpretation.eval probabilityInterpretation
        erasurePipeline =
      FinStoch.comp (FinStoch.identity Ript.Examples.StochasticBits.bit)
        eraseBitChannel :=
  rfl

@[simp]
theorem quantum_pipeline_eval :
    ResourceChangingInterpretation.eval quantumInterpretation erasurePipeline =
      KrausChannel.comp (KrausChannel.identity classicalQubit) quantumReset :=
  rfl

/-- Identity exposure does not change the quantum reset denotation. -/
theorem quantum_pipeline_eq_reset :
    ResourceChangingInterpretation.eval quantumInterpretation erasurePipeline =
      quantumReset := by
  rw [quantum_pipeline_eval]
  apply KrausChannel.ext
  funext ρ
  simp [KrausChannel.comp, KrausChannel.identity,
    KrausChannel.ofOperators]

@[simp]
theorem causal_pipeline_eval :
    ResourceChangingInterpretation.eval causalInterpretation erasurePipeline =
      FinStoch.comp
        (Ript.Examples.SimpleCausalModel.chainModel.mechanism
          Ript.Examples.SimpleCausalModel.effect).toFinStoch
        eraseBitChannel :=
  rfl

@[simp]
theorem computation_pipeline_eval :
    ResourceChangingInterpretation.eval computationInterpretation
        erasurePipeline =
      Ript.Examples.SimpleComputation.totalQuery ≫ computationErase :=
  rfl

@[simp]
theorem semantic_pipeline_eval :
    ResourceChangingInterpretation.eval semanticInterpretation erasurePipeline =
      FinStoch.comp Ript.Examples.SimpleDecision.perfectExperiment
        constantExperiment :=
  rfl

@[simp]
theorem thermal_pipeline_eval :
    ResourceChangingInterpretation.eval thermalInterpretation erasurePipeline =
      GibbsPreserving.comp (GibbsPreserving.identity thermalMemoryBattery)
        Ript.Examples.ExactWorkErasure.exactWorkErasureProcess :=
  rfl

/-- Identity exposure does not change the work-erasure denotation. -/
theorem thermal_pipeline_eq_process :
    ResourceChangingInterpretation.eval thermalInterpretation erasurePipeline =
      Ript.Examples.ExactWorkErasure.exactWorkErasureProcess := by
  rw [thermal_pipeline_eval]
  apply GibbsPreserving.ext
  apply FinStoch.ext
  intro input output
  simp [GibbsPreserving.comp, GibbsPreserving.identity,
    FinStoch.comp, FinStoch.identity]

/-! ## Six model-specific erasure theorems -/

/-- Classical erasure outputs `false` with probability one. -/
theorem probability_erases (value : Bool) :
    (ResourceChangingInterpretation.eval probabilityInterpretation
      erasurePipeline).prob value false = 1 := by
  rw [probability_pipeline_eval]
  change (∑ middle : Bool,
    (if value = middle then (1 : ℚ≥0) else 0) * 1) = 1
  rw [Fintype.sum_bool]
  cases value <;> norm_num

/-- Quantum reset maps every diagonal Boolean basis state to pure `false`. -/
theorem quantum_erases (value : Bool) :
    (ResourceChangingInterpretation.eval quantumInterpretation
      erasurePipeline).applyDensity
        (diagonalDensity (FinDist.pure
          (X := Ript.Examples.StochasticBits.bit) value)) =
      diagonalDensity (FinDist.pure
        (X := Ript.Examples.StochasticBits.bit) false) := by
  rw [quantum_pipeline_eq_reset]
  calc
    quantumReset.applyDensity
        (diagonalDensity (FinDist.pure
          (X := Ript.Examples.StochasticBits.bit) value)) =
      diagonalDensity
        ((FinDist.pure (X := Ript.Examples.StochasticBits.bit) value).push
          eraseBitChannel) :=
      measurementPreparation_diagonalDensity _ _
    _ = diagonalDensity (FinDist.pure
        (X := Ript.Examples.StochasticBits.bit) false) := by
      congr 1
      change FinDist.bind
          (FinDist.pure (X := Ript.Examples.StochasticBits.bit) value)
          (fun _ : Ript.Examples.StochasticBits.bit ↦
            FinDist.pure (X := Ript.Examples.StochasticBits.bit) false) =
        FinDist.pure (X := Ript.Examples.StochasticBits.bit) false
      exact FinDist.pure_bind
        (show Ript.Examples.StochasticBits.bit from value)
        (fun _ : Ript.Examples.StochasticBits.bit ↦
          FinDist.pure (show Ript.Examples.StochasticBits.bit from false))

/-- The causal pipeline erases the child value on every parent input. -/
theorem causal_erases (value : Bool) :
    (ResourceChangingInterpretation.eval causalInterpretation
      erasurePipeline).prob (causalParentInput value) false = 1 := by
  rw [causal_pipeline_eval]
  change (∑ middle : Bool,
    (Ript.Examples.SimpleCausalModel.chainModel.mechanism
      Ript.Examples.SimpleCausalModel.effect).toFinStoch.prob
        (causalParentInput value) middle * 1) = 1
  simp only [mul_one]
  have hnormalized :=
    (Ript.Examples.SimpleCausalModel.chainModel.mechanism
      Ript.Examples.SimpleCausalModel.effect).toFinStoch.normalized
        (causalParentInput value)
  exact hnormalized

/-- The actual hard intervention replaces the child mechanism by pure
`false`, independently of its parents. -/
theorem causal_intervention_replaces_mechanism
    (parents : Ript.Examples.SimpleCausalModel.chainModel.dag.ParentAssignment
      Bool Ript.Examples.SimpleCausalModel.effect) :
    (((Ript.Examples.SimpleCausalModel.chainModel.intervene
      forceEffectFalse).mechanism
        Ript.Examples.SimpleCausalModel.effect).run parents) =
      FinDist.pure false := by
  exact FiniteCausalModel.intervene_same _ _ _ _

/-- The total program always returns `false`. -/
theorem computation_erases (value : Bool) :
    (ResourceChangingInterpretation.eval computationInterpretation
      erasurePipeline).run value = false :=
  rfl

/-- Native computation cost is exactly two steps, one query, and one gate. -/
theorem computation_erasure_cost :
    processCost (R := ComputationResource)
        (ResourceChangingInterpretation.eval computationInterpretation
          erasurePipeline) = ComputationResource.of 2 1 0 1 := by
  rw [computation_pipeline_eval]
  change ComputationResource.of 1 1 0 0 +
      ComputationResource.of 1 0 0 1 = ComputationResource.of 2 1 0 1
  funext kind
  fin_cases kind <;> rfl

/-- The constant experiment is Blackwell equivalent to the independent
uninformative experiment. -/
theorem constant_blackwellEquivalent_uninformative :
    BlackwellEquivalent constantExperiment
      Ript.Examples.SimpleDecision.uninformativeExperiment := by
  constructor
  · refine ⟨Ript.Examples.SimpleDecision.uninformativeExperiment, ?_⟩
    change FinStoch.comp constantExperiment
      Ript.Examples.SimpleDecision.uninformativeExperiment =
        Ript.Examples.SimpleDecision.uninformativeExperiment
    apply FinStoch.ext
    intro state observation
    change Bool at state observation
    change (∑ middle : Bool,
      (if false = middle then (1 : ℚ≥0) else 0) * (1 / 2)) = 1 / 2
    rw [Fintype.sum_bool]
    norm_num
  · refine ⟨constantExperiment, ?_⟩
    change FinStoch.comp Ript.Examples.SimpleDecision.uninformativeExperiment
      constantExperiment = constantExperiment
    apply FinStoch.ext
    intro state observation
    change Bool at state observation
    change (∑ middle : Bool,
      (1 / 2 : ℚ≥0) *
        (if false = observation then 1 else 0)) =
      if false = observation then 1 else 0
    rw [Fintype.sum_bool]
    cases observation <;> norm_num

/-- The semantic pipeline reduces exactly to the constant experiment. -/
theorem semantic_pipeline_eq_constant :
    ResourceChangingInterpretation.eval semanticInterpretation
      erasurePipeline = constantExperiment := by
  rw [semantic_pipeline_eval]
  apply FinStoch.ext
  intro state observation
  simp [Ript.Examples.SimpleDecision.perfectExperiment,
    FinStoch.comp, FinStoch.identity]

/-- Erasing the observation destroys the full `1/2` guessing value. -/
theorem semantic_erasure_value_zero :
    semanticValue Ript.Examples.SimpleDecision.bitGuessing
        Ript.Examples.SimpleDecision.uninformativeExperiment
        (ResourceChangingInterpretation.eval semanticInterpretation
          erasurePipeline) = 0 := by
  calc
    semanticValue Ript.Examples.SimpleDecision.bitGuessing
        Ript.Examples.SimpleDecision.uninformativeExperiment
        (ResourceChangingInterpretation.eval semanticInterpretation
          erasurePipeline) =
      semanticValue Ript.Examples.SimpleDecision.bitGuessing
        Ript.Examples.SimpleDecision.uninformativeExperiment
        constantExperiment := congrArg
          (semanticValue Ript.Examples.SimpleDecision.bitGuessing
            Ript.Examples.SimpleDecision.uninformativeExperiment)
          semantic_pipeline_eq_constant
    _ = semanticValue Ript.Examples.SimpleDecision.bitGuessing
        Ript.Examples.SimpleDecision.uninformativeExperiment
        Ript.Examples.SimpleDecision.uninformativeExperiment :=
      semanticValue_eq_of_equivalent
        Ript.Examples.SimpleDecision.bitGuessing
        Ript.Examples.SimpleDecision.uninformativeExperiment
        constant_blackwellEquivalent_uninformative
    _ = 0 := semanticValue_baseline _ _

/-- The work-assisted thermal process exactly erases fair memory while
discharging the pure high battery. -/
theorem thermal_erases :
    (Ript.Examples.SimpleThermalModel.fairEquilibrium.tensor
      Ript.Examples.ExactWorkErasure.batteryHigh).push
        (ResourceChangingInterpretation.eval thermalInterpretation
          erasurePipeline).channel =
      Ript.Examples.SimpleThermalModel.erasedBit.tensor
        Ript.Examples.ExactWorkErasure.batteryLow := by
  have hchannel := congrArg GibbsPreserving.channel
    thermal_pipeline_eq_process
  rw [hchannel]
  exact Ript.Examples.ExactWorkErasure.exactWorkErasureChannel_erases

/-- At inverse temperature one, the entropy-neutral battery pays exactly
`log 2` and saturates the mechanical Landauer bound. -/
theorem thermal_erasure_landauer_saturation :
    (Ript.Examples.ExactWorkErasure.exactWorkErasure 1 (by norm_num)).systemFreeEnergyIncrease =
      (Ript.Examples.ExactWorkErasure.exactWorkErasure 1 (by norm_num)).batteryEnergyDecrease :=
  Ript.Examples.ExactWorkErasure.exactWorkErasure_saturates_landauer_work
    1 (by norm_num)

/-- One proposition packages operational erasure, causal intervention,
semantic information loss, exact computation resources, and Landauer payment. -/
structure SixModelErasureAgreement : Prop where
  probability : ∀ value : Bool,
    (ResourceChangingInterpretation.eval probabilityInterpretation
      erasurePipeline).prob value false = 1
  quantum : ∀ value : Bool,
    (ResourceChangingInterpretation.eval quantumInterpretation
      erasurePipeline).applyDensity
        (diagonalDensity (FinDist.pure
          (X := Ript.Examples.StochasticBits.bit) value)) =
      diagonalDensity (FinDist.pure
        (X := Ript.Examples.StochasticBits.bit) false)
  causal : ∀ value : Bool,
    (ResourceChangingInterpretation.eval causalInterpretation
      erasurePipeline).prob (causalParentInput value) false = 1
  causalIntervention : ∀ parents,
    (((Ript.Examples.SimpleCausalModel.chainModel.intervene
      forceEffectFalse).mechanism
        Ript.Examples.SimpleCausalModel.effect).run parents) =
      FinDist.pure false
  computation : ∀ value : Bool,
    (ResourceChangingInterpretation.eval computationInterpretation
      erasurePipeline).run value = false
  computationCost :
    processCost (R := ComputationResource)
        (ResourceChangingInterpretation.eval computationInterpretation
          erasurePipeline) = ComputationResource.of 2 1 0 1
  semantic :
    semanticValue Ript.Examples.SimpleDecision.bitGuessing
        Ript.Examples.SimpleDecision.uninformativeExperiment
        (ResourceChangingInterpretation.eval semanticInterpretation
          erasurePipeline) = 0
  thermal :
    (Ript.Examples.SimpleThermalModel.fairEquilibrium.tensor
      Ript.Examples.ExactWorkErasure.batteryHigh).push
        (ResourceChangingInterpretation.eval thermalInterpretation
          erasurePipeline).channel =
      Ript.Examples.SimpleThermalModel.erasedBit.tensor
        Ript.Examples.ExactWorkErasure.batteryLow
  landauer :
    (Ript.Examples.ExactWorkErasure.exactWorkErasure 1 (by norm_num)).systemFreeEnergyIncrease =
      (Ript.Examples.ExactWorkErasure.exactWorkErasure 1 (by norm_num)).batteryEnergyDecrease

/-- **Six-model operational erasure agreement theorem.** -/
theorem sixModelErasureAgreement : SixModelErasureAgreement where
  probability := probability_erases
  quantum := quantum_erases
  causal := causal_erases
  causalIntervention := causal_intervention_replaces_mechanism
  computation := computation_erases
  computationCost := computation_erasure_cost
  semantic := semantic_erasure_value_zero
  thermal := thermal_erases
  landauer := thermal_erasure_landauer_saturation

end Ript.Examples.OperationalErasureRealizations
