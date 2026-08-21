import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Ript.Examples.CommonBitRealizations
import Ript.Examples.QubitInstrument
import Ript.Models.Computation.Randomized.Monoidal
import Ript.Models.Quantum.ClassicalEmbedding
import Ript.Models.Quantum.Monoidal
import Ript.Models.Thermal.Monoidal
import Ript.Semantics.ResourceChangingMonoidalInitiality

/-!
# One exact noisy Boolean process in six models

The common generator is a binary symmetric channel with flip probability
`1/4`.  It is interpreted as an exact stochastic channel, a genuine coherent
random-unitary quantum channel, a noisy causal mechanism, a randomized program
with four-dimensional resources, a task-relative experiment, and a
Gibbs-preserving thermal process.
-/

set_option autoImplicit false

namespace Ript.Examples.NoisyBitRealizations

open CategoryTheory
open Ript.Core
open Ript.Models.Causal
open Ript.Models.Computation
open Ript.Models.Decision.SemanticValue
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic
open Ript.Models.Quantum
open Ript.Models.Quantum.ClassicalEmbedding
open Ript.Models.Thermal
open Ript.Semantics
open Ript.Syntax
open scoped BigOperators ComplexConjugate ComplexOrder

/-! ## Common syntax -/

/-- Input and output interfaces of the noisy process. -/
inductive Wire where
  | input
  | output
  deriving DecidableEq, Repr

/-- One primitive exact noisy channel. -/
inductive Generator : FreeMonoidalCategory Wire → FreeMonoidalCategory Wire → Type where
  | noise : Generator (.of .input) (.of .output)

/-- Unit-cost symmetric monoidal noise signature. -/
def signature : MonoidalSignature Nat where
  Wire := Wire
  Gen := Generator
  cost
    | .noise => 1

/-- One noisy process expression. -/
def noiseExpr : MonoidalExpr signature (.of .input) (.of .output) :=
  .gen .noise

/-- Two independent noisy processes. -/
def parallelNoiseExpr :
    MonoidalExpr signature
      (.tensor (.of .input) (.of .input))
      (.tensor (.of .output) (.of .output)) :=
  .tensor (.gen .noise) (.gen .noise)

@[simp]
theorem noiseExpr_cost : noiseExpr.syntaxCost = 1 := rfl

@[simp]
theorem parallelNoiseExpr_cost : parallelNoiseExpr.syntaxCost = 2 := rfl

/-! ## Exact stochastic noise -/

/-- Exact binary symmetric channel with crossover probability `1/4`. -/
def quarterNoise :
    FinStoch Ript.Examples.StochasticBits.bit
      Ript.Examples.StochasticBits.bit where
  prob input output := if output = input then 3 / 4 else 1 / 4
  normalized input := by
    change Bool at input
    cases input <;> simp <;> norm_num

@[simp]
theorem quarterNoise_apply (input output : Bool) :
    quarterNoise.prob input output =
      if output = input then 3 / 4 else 1 / 4 :=
  rfl

/-- Exact probabilistic interpretation. -/
def probabilityInterpretation :
    ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.FiniteStochastic.Object)
      (OrderAddMonoidHom.id Nat) where
  wire _ := Ript.Examples.StochasticBits.bit
  mapGen
    | .noise => quarterNoise
  mapGen_cost
    | .noise => Nat.zero_le 1

/-! ## Random-unitary quantum noise -/

/-- Probability assigned to the identity or Pauli-X branch. -/
def quantumBranchWeight (branch : Bool) : ℚ≥0 :=
  if branch then 1 / 4 else 3 / 4

@[simp]
theorem probabilityAmplitude_mul_starRingEnd (p : ℚ≥0) :
    probabilityAmplitude p *
      (starRingEnd ℂ) (probabilityAmplitude p) = (p : ℂ) :=
  probabilityAmplitude_mul_star p

@[simp]
theorem starRingEnd_probabilityAmplitude_mul (p : ℚ≥0) :
    (starRingEnd ℂ) (probabilityAmplitude p) *
      probabilityAmplitude p = (p : ℂ) :=
  probabilityAmplitude_star_mul p

/-- Weighted identity or Pauli-X Kraus operator. -/
noncomputable def quantumNoiseOperator (branch : Bool) :
    Matrix Ript.Examples.QubitChannel.qubit
      Ript.Examples.QubitChannel.qubit ℂ :=
  fun row column ↦
    probabilityAmplitude (quantumBranchWeight branch) *
      if branch then Ript.Examples.QubitChannel.bitFlipOperator row column
      else (1 : Matrix Ript.Examples.QubitChannel.qubit
        Ript.Examples.QubitChannel.qubit ℂ) row column

theorem quantumNoiseOperator_complete :
    (∑ branch : Bool,
      Matrix.conjTranspose (quantumNoiseOperator branch) *
        quantumNoiseOperator branch) = 1 := by
  ext row column
  change Bool at row column
  cases row <;> cases column <;>
    rw [Fintype.sum_bool] <;>
    simp [quantumNoiseOperator, quantumBranchWeight,
      Ript.Examples.QubitChannel.bitFlipOperator, Matrix.mul_apply,
      Matrix.one_apply, starRingEnd_probabilityAmplitude_mul] <;>
    norm_num

/-- Genuine random-unitary qubit noise; unlike measurement--preparation it
does not dephase before applying the stochastic bit flip. -/
noncomputable def quantumNoise :
    KrausChannel Ript.Examples.QubitChannel.qubit
      Ript.Examples.QubitChannel.qubit :=
  KrausChannel.ofOperators quantumNoiseOperator quantumNoiseOperator_complete

/-- Coherent random-unitary quantum interpretation. -/
noncomputable def quantumInterpretation :
    ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.Quantum.Object)
      (OrderAddMonoidHom.id Nat) where
  wire _ := Ript.Examples.QubitChannel.qubit
  mapGen
    | .noise => quantumNoise
  mapGen_cost
    | .noise => Nat.zero_le 1

theorem quantumNoise_basis_diagonal (input output : Bool) :
    (quantumNoise.applyDensity
      (Ript.Examples.QubitChannel.basisDensity input)).matrix output output =
        if output = input then (3 : ℂ) / 4 else (1 : ℂ) / 4 := by
  change Bool at input output
  cases input <;> cases output <;>
    simp [quantumNoise, quantumNoiseOperator, quantumBranchWeight,
      KrausChannel.ofOperators, Ript.Examples.QubitChannel.bitFlipOperator,
      Ript.Examples.QubitChannel.basisDensity, Matrix.mul_apply,
      Matrix.diagonal_apply, probabilityAmplitude_mul_starRingEnd]

/-- Random-unitary bit-flip noise preserves the coherent plus state exactly. -/
theorem quantumNoise_plus_fixed :
    quantumNoise.applyDensity Ript.Examples.QubitInstrument.plusDensity =
      Ript.Examples.QubitInstrument.plusDensity := by
  apply DensityMatrix.ext
  ext row column
  change Bool at row column
  cases row <;> cases column <;>
    simp [quantumNoise, quantumNoiseOperator, quantumBranchWeight,
      KrausChannel.ofOperators, Ript.Examples.QubitChannel.bitFlipOperator,
      Ript.Examples.QubitInstrument.plusDensity,
      Ript.Examples.QubitInstrument.plusProjector,
      Ript.Examples.QubitInstrument.plusVector,
      Matrix.mul_apply, Matrix.vecMulVec_apply,
      probabilityAmplitude_mul_starRingEnd] <;>
    norm_num

/-- The random-unitary channel retains the plus-state off-diagonal coherence. -/
theorem quantumNoise_plus_offDiagonal :
    (quantumNoise.applyDensity
      Ript.Examples.QubitInstrument.plusDensity).matrix false true =
        (2 : ℂ)⁻¹ := by
  rw [quantumNoise_plus_fixed]
  exact Ript.Examples.QubitInstrument.plusDensity_entry false true

/-- The classical measurement--preparation realization of the same BSC
removes that off-diagonal coherence. -/
theorem classicalNoise_plus_offDiagonal_zero :
    (measurementPreparation quarterNoise).map
        Ript.Examples.QubitInstrument.plusDensity.matrix false true = 0 := by
  rw [measurementPreparation_map_apply]
  simp

/-- The two quantum realizations of the same classical BSC are operationally
distinct on coherent input. -/
theorem randomUnitary_ne_measurementPreparation_on_plus :
    (quantumNoise.applyDensity
      Ript.Examples.QubitInstrument.plusDensity).matrix false true ≠
      (measurementPreparation quarterNoise).map
        Ript.Examples.QubitInstrument.plusDensity.matrix false true := by
  rw [quantumNoise_plus_offDiagonal,
    classicalNoise_plus_offDiagonal_zero]
  norm_num

/-! ## Noisy causal mechanism -/

/-- Local child mechanism with exact quarter crossover noise. -/
def causalNoiseMechanism :
    Mechanism Ript.Examples.SimpleCausalModel.chainDAG Bool
      Ript.Examples.SimpleCausalModel.effect where
  run parents :=
    { prob := fun output ↦
        if output =
            parents ⟨Ript.Examples.SimpleCausalModel.cause, by
              simp [Ript.Examples.SimpleCausalModel.chainDAG,
                Ript.Examples.SimpleCausalModel.cause,
                Ript.Examples.SimpleCausalModel.effect]⟩
          then 3 / 4 else 1 / 4
      normalized := by
        rw [Fintype.sum_bool]
        let parentValue : Bool :=
          parents ⟨Ript.Examples.SimpleCausalModel.cause, by
            simp [Ript.Examples.SimpleCausalModel.chainDAG,
              Ript.Examples.SimpleCausalModel.cause,
              Ript.Examples.SimpleCausalModel.effect]⟩
        change (if true = parentValue then 3 / 4 else 1 / 4) +
          (if false = parentValue then 3 / 4 else 1 / 4) = 1
        cases parentValue <;> norm_num }

/-- Causal-mechanism interpretation. -/
def causalInterpretation :
    ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.FiniteStochastic.Object)
      (OrderAddMonoidHom.id Nat) where
  wire
    | .input => Ript.Examples.CommonBitRealizations.causalInput
    | .output => Ript.Examples.StochasticBits.bit
  mapGen
    | .noise => causalNoiseMechanism.toFinStoch
  mapGen_cost
    | .noise => Nat.zero_le 1

/-! ## Randomized computation -/

/-- Boolean interface in randomized computation. -/
abbrev randomizedBit : Ript.Models.Computation.Randomized.Object :=
  ⟨Ript.Examples.StochasticBits.bit⟩

/-- One scalar syntax unit becomes one step, query, and gate. -/
def noiseComputationResourceMap : Nat →+o ComputationResource where
  toFun units := ComputationResource.of units units 0 units
  map_zero' := by funext kind; fin_cases kind <;> rfl
  map_add' left right := by
    funext kind
    fin_cases kind <;> simp [ComputationResource.of]
  monotone' left right less kind := by
    fin_cases kind <;> simp [ComputationResource.of, less]

/-- Exact randomized BSC program with its native resource vector. -/
def randomizedNoiseProgram : randomizedBit ⟶ randomizedBit :=
  ⟨quarterNoise, ComputationResource.of 1 1 0 1⟩

/-- Four-resource randomized-computation interpretation. -/
def computationInterpretation :
    ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature)
      (C := Ript.Models.Computation.Randomized.Object)
      noiseComputationResourceMap where
  wire _ := randomizedBit
  mapGen
    | .noise => randomizedNoiseProgram
  mapGen_cost
    | .noise => le_rfl

/-! ## Semantic and thermal interpretations -/

/-- Task-semantic experiment interpretation. -/
def semanticInterpretation :
    ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.FiniteStochastic.Object)
      (OrderAddMonoidHom.id Nat) where
  wire _ := Ript.Examples.SimpleDecision.decisionBit
  mapGen
    | .noise => quarterNoise
  mapGen_cost
    | .noise => Nat.zero_le 1

/-- Gibbs-preserving thermal BSC. -/
def thermalNoise :
    GibbsPreserving Ript.Examples.SimpleThermalModel.thermalBit
      Ript.Examples.SimpleThermalModel.thermalBit where
  channel := quarterNoise
  preserves_equilibrium := by
    apply FinDist.ext
    intro output
    change Bool at output
    change (∑ input : Bool, (1 : ℚ≥0) / 2 *
      (if output = input then 3 / 4 else 1 / 4)) = 1 / 2
    cases output <;> rw [Fintype.sum_bool] <;> norm_num

/-- Thermodynamic interpretation. -/
def thermalInterpretation :
    ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := ThermalObject)
      (OrderAddMonoidHom.id Nat) where
  wire _ := Ript.Examples.SimpleThermalModel.thermalBit
  mapGen
    | .noise => thermalNoise
  mapGen_cost
    | .noise => Nat.zero_le 1

/-! ## Six-model observables -/

theorem probability_noise (input output : Bool) :
    (ResourceChangingMonoidalInterpretation.eval probabilityInterpretation
      noiseExpr).prob input output =
        if output = input then 3 / 4 else 1 / 4 :=
  rfl

theorem quantum_noise (input output : Bool) :
    ((ResourceChangingMonoidalInterpretation.eval quantumInterpretation
      noiseExpr).applyDensity
        (Ript.Examples.QubitChannel.basisDensity input)).matrix output output =
      if output = input then (3 : ℂ) / 4 else (1 : ℂ) / 4 :=
  quantumNoise_basis_diagonal input output

theorem causal_noise (input output : Bool) :
    (ResourceChangingMonoidalInterpretation.eval causalInterpretation
      noiseExpr).prob
        (Ript.Examples.CommonBitRealizations.causalParentInput input) output =
      if output = input then 3 / 4 else 1 / 4 := by
  change (causalNoiseMechanism.run
    (Ript.Examples.CommonBitRealizations.causalParentInput input)).prob output = _
  rfl

theorem computation_noise (input output : Bool) :
    Ript.Models.Computation.Randomized.probability
      (ResourceChangingMonoidalInterpretation.eval computationInterpretation
        noiseExpr) input output =
      if output = input then 3 / 4 else 1 / 4 :=
  rfl

theorem computation_noise_cost :
    processCost (R := ComputationResource)
        (ResourceChangingMonoidalInterpretation.eval computationInterpretation
          noiseExpr) = noiseComputationResourceMap 1 :=
  rfl

theorem computation_parallel_noise_cost :
    processCost (R := ComputationResource)
        (ResourceChangingMonoidalInterpretation.eval computationInterpretation
          parallelNoiseExpr) = noiseComputationResourceMap 2 := by
  change randomizedNoiseProgram.resource + randomizedNoiseProgram.resource = _
  funext kind
  fin_cases kind <;> rfl

theorem semantic_noise (input output : Bool) :
    (ResourceChangingMonoidalInterpretation.eval semanticInterpretation
      noiseExpr).prob input output =
      if output = input then 3 / 4 else 1 / 4 :=
  rfl

theorem thermal_noise (input output : Bool) :
    (ResourceChangingMonoidalInterpretation.eval thermalInterpretation
      noiseExpr).channel.prob input output =
      if output = input then 3 / 4 else 1 / 4 :=
  rfl

/-- Exact posterior loss mass for every observation/action pair. -/
theorem semanticNoise_actionRisk (observation action : Bool) :
    Ript.Models.Decision.FiniteRisk.actionRiskMass
      Ript.Examples.SimpleDecision.bitGuessing quarterNoise
        observation action =
      if action = observation then (1 : ℚ≥0) / 8 else 3 / 8 := by
  change Bool at observation
  cases observation <;> cases action <;>
    rw [Ript.Models.Decision.FiniteRisk.actionRiskMass,
      Fintype.sum_bool] <;>
    norm_num [
      Ript.Examples.SimpleDecision.bitGuessing,
      Ript.Examples.SimpleDecision.uniformBitPrior,
      Ript.Examples.SimpleDecision.decisionBit,
      quarterNoise]
  all_goals simp

/-- Each observation contributes exact optimal posterior loss mass `1/8`. -/
theorem semanticNoise_optimalActionRisk (observation : Bool) :
    Ript.Models.Decision.FiniteRisk.optimalActionRisk
      Ript.Examples.SimpleDecision.bitGuessing quarterNoise observation =
        (1 : ℚ≥0) / 8 := by
  apply le_antisymm
  · calc
      Ript.Models.Decision.FiniteRisk.optimalActionRisk
          Ript.Examples.SimpleDecision.bitGuessing quarterNoise observation ≤
        Ript.Models.Decision.FiniteRisk.actionRiskMass
          Ript.Examples.SimpleDecision.bitGuessing quarterNoise
            observation observation :=
        Ript.Models.Decision.FiniteRisk.optimalActionRisk_le_actionRisk
          _ _ _ _
      _ = (1 : ℚ≥0) / 8 := by rw [semanticNoise_actionRisk]; simp
  · apply Finset.le_min'
    intro risk member
    rcases Finset.mem_image.mp member with ⟨action, _, rfl⟩
    rw [semanticNoise_actionRisk]
    split_ifs
    · exact le_rfl
    · exact_mod_cast (show (1 : ℚ) / 8 ≤ 3 / 8 by norm_num)

/-- The noisy experiment has exact optimal Boolean guessing risk `1/4`. -/
theorem semanticNoise_quarter_risk :
    Ript.Models.Decision.FiniteRisk.finiteBayesRisk
      Ript.Examples.SimpleDecision.bitGuessing quarterNoise =
        (1 : ℚ≥0) / 4 := by
  rw [Ript.Models.Decision.FiniteRisk.finiteBayesRisk]
  simp_rw [semanticNoise_optimalActionRisk]
  rw [Fintype.sum_bool]
  norm_num

/-- Relative to no information, quarter-flip noise retains exact semantic
value `1/4`. -/
theorem semanticNoise_quarter_value :
    semanticValue Ript.Examples.SimpleDecision.bitGuessing
        Ript.Examples.SimpleDecision.uninformativeExperiment quarterNoise =
      (1 : ℚ≥0) / 4 := by
  rw [semanticValue,
    Ript.Examples.SimpleDecision.uninformative_information_half_risk,
    semanticNoise_quarter_risk]
  have less : (1 : ℚ≥0) / 4 ≤ (1 : ℚ≥0) / 2 := by
    exact_mod_cast (show (1 : ℚ) / 4 ≤ 1 / 2 by norm_num)
  rw [tsub_eq_iff_eq_add_of_le less]
  norm_num

/-- **Six-model exact noise agreement.** -/
theorem sixModelNoiseAgreement :
    (∀ input output : Bool,
      (ResourceChangingMonoidalInterpretation.eval probabilityInterpretation
        noiseExpr).prob input output =
          if output = input then 3 / 4 else 1 / 4) ∧
    (∀ input output : Bool,
      ((ResourceChangingMonoidalInterpretation.eval quantumInterpretation
        noiseExpr).applyDensity
          (Ript.Examples.QubitChannel.basisDensity input)).matrix output output =
        if output = input then (3 : ℂ) / 4 else (1 : ℂ) / 4) ∧
    (∀ input output : Bool,
      (ResourceChangingMonoidalInterpretation.eval causalInterpretation
        noiseExpr).prob
          (Ript.Examples.CommonBitRealizations.causalParentInput input) output =
        if output = input then 3 / 4 else 1 / 4) ∧
    (∀ input output : Bool,
      Ript.Models.Computation.Randomized.probability
        (ResourceChangingMonoidalInterpretation.eval computationInterpretation
          noiseExpr) input output =
        if output = input then 3 / 4 else 1 / 4) ∧
    (∀ input output : Bool,
      (ResourceChangingMonoidalInterpretation.eval semanticInterpretation
        noiseExpr).prob input output =
        if output = input then 3 / 4 else 1 / 4) ∧
    (∀ input output : Bool,
      (ResourceChangingMonoidalInterpretation.eval thermalInterpretation
        noiseExpr).channel.prob input output =
        if output = input then 3 / 4 else 1 / 4) :=
  ⟨probability_noise, quantum_noise, causal_noise, computation_noise,
    semantic_noise, thermal_noise⟩

/-! ## Canonical free lifts -/

/-- Canonical strong symmetric probability lift. -/
noncomputable def probabilityFreeLift :=
  ResourceChangingMonoidalFree.lift probabilityInterpretation

/-- Canonical strong symmetric quantum lift. -/
noncomputable def quantumFreeLift :=
  ResourceChangingMonoidalFree.lift quantumInterpretation

/-- Canonical strong symmetric causal lift. -/
noncomputable def causalFreeLift :=
  ResourceChangingMonoidalFree.lift causalInterpretation

/-- Canonical strong symmetric randomized-computation lift. -/
noncomputable def computationFreeLift :=
  ResourceChangingMonoidalFree.lift computationInterpretation

/-- Canonical strong symmetric semantic lift. -/
noncomputable def semanticFreeLift :=
  ResourceChangingMonoidalFree.lift semanticInterpretation

/-- Canonical strong symmetric thermal lift. -/
noncomputable def thermalFreeLift :=
  ResourceChangingMonoidalFree.lift thermalInterpretation

theorem sixModelNoiseFreeLiftOnGenerator :
    probabilityFreeLift.toFunctor.map
        (MonoidalTermModel.quote signature (.gen .noise)) =
          probabilityInterpretation.mapGen .noise ∧
    quantumFreeLift.toFunctor.map
        (MonoidalTermModel.quote signature (.gen .noise)) =
          quantumInterpretation.mapGen .noise ∧
    causalFreeLift.toFunctor.map
        (MonoidalTermModel.quote signature (.gen .noise)) =
          causalInterpretation.mapGen .noise ∧
    computationFreeLift.toFunctor.map
        (MonoidalTermModel.quote signature (.gen .noise)) =
          computationInterpretation.mapGen .noise ∧
    semanticFreeLift.toFunctor.map
        (MonoidalTermModel.quote signature (.gen .noise)) =
          semanticInterpretation.mapGen .noise ∧
    thermalFreeLift.toFunctor.map
        (MonoidalTermModel.quote signature (.gen .noise)) =
          thermalInterpretation.mapGen .noise :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Ript.Examples.NoisyBitRealizations
