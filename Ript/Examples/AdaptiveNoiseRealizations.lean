import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Ript.Examples.NoisyBitRealizations
import Ript.Syntax.Branching

/-!
# One adaptive multi-generator noise tree in six models

This file advances the common one-generator noise example to a genuine finite
branching protocol.  The first node performs quarter-flip noise.  Its observed
outcome selects either another quarter-flip node or a half-flip node.  Complete
histories are retained, so the same four-branch normal form can be compared
exactly across probability, quantum, causal, randomized-computation, semantic,
and thermal realizations.
-/

set_option autoImplicit false

namespace Ript.Examples.AdaptiveNoiseRealizations

open CategoryTheory
open scoped BigOperators ComplexConjugate ComplexOrder

open Ript.Core
open Ript.Models.Causal
open Ript.Models.Computation
open Ript.Models.Decision.FiniteRisk
open Ript.Models.Decision.SemanticValue
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic
open Ript.Models.Quantum
open Ript.Models.Quantum.ClassicalEmbedding
open Ript.Models.Thermal
open Ript.Syntax.Branching

/-! ## Common executable branching language -/

/-- Two operationally distinct primitive noise generators. -/
inductive NoiseGenerator where
  | quarterFlip
  | halfFlip
  deriving DecidableEq, Repr

/-- Quarter noise costs one unit; half noise costs two. -/
def noiseCost : CostModel NoiseGenerator where
  cost
    | .quarterFlip => 1
    | .halfFlip => 2

/-- Exact outcome weight of either primitive random flip. -/
def noiseWeight : NoiseGenerator → Bool → ℚ≥0
  | .quarterFlip, false => 3 / 4
  | .quarterFlip, true => 1 / 4
  | .halfFlip, _ => 1 / 2

/-- Both generators update the residual bit by the recorded flip outcome. -/
def flipTransition (_ : NoiseGenerator) (outcome input : Bool) : Bool :=
  xor input outcome

/-- Strictly positive exact branch semantics for the two noise generators. -/
def noiseSemantics : Semantics NoiseGenerator Bool where
  weight := noiseWeight
  normalized generator := by
    cases generator <;> rw [Fintype.sum_bool] <;>
      norm_num [noiseWeight]
  positive generator outcome := by
    cases generator <;> cases outcome <;> norm_num [noiseWeight]
  transition := flipTransition

/-- A depth-two adaptive tree.  A non-flip selects another quarter-flip node;
a flip selects the distinct half-flip generator. -/
def adaptiveProtocol : Tree NoiseGenerator 2 :=
  .node .quarterFlip fun first ↦
    .node (if first then .halfFlip else .quarterFlip) fun _ ↦ .leaf

/-- The common four-history carrier of the adaptive protocol. -/
abbrev ProtocolHistory := History 2

/-- Construct one concrete two-bit history. -/
def history (first second : Bool) : ProtocolHistory :=
  ⟨first, second, PUnit.unit⟩

/-- The complete history space is finite and has exactly four elements. -/
theorem protocolHistory_card : Fintype.card ProtocolHistory = 4 := by
  decide

@[simp]
theorem adaptiveProtocol_budget : adaptiveProtocol.budget noiseCost = 3 := by
  decide

@[simp]
theorem adaptiveProtocol_historyCost_false (second : Bool) :
    adaptiveProtocol.historyCost noiseCost (history false second) = 2 :=
  rfl

@[simp]
theorem adaptiveProtocol_historyCost_true (second : Bool) :
    adaptiveProtocol.historyCost noiseCost (history true second) = 3 :=
  rfl

/-- Exact probability of the `00` branch. -/
@[simp]
theorem historyProbability_false_false :
    adaptiveProtocol.historyProbability noiseSemantics
        (history false false) = 9 / 16 := by
  change (3 / 4 : ℚ≥0) * (3 / 4 * 1) = 9 / 16
  norm_num

/-- Exact probability of the `01` branch. -/
@[simp]
theorem historyProbability_false_true :
    adaptiveProtocol.historyProbability noiseSemantics
        (history false true) = 3 / 16 := by
  change (3 / 4 : ℚ≥0) * (1 / 4 * 1) = 3 / 16
  norm_num

/-- Exact probability of the `10` branch. -/
@[simp]
theorem historyProbability_true_false :
    adaptiveProtocol.historyProbability noiseSemantics
        (history true false) = 1 / 8 := by
  change (1 / 4 : ℚ≥0) * (1 / 2 * 1) = 1 / 8
  norm_num

/-- Exact probability of the `11` branch. -/
@[simp]
theorem historyProbability_true_true :
    adaptiveProtocol.historyProbability noiseSemantics
        (history true true) = 1 / 8 := by
  change (1 / 4 : ℚ≥0) * (1 / 2 * 1) = 1 / 8
  norm_num

/-- The four exact adaptive branch probabilities normalize to one. -/
theorem adaptiveProtocol_history_normalized :
    ∑ protocolHistory,
      adaptiveProtocol.historyProbability noiseSemantics protocolHistory = 1 :=
  adaptiveProtocol.historyProbability_normalized noiseSemantics

/-- Final state is the input bit flipped by both recorded outcomes. -/
theorem adaptiveProtocol_finalState (input first second : Bool) :
    adaptiveProtocol.finalState noiseSemantics input (history first second) =
      xor (xor input first) second :=
  rfl

/-! ## Probability representation and completeness -/

/-- Exact history-recording stochastic execution of the adaptive tree. -/
def probabilityProtocol :
    FinStoch (Object.of Bool) (Object.of (ProtocolHistory × Bool)) :=
  adaptiveProtocol.run noiseSemantics

/-- Every stochastic entry is represented by its unique finite branch normal
form. -/
theorem probabilityProtocol_branch_representation
    (input first second output : Bool) :
    probabilityProtocol.prob input (history first second, output) =
      if xor (xor input first) second = output
        then adaptiveProtocol.historyProbability noiseSemantics
          (history first second)
        else 0 := by
  rw [probabilityProtocol, Tree.run_apply,
    adaptiveProtocol_finalState]

/-- The abstract representation theorem specializes to this multi-generator
adaptive protocol. -/
theorem probabilityProtocol_representation :
    probabilityProtocol =
      (adaptiveProtocol.normalForm noiseSemantics).toFinStoch :=
  rfl

/-- Two depth-two trees in this semantics are observationally equal exactly
when their canonical finite branch tables are equal. -/
theorem probabilityProtocol_completeness
    {first second : Tree NoiseGenerator 2} :
    first.run noiseSemantics = second.run noiseSemantics ↔
      first.normalForm noiseSemantics = second.normalForm noiseSemantics :=
  Tree.observationalCompleteness noiseSemantics

/-! ## Reversible decoding of recorded noise -/

/-- Recover the original bit from the final bit and complete flip history. -/
def decodeHistory (result : ProtocolHistory × Bool) : Bool :=
  xor (xor result.2 result.1.1) result.1.2.1

/-- Decoding the represented output recovers the input exactly. -/
@[simp]
theorem decodeHistory_finalState (input first second : Bool) :
    decodeHistory
        (history first second,
          adaptiveProtocol.finalState noiseSemantics input
            (history first second)) = input := by
  cases input <;> cases first <;> cases second <;> rfl

/-- Keeping the complete noise history makes the stochastic protocol exactly
reversible by deterministic post-processing. -/
theorem probabilityProtocol_decode :
    FinStoch.comp probabilityProtocol (FinStoch.dirac decodeHistory) =
      FinStoch.identity (Object.of Bool) := by
  apply adaptiveProtocol.run_comp_dirac_of_decode noiseSemantics decodeHistory
  intro input protocolHistory
  rcases protocolHistory with ⟨first, second, historyTail⟩
  cases historyTail
  exact decodeHistory_finalState input first second

/-! ## Randomized computation -/

/-- The adaptive protocol as one randomized program.  Its vector records the
worst-case three primitive units and the two stored outcome bits. -/
def randomizedProtocol :
    Ript.Models.Computation.Randomized.Object.of Bool ⟶
      Ript.Models.Computation.Randomized.Object.of
        (ProtocolHistory × Bool) :=
  ⟨probabilityProtocol, ComputationResource.of 3 3 2 3⟩

@[simp]
theorem randomizedProtocol_resource :
    processCost (R := ComputationResource) randomizedProtocol =
      ComputationResource.of 3 3 2 3 :=
  rfl

/-- The randomized program's scalar worst-case charge is exactly the common
tree budget. -/
theorem randomizedProtocol_steps_eq_budget :
    randomizedProtocol.resource .steps = adaptiveProtocol.budget noiseCost :=
  rfl

/-- The exact budget checker accepts the protocol at its declared vector. -/
theorem randomizedProtocol_within_declared_budget :
    Ript.Models.Computation.Randomized.withinBudget
      (ComputationResource.of 3 3 2 3) randomizedProtocol = true := by
  decide

/-! ## Coherent quantum-instrument-tree realization -/

/-- Weighted identity/Pauli-X operator for an arbitrary exact binary random
flip. -/
noncomputable def randomFlipOperator
    (weight : Bool → ℚ≥0) (branch : Bool) :
    Matrix Ript.Examples.QubitChannel.qubit
      Ript.Examples.QubitChannel.qubit ℂ :=
  fun row column ↦
    probabilityAmplitude (weight branch) *
      if branch then Ript.Examples.QubitChannel.bitFlipOperator row column
      else (1 : Matrix Ript.Examples.QubitChannel.qubit
        Ript.Examples.QubitChannel.qubit ℂ) row column

/-- Normalized binary weights give a complete random-unitary Kraus family. -/
theorem randomFlipOperator_complete
    (weight : Bool → ℚ≥0)
    (normalized : ∑ branch, weight branch = 1) :
    (∑ branch : Bool,
      Matrix.conjTranspose (randomFlipOperator weight branch) *
        randomFlipOperator weight branch) = 1 := by
  have normalizedComplex :
      (weight false : ℂ) + (weight true : ℂ) = 1 := by
    rw [Fintype.sum_bool] at normalized
    have reordered : weight false + weight true = 1 := by
      simpa [add_comm] using normalized
    exact_mod_cast reordered
  ext row column
  change Bool at row column
  cases row <;> cases column <;>
    rw [Fintype.sum_bool] <;>
    simp [randomFlipOperator,
      Ript.Examples.QubitChannel.bitFlipOperator, Matrix.mul_apply,
      Matrix.one_apply,
      Ript.Examples.NoisyBitRealizations.starRingEnd_probabilityAmplitude_mul] <;>
    simpa [add_comm] using normalizedComplex

/-- Random-unitary channel generated by exact binary weights. -/
noncomputable def randomFlipChannel
    (weight : Bool → ℚ≥0)
    (normalized : ∑ branch, weight branch = 1) :
    KrausChannel Ript.Examples.QubitChannel.qubit
      Ript.Examples.QubitChannel.qubit :=
  KrausChannel.ofOperators (randomFlipOperator weight)
    (randomFlipOperator_complete weight normalized)

/-- One unnormalized random-unitary branch. -/
noncomputable def randomFlipOperation
    (weight : Bool → ℚ≥0) (branch : Bool) :
    KrausOperation Ript.Examples.QubitChannel.qubit
      Ript.Examples.QubitChannel.qubit :=
  KrausOperation.ofOperators (I := PUnit)
    (fun _ ↦ randomFlipOperator weight branch)

/-- Instrument exposing the random-unitary branch while retaining the
residual coherent qubit. -/
noncomputable def randomFlipInstrument
    (weight : Bool → ℚ≥0)
    (normalized : ∑ branch, weight branch = 1) :
    KrausInstrument Bool Ript.Examples.QubitChannel.qubit
      Ript.Examples.QubitChannel.qubit where
  branch := randomFlipOperation weight
  total := randomFlipChannel weight normalized
  total_map ρ := by
    simp [randomFlipChannel, randomFlipOperation,
      KrausChannel.ofOperators, KrausOperation.ofOperators]

/-- Exact action of one random-flip operation on a classical basis state. -/
theorem randomFlipOperation_basis
    (weight : Bool → ℚ≥0) (branch input : Bool) :
    (randomFlipOperation weight branch).map
        (Ript.Examples.QubitChannel.basisDensity input).matrix =
      (weight branch : ℂ) •
        (Ript.Examples.QubitChannel.basisDensity (xor input branch)).matrix := by
  ext row column
  change Bool at row column
  cases branch <;> cases input <;> cases row <;> cases column <;>
    simp [randomFlipOperation, randomFlipOperator,
      KrausOperation.ofOperators,
      Ript.Examples.QubitChannel.bitFlipOperator,
      Ript.Examples.QubitChannel.basisDensity, Matrix.mul_apply,
      Matrix.diagonal_apply,
      Ript.Examples.NoisyBitRealizations.probabilityAmplitude_mul_starRingEnd]

/-- A recorded non-flip branch only scales its input matrix. -/
theorem randomFlipOperation_false
    (weight : Bool → ℚ≥0)
    (ρ : Matrix Ript.Examples.QubitChannel.qubit
      Ript.Examples.QubitChannel.qubit ℂ) :
    (randomFlipOperation weight false).map ρ =
      (weight false : ℂ) • ρ := by
  ext row column
  change Bool at row column
  cases row <;> cases column <;>
    simp only [randomFlipOperation, randomFlipOperator,
      KrausOperation.ofOperators, Matrix.mul_apply, Fintype.sum_unique,
      Matrix.one_apply, Matrix.conjTranspose_apply,
      mul_ite, mul_one, mul_zero] <;>
    simpa using probabilityAmplitude_mul_middle_star
      (weight false) (ρ _ _)

/-- Quantum instrument assigned to either common noise generator. -/
noncomputable def generatorInstrument (generator : NoiseGenerator) :
    KrausInstrument Bool Ript.Examples.QubitChannel.qubit
      Ript.Examples.QubitChannel.qubit :=
  randomFlipInstrument (noiseWeight generator)
    (noiseSemantics.normalized generator)

/-- The common adaptive protocol as a first-class coherent quantum instrument
tree. -/
noncomputable def quantumProtocolTree :
    InstrumentTree Ript.Examples.QubitChannel.qubit
      Ript.Examples.QubitChannel.qubit :=
  .step (generatorInstrument .quarterFlip) 1 fun first ↦
    .step (generatorInstrument
      (if first then .halfFlip else .quarterFlip))
      (if first then 2 else 1) fun _ ↦
        .done (KrausChannel.identity Ript.Examples.QubitChannel.qubit)

/-- The quantum tree has the same four complete histories as the common
branching language. -/
def quantumHistoryEquiv : quantumProtocolTree.History ≃ ProtocolHistory :=
  Equiv.refl _

/-- Insert a concrete common history into the definitionally identical
quantum history space. -/
def quantumHistory (first second : Bool) : quantumProtocolTree.History :=
  ⟨first, second, PUnit.unit⟩

@[simp]
theorem quantumProtocolTree_budget : quantumProtocolTree.budget = 4 := by
  decide

/-- The quantum branch map sends a basis state to the same deterministic
residual bit and exact branch weight as the common normal form. -/
theorem quantumProtocol_branch_basis
    (input first second : Bool) :
    quantumProtocolTree.branchMap (quantumHistory first second)
        (Ript.Examples.QubitChannel.basisDensity input).matrix =
      (adaptiveProtocol.historyProbability noiseSemantics
          (history first second) : ℂ) •
        (Ript.Examples.QubitChannel.basisDensity
          (xor (xor input first) second)).matrix := by
  simp only [quantumProtocolTree, quantumHistory,
    InstrumentTree.branchMap, generatorInstrument,
    randomFlipInstrument, KrausChannel.identity_map]
  change
    (randomFlipOperation
      (noiseWeight (if first then .halfFlip else .quarterFlip)) second).map
      ((randomFlipOperation (noiseWeight .quarterFlip) first).map
        (Ript.Examples.QubitChannel.basisDensity input).matrix) = _
  rw [randomFlipOperation_basis, KrausOperation.map_smul,
    randomFlipOperation_basis]
  cases input <;> cases first <;> cases second <;>
    norm_num [noiseWeight, smul_smul]

/-- **Quantum/classical branch representation.**  On every classical basis
input, each diagonal block of the coherent recorded quantum channel equals
the corresponding entry of the common exact stochastic normal form. -/
theorem quantumProtocol_basis_block
    (input first second output : Bool) :
    (quantumProtocolTree.eval.recordedChannel.map
      (Ript.Examples.QubitChannel.basisDensity input).matrix)
        (quantumHistory first second, output)
        (quantumHistory first second, output) =
      (probabilityProtocol.prob input
        (history first second, output) : ℂ) := by
  rw [quantumProtocolTree.recordedChannel_history_block]
  simp only [ite_true]
  rw [quantumProtocol_branch_basis,
    probabilityProtocol_branch_representation]
  cases input <;> cases first <;> cases second <;> cases output <;>
    simp [Ript.Examples.QubitChannel.basisDensity]

/-- One no-flip history retains a nonzero coherent off-diagonal block. -/
theorem quantumProtocol_coherent_block :
    (quantumProtocolTree.eval.recordedChannel.map
      Ript.Examples.QubitInstrument.plusDensity.matrix)
        (quantumHistory false false, false)
        (quantumHistory false false, true) = (9 : ℂ) / 32 := by
  rw [quantumProtocolTree.recordedChannel_history_block]
  simp only [ite_true]
  simp only [quantumProtocolTree, quantumHistory,
    InstrumentTree.branchMap, generatorInstrument,
    randomFlipInstrument, KrausChannel.identity_map]
  change
    ((randomFlipOperation (noiseWeight .quarterFlip) false).map
      ((randomFlipOperation (noiseWeight .quarterFlip) false).map
        Ript.Examples.QubitInstrument.plusDensity.matrix)) false true = _
  rw [randomFlipOperation_false, randomFlipOperation_false]
  change (noiseWeight .quarterFlip false : ℂ) *
    ((noiseWeight .quarterFlip false : ℂ) *
      Ript.Examples.QubitInstrument.plusDensity.matrix false true) = _
  rw [Ript.Examples.QubitInstrument.plusDensity_entry]
  norm_num [noiseWeight, smul_smul]

/-- Measurement--preparation of the same classical tree has no such coherent
off-diagonal output block. -/
theorem classicalProtocol_coherent_block_zero :
    (measurementPreparation probabilityProtocol).map
      Ript.Examples.QubitInstrument.plusDensity.matrix
        (history false false, false)
        (history false false, true) = 0 := by
  have unequal :
      (history false false, false) ≠
        (history false false, true) := by
    intro equal
    have := congrArg Prod.snd equal
    contradiction
  rw [measurementPreparation_map_apply]
  exact if_neg unequal

/-- The coherent quantum tree is operationally distinct from the classical
measurement--preparation realization of the same branch table. -/
theorem quantumProtocol_ne_measurementPreparation :
    (quantumProtocolTree.eval.recordedChannel.map
      Ript.Examples.QubitInstrument.plusDensity.matrix)
        (quantumHistory false false, false)
        (quantumHistory false false, true) ≠
      (measurementPreparation probabilityProtocol).map
        Ript.Examples.QubitInstrument.plusDensity.matrix
          (history false false, false)
          (history false false, true) := by
  rw [quantumProtocol_coherent_block,
    classicalProtocol_coherent_block_zero]
  norm_num

/-! ## A four-node causal realization -/

/-- Causal nodes: input, first noise outcome, adaptive second outcome, output. -/
def inputNode : Fin 4 := 0

/-- First exogenous noise-outcome node. -/
def firstNode : Fin 4 := 1

/-- Outcome node whose mechanism is selected by `firstNode`. -/
def secondNode : Fin 4 := 2

/-- Deterministic residual-state output node. -/
def outputNode : Fin 4 := 3

/-- DAG of the adaptive causal realization.  The first noise is exogenous;
the first outcome selects the second mechanism, and all state data determine
the final output. -/
def adaptiveDAG : FiniteDAG 4 where
  parents node :=
    if node = secondNode then {firstNode}
    else if node = outputNode then {inputNode, firstNode, secondNode}
    else ∅
  parent_before child parent membership := by
    fin_cases child <;> fin_cases parent <;>
      simp [inputNode, firstNode, secondNode, outputNode] at membership ⊢

/-- Generator outcome distribution used as a local causal mechanism. -/
def branchDistribution (generator : NoiseGenerator) :
    FinDist (Object.of Bool) where
  prob := noiseWeight generator
  normalized := noiseSemantics.normalized generator

/-- Fair exogenous input mechanism. -/
def adaptiveInputMechanism : Mechanism adaptiveDAG Bool inputNode where
  run _ := Ript.Examples.SimpleCausalModel.fairBitDistribution

/-- First quarter-flip outcome mechanism. -/
def adaptiveFirstMechanism : Mechanism adaptiveDAG Bool firstNode where
  run _ := branchDistribution .quarterFlip

/-- The first outcome selects the second local mechanism. -/
def adaptiveSecondMechanism : Mechanism adaptiveDAG Bool secondNode where
  run parents :=
    branchDistribution
      (if parents ⟨firstNode, by
        simp [adaptiveDAG, firstNode, secondNode, outputNode]⟩
        then .halfFlip else .quarterFlip)

/-- Final output is the deterministic parity update of the three parents. -/
def adaptiveOutputMechanism : Mechanism adaptiveDAG Bool outputNode where
  run parents :=
    FinDist.pure
      (xor
        (xor
          (parents ⟨inputNode, by
            simp [adaptiveDAG, inputNode, firstNode, secondNode,
              outputNode]⟩)
          (parents ⟨firstNode, by
            simp [adaptiveDAG, inputNode, firstNode, secondNode,
              outputNode]⟩))
        (parents ⟨secondNode, by
          simp [adaptiveDAG, inputNode, firstNode, secondNode,
            outputNode]⟩))

/-- Exact adaptive structural causal model whose factorization is the same
four-branch protocol table. -/
def adaptiveCausalModel : FiniteCausalModel 4 Bool where
  dag := adaptiveDAG
  mechanism :=
    Fin.cases adaptiveInputMechanism
      (Fin.cases adaptiveFirstMechanism
        (Fin.cases adaptiveSecondMechanism fun last ↦ by
          have equal : last = 0 := Fin.eq_zero last
          subst last
          exact adaptiveOutputMechanism))

@[simp]
theorem adaptiveCausalModel_input :
    adaptiveCausalModel.mechanism inputNode = adaptiveInputMechanism :=
  rfl

@[simp]
theorem adaptiveCausalModel_first :
    adaptiveCausalModel.mechanism firstNode = adaptiveFirstMechanism :=
  rfl

@[simp]
theorem adaptiveCausalModel_second :
    adaptiveCausalModel.mechanism secondNode = adaptiveSecondMechanism :=
  rfl

@[simp]
theorem adaptiveCausalModel_output :
    adaptiveCausalModel.mechanism outputNode = adaptiveOutputMechanism :=
  rfl

@[simp]
theorem adaptiveCausalModel_zero
    (parents : adaptiveCausalModel.dag.ParentAssignment Bool (0 : Fin 4)) :
    (adaptiveCausalModel.mechanism 0).run parents =
      Ript.Examples.SimpleCausalModel.fairBitDistribution :=
  rfl

@[simp]
theorem adaptiveCausalModel_one
    (parents : adaptiveCausalModel.dag.ParentAssignment Bool (1 : Fin 4)) :
    (adaptiveCausalModel.mechanism 1).run parents =
      branchDistribution .quarterFlip :=
  rfl

@[simp]
theorem adaptiveCausalModel_two
    (parents : adaptiveCausalModel.dag.ParentAssignment Bool (2 : Fin 4)) :
    (adaptiveCausalModel.mechanism 2).run parents =
      branchDistribution
        (if parents ⟨firstNode, by
          simp [adaptiveCausalModel, adaptiveDAG, firstNode, secondNode,
            outputNode]⟩ then .halfFlip else .quarterFlip) :=
  rfl

@[simp]
theorem adaptiveCausalModel_three
    (parents : adaptiveCausalModel.dag.ParentAssignment Bool (3 : Fin 4)) :
    (adaptiveCausalModel.mechanism 3).run parents =
      FinDist.pure
        (xor
          (xor
            (parents ⟨inputNode, by
              simp [adaptiveCausalModel, adaptiveDAG, inputNode, firstNode,
                secondNode, outputNode]⟩)
            (parents ⟨firstNode, by
              simp [adaptiveCausalModel, adaptiveDAG, inputNode, firstNode,
                secondNode, outputNode]⟩))
          (parents ⟨secondNode, by
            simp [adaptiveCausalModel, adaptiveDAG, inputNode, firstNode,
              secondNode, outputNode]⟩)) :=
  rfl

@[simp]
theorem adaptiveCausalModel_succ_zero
    (parents : adaptiveCausalModel.dag.ParentAssignment Bool
      (Fin.succ (0 : Fin 3))) :
    (adaptiveCausalModel.mechanism (Fin.succ (0 : Fin 3))).run parents =
      branchDistribution .quarterFlip :=
  rfl

@[simp]
theorem adaptiveCausalModel_succ_succ_zero
    (parents : adaptiveCausalModel.dag.ParentAssignment Bool
      (Fin.succ (Fin.succ (0 : Fin 2)))) :
    (adaptiveCausalModel.mechanism
      (Fin.succ (Fin.succ (0 : Fin 2)))).run parents =
      branchDistribution
        (if parents ⟨firstNode, by
          simp [adaptiveCausalModel, adaptiveDAG, firstNode, secondNode,
            outputNode]⟩ then .halfFlip else .quarterFlip) :=
  rfl

@[simp]
theorem adaptiveCausalModel_succ_succ_succ_zero
    (parents : adaptiveCausalModel.dag.ParentAssignment Bool
      (Fin.succ (2 : Fin 3))) :
    (adaptiveCausalModel.mechanism
      (Fin.succ (2 : Fin 3))).run parents =
      FinDist.pure
        (xor
          (xor
            (parents ⟨inputNode, by
              simp [adaptiveCausalModel, adaptiveDAG, inputNode, firstNode,
                secondNode, outputNode]⟩)
            (parents ⟨firstNode, by
              simp [adaptiveCausalModel, adaptiveDAG, inputNode, firstNode,
                secondNode, outputNode]⟩))
          (parents ⟨secondNode, by
            simp [adaptiveCausalModel, adaptiveDAG, inputNode, firstNode,
              secondNode, outputNode]⟩)) :=
  rfl

/-- The causal observational joint factors exactly as a fair input times the
common adaptive protocol conditional. -/
theorem causal_joint_representation
    (input first second output : Bool) :
    adaptiveCausalModel.joint.prob ![input, first, second, output] =
      (1 / 2 : ℚ≥0) *
        probabilityProtocol.prob input (history first second, output) := by
  rw [adaptiveCausalModel.observational_factorization]
  simp only [Fin.prod_univ_succ, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two]
  cases input <;> cases first <;> cases second <;> cases output <;>
    norm_num [adaptiveCausalModel, adaptiveDAG, inputNode, firstNode,
      secondNode, outputNode, branchDistribution,
      adaptiveInputMechanism, adaptiveFirstMechanism,
      adaptiveSecondMechanism, adaptiveOutputMechanism,
      Ript.Examples.SimpleCausalModel.fairBitDistribution,
      probabilityProtocol, adaptiveProtocol, noiseSemantics, noiseWeight,
      flipTransition, history, Tree.run, Tree.normalForm,
      NormalForm.toFinStoch, Tree.historyProbability, Tree.finalState,
      FinDist.pure]
  all_goals
    simp only [Matrix.cons_val_two]
    norm_num [noiseWeight]

/-! ## Task-semantic information -/

/-- The complete recorded tree is a finite experiment about its input bit. -/
abbrev semanticProtocol := probabilityProtocol

/-- The decoding decision has exact zero loss. -/
theorem semanticProtocol_decode_zero_risk :
    deterministicDecisionRisk Ript.Examples.SimpleDecision.bitGuessing
      semanticProtocol decodeHistory = 0 := by
  unfold deterministicDecisionRisk randomizedDecisionRisk
  rw [probabilityProtocol_decode]
  change (∑ state : Bool, ∑ action : Bool,
    Ript.Examples.SimpleDecision.uniformBitPrior.prob state *
      (FinStoch.identity (Object.of Bool)).prob state action *
        (if state = action then 0 else 1)) = 0
  rw [Fintype.sum_bool]
  simp [FinStoch.identity]

/-- The recorded adaptive protocol has exact Bayes risk zero. -/
theorem semanticProtocol_zero_risk :
    finiteBayesRisk Ript.Examples.SimpleDecision.bitGuessing
      semanticProtocol = 0 := by
  apply le_antisymm
  · exact (finiteBayesRisk_le_deterministicDecisionRisk
      Ript.Examples.SimpleDecision.bitGuessing semanticProtocol
        decodeHistory).trans_eq semanticProtocol_decode_zero_risk
  · exact zero_le

/-- Relative to the uninformative baseline, retaining the complete adaptive
history has the full Boolean guessing value `1/2`. -/
theorem semanticProtocol_value :
    semanticValue Ript.Examples.SimpleDecision.bitGuessing
        Ript.Examples.SimpleDecision.uninformativeExperiment
        semanticProtocol = (1 : ℚ≥0) / 2 := by
  rw [semanticValue,
    Ript.Examples.SimpleDecision.uninformative_information_half_risk,
    semanticProtocol_zero_risk]
  norm_num

/-! ## Thermodynamic realization -/

/-- Output equilibrium induced by the common protocol from a uniform thermal
bit.  The recorded history is part of the physical output system. -/
def adaptiveThermalOutput : ThermalObject where
  system := Object.of (ProtocolHistory × Bool)
  equilibrium :=
    Ript.Examples.SimpleThermalModel.thermalBit.equilibrium.push
      probabilityProtocol

/-- The common adaptive channel is Gibbs-preserving for its induced exact
output equilibrium. -/
def thermalProtocol :
    GibbsPreserving Ript.Examples.SimpleThermalModel.thermalBit
      adaptiveThermalOutput where
  channel := probabilityProtocol
  preserves_equilibrium := rfl

/-- The induced thermal equilibrium exposes each history probability times a
uniform residual-bit factor. -/
theorem adaptiveThermalOutput_equilibrium
    (first second output : Bool) :
    adaptiveThermalOutput.equilibrium.prob (history first second, output) =
      adaptiveProtocol.historyProbability noiseSemantics
        (history first second) / 2 := by
  change (∑ input : Bool, (1 / 2 : ℚ≥0) *
      probabilityProtocol.prob input (history first second, output)) = _
  rw [Fintype.sum_bool]
  cases first <;> cases second <;> cases output <;>
    norm_num [probabilityProtocol_branch_representation]

/-! ## Cross-model representation and a concrete completeness witness -/

/-- A non-adaptive comparison tree using quarter-flip noise at both levels. -/
def fixedQuarterProtocol : Tree NoiseGenerator 2 :=
  .node .quarterFlip fun _ ↦
    .node .quarterFlip fun _ ↦ .leaf

/-- The adaptive and fixed trees have distinct canonical branch normal forms:
history `10` has mass `1/8` versus `3/16`. -/
theorem adaptiveProtocol_normalForm_ne_fixedQuarter :
    adaptiveProtocol.normalForm noiseSemantics ≠
      fixedQuarterProtocol.normalForm noiseSemantics := by
  intro equalNormalForms
  have entryEqual := congrArg
    (fun normalForm ↦ normalForm.probability (history true false))
    equalNormalForms
  change adaptiveProtocol.historyProbability noiseSemantics
      (history true false) =
    fixedQuarterProtocol.historyProbability noiseSemantics
      (history true false) at entryEqual
  rw [historyProbability_true_false] at entryEqual
  change (1 / 8 : ℚ≥0) = (1 / 4) * ((3 / 4) * 1) at entryEqual
  norm_num at entryEqual

/-- Observational completeness turns the normal-form distinction into an
operational stochastic-channel distinction. -/
theorem adaptiveProtocol_run_ne_fixedQuarter :
    adaptiveProtocol.run noiseSemantics ≠
      fixedQuarterProtocol.run noiseSemantics := by
  intro equalRuns
  exact adaptiveProtocol_normalForm_ne_fixedQuarter
    ((Tree.observationalCompleteness noiseSemantics).mp equalRuns)

/-- Quantum and common histories incur the same exact realized path cost,
even though `InstrumentTree.budget` deliberately uses the more conservative
sum-of-branches bound while the common tree computes a worst-case maximum. -/
theorem quantumProtocol_historyCost_eq_common (first second : Bool) :
    quantumProtocolTree.historyCost (quantumHistory first second) =
      adaptiveProtocol.historyCost noiseCost (history first second) := by
  cases first <;> cases second <;> rfl

/-- **Six-model adaptive-tree representation package.**  Every model exposes
the same exact finite branch table at its classical operational boundary,
while retaining its native causal, resource, semantic, thermal, or coherent
quantum structure. -/
theorem sixModelAdaptiveRepresentation :
    (∀ input first second output : Bool,
      probabilityProtocol.prob input (history first second, output) =
        if xor (xor input first) second = output
          then adaptiveProtocol.historyProbability noiseSemantics
            (history first second)
          else 0) ∧
    (∀ input first second output : Bool,
      (quantumProtocolTree.eval.recordedChannel.map
        (Ript.Examples.QubitChannel.basisDensity input).matrix)
          (quantumHistory first second, output)
          (quantumHistory first second, output) =
        (probabilityProtocol.prob input
          (history first second, output) : ℂ)) ∧
    (∀ input first second output : Bool,
      adaptiveCausalModel.joint.prob ![input, first, second, output] =
        (1 / 2 : ℚ≥0) *
          probabilityProtocol.prob input (history first second, output)) ∧
    (randomizedProtocol.channel = probabilityProtocol ∧
      randomizedProtocol.resource = ComputationResource.of 3 3 2 3) ∧
    (semanticValue Ript.Examples.SimpleDecision.bitGuessing
        Ript.Examples.SimpleDecision.uninformativeExperiment
        semanticProtocol = (1 : ℚ≥0) / 2) ∧
    (thermalProtocol.channel = probabilityProtocol ∧
      ∀ first second output : Bool,
        adaptiveThermalOutput.equilibrium.prob
            (history first second, output) =
          adaptiveProtocol.historyProbability noiseSemantics
            (history first second) / 2) :=
  ⟨probabilityProtocol_branch_representation,
    quantumProtocol_basis_block,
    causal_joint_representation,
    ⟨rfl, rfl⟩,
    semanticProtocol_value,
    ⟨rfl, adaptiveThermalOutput_equilibrium⟩⟩

#eval decide (Fintype.card ProtocolHistory = 4)
#eval decide
  (adaptiveProtocol.historyProbability noiseSemantics
    (history false false) = (9 : ℚ≥0) / 16)
#eval decide (adaptiveProtocol.budget noiseCost = 3)
#eval Ript.Models.Computation.Randomized.withinBudget
  (ComputationResource.of 3 3 2 3) randomizedProtocol

end Ript.Examples.AdaptiveNoiseRealizations
