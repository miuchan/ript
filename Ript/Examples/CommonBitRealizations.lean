import Mathlib.Tactic.FinCases
import Ript.Examples.QubitChannel
import Ript.Examples.SimpleCausalModel
import Ript.Examples.SimpleComputation
import Ript.Examples.SimpleDecision
import Ript.Examples.SimpleThermalModel
import Ript.Semantics.ResourceChangingInterpretation

/-!
# One process language realized in six information models

This file gives the first literal common-syntax slice across all six model
families named by Ript's governing objective.  The shared language has one
unit-cost primitive, Boolean flip, with abstract input and output interfaces.
Its interpretations are genuinely model specific:

* exact finite stochastic negation;
* the Pauli-X Kraus channel;
* a negating local mechanism in a finite causal DAG;
* a total executable gate with four-coordinate computation cost;
* an information-preserving experiment for the Boolean guessing task;
* a Gibbs-preserving flip of a degenerate thermal bit.

The theorem `sixModelFlipAgreement` compares their observable Boolean actions
without identifying the models. Computation retains its vector resource;
quantum and thermal analytic observables remain separate from the explicitly
zero abstract process cost used by this slice.
-/

set_option autoImplicit false

namespace Ript.Examples.CommonBitRealizations

open CategoryTheory
open Ript.Core
open Ript.Models.Computation
open Ript.Models.Decision.Blackwell
open Ript.Models.Decision.SemanticValue
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic
open Ript.Models.FiniteStochastic.FinStoch
open Ript.Models.Causal
open Ript.Models.Quantum
open Ript.Models.Thermal
open Ript.Semantics
open Ript.Syntax

/-- Abstract interfaces of the common Boolean process.  They are distinct so
the causal realization may interpret the input as a parent assignment and the
output as one node value. -/
inductive Interface where
  | input
  | output
  deriving DecidableEq, Repr

/-- The sole common primitive flips one Boolean value. -/
inductive Generator : Interface → Interface → Type where
  | flip : Generator .input .output

/-- The common sequential signature declares one scalar unit for flip. -/
def signature : Signature Nat where
  Obj := Interface
  Gen := Generator
  cost
    | .flip => 1

/-- The common one-step process expression. -/
def flipExpr : Expr signature .input .output :=
  .gen .flip

/-- The common syntax computes exactly one scalar resource unit. -/
@[simp]
theorem flipExpr_syntaxCost : flipExpr.syntaxCost = 1 :=
  rfl

/-! ## Classical probability -/

/-- Exact stochastic realization by deterministic Boolean negation. -/
def probabilityInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.FiniteStochastic.Object)
      (OrderAddMonoidHom.id Nat) where
  obj
    | .input => Ript.Examples.StochasticBits.bit
    | .output => Ript.Examples.StochasticBits.bit
  mapGen
    | .flip => Ript.Examples.StochasticBits.deterministicNot
  mapGen_cost
    | .flip => Nat.zero_le 1

/-! ## Finite quantum processes -/

/-- The current quantum slice uses a zero-valued abstract scalar cost; its
physical resource refinements remain separate from the channel laws. -/
local instance quantumZeroCost :
    HasProcessCost Ript.Models.Quantum.Object Nat where
  cost _ := 0
  cost_id _ := rfl
  cost_comp _ _ := Nat.zero_le 0

/-- Quantum realization by the Pauli-X Kraus channel. -/
def quantumInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.Quantum.Object)
      (OrderAddMonoidHom.id Nat) where
  obj
    | .input => Ript.Examples.QubitChannel.qubit
    | .output => Ript.Examples.QubitChannel.qubit
  mapGen
    | .flip => Ript.Examples.QubitChannel.bitFlip
  mapGen_cost
    | .flip => Nat.zero_le 1

/-! ## Finite causal mechanisms -/

/-- Parent-assignment object of the child in the existing two-node chain. -/
abbrev causalInput : Ript.Models.FiniteStochastic.Object :=
  Ript.Models.FiniteStochastic.Object.of
    (Ript.Examples.SimpleCausalModel.chainDAG.ParentAssignment Bool
      Ript.Examples.SimpleCausalModel.effect)

/-- A causal child mechanism that outputs the negation of its parent. -/
def causalFlipMechanism :
    Mechanism Ript.Examples.SimpleCausalModel.chainDAG Bool
      Ript.Examples.SimpleCausalModel.effect where
  run parents := FinDist.pure
    (!(parents ⟨Ript.Examples.SimpleCausalModel.cause, by
      simp [Ript.Examples.SimpleCausalModel.chainDAG,
        Ript.Examples.SimpleCausalModel.cause,
        Ript.Examples.SimpleCausalModel.effect]⟩))

/-- Causal realization by the exact stochastic channel of the local
mechanism, rather than by an unrelated Boolean function. -/
def causalInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.FiniteStochastic.Object)
      (OrderAddMonoidHom.id Nat) where
  obj
    | .input => causalInput
    | .output => Ript.Examples.StochasticBits.bit
  mapGen
    | .flip => causalFlipMechanism.toFinStoch
  mapGen_cost
    | .flip => Nat.zero_le 1

/-- Encode one Boolean parent value as the unique-parent assignment. -/
def causalParentInput (value : Bool) : causalInput :=
  fun _ ↦ value

/-! ## Resource-aware computation -/

/-- Translate each common scalar unit to one formal evaluation step and one
circuit gate, preserving the unused query and storage coordinates at zero. -/
def computationResourceMap : Nat →+o ComputationResource where
  toFun units := ComputationResource.of units 0 0 units
  map_zero' := by
    funext kind
    fin_cases kind <;> rfl
  map_add' left right := by
    funext kind
    fin_cases kind <;> simp [ComputationResource.of]
  monotone' left right h kind := by
    fin_cases kind <;> simp [ComputationResource.of, h]

/-- Computational realization by the existing total Boolean gate. -/
def computationInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.Computation.Total.Object)
      computationResourceMap where
  obj
    | .input => Ript.Examples.SimpleComputation.totalBit
    | .output => Ript.Examples.SimpleComputation.totalBit
  mapGen
    | .flip => Ript.Examples.SimpleComputation.totalNot
  mapGen_cost
    | .flip => le_rfl

/-! ## Task-relative semantic information -/

/-- The same exact negation channel regarded as an experiment: its observation
is a reversible relabeling of the hidden Boolean state. -/
def semanticFlipExperiment :
    FinStoch Ript.Examples.SimpleDecision.decisionBit
      Ript.Examples.SimpleDecision.decisionBit :=
  FinStoch.dirac Bool.not

/-- Semantic-information realization of the common syntax. -/
def semanticInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.FiniteStochastic.Object)
      (OrderAddMonoidHom.id Nat) where
  obj
    | .input => Ript.Examples.SimpleDecision.decisionBit
    | .output => Ript.Examples.SimpleDecision.decisionBit
  mapGen
    | .flip => semanticFlipExperiment
  mapGen_cost
    | .flip => Nat.zero_le 1

/-- Two reversible observation relabelings recover perfect observation. -/
theorem semanticFlip_involutive :
    FinStoch.comp semanticFlipExperiment semanticFlipExperiment =
      Ript.Examples.SimpleDecision.perfectExperiment := by
  apply FinStoch.ext
  intro input output
  change Bool at input output
  change (∑ middle : Bool,
    (if (!input) = middle then (1 : ℚ≥0) else 0) *
      (if (!middle) = output then 1 else 0)) =
    if input = output then 1 else 0
  cases input <;> cases output <;>
    rw [Fintype.sum_bool] <;> norm_num

/-- Flipped observation and perfect observation are Blackwell equivalent. -/
theorem semanticFlip_blackwellEquivalent_perfect :
    BlackwellEquivalent semanticFlipExperiment
      Ript.Examples.SimpleDecision.perfectExperiment := by
  constructor
  · refine ⟨semanticFlipExperiment, ?_⟩
    exact semanticFlip_involutive
  · refine ⟨semanticFlipExperiment, ?_⟩
    change FinStoch.comp
      (FinStoch.identity Ript.Examples.SimpleDecision.decisionBit)
      semanticFlipExperiment = semanticFlipExperiment
    apply FinStoch.ext
    intro input output
    simp [FinStoch.comp, FinStoch.identity]

/-- Reversible relabeling preserves the full task-relative value of perfect
Boolean information. -/
theorem semanticFlip_guessing_value :
    semanticValue Ript.Examples.SimpleDecision.bitGuessing
        Ript.Examples.SimpleDecision.uninformativeExperiment
        semanticFlipExperiment = (1 : ℚ≥0) / 2 := by
  rw [semanticValue_eq_of_equivalent
    Ript.Examples.SimpleDecision.bitGuessing
    Ript.Examples.SimpleDecision.uninformativeExperiment
    semanticFlip_blackwellEquivalent_perfect]
  exact Ript.Examples.SimpleDecision.perfect_guessing_semantic_value

/-! ## Finite thermodynamics -/

/-- The finite thermal slice uses zero abstract scalar process cost; its
free-energy and work quantities remain explicit semantic observables. -/
local instance thermalZeroCost : HasProcessCost ThermalObject Nat where
  cost _ := 0
  cost_id _ := rfl
  cost_comp _ _ := Nat.zero_le 0

/-- Thermodynamic realization by the equilibrium-preserving Boolean flip. -/
def thermalInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := ThermalObject)
      (OrderAddMonoidHom.id Nat) where
  obj
    | .input => Ript.Examples.SimpleThermalModel.thermalBit
    | .output => Ript.Examples.SimpleThermalModel.thermalBit
  mapGen
    | .flip => Ript.Examples.SimpleThermalModel.thermalFlip
  mapGen_cost
    | .flip => Nat.zero_le 1

/-! ## Cross-model representation and comparison -/

/-- Probability realization flips a Boolean value with exact probability
one. -/
theorem probability_flip (value : Bool) :
    (ResourceChangingInterpretation.eval probabilityInterpretation flipExpr).prob
      value (!value) = 1 := by
  simp [ResourceChangingInterpretation.eval,
    ResourceChangingInterpretation.toMappedCost, Ript.Semantics.eval,
    Expr.mapCost, flipExpr,
    probabilityInterpretation, Ript.Examples.StochasticBits.deterministicNot,
    FinStoch.dirac]

/-- Pauli-X implements the same action on computational-basis states. -/
theorem quantum_flip (value : Bool) :
    (ResourceChangingInterpretation.eval quantumInterpretation flipExpr).applyDensity
        (Ript.Examples.QubitChannel.basisDensity value) =
      Ript.Examples.QubitChannel.basisDensity (!value) :=
  Ript.Examples.QubitChannel.bitFlip_basisDensity value

/-- The causal child mechanism assigns exact probability one to the negated
parent value. -/
theorem causal_flip (value : Bool) :
    (ResourceChangingInterpretation.eval causalInterpretation flipExpr).prob
      (causalParentInput value) (!value) = 1 := by
  simp [ResourceChangingInterpretation.eval,
    ResourceChangingInterpretation.toMappedCost, Ript.Semantics.eval,
    Expr.mapCost, flipExpr,
    causalInterpretation, causalFlipMechanism, causalParentInput,
    Mechanism.toFinStoch, FinDist.pure]

/-- The total computation executes Boolean negation. -/
theorem computation_flip (value : Bool) :
    (ResourceChangingInterpretation.eval computationInterpretation flipExpr).run
      value = !value :=
  rfl

/-- The computation retains the exact translated two-coordinate resource
cost. -/
theorem computation_flip_cost :
    processCost (R := ComputationResource)
        (ResourceChangingInterpretation.eval computationInterpretation flipExpr) =
      computationResourceMap flipExpr.syntaxCost :=
  rfl

/-- The semantic experiment implements deterministic negation on its
observation boundary. -/
theorem semantic_flip (value : Bool) :
    (ResourceChangingInterpretation.eval semanticInterpretation flipExpr).prob
      value (!value) = 1 := by
  simp [ResourceChangingInterpretation.eval,
    ResourceChangingInterpretation.toMappedCost, Ript.Semantics.eval,
    Expr.mapCost, flipExpr,
    semanticInterpretation, semanticFlipExperiment, FinStoch.dirac]

/-- The Gibbs-preserving process implements the same deterministic Boolean
action on the exact operational channel. -/
theorem thermal_flip (value : Bool) :
    (ResourceChangingInterpretation.eval thermalInterpretation flipExpr).channel.prob
      value (!value) = 1 := by
  simp [ResourceChangingInterpretation.eval,
    ResourceChangingInterpretation.toMappedCost, Ript.Semantics.eval,
    Expr.mapCost, flipExpr,
    thermalInterpretation, Ript.Examples.SimpleThermalModel.thermalFlip,
    Ript.Examples.SimpleThermalModel.flipChannel, FinStoch.dirac]

/-- One proposition packages the shared observable contract while retaining
the quantum state equation, causal mechanism, semantic value, thermodynamic
certificate, and native computation-resource equality. -/
structure SixModelFlipAgreement : Prop where
  probability : ∀ value : Bool,
    (ResourceChangingInterpretation.eval probabilityInterpretation flipExpr).prob
      value (!value) = 1
  quantum : ∀ value : Bool,
    (ResourceChangingInterpretation.eval quantumInterpretation flipExpr).applyDensity
        (Ript.Examples.QubitChannel.basisDensity value) =
      Ript.Examples.QubitChannel.basisDensity (!value)
  causal : ∀ value : Bool,
    (ResourceChangingInterpretation.eval causalInterpretation flipExpr).prob
      (causalParentInput value) (!value) = 1
  computation : ∀ value : Bool,
    (ResourceChangingInterpretation.eval computationInterpretation flipExpr).run
      value = !value
  semantic :
    semanticValue Ript.Examples.SimpleDecision.bitGuessing
        Ript.Examples.SimpleDecision.uninformativeExperiment
        semanticFlipExperiment = (1 : ℚ≥0) / 2
  thermal : ∀ value : Bool,
    (ResourceChangingInterpretation.eval thermalInterpretation flipExpr).channel.prob
      value (!value) = 1

/-- **First six-model common-syntax agreement theorem.** -/
theorem sixModelFlipAgreement : SixModelFlipAgreement where
  probability := probability_flip
  quantum := quantum_flip
  causal := causal_flip
  computation := computation_flip
  semantic := semanticFlip_guessing_value
  thermal := thermal_flip

end Ript.Examples.CommonBitRealizations
