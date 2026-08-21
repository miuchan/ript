import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Ript.Examples.CommonBitRealizations
import Ript.Models.Computation.Total.Monoidal
import Ript.Models.FiniteStochastic.Monoidal
import Ript.Examples.QubitChannel
import Ript.Models.Quantum.Monoidal
import Ript.Models.Thermal.Monoidal
import Ript.Semantics.ResourceChangingMonoidalInitiality

/-!
# One parallel process language in six information models

This file upgrades the common Boolean flip from a sequential slice to a
symmetric monoidal one.  The expression `flip ⊗ flip` acts independently on
two inputs in probability, the full finite Kraus quantum category,
finite causal mechanisms, resource-exact total computation, semantic
experiments, and Gibbs-preserving thermodynamics.
-/

set_option autoImplicit false

namespace Ript.Examples.ParallelBitRealizations

open CategoryTheory
open MonoidalCategory
open Ript.Core
open Ript.Models.Computation
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic
open Ript.Models.Quantum
open Ript.Models.Thermal
open Ript.Semantics
open Ript.Syntax

/-! ## Common monoidal syntax -/

/-- Distinct input and output wires permit the causal realization to use its
parent-assignment input object. -/
inductive Wire where
  | input
  | output
  deriving DecidableEq, Repr

/-- One primitive Boolean flip. -/
inductive Generator : FreeMonoidalCategory Wire → FreeMonoidalCategory Wire → Type where
  | flip : Generator (.of .input) (.of .output)

/-- Unit-cost symmetric monoidal signature. -/
def signature : MonoidalSignature Nat where
  Wire := Wire
  Gen := Generator
  cost
    | .flip => 1

/-- One flip expression. -/
def flipExpr : MonoidalExpr signature (.of .input) (.of .output) :=
  .gen .flip

/-- Two independent flips in parallel. -/
def parallelFlipExpr :
    MonoidalExpr signature
      (.tensor (.of .input) (.of .input))
      (.tensor (.of .output) (.of .output)) :=
  .tensor (.gen .flip) (.gen .flip)

@[simp]
theorem parallelFlipExpr_cost : parallelFlipExpr.syntaxCost = 2 :=
  rfl

/-! ## Six interpretations -/

/-- Exact stochastic symmetric monoidal interpretation. -/
def probabilityInterpretation :
    ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.FiniteStochastic.Object)
      (OrderAddMonoidHom.id Nat) where
  wire _ := Ript.Examples.StochasticBits.bit
  mapGen
    | .flip => Ript.Examples.StochasticBits.deterministicNot
  mapGen_cost
    | .flip => Nat.zero_le 1

namespace QuantumImage

/-- Boolean computational basis as a genuine two-dimensional quantum object. -/
abbrev bit : Ript.Models.Quantum.Object :=
  Ript.Examples.QubitChannel.qubit

/-- Pauli-X as a one-operator Kraus channel. -/
def flip : bit ⟶ bit :=
  Ript.Examples.QubitChannel.bitFlip

end QuantumImage

/-- Full finite-Kraus quantum interpretation. -/
def quantumInterpretation :
    ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature)
      (C := Ript.Models.Quantum.Object)
      (OrderAddMonoidHom.id Nat) where
  wire _ := QuantumImage.bit
  mapGen
    | .flip => QuantumImage.flip
  mapGen_cost
    | .flip => Nat.zero_le 1

/-- Parallel interpretation by two independent finite causal mechanisms. -/
def causalInterpretation :
    ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.FiniteStochastic.Object)
      (OrderAddMonoidHom.id Nat) where
  wire
    | .input => Ript.Examples.CommonBitRealizations.causalInput
    | .output => Ript.Examples.StochasticBits.bit
  mapGen
    | .flip =>
        Ript.Examples.CommonBitRealizations.causalFlipMechanism.toFinStoch
  mapGen_cost
    | .flip => Nat.zero_le 1

/-- Parallel total-computation interpretation with native vector resources. -/
def computationInterpretation :
    ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.Computation.Total.Object)
      Ript.Examples.CommonBitRealizations.computationResourceMap where
  wire _ := Ript.Examples.SimpleComputation.totalBit
  mapGen
    | .flip => Ript.Examples.SimpleComputation.totalNot
  mapGen_cost
    | .flip => le_rfl

/-- Parallel semantic-experiment interpretation. -/
def semanticInterpretation :
    ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.FiniteStochastic.Object)
      (OrderAddMonoidHom.id Nat) where
  wire _ := Ript.Examples.SimpleDecision.decisionBit
  mapGen
    | .flip => Ript.Examples.CommonBitRealizations.semanticFlipExperiment
  mapGen_cost
    | .flip => Nat.zero_le 1

/-- Parallel Gibbs-preserving thermal interpretation. -/
def thermalInterpretation :
    ResourceChangingMonoidalInterpretation.Interpretation
      (signature := signature) (C := ThermalObject)
      (OrderAddMonoidHom.id Nat) where
  wire _ := Ript.Examples.SimpleThermalModel.thermalBit
  mapGen
    | .flip => Ript.Examples.SimpleThermalModel.thermalFlip
  mapGen_cost
    | .flip => Nat.zero_le 1

/-! ## Model-specific parallel observables -/

theorem probability_parallel (left right : Bool) :
    (ResourceChangingMonoidalInterpretation.eval probabilityInterpretation
      parallelFlipExpr).prob (left, right) (!left, !right) = 1 := by
  change (FinStoch.tensor
    Ript.Examples.StochasticBits.deterministicNot
    Ript.Examples.StochasticBits.deterministicNot).prob
      (left, right) (!left, !right) = 1
  simp [
    Ript.Examples.StochasticBits.deterministicNot, FinStoch.dirac]

/-- Kraus denotation of the parallel Pauli-X process in the full quantum
category. -/
def quantumParallelKraus :
    KrausChannel (Object.tensor QuantumImage.bit QuantumImage.bit)
      (Object.tensor QuantumImage.bit QuantumImage.bit) :=
  ResourceChangingMonoidalInterpretation.eval quantumInterpretation
    parallelFlipExpr

/-- The full-Kraus interpretation acts componentwise on arbitrary product
density matrices, not only on diagonal classical states. -/
theorem quantum_parallel_product
    (ρ σ : DensityMatrix Ript.Examples.QubitChannel.qubit) :
    quantumParallelKraus.applyDensity (ρ.tensor σ) =
      (Ript.Examples.QubitChannel.bitFlip.applyDensity ρ).tensor
        (Ript.Examples.QubitChannel.bitFlip.applyDensity σ) := by
  change (KrausChannel.tensor Ript.Examples.QubitChannel.bitFlip
    Ript.Examples.QubitChannel.bitFlip).applyDensity (ρ.tensor σ) = _
  rw [KrausChannel.tensor_applyDensity]

theorem quantum_parallel_basis (left right : Bool) :
    quantumParallelKraus.applyDensity
        ((Ript.Examples.QubitChannel.basisDensity left).tensor
          (Ript.Examples.QubitChannel.basisDensity right)) =
      (Ript.Examples.QubitChannel.basisDensity (!left)).tensor
        (Ript.Examples.QubitChannel.basisDensity (!right)) := by
  change (KrausChannel.tensor Ript.Examples.QubitChannel.bitFlip
    Ript.Examples.QubitChannel.bitFlip).applyDensity
      ((Ript.Examples.QubitChannel.basisDensity left).tensor
        (Ript.Examples.QubitChannel.basisDensity right)) = _
  exact Ript.Examples.QubitChannel.bitFlip_tensor_basisDensity left right

theorem causal_parallel (left right : Bool) :
    (ResourceChangingMonoidalInterpretation.eval causalInterpretation
      parallelFlipExpr).prob
        (Ript.Examples.CommonBitRealizations.causalParentInput left,
          Ript.Examples.CommonBitRealizations.causalParentInput right)
        (!left, !right) = 1 := by
  change (FinStoch.tensor
    Ript.Examples.CommonBitRealizations.causalFlipMechanism.toFinStoch
    Ript.Examples.CommonBitRealizations.causalFlipMechanism.toFinStoch).prob
      (Ript.Examples.CommonBitRealizations.causalParentInput left,
        Ript.Examples.CommonBitRealizations.causalParentInput right)
      (!left, !right) = 1
  simp [
    Ript.Examples.CommonBitRealizations.causalFlipMechanism,
    Ript.Examples.CommonBitRealizations.causalParentInput,
    Ript.Models.Causal.Mechanism.toFinStoch]

theorem computation_parallel (left right : Bool) :
    (ResourceChangingMonoidalInterpretation.eval computationInterpretation
      parallelFlipExpr).run (left, right) = (!left, !right) :=
  rfl

theorem computation_parallel_cost :
    processCost (R := ComputationResource)
        (ResourceChangingMonoidalInterpretation.eval computationInterpretation
          parallelFlipExpr) =
      Ript.Examples.CommonBitRealizations.computationResourceMap 2 :=
  by
    change
      (Ript.Models.Computation.Total.tensor
        Ript.Examples.SimpleComputation.totalNot
        Ript.Examples.SimpleComputation.totalNot).resource = _
    funext kind
    fin_cases kind <;> rfl

theorem semantic_parallel (left right : Bool) :
    (ResourceChangingMonoidalInterpretation.eval semanticInterpretation
      parallelFlipExpr).prob (left, right) (!left, !right) = 1 := by
  change (FinStoch.tensor
    Ript.Examples.CommonBitRealizations.semanticFlipExperiment
    Ript.Examples.CommonBitRealizations.semanticFlipExperiment).prob
      (left, right) (!left, !right) = 1
  simp [
    Ript.Examples.CommonBitRealizations.semanticFlipExperiment,
    FinStoch.dirac]

theorem thermal_parallel (left right : Bool) :
    (ResourceChangingMonoidalInterpretation.eval thermalInterpretation
      parallelFlipExpr).channel.prob (left, right) (!left, !right) = 1 := by
  change (GibbsPreserving.tensor
    Ript.Examples.SimpleThermalModel.thermalFlip
    Ript.Examples.SimpleThermalModel.thermalFlip).channel.prob
      (left, right) (!left, !right) = 1
  simp [Ript.Examples.SimpleThermalModel.thermalFlip,
    Ript.Examples.SimpleThermalModel.flipChannel, GibbsPreserving.tensor,
    FinStoch.tensor, FinStoch.dirac]

/-- **Six-model parallel agreement theorem.** -/
theorem sixModelParallelAgreement :
    (∀ left right : Bool, (ResourceChangingMonoidalInterpretation.eval
      probabilityInterpretation parallelFlipExpr).prob
        (left, right) (!left, !right) = 1) ∧
    (∀ left right : Bool, quantumParallelKraus.applyDensity
        ((Ript.Examples.QubitChannel.basisDensity left).tensor
          (Ript.Examples.QubitChannel.basisDensity right)) =
      (Ript.Examples.QubitChannel.basisDensity (!left)).tensor
        (Ript.Examples.QubitChannel.basisDensity (!right))) ∧
    (∀ left right : Bool, (ResourceChangingMonoidalInterpretation.eval
      causalInterpretation parallelFlipExpr).prob
        (Ript.Examples.CommonBitRealizations.causalParentInput left,
          Ript.Examples.CommonBitRealizations.causalParentInput right)
        (!left, !right) = 1) ∧
    (∀ left right : Bool, (ResourceChangingMonoidalInterpretation.eval
      computationInterpretation parallelFlipExpr).run
        (left, right) = (!left, !right)) ∧
    (∀ left right : Bool, (ResourceChangingMonoidalInterpretation.eval
      semanticInterpretation parallelFlipExpr).prob
        (left, right) (!left, !right) = 1) ∧
    (∀ left right : Bool, (ResourceChangingMonoidalInterpretation.eval
      thermalInterpretation parallelFlipExpr).channel.prob
        (left, right) (!left, !right) = 1) :=
  ⟨probability_parallel, quantum_parallel_basis, causal_parallel,
    computation_parallel, semantic_parallel, thermal_parallel⟩

/-! ## Universal lifts -/

/-- Canonical strong symmetric free lift into probability. -/
def probabilityFreeLift :
    ResourceChangeFunctor (MonoidalTermModel signature)
      Ript.Models.FiniteStochastic.Object Nat Nat
      (OrderAddMonoidHom.id Nat) :=
  ResourceChangingMonoidalFree.lift probabilityInterpretation

/-- Canonical strong symmetric free lift into the full finite Kraus category. -/
def quantumFreeLift :
    ResourceChangeFunctor (MonoidalTermModel signature)
      Ript.Models.Quantum.Object Nat Nat
      (OrderAddMonoidHom.id Nat) :=
  ResourceChangingMonoidalFree.lift quantumInterpretation

/-- Canonical strong symmetric free lift into causal channels. -/
def causalFreeLift :
    ResourceChangeFunctor (MonoidalTermModel signature)
      Ript.Models.FiniteStochastic.Object Nat Nat
      (OrderAddMonoidHom.id Nat) :=
  ResourceChangingMonoidalFree.lift causalInterpretation

/-- Canonical strong symmetric free lift into resource-aware computation. -/
def computationFreeLift :
    ResourceChangeFunctor (MonoidalTermModel signature)
      Ript.Models.Computation.Total.Object Nat ComputationResource
      Ript.Examples.CommonBitRealizations.computationResourceMap :=
  ResourceChangingMonoidalFree.lift computationInterpretation

/-- Canonical strong symmetric free lift into semantic experiments. -/
def semanticFreeLift :
    ResourceChangeFunctor (MonoidalTermModel signature)
      Ript.Models.FiniteStochastic.Object Nat Nat
      (OrderAddMonoidHom.id Nat) :=
  ResourceChangingMonoidalFree.lift semanticInterpretation

/-- Canonical strong symmetric free lift into thermal processes. -/
def thermalFreeLift :
    ResourceChangeFunctor (MonoidalTermModel signature)
      ThermalObject Nat Nat (OrderAddMonoidHom.id Nat) :=
  ResourceChangingMonoidalFree.lift thermalInterpretation

/-- All six parallel interpretations induce canonical strong symmetric
monoidal resource-changing lifts from one free term model. -/
theorem sixModelMonoidalFreeLiftOnGenerator :
    probabilityFreeLift.toFunctor.map
        (MonoidalTermModel.quote signature (.gen .flip)) =
          probabilityInterpretation.mapGen .flip ∧
    quantumFreeLift.toFunctor.map
        (MonoidalTermModel.quote signature (.gen .flip)) =
          quantumInterpretation.mapGen .flip ∧
    causalFreeLift.toFunctor.map
        (MonoidalTermModel.quote signature (.gen .flip)) =
          causalInterpretation.mapGen .flip ∧
    computationFreeLift.toFunctor.map
        (MonoidalTermModel.quote signature (.gen .flip)) =
          computationInterpretation.mapGen .flip ∧
    semanticFreeLift.toFunctor.map
        (MonoidalTermModel.quote signature (.gen .flip)) =
          semanticInterpretation.mapGen .flip ∧
    thermalFreeLift.toFunctor.map
        (MonoidalTermModel.quote signature (.gen .flip)) =
          thermalInterpretation.mapGen .flip :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Ript.Examples.ParallelBitRealizations
