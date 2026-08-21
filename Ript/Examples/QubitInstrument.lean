import Mathlib.Tactic.NormNum
import Ript.Examples.QubitChannel
import Ript.Models.Quantum.Instrument
import Ript.Models.Quantum.InstrumentTree

/-!
# A finite computational-basis quantum instrument

This example measures a qubit in the Boolean computational basis.  Each
outcome is a one-projector quantum operation, while their sum is the
trace-preserving dephasing channel.  A coherent `|+⟩` input produces two exact
half-probability outcomes and the corresponding normalized basis posterior.
-/

set_option autoImplicit false

namespace Ript.Examples.QubitInstrument

open Matrix
open Ript.Models.Quantum
open scoped BigOperators ComplexConjugate ComplexOrder

/-- Projector onto one computational-basis outcome. -/
def basisProjector (outcome : Bool) :
    Matrix QubitChannel.qubit QubitChannel.qubit ℂ :=
  Matrix.single outcome outcome 1

/-- The two computational-basis projectors resolve the identity. -/
theorem basisProjector_complete :
    ∑ outcome : Bool, (basisProjector outcome)ᴴ * basisProjector outcome = 1 := by
  ext row column
  change Bool at row column
  cases row <;> cases column <;>
    simp [basisProjector]

/-- One unnormalized measurement branch. -/
def branch (outcome : Bool) :
    KrausOperation QubitChannel.qubit QubitChannel.qubit :=
  KrausOperation.ofOperators (I := PUnit) (fun _ ↦ basisProjector outcome)

/-- Forgetting the outcome gives complete computational-basis dephasing. -/
def dephase : KrausChannel QubitChannel.qubit QubitChannel.qubit :=
  KrausChannel.ofOperators basisProjector basisProjector_complete

/-- The Boolean computational-basis projective instrument. -/
def computationalMeasurement :
    KrausInstrument Bool QubitChannel.qubit QubitChannel.qubit where
  branch := branch
  total := dephase
  total_map ρ := by
    ext row column
    change Bool at row column
    cases row <;> cases column <;>
      simp [dephase, branch, basisProjector, KrausChannel.ofOperators,
        KrausOperation.ofOperators]

/-- Unnormalized branch action on a computational-basis state. -/
theorem branch_basisDensity (outcome value : Bool) :
    (branch outcome).map (QubitChannel.basisDensity value).matrix =
      if outcome = value then (QubitChannel.basisDensity value).matrix else 0 := by
  ext row column
  change Bool at outcome value row column
  cases outcome <;> cases value <;> cases row <;> cases column <;>
    simp [branch, basisProjector, KrausOperation.ofOperators,
      QubitChannel.basisDensity]

/-- Measurement of a basis state has the deterministic matching outcome. -/
theorem outcomeProbability_basis (outcome value : Bool) :
    computationalMeasurement.outcomeProbability
        (QubitChannel.basisDensity value) outcome =
      if outcome = value then 1 else 0 := by
  apply NNReal.eq
  simp only [KrausInstrument.outcomeProbability_coe_real]
  change ((branch outcome).map
    (QubitChannel.basisDensity value).matrix).trace.re = _
  rw [branch_basisDensity]
  split_ifs with equal
  · rw [(QubitChannel.basisDensity value).trace_one]
    norm_num
  · simp

/-- Constant Boolean vector representing the unnormalized `|+⟩` state. -/
def plusVector : Bool → ℂ := fun _ ↦ 1

/-- Rank-one projector onto the unnormalized plus vector. -/
def plusProjector : Matrix QubitChannel.qubit QubitChannel.qubit ℂ :=
  Matrix.vecMulVec plusVector (star plusVector)

theorem plusProjector_posSemidef : plusProjector.PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star plusVector

theorem plusDensity_trace_one :
    Matrix.trace (((2 : ℝ)⁻¹ • plusProjector)) = 1 := by
  rw [Matrix.trace_smul]
  have hcard : Fintype.card QubitChannel.qubit = 2 := by decide
  norm_num [plusProjector, plusVector, Matrix.trace_vecMulVec, dotProduct,
    hcard]

/-- Coherent plus state with every matrix entry equal to one half. -/
noncomputable def plusDensity : DensityMatrix QubitChannel.qubit where
  matrix := ((2 : ℝ)⁻¹ • plusProjector)
  posSemidef := plusProjector_posSemidef.smul (by norm_num)
  trace_one := plusDensity_trace_one

theorem plusDensity_entry (row column : Bool) :
    plusDensity.matrix row column = (2 : ℂ)⁻¹ := by
  norm_num [plusDensity, plusProjector, plusVector, Matrix.vecMulVec_apply]

/-- Each computational-basis outcome has exact probability one half on the
coherent plus state. -/
theorem outcomeProbability_plus (outcome : Bool) :
    computationalMeasurement.outcomeProbability plusDensity outcome =
      (2 : NNReal)⁻¹ := by
  apply NNReal.eq
  change
    ((branch outcome).map plusDensity.matrix).trace.re =
      (((2 : NNReal)⁻¹ : NNReal) : ℝ)
  cases outcome
  all_goals norm_num [branch, basisProjector, KrausOperation.ofOperators,
      plusDensity, plusProjector, plusVector, Matrix.trace,
      Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
      Matrix.single_apply]

/-- Conditioning the plus-state measurement on its observed result yields the
matching basis state. -/
theorem posterior_plus (outcome : Bool) :
    computationalMeasurement.posterior plusDensity outcome
        (by rw [outcomeProbability_plus]; norm_num) =
      QubitChannel.basisDensity outcome := by
  apply DensityMatrix.ext
  ext row column
  change Bool at outcome row column
  cases outcome <;> cases row <;> cases column <;>
    norm_num [KrausInstrument.posterior, computationalMeasurement,
      outcomeProbability_plus, branch, basisProjector,
      KrausOperation.ofOperators, plusDensity, plusProjector, plusVector,
      QubitChannel.basisDensity, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.vecMulVec_apply, Matrix.single_apply]
  all_goals simp

/-- Two independent plus-state measurements have exact joint probability one
quarter for every outcome pair. -/
theorem tensor_outcomeProbability_plus (left right : Bool) :
    (computationalMeasurement.tensor computationalMeasurement).outcomeProbability
        (plusDensity.tensor plusDensity) (left, right) = (4 : NNReal)⁻¹ := by
  rw [KrausInstrument.tensor_outcomeProbability,
    outcomeProbability_plus, outcomeProbability_plus]
  norm_num

/-! ## Adaptive classical feedback -/

/-- Outcome-controlled correction: flip the residual qubit only after the
`true` measurement result. -/
def correctionChannel (outcome : Bool) :
    KrausChannel QubitChannel.qubit QubitChannel.qubit :=
  if outcome then QubitChannel.bitFlip
  else KrausChannel.identity QubitChannel.qubit

/-- Measure the qubit and use its classical result to correct every posterior
to the `false` basis state. -/
noncomputable def correctedMeasurement :
    KrausInstrument Bool QubitChannel.qubit QubitChannel.qubit :=
  computationalMeasurement.controlledPostcompose correctionChannel

/-- Classical feedback does not alter the measurement outcome weights. -/
theorem corrected_outcomeProbability_plus (outcome : Bool) :
    correctedMeasurement.outcomeProbability plusDensity outcome =
      (2 : NNReal)⁻¹ := by
  rw [correctedMeasurement,
    KrausInstrument.controlledPostcompose_outcomeProbability,
    outcomeProbability_plus]

/-- Both controlled branches are the same half-normalized `false` projector
on the coherent plus input. -/
theorem corrected_branch_plus (outcome : Bool) :
    (correctedMeasurement.branch outcome).map plusDensity.matrix =
      ((2 : ℝ)⁻¹ • (QubitChannel.basisDensity false).matrix) := by
  ext row column
  change Bool at outcome row column
  cases outcome <;> cases row <;> cases column <;>
    norm_num [correctedMeasurement, correctionChannel,
      KrausInstrument.controlledPostcompose_branch_map,
      computationalMeasurement, branch, basisProjector,
      KrausOperation.ofOperators, KrausOperation.ofChannel,
      QubitChannel.bitFlip, QubitChannel.bitFlipOperator,
      KrausChannel.identity, KrausChannel.ofOperators,
      plusDensity, plusProjector, plusVector,
      QubitChannel.basisDensity, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.vecMulVec_apply, Matrix.single_apply]
  all_goals simp

/-- Conditioning after adaptive correction yields `false` for either recorded
measurement result. -/
theorem corrected_posterior_plus (outcome : Bool) :
    correctedMeasurement.posterior plusDensity outcome
        (by rw [corrected_outcomeProbability_plus]; norm_num) =
      QubitChannel.basisDensity false := by
  apply DensityMatrix.ext
  change
    ((correctedMeasurement.outcomeProbability plusDensity outcome : ℝ)⁻¹) •
        (correctedMeasurement.branch outcome).map plusDensity.matrix =
      (QubitChannel.basisDensity false).matrix
  rw [corrected_branch_plus, corrected_outcomeProbability_plus]
  rw [smul_smul]
  norm_num

/-- Forgetting the result of the adaptive measurement resets the coherent
input exactly to the `false` basis state. -/
theorem corrected_total_plus :
    correctedMeasurement.total.applyDensity plusDensity =
      QubitChannel.basisDensity false := by
  apply DensityMatrix.ext
  rw [KrausChannel.applyDensity_matrix, correctedMeasurement.total_map]
  simp_rw [corrected_branch_plus]
  simp only [Fintype.sum_bool]
  ext row column
  change ((2 : ℝ)⁻¹ * (QubitChannel.basisDensity false).matrix row column) +
      ((2 : ℝ)⁻¹ * (QubitChannel.basisDensity false).matrix row column) =
    (QubitChannel.basisDensity false).matrix row column
  norm_num
  ring

/-! ## A genuinely dependent two-round outcome tree -/

/-- If the first result is `false`, the second round only acknowledges it; if
the first result is `true`, the qubit is measured again with a Boolean
result. -/
abbrev SecondOutcome (first : Bool) : Type :=
  match first with
  | false => PUnit
  | true => Bool

instance secondOutcomeFintype (first : Bool) : Fintype (SecondOutcome first) := by
  cases first <;> simp [SecondOutcome] <;> infer_instance

instance secondOutcomeDecidableEq (first : Bool) :
    DecidableEq (SecondOutcome first) := by
  cases first <;> simp [SecondOutcome] <;> infer_instance

/-- The first outcome selects a one-outcome identity continuation or a second
computational measurement. -/
def secondRound (first : Bool) :
    KrausInstrument (SecondOutcome first)
      QubitChannel.qubit QubitChannel.qubit :=
  match first with
  | false => KrausInstrument.ofChannel
      (KrausChannel.identity QubitChannel.qubit)
  | true => computationalMeasurement

/-- Dependent two-round measurement tree. -/
noncomputable def twoRoundTree :
    KrausInstrument (Σ first, SecondOutcome first)
      QubitChannel.qubit QubitChannel.qubit :=
  computationalMeasurement.bind secondRound

/-- The short `false` branch retains probability one half. -/
theorem twoRoundTree_false_probability :
    twoRoundTree.outcomeProbability plusDensity ⟨false, PUnit.unit⟩ =
      (2 : NNReal)⁻¹ := by
  rw [twoRoundTree, KrausInstrument.bind_outcomeProbability
    (positive := by rw [outcomeProbability_plus]; norm_num)]
  simp [secondRound, outcomeProbability_plus]

/-- Repeating the measurement after first observing `true` returns `true`
with joint probability one half. -/
theorem twoRoundTree_true_true_probability :
    twoRoundTree.outcomeProbability plusDensity ⟨true, true⟩ =
      (2 : NNReal)⁻¹ := by
  rw [twoRoundTree, KrausInstrument.bind_outcomeProbability
    (positive := by rw [outcomeProbability_plus]; norm_num)]
  simp [secondRound, outcomeProbability_plus, posterior_plus,
    outcomeProbability_basis]

/-- The inconsistent history `true` followed by `false` has zero
probability. -/
theorem twoRoundTree_true_false_probability :
    twoRoundTree.outcomeProbability plusDensity ⟨true, false⟩ = 0 := by
  rw [twoRoundTree, KrausInstrument.bind_outcomeProbability
    (positive := by rw [outcomeProbability_plus]; norm_num)]
  simp [secondRound, outcomeProbability_plus, posterior_plus,
    outcomeProbability_basis]

/-- The three dependent histories remain globally normalized. -/
theorem twoRoundTree_normalized :
    ∑ result, twoRoundTree.outcomeProbability plusDensity result = 1 :=
  KrausInstrument.outcomeProbability_normalized twoRoundTree plusDensity

/-! ## First-class recursive tree syntax -/

/-- The same adaptive protocol represented as a first-class recursive tree:
stop immediately after `false`, but measure once more after `true`. -/
def recursiveTree :
    InstrumentTree QubitChannel.qubit QubitChannel.qubit :=
  .step computationalMeasurement 1 (fun first ↦
    match first with
    | false => .done (KrausChannel.identity QubitChannel.qubit)
    | true => .step computationalMeasurement 1 (fun _ ↦
        .done (KrausChannel.identity QubitChannel.qubit)))

/-- Canonical short history. -/
def recursiveTreeShortHistory : recursiveTree.History :=
  ⟨false, PUnit.unit⟩

/-- Canonical long history after the first `true` result. -/
def recursiveTreeLongHistory (second : Bool) : recursiveTree.History :=
  ⟨true, second, PUnit.unit⟩

/-- The dependent recursive tree has exactly three canonical histories. -/
theorem recursiveTree_history_card :
    Fintype.card recursiveTree.History = 3 := by
  decide

@[simp]
theorem recursiveTree_budget : recursiveTree.budget = 2 := by
  decide

@[simp]
theorem recursiveTree_short_cost :
    recursiveTree.historyCost recursiveTreeShortHistory = 1 :=
  rfl

@[simp]
theorem recursiveTree_long_cost (second : Bool) :
    recursiveTree.historyCost (recursiveTreeLongHistory second) = 2 :=
  rfl

/-- The evaluated recursive tree is normalized over all three histories. -/
theorem recursiveTree_normalized :
    ∑ history, recursiveTree.eval.outcomeProbability plusDensity history = 1 :=
  recursiveTree.eval_outcomeProbability_normalized plusDensity

/-- Every recursive-tree history branch is represented exactly by its
canonical history normal form. -/
theorem recursiveTree_history_representation
    (history : recursiveTree.History)
    (ρ : Matrix QubitChannel.qubit QubitChannel.qubit ℂ) :
    ((recursiveTree.eval.branch history).map ρ) =
      recursiveTree.branchMap history ρ :=
  recursiveTree.eval_branch_map history ρ

end Ript.Examples.QubitInstrument
