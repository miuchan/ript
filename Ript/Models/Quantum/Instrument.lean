import Mathlib.Data.NNReal.Defs
import Ript.Models.Quantum.Operation

/-!
# Finite quantum instruments

A finite quantum instrument is a finite family of completely positive quantum
operations whose sum is a trace-preserving Kraus channel.  This formulation
keeps every outcome branch extensional, exposes normalized outcome
probabilities and posterior states, and supports serial channel processing and
independent tensor products.
-/

set_option autoImplicit false

namespace Ript.Models.Quantum

open Matrix
open scoped BigOperators ComplexOrder Kronecker

universe u

/-- A finite family of quantum-operation branches whose sum is a channel. -/
structure KrausInstrument (Outcome : Type u) [Fintype Outcome]
    (X Y : Object.{u}) where
  /-- Completely positive operation for each classical outcome. -/
  branch : Outcome → KrausOperation X Y
  /-- Trace-preserving channel obtained after forgetting the outcome. -/
  total : KrausChannel X Y
  /-- The total channel is exactly the sum of all outcome branches. -/
  total_map : ∀ ρ, total.map ρ = ∑ outcome, (branch outcome).map ρ

namespace KrausInstrument

variable {Outcome Result : Type u} [Fintype Outcome] [Fintype Result]
variable {V W X Y Z T : Object.{u}}

/-- Trivial one-outcome instrument for the identity channel. -/
def identity (X : Object.{u}) : KrausInstrument PUnit X X where
  branch _ := KrausOperation.ofChannel (KrausChannel.identity X)
  total := KrausChannel.identity X
  total_map ρ := by simp

/-- Regard an ordinary trace-preserving channel as a one-outcome
instrument. -/
def ofChannel (channel : KrausChannel X Y) : KrausInstrument PUnit X Y where
  branch _ := KrausOperation.ofChannel channel
  total := channel
  total_map ρ := by simp

/-- Sequential composition records both the first and second outcomes.  Its
total channel is ordinary channel composition, while every joint branch is
the serial composite of the corresponding operations. -/
def comp (first : KrausInstrument Outcome X Y)
    (second : KrausInstrument Result Y Z) :
    KrausInstrument (Outcome × Result) X Z where
  branch pair :=
    KrausOperation.comp (first.branch pair.1) (second.branch pair.2)
  total := KrausChannel.comp first.total second.total
  total_map ρ := by
    rw [KrausChannel.comp_map, first.total_map]
    change second.total.toLinearMap
        (∑ outcome, (first.branch outcome).map ρ) = _
    rw [map_sum]
    simp only [Fintype.sum_prod_type]
    apply Fintype.sum_congr
    intro outcome
    change second.total.map ((first.branch outcome).map ρ) =
      ∑ result, (second.branch result).map ((first.branch outcome).map ρ)
    rw [second.total_map]

@[simp]
theorem comp_branch_map (first : KrausInstrument Outcome X Y)
    (second : KrausInstrument Result Y Z) (outcome : Outcome)
    (result : Result) (ρ : Matrix X X ℂ) :
    (((first.comp second).branch (outcome, result)).map ρ) =
      (second.branch result).map ((first.branch outcome).map ρ) :=
  rfl

@[simp]
theorem identity_branch_map (X : Object.{u}) (ρ : Matrix X X ℂ) :
    (((identity X).branch PUnit.unit).map ρ) = ρ := by
  simp [identity]

/-- The total channel is determined by the outcome operations. -/
@[ext]
theorem ext (first second : KrausInstrument Outcome X Y)
    (branch_eq : first.branch = second.branch) : first = second := by
  have total_eq : first.total = second.total := by
    apply KrausChannel.ext
    funext ρ
    rw [first.total_map, second.total_map, branch_eq]
  cases first
  cases second
  cases branch_eq
  cases total_eq
  rfl

/-- Sum of all branch linear maps. -/
def branchSumLinearMap (instrument : KrausInstrument Outcome X Y) :
    Matrix X X ℂ →ₗ[ℂ] Matrix Y Y ℂ :=
  ∑ outcome, (instrument.branch outcome).toLinearMap

@[simp]
theorem branchSumLinearMap_apply (instrument : KrausInstrument Outcome X Y)
    (ρ : Matrix X X ℂ) :
    instrument.branchSumLinearMap ρ =
      ∑ outcome, (instrument.branch outcome).map ρ := by
  simp [branchSumLinearMap]

/-- Linear-map form of the instrument normalization equation. -/
theorem total_toLinearMap (instrument : KrausInstrument Outcome X Y) :
    instrument.total.toLinearMap = instrument.branchSumLinearMap := by
  apply LinearMap.ext
  intro ρ
  change instrument.total.map ρ = _
  rw [instrument.branchSumLinearMap_apply]
  exact instrument.total_map ρ

/-- Each outcome branch sends positive matrices to positive matrices. -/
theorem branch_posSemidef (instrument : KrausInstrument Outcome X Y)
    (outcome : Outcome) {ρ : Matrix X X ℂ} (hρ : ρ.PosSemidef) :
    ((instrument.branch outcome).map ρ).PosSemidef :=
  (instrument.branch outcome).map_posSemidef hρ

/-- The trace of every outcome branch is a nonnegative complex real. -/
theorem branch_trace_nonneg (instrument : KrausInstrument Outcome X Y)
    (state : DensityMatrix X) (outcome : Outcome) :
    0 ≤ ((instrument.branch outcome).map state.matrix).trace :=
  (instrument.branch_posSemidef outcome state.posSemidef).trace_nonneg

/-- Born weight of one instrument outcome as a nonnegative real. -/
noncomputable def outcomeProbability
    (instrument : KrausInstrument Outcome X Y) (state : DensityMatrix X)
    (outcome : Outcome) : NNReal :=
  ⟨((instrument.branch outcome).map state.matrix).trace.re,
    (Complex.nonneg_iff.mp
      (instrument.branch_trace_nonneg state outcome)).1⟩

@[simp]
theorem outcomeProbability_coe_real
    (instrument : KrausInstrument Outcome X Y) (state : DensityMatrix X)
    (outcome : Outcome) :
    (instrument.outcomeProbability state outcome : ℝ) =
      ((instrument.branch outcome).map state.matrix).trace.re :=
  rfl

/-- The nonnegative real outcome probability, embedded into `ℂ`, is exactly
the branch trace. -/
theorem outcomeProbability_coe_complex
    (instrument : KrausInstrument Outcome X Y) (state : DensityMatrix X)
    (outcome : Outcome) :
    ((instrument.outcomeProbability state outcome : ℝ) : ℂ) =
      ((instrument.branch outcome).map state.matrix).trace := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp
      (instrument.branch_trace_nonneg state outcome)).2

/-- Instrument outcome probabilities sum exactly to one. -/
theorem outcomeProbability_normalized
    (instrument : KrausInstrument Outcome X Y) (state : DensityMatrix X) :
    ∑ outcome, instrument.outcomeProbability state outcome = 1 := by
  apply NNReal.eq
  have totalTrace :
      (∑ outcome,
          ((instrument.branch outcome).map state.matrix).trace) = 1 := by
    rw [← Matrix.trace_sum, ← instrument.total_map,
      instrument.total.map_trace, state.trace_one]
  have realTotal := congrArg Complex.re totalTrace
  simpa using realTotal

@[simp]
theorem ofChannel_outcomeProbability (channel : KrausChannel X Y)
    (state : DensityMatrix X) :
    (ofChannel channel).outcomeProbability state PUnit.unit = 1 := by
  apply NNReal.eq
  change (channel.map state.matrix).trace.re = 1
  rw [channel.map_trace, state.trace_one]
  norm_num

/-! ## Classical-record channel representation -/

 /-- A proof-only selected Kraus representation for an operation family. -/
noncomputable def chosenOperationRepresentation
    (operations : Outcome → KrausOperation X Y) (outcome : Outcome) :
    KrausOperationRepresentation X Y (operations outcome).map :=
  Classical.choice (operations outcome).has_representation

/-- If the sum of a finite family of completely positive operations preserves
the trace of every matrix, then the union of any selected branch Kraus
families satisfies the channel completeness equation. -/
theorem operationFamily_complete_of_tracePreserving
    (operations : Outcome → KrausOperation X Y)
    (tracePreserving : ∀ ρ : Matrix X X ℂ,
      (∑ outcome, (operations outcome).map ρ).trace = ρ.trace) :
    ∑ outcome, ∑ i : (chosenOperationRepresentation operations outcome).index,
        ((chosenOperationRepresentation operations outcome).operators i)ᴴ *
          (chosenOperationRepresentation operations outcome).operators i = 1 := by
  let operatorSum : Matrix X X ℂ :=
    ∑ outcome, ∑ i : (chosenOperationRepresentation operations outcome).index,
      ((chosenOperationRepresentation operations outcome).operators i)ᴴ *
        (chosenOperationRepresentation operations outcome).operators i
  change operatorSum = 1
  apply Matrix.ext
  intro x x'
  let probe : Matrix X X ℂ := Matrix.single x' x 1
  have totalTrace := tracePreserving probe
  have operatorTrace : (operatorSum * probe).trace = probe.trace := by
    calc
      (operatorSum * probe).trace =
          ∑ outcome, ∑ i :
              (chosenOperationRepresentation operations outcome).index,
            ((((chosenOperationRepresentation operations outcome).operators i)ᴴ *
              (chosenOperationRepresentation operations outcome).operators i) *
                probe).trace := by
          simp [operatorSum, Matrix.sum_mul, Matrix.trace_sum]
      _ = ∑ outcome, ∑ i :
              (chosenOperationRepresentation operations outcome).index,
            (((chosenOperationRepresentation operations outcome).operators i *
              probe) *
                ((chosenOperationRepresentation operations outcome).operators i)ᴴ).trace := by
          apply Fintype.sum_congr
          intro outcome
          apply Fintype.sum_congr
          intro i
          symm
          rw [Matrix.trace_mul_cycle]
      _ = (∑ outcome, (operations outcome).map probe).trace := by
          simp_rw [(chosenOperationRepresentation operations _).map_eq]
          rw [Matrix.trace_sum]
          apply Fintype.sum_congr
          intro outcome
          rw [Matrix.trace_sum]
      _ = probe.trace := totalTrace
  by_cases equal : x = x'
  · subst x'
    dsimp [probe] at operatorTrace
    rw [Matrix.trace_mul_single,
      Matrix.trace_single_eq_same x 1] at operatorTrace
    simpa [operatorSum, Matrix.one_apply] using operatorTrace
  · have reverse : x' ≠ x := Ne.symm equal
    dsimp [probe] at operatorTrace
    rw [Matrix.trace_mul_single,
      Matrix.trace_single_eq_of_ne x' x 1 reverse] at operatorTrace
    simpa [operatorSum, Matrix.one_apply, equal] using operatorTrace

/-- A proof-only selected Kraus representation for one instrument branch. -/
noncomputable abbrev chosenBranchRepresentation
    (instrument : KrausInstrument Outcome X Y) (outcome : Outcome) :
    KrausOperationRepresentation X Y (instrument.branch outcome).map :=
  chosenOperationRepresentation instrument.branch outcome

/-- Trace preservation of an instrument total supplies completeness of its
combined selected branch family. -/
theorem chosenBranchRepresentation_complete
    (instrument : KrausInstrument Outcome X Y) :
    ∑ outcome, ∑ i : (instrument.chosenBranchRepresentation outcome).index,
        ((instrument.chosenBranchRepresentation outcome).operators i)ᴴ *
          (instrument.chosenBranchRepresentation outcome).operators i = 1 := by
  apply operationFamily_complete_of_tracePreserving instrument.branch
  intro ρ
  rw [← instrument.total_map]
  exact instrument.total.map_trace ρ

/-- Construct a normalized instrument directly from a trace-preserving finite
family of completely positive operations. -/
noncomputable def ofTracePreservingOperations
    (operations : Outcome → KrausOperation X Y)
    (tracePreserving : ∀ ρ : Matrix X X ℂ,
      (∑ outcome, (operations outcome).map ρ).trace = ρ.trace) :
    KrausInstrument Outcome X Y where
  branch := operations
  total := KrausChannel.ofOperators
    (I := Σ outcome,
      (chosenOperationRepresentation operations outcome).index)
    (fun label ↦
      (chosenOperationRepresentation operations label.1).operators label.2)
    (by
      rw [Fintype.sum_sigma]
      exact operationFamily_complete_of_tracePreserving operations
        tracePreserving)
  total_map ρ := by
    simp only [KrausChannel.ofOperators, Fintype.sum_sigma]
    apply Fintype.sum_congr
    intro outcome
    exact (chosenOperationRepresentation operations outcome).map_eq ρ |>.symm

/-- Embed one branch operator into the block indexed by its classical
outcome. -/
def recordOperator [DecidableEq Outcome] (outcome : Outcome)
    (operator : Matrix Y X ℂ) : Matrix (Outcome × Y) X ℂ :=
  fun row column ↦ if row.1 = outcome then operator row.2 column else 0

/-- Adding a classical record does not change `KᴴK`. -/
theorem recordOperator_conjTranspose_mul [DecidableEq Outcome]
    (outcome : Outcome) (operator : Matrix Y X ℂ) :
    (recordOperator outcome operator)ᴴ * recordOperator outcome operator =
      operatorᴴ * operator := by
  ext x x'
  simp [recordOperator, Matrix.mul_apply, Fintype.sum_prod_type]

omit [Fintype Outcome] in
/-- One recorded Kraus summand occupies exactly one diagonal classical
block. -/
theorem recordOperator_action [DecidableEq Outcome] (label : Outcome)
    (operator : Matrix Y X ℂ) (ρ : Matrix X X ℂ)
    (outcome outcome' : Outcome) (y y' : Y) :
    (recordOperator label operator * ρ * (recordOperator label operator)ᴴ)
        (outcome, y) (outcome', y') =
      if outcome = label ∧ outcome' = label then
        (operator * ρ * operatorᴴ) y y' else 0 := by
  by_cases first : outcome = label <;>
    by_cases second : outcome' = label <;>
      simp [recordOperator, Matrix.mul_apply, first, second]

/-- Quantum object used for the explicit classical outcome register. -/
abbrev outcomeObject (Outcome : Type u) [Fintype Outcome]
    [DecidableEq Outcome] : Object.{u} :=
  ⟨Outcome, inferInstance, inferInstance⟩

/-- Every finite instrument is represented by a single channel whose output
contains a classical outcome register and the residual quantum system. -/
noncomputable def recordedChannel [DecidableEq Outcome]
    (instrument : KrausInstrument Outcome X Y) :
    KrausChannel X (Object.tensor (outcomeObject Outcome) Y) :=
  KrausChannel.ofOperators
    (I := Σ outcome,
      (instrument.chosenBranchRepresentation outcome).index)
    (fun label ↦ recordOperator label.1
      ((instrument.chosenBranchRepresentation label.1).operators label.2))
    (by
      rw [Fintype.sum_sigma]
      simp_rw [recordOperator_conjTranspose_mul]
      exact instrument.chosenBranchRepresentation_complete)

/-- Matrix blocks of the recorded channel recover exactly the corresponding
instrument branch; off-diagonal classical blocks vanish. -/
theorem recordedChannel_map_apply [DecidableEq Outcome]
    (instrument : KrausInstrument Outcome X Y) (ρ : Matrix X X ℂ)
    (outcome outcome' : Outcome) (y y' : Y) :
    (instrument.recordedChannel.map ρ) (outcome, y) (outcome', y') =
      if outcome = outcome' then
        (instrument.branch outcome).map ρ y y' else 0 := by
  rw [recordedChannel]
  simp only [KrausChannel.ofOperators, Matrix.sum_apply,
    Fintype.sum_sigma]
  simp_rw [recordOperator_action]
  by_cases equal : outcome = outcome'
  · subst outcome'
    simp only [if_pos]
    rw [(instrument.chosenBranchRepresentation outcome).map_eq]
    simp [Matrix.sum_apply]
  · rw [if_neg equal]
    apply (Finset.sum_eq_zero fun label _ ↦ ?_)
    split_ifs with both
    · exact (equal (both.1.trans both.2.symm)).elim
    · simp

/-- The classical-record channel faithfully represents the entire finite
instrument: equality of recorded channels reflects equality of every quantum
operation branch and hence of the normalized instrument. -/
theorem recordedChannel_injective [DecidableEq Outcome] :
    Function.Injective
      (recordedChannel : KrausInstrument Outcome X Y →
        KrausChannel X (Object.tensor (outcomeObject Outcome) Y)) := by
  intro first second equal
  apply KrausInstrument.ext first second
  funext outcome
  apply KrausOperation.ext
  funext ρ
  apply Matrix.ext
  intro y y'
  have blockEqual := congrArg
    (fun channel ↦ channel.map ρ (outcome, y) (outcome, y')) equal
  have firstBlock := recordedChannel_map_apply
    first ρ outcome outcome y y'
  have secondBlock := recordedChannel_map_apply
    second ρ outcome outcome y y'
  simp only [if_pos] at firstBlock secondBlock
  exact firstBlock.symm.trans (blockEqual.trans secondBlock)

/-- Equality of finite instruments is equivalent to equality of their
classical-record channel representations. -/
theorem recordedChannel_eq_iff [DecidableEq Outcome]
    (first second : KrausInstrument Outcome X Y) :
    first.recordedChannel = second.recordedChannel ↔ first = second :=
  ⟨fun equal ↦ recordedChannel_injective equal,
    fun equal ↦ congrArg recordedChannel equal⟩

/-! ## Intrinsic image of the classical-record representation -/

/-- Restrict one Kraus operator with output rows `Outcome × Y` to the
rows belonging to one classical outcome. -/
def outcomeOperator (outcome : Outcome)
    (operator : Matrix (Outcome × Y) X ℂ) : Matrix Y X ℂ :=
  fun y x ↦ operator (outcome, y) x

/-- Slicing an output operator over every classical outcome preserves its
`KᴴK` contribution. -/
theorem outcomeOperator_complete
    (operator : Matrix (Outcome × Y) X ℂ) :
    ∑ outcome, (outcomeOperator outcome operator)ᴴ *
        outcomeOperator outcome operator = operatorᴴ * operator := by
  ext x x'
  simp only [Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, outcomeOperator]
  rw [Fintype.sum_prod_type]

section ClassicalOutcome

variable [DecidableEq Outcome]

/-- A proof-only selected Kraus representation of a channel whose output
contains a classical result register. -/
noncomputable def chosenRecordedChannelRepresentation
    (channel : KrausChannel X
      (Object.tensor (outcomeObject Outcome) Y)) :
    KrausRepresentation X (Object.tensor (outcomeObject Outcome) Y)
      channel.map :=
  Classical.choice channel.has_representation

/-- Extract the completely positive operation associated with one diagonal
classical-result block of a recorded-output channel. -/
noncomputable def extractOperation
    (channel : KrausChannel X
      (Object.tensor (outcomeObject Outcome) Y))
    (outcome : Outcome) : KrausOperation X Y :=
  KrausOperation.ofOperators
    (fun i ↦ outcomeOperator (X := X) (Y := Y) outcome
      ((chosenRecordedChannelRepresentation channel).operators i))

/-- The extracted operation is exactly the corresponding diagonal block of
the original channel. -/
theorem extractOperation_map
    (channel : KrausChannel X
      (Object.tensor (outcomeObject Outcome) Y))
    (outcome : Outcome) (ρ : Matrix X X ℂ) (y y' : Y) :
    (extractOperation channel outcome).map ρ y y' =
      channel.map ρ (outcome, y) (outcome, y') := by
  rw [(chosenRecordedChannelRepresentation channel).map_eq]
  simp only [extractOperation, KrausOperation.ofOperators,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    outcomeOperator]

/-- The extracted diagonal operations have trace-preserving total even when
the original channel also contains coherent off-diagonal outcome blocks. -/
theorem extractOperations_tracePreserving
    (channel : KrausChannel X
      (Object.tensor (outcomeObject Outcome) Y))
    (ρ : Matrix X X ℂ) :
    (∑ outcome, (extractOperation channel outcome).map ρ).trace =
      ρ.trace := by
  rw [Matrix.trace_sum]
  calc
    ∑ outcome, ((extractOperation channel outcome).map ρ).trace =
        (channel.map ρ).trace := by
      simp only [Matrix.trace, Matrix.diag]
      simp_rw [extractOperation_map]
      rw [Fintype.sum_prod_type]
    _ = ρ.trace := channel.map_trace ρ

/-- Canonical instrument extracted from the diagonal classical-result blocks
of an arbitrary recorded-output channel. -/
noncomputable def extractInstrument
    (channel : KrausChannel X
      (Object.tensor (outcomeObject Outcome) Y)) :
    KrausInstrument Outcome X Y :=
  ofTracePreservingOperations
    (extractOperation channel)
    (extractOperations_tracePreserving channel)

@[simp]
theorem extractInstrument_branch_map
    (channel : KrausChannel X
      (Object.tensor (outcomeObject Outcome) Y))
    (outcome : Outcome) (ρ : Matrix X X ℂ) :
    ((extractInstrument channel).branch outcome).map ρ =
      (extractOperation channel outcome).map ρ :=
  rfl

/-- Recording the extracted instrument block-diagonalizes the original
channel in its classical outcome register. -/
theorem extractInstrument_recordedChannel_map_apply
    (channel : KrausChannel X
      (Object.tensor (outcomeObject Outcome) Y))
    (ρ : Matrix X X ℂ) (outcome outcome' : Outcome) (y y' : Y) :
    ((extractInstrument channel).recordedChannel.map ρ)
        (outcome, y) (outcome', y') =
      if outcome = outcome' then
        channel.map ρ (outcome, y) (outcome, y') else 0 := by
  rw [recordedChannel_map_apply]
  split_ifs with equal
  · calc
      ((extractInstrument channel).branch outcome).map ρ y y' =
          (extractOperation channel outcome).map ρ y y' :=
        congrArg (fun matrix ↦ matrix y y')
          (extractInstrument_branch_map channel outcome ρ)
      _ = channel.map ρ (outcome, y) (outcome, y') :=
        extractOperation_map channel outcome ρ y y'
  · rfl

/-- Intrinsic classicality condition for a channel with an outcome register:
all off-diagonal outcome blocks vanish on every input matrix. -/
def IsClassicallyRecorded
    (channel : KrausChannel X
      (Object.tensor (outcomeObject Outcome) Y)) : Prop :=
  ∀ (ρ : Matrix X X ℂ) (outcome outcome' : Outcome) (y y' : Y),
    channel.map ρ (outcome, y) (outcome', y') =
      if outcome = outcome' then
        channel.map ρ (outcome, y) (outcome, y') else 0

/-- Every channel obtained by recording a finite instrument satisfies the
intrinsic block-diagonal classicality condition. -/
theorem recordedChannel_isClassicallyRecorded
    (instrument : KrausInstrument Outcome X Y) :
    IsClassicallyRecorded instrument.recordedChannel := by
  intro ρ outcome outcome' y y'
  rw [recordedChannel_map_apply]
  split_ifs with equal
  · subst outcome'
    rw [recordedChannel_map_apply]
    simp
  · rfl

/-- The canonical extracted instrument records back to the original channel
exactly when the latter is intrinsically classical on its outcome register. -/
theorem recordedChannel_extractInstrument_eq_iff
    (channel : KrausChannel X
      (Object.tensor (outcomeObject Outcome) Y)) :
    (extractInstrument channel).recordedChannel = channel ↔
      IsClassicallyRecorded channel := by
  constructor
  · intro equal ρ outcome outcome' y y'
    have cellEqual := congrArg
      (fun current ↦ current.map ρ (outcome, y) (outcome', y')) equal
    rw [extractInstrument_recordedChannel_map_apply] at cellEqual
    exact cellEqual.symm
  · intro classical
    apply KrausChannel.ext
    funext ρ
    apply Matrix.ext
    rintro ⟨outcome, y⟩ ⟨outcome', y'⟩
    rw [extractInstrument_recordedChannel_map_apply]
    exact (classical ρ outcome outcome' y y').symm

/-- **Intrinsic image theorem.**  A finite channel into a classical outcome
register and residual quantum system is the recorded representation of a
unique finite instrument exactly when its outcome register is block diagonal. -/
theorem isClassicallyRecorded_iff_existsUnique
    (channel : KrausChannel X
      (Object.tensor (outcomeObject Outcome) Y)) :
    IsClassicallyRecorded channel ↔
      ∃! instrument : KrausInstrument Outcome X Y,
        instrument.recordedChannel = channel := by
  constructor
  · intro classical
    have extracted :=
      (recordedChannel_extractInstrument_eq_iff channel).2 classical
    refine ⟨extractInstrument channel, extracted, ?_⟩
    intro instrument equal
    apply recordedChannel_injective
    exact equal.trans extracted.symm
  · rintro ⟨instrument, equal, unique⟩
    rw [← equal]
    exact recordedChannel_isClassicallyRecorded instrument

end ClassicalOutcome

/-- Normalized posterior state for an outcome of strictly positive
probability. -/
noncomputable def posterior
    (instrument : KrausInstrument Outcome X Y) (state : DensityMatrix X)
    (outcome : Outcome)
    (positive : 0 < instrument.outcomeProbability state outcome) :
    DensityMatrix Y where
  matrix :=
    ((instrument.outcomeProbability state outcome : ℝ)⁻¹) •
      (instrument.branch outcome).map state.matrix
  posSemidef :=
    (instrument.branch_posSemidef outcome state.posSemidef).smul
      (inv_nonneg.mpr (instrument.outcomeProbability state outcome).2)
  trace_one := by
    rw [Matrix.trace_smul, ← instrument.outcomeProbability_coe_complex]
    rw [Complex.real_smul]
    norm_cast
    exact inv_mul_cancel₀ (by exact_mod_cast positive.ne')

/-- Multiplying a normalized posterior by its outcome probability recovers the
original unnormalized branch state. -/
theorem probability_smul_posterior
    (instrument : KrausInstrument Outcome X Y) (state : DensityMatrix X)
    (outcome : Outcome)
    (positive : 0 < instrument.outcomeProbability state outcome) :
    (instrument.outcomeProbability state outcome : ℝ) •
        (instrument.posterior state outcome positive).matrix =
      (instrument.branch outcome).map state.matrix := by
  change
    (instrument.outcomeProbability state outcome : ℝ) •
        (((instrument.outcomeProbability state outcome : ℝ)⁻¹) •
          (instrument.branch outcome).map state.matrix) = _
  rw [smul_smul]
  have nonzero :
      (instrument.outcomeProbability state outcome : ℝ) ≠ 0 := by
    exact_mod_cast positive.ne'
  rw [mul_inv_cancel₀ nonzero, one_smul]

/-- Relabel the finite classical outcomes of an instrument by an
equivalence. -/
def relabel (equivalence : Outcome ≃ Result)
    (instrument : KrausInstrument Outcome X Y) :
    KrausInstrument Result X Y where
  branch result := instrument.branch (equivalence.symm result)
  total := instrument.total
  total_map ρ := by
    rw [instrument.total_map]
    exact (equivalence.symm.sum_comp
      (fun outcome ↦ (instrument.branch outcome).map ρ)).symm

@[simp]
theorem relabel_branch (equivalence : Outcome ≃ Result)
    (instrument : KrausInstrument Outcome X Y) (result : Result) :
    (instrument.relabel equivalence).branch result =
      instrument.branch (equivalence.symm result) :=
  rfl

/-- Outcome probabilities are invariant under equivalent relabeling. -/
theorem relabel_outcomeProbability (equivalence : Outcome ≃ Result)
    (instrument : KrausInstrument Outcome X Y) (state : DensityMatrix X)
    (result : Result) :
    (instrument.relabel equivalence).outcomeProbability state result =
      instrument.outcomeProbability state (equivalence.symm result) :=
  rfl

/-! ## Dependent multi-round composition -/

variable {Next : Outcome → Type u}
  [nextFintype : ∀ outcome, Fintype (Next outcome)]

/-- Dependent instrument bind.  The first outcome selects the complete next
instrument, whose result type may itself depend on that first outcome. -/
noncomputable def bind (first : KrausInstrument Outcome X Y)
    (next : ∀ outcome, KrausInstrument (Next outcome) Y Z) :
    KrausInstrument (Σ outcome, Next outcome) X Z :=
  ofTracePreservingOperations
    (fun result ↦ KrausOperation.comp (first.branch result.1)
      ((next result.1).branch result.2))
    (by
      intro ρ
      calc
        (∑ result : Σ outcome, Next outcome,
            (KrausOperation.comp (first.branch result.1)
              ((next result.1).branch result.2)).map ρ).trace =
            ∑ outcome, ∑ result : Next outcome,
              (((next outcome).branch result).map
                ((first.branch outcome).map ρ)).trace := by
          rw [Fintype.sum_sigma, Matrix.trace_sum]
          apply Fintype.sum_congr
          intro outcome
          rw [Matrix.trace_sum]
          rfl
        _ = ∑ outcome,
              ((next outcome).total.map
                ((first.branch outcome).map ρ)).trace := by
          apply Fintype.sum_congr
          intro outcome
          rw [(next outcome).total_map, Matrix.trace_sum]
        _ = ∑ outcome,
              ((first.branch outcome).map ρ).trace := by
          apply Fintype.sum_congr
          intro outcome
          rw [(next outcome).total.map_trace]
        _ = (∑ outcome,
              (first.branch outcome).map ρ).trace := by
          rw [Matrix.trace_sum]
        _ = (first.total.map ρ).trace := by rw [first.total_map]
        _ = ρ.trace := first.total.map_trace ρ)

@[simp]
theorem bind_branch_map (first : KrausInstrument Outcome X Y)
    (next : ∀ outcome, KrausInstrument (Next outcome) Y Z)
    (outcome : Outcome) (result : Next outcome) (ρ : Matrix X X ℂ) :
    ((first.bind next).branch ⟨outcome, result⟩).map ρ =
      ((next outcome).branch result).map
        ((first.branch outcome).map ρ) :=
  rfl

/-- Born's chain rule for a dependent second-round instrument. -/
theorem bind_outcomeProbability
    (first : KrausInstrument Outcome X Y)
    (next : ∀ outcome, KrausInstrument (Next outcome) Y Z)
    (state : DensityMatrix X) (outcome : Outcome) (result : Next outcome)
    (positive : 0 < first.outcomeProbability state outcome) :
    (first.bind next).outcomeProbability state ⟨outcome, result⟩ =
      first.outcomeProbability state outcome *
        (next outcome).outcomeProbability
          (first.posterior state outcome positive) result := by
  apply NNReal.eq
  change
    (((next outcome).branch result).map
      ((first.branch outcome).map state.matrix)).trace.re =
      (first.outcomeProbability state outcome : ℝ) *
        (((next outcome).branch result).map
          (first.posterior state outcome positive).matrix).trace.re
  rw [← first.probability_smul_posterior state outcome positive,
    KrausOperation.map_real_smul, Matrix.trace_smul]
  simp [Complex.real_smul]

/-- Canonical reassociation of dependent two-round outcome trees. -/
def bindAssocEquiv (Next : Outcome → Type u)
    (Final : (Σ outcome, Next outcome) → Type u) :
    (Σ pair : Σ outcome, Next outcome, Final pair) ≃
      (Σ outcome, Σ result : Next outcome, Final ⟨outcome, result⟩) where
  toFun
    | ⟨⟨outcome, result⟩, final⟩ => ⟨outcome, result, final⟩
  invFun
    | ⟨outcome, result, final⟩ => ⟨⟨outcome, result⟩, final⟩
  left_inv := by rintro ⟨⟨outcome, result⟩, final⟩; rfl
  right_inv := by rintro ⟨outcome, result, final⟩; rfl

variable {Final : (Σ outcome, Next outcome) → Type u}
  [finalFintype : ∀ pair, Fintype (Final pair)]

/-- Dependent instrument bind is associative after the canonical equivalence
between the two nested outcome-tree shapes. -/
theorem bind_assoc (first : KrausInstrument Outcome X Y)
    (next : ∀ outcome, KrausInstrument (Next outcome) Y Z)
    (final : ∀ pair, KrausInstrument (Final pair) Z T) :
    ((first.bind next).bind final).relabel (bindAssocEquiv Next Final) =
      first.bind (fun outcome ↦
        (next outcome).bind (fun result ↦ final ⟨outcome, result⟩)) := by
  apply KrausInstrument.ext
  funext outcomeTree
  apply KrausOperation.ext
  funext ρ
  rfl

/-- Postprocess every instrument branch by the same trace-preserving quantum
channel.  Outcome probabilities are retained, while posterior systems evolve
through the channel. -/
def postcompose (instrument : KrausInstrument Outcome X Y)
    (channel : KrausChannel Y Z) : KrausInstrument Outcome X Z where
  branch outcome :=
    KrausOperation.comp (instrument.branch outcome)
      (KrausOperation.ofChannel channel)
  total := KrausChannel.comp instrument.total channel
  total_map ρ := by
    rw [KrausChannel.comp_map, instrument.total_map]
    change channel.toLinearMap
        (∑ outcome, (instrument.branch outcome).map ρ) = _
    rw [map_sum]
    rfl

/-- Preprocess the input by a trace-preserving channel before applying the
instrument. -/
def precompose (channel : KrausChannel V X)
    (instrument : KrausInstrument Outcome X Y) :
    KrausInstrument Outcome V Y where
  branch outcome :=
    KrausOperation.comp (KrausOperation.ofChannel channel)
      (instrument.branch outcome)
  total := KrausChannel.comp channel instrument.total
  total_map ρ := by
    rw [KrausChannel.comp_map, instrument.total_map]
    rfl

@[simp]
theorem postcompose_branch_map
    (instrument : KrausInstrument Outcome X Y) (channel : KrausChannel Y Z)
    (outcome : Outcome) (ρ : Matrix X X ℂ) :
    ((instrument.postcompose channel).branch outcome).map ρ =
      channel.map ((instrument.branch outcome).map ρ) := rfl

@[simp]
theorem precompose_branch_map (channel : KrausChannel V X)
    (instrument : KrausInstrument Outcome X Y) (outcome : Outcome)
    (ρ : Matrix V V ℂ) :
    ((instrument.precompose channel).branch outcome).map ρ =
      (instrument.branch outcome).map (channel.map ρ) := rfl

/-- Trace-preserving postprocessing does not change any outcome
probability. -/
theorem postcompose_outcomeProbability
    (instrument : KrausInstrument Outcome X Y) (channel : KrausChannel Y Z)
    (state : DensityMatrix X) (outcome : Outcome) :
    (instrument.postcompose channel).outcomeProbability state outcome =
      instrument.outcomeProbability state outcome := by
  apply NNReal.eq
  change
    (channel.map ((instrument.branch outcome).map state.matrix)).trace.re =
      ((instrument.branch outcome).map state.matrix).trace.re
  rw [channel.map_trace]

/-- Classically controlled postprocessing: the observed outcome selects a
possibly different trace-preserving channel for the residual system. -/
noncomputable def controlledPostcompose
    (instrument : KrausInstrument Outcome X Y)
    (channel : Outcome → KrausChannel Y Z) :
    KrausInstrument Outcome X Z :=
  ofTracePreservingOperations
    (fun outcome ↦ KrausOperation.comp (instrument.branch outcome)
      (KrausOperation.ofChannel (channel outcome)))
    (by
      intro ρ
      calc
        (∑ outcome,
            (KrausOperation.comp (instrument.branch outcome)
              (KrausOperation.ofChannel (channel outcome))).map ρ).trace =
            ∑ outcome,
              ((channel outcome).map
                ((instrument.branch outcome).map ρ)).trace := by
          rw [Matrix.trace_sum]
          rfl
        _ = ∑ outcome,
              ((instrument.branch outcome).map ρ).trace := by
          apply Fintype.sum_congr
          intro outcome
          rw [(channel outcome).map_trace]
        _ = (∑ outcome,
              (instrument.branch outcome).map ρ).trace := by
          rw [Matrix.trace_sum]
        _ = (instrument.total.map ρ).trace := by
          rw [instrument.total_map]
        _ = ρ.trace := instrument.total.map_trace ρ)

@[simp]
theorem controlledPostcompose_branch_map
    (instrument : KrausInstrument Outcome X Y)
    (channel : Outcome → KrausChannel Y Z) (outcome : Outcome)
    (ρ : Matrix X X ℂ) :
    ((instrument.controlledPostcompose channel).branch outcome).map ρ =
      (channel outcome).map ((instrument.branch outcome).map ρ) :=
  rfl

/-- Classically controlled trace-preserving postprocessing retains the
probability of every recorded outcome. -/
theorem controlledPostcompose_outcomeProbability
    (instrument : KrausInstrument Outcome X Y)
    (channel : Outcome → KrausChannel Y Z) (state : DensityMatrix X)
    (outcome : Outcome) :
    (instrument.controlledPostcompose channel).outcomeProbability
        state outcome = instrument.outcomeProbability state outcome := by
  apply NNReal.eq
  change
    ((channel outcome).map
      ((instrument.branch outcome).map state.matrix)).trace.re =
      ((instrument.branch outcome).map state.matrix).trace.re
  rw [(channel outcome).map_trace]

/-- Independent tensor product of two finite instruments.  Outcomes pair and
branches tensor componentwise. -/
def tensor (first : KrausInstrument Outcome V W)
    (second : KrausInstrument Result X Y) :
    KrausInstrument (Outcome × Result) (Object.tensor V X)
      (Object.tensor W Y) where
  branch pair :=
    KrausOperation.tensor (first.branch pair.1) (second.branch pair.2)
  total := KrausChannel.tensor first.total second.total
  total_map τ := by
    let branchSum :
        Matrix (V × X) (V × X) ℂ →ₗ[ℂ] Matrix (W × Y) (W × Y) ℂ :=
      ∑ pair : Outcome × Result,
        (KrausOperation.tensor (first.branch pair.1)
          (second.branch pair.2)).toLinearMap
    have mapsEqual :
        (KrausChannel.tensor first.total second.total).toLinearMap =
          branchSum := by
      apply KrausChannel.linearMap_ext_kronecker
      intro ρ σ
      change (KrausChannel.tensor first.total second.total).map (ρ ⊗ₖ σ) =
        branchSum (ρ ⊗ₖ σ)
      rw [KrausChannel.tensor_map_kronecker, first.total_map, second.total_map,
        KrausChannel.sum_kronecker_sum]
      simp only [branchSum, LinearMap.sum_apply, Fintype.sum_prod_type]
      apply Fintype.sum_congr
      intro outcome
      apply Fintype.sum_congr
      intro result
      change
        (first.branch outcome).map ρ ⊗ₖ (second.branch result).map σ =
          (KrausOperation.tensor (first.branch outcome)
            (second.branch result)).map (ρ ⊗ₖ σ)
      exact (KrausOperation.tensor_map_kronecker _ _ _ _).symm
    change (KrausChannel.tensor first.total second.total).toLinearMap τ =
      ∑ pair : Outcome × Result,
        (KrausOperation.tensor (first.branch pair.1)
          (second.branch pair.2)).map τ
    rw [mapsEqual]
    simp only [branchSum, LinearMap.sum_apply]
    apply Fintype.sum_congr
    intro pair
    rfl

@[simp]
theorem tensor_branch_map_kronecker
    (first : KrausInstrument Outcome V W)
    (second : KrausInstrument Result X Y) (outcome : Outcome)
    (result : Result) (ρ : Matrix V V ℂ) (σ : Matrix X X ℂ) :
    (((first.tensor second).branch (outcome, result)).map (ρ ⊗ₖ σ)) =
      (first.branch outcome).map ρ ⊗ₖ (second.branch result).map σ := by
  exact KrausOperation.tensor_map_kronecker _ _ _ _

/-- Outcome probabilities of independent product instruments factor. -/
theorem tensor_outcomeProbability
    (first : KrausInstrument Outcome V W)
    (second : KrausInstrument Result X Y)
    (firstState : DensityMatrix V) (secondState : DensityMatrix X)
    (outcome : Outcome) (result : Result) :
    (first.tensor second).outcomeProbability
        (firstState.tensor secondState) (outcome, result) =
      first.outcomeProbability firstState outcome *
        second.outcomeProbability secondState result := by
  apply NNReal.eq
  simp only [outcomeProbability_coe_real, NNReal.coe_mul,
    DensityMatrix.tensor_matrix, tensor_branch_map_kronecker]
  change
    (((first.branch outcome).map firstState.matrix ⊗ₖ
      (second.branch result).map secondState.matrix).trace).re = _
  rw [Matrix.trace_kronecker]
  have firstReal := first.outcomeProbability_coe_complex firstState outcome
  have secondReal := second.outcomeProbability_coe_complex secondState result
  rw [← firstReal, ← secondReal]
  simp

end KrausInstrument

end Ript.Models.Quantum
