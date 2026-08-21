import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Ript.Examples.DiamondBitTheory
import Ript.Examples.OperationalErasureRealizations
import Ript.Semantics.ResourceChangingSequentialInitiality
import Ript.Semantics.SequentialNormalForm

/-!
# Six separating models of the non-thin diamond theory

Each interpretation realizes the reversible branch and the erasure branch by
different semantic morphisms.  Path separation invokes genuinely
model-specific evidence: stochastic entries, quantum basis states, a causal
mechanism, executable functions, experiment channels, and a thermal
memory--battery transition.
-/

set_option autoImplicit false

namespace Ript.Examples.DiamondBitRealizations

open CategoryTheory
open Ript.Core
open Ript.Examples.DiamondBitTheory
open Ript.Models.Computation
open Ript.Models.Causal
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic
open Ript.Models.FiniteStochastic.FinStoch
open Ript.Models.Quantum
open Ript.Models.Quantum.ClassicalEmbedding
open Ript.Models.Thermal
open Ript.Semantics
open Ript.Syntax

universe u v

/-! ## Resource translations -/

/-- Sum all four common resource coordinates into one scalar bound. -/
def scalarResourceMap : Resource →+o Nat where
  toFun resource := resource ResourceKind.reversibleFirst +
    resource ResourceKind.reversibleSecond +
    resource ResourceKind.exposure + resource ResourceKind.erasure
  map_zero' := rfl
  map_add' left right := by
    simp
    omega
  monotone' left right h := by
    exact Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add (h ResourceKind.reversibleFirst)
          (h ResourceKind.reversibleSecond))
        (h ResourceKind.exposure))
      (h ResourceKind.erasure)

/-- Map reversible edges to gates, exposure to a query, and erasure to a gate;
every primitive also consumes one formal step. -/
def computationResourceMap : Resource →+o ComputationResource where
  toFun resource := ComputationResource.of
    (resource ResourceKind.reversibleFirst +
      resource ResourceKind.reversibleSecond +
      resource ResourceKind.exposure + resource ResourceKind.erasure)
    (resource ResourceKind.exposure) 0
    (resource ResourceKind.reversibleFirst +
      resource ResourceKind.reversibleSecond + resource ResourceKind.erasure)
  map_zero' := by
    funext kind
    fin_cases kind <;> rfl
  map_add' left right := by
    funext kind
    fin_cases kind <;>
      simp [ComputationResource.of, add_left_comm, add_comm]
  monotone' left right h kind := by
    fin_cases kind
    · exact Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add (h ResourceKind.reversibleFirst)
            (h ResourceKind.reversibleSecond))
          (h ResourceKind.exposure))
        (h ResourceKind.erasure)
    · exact h ResourceKind.exposure
    · exact le_rfl
    · exact Nat.add_le_add
        (Nat.add_le_add (h ResourceKind.reversibleFirst)
          (h ResourceKind.reversibleSecond))
        (h ResourceKind.erasure)

/-! ## Probability -/

/-- Reversible negations compete with deterministic erasure. -/
def probabilityInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.FiniteStochastic.Object)
      scalarResourceMap where
  obj _ := Ript.Examples.StochasticBits.bit
  mapGen
    | .reversibleFirst => Ript.Examples.StochasticBits.deterministicNot
    | .reversibleSecond => Ript.Examples.StochasticBits.deterministicNot
    | .expose => FinStoch.identity Ript.Examples.StochasticBits.bit
    | .erase => Ript.Examples.OperationalErasureRealizations.eraseBitChannel
  mapGen_cost generator := by
    cases generator <;> exact Nat.zero_le _

/-- The reversible stochastic path is identity. -/
theorem probability_reversiblePath :
    ResourceChangingInterpretation.eval probabilityInterpretation
        reversiblePath = FinStoch.identity Ript.Examples.StochasticBits.bit :=
  Ript.Examples.CompositionalBitRealizations.probability_doubleFlip

/-- The stochastic erasure path is the constant-false channel. -/
theorem probability_erasurePath :
    ResourceChangingInterpretation.eval probabilityInterpretation erasurePath =
      Ript.Examples.OperationalErasureRealizations.eraseBitChannel := by
  apply FinStoch.ext
  intro input output
  change Bool at input output
  change (∑ middle : Bool,
    (if input = middle then (1 : ℚ≥0) else 0) *
      (if false = output then 1 else 0)) =
    if false = output then 1 else 0
  rw [Fintype.sum_bool]
  cases input <;> cases output <;> norm_num

/-- Classical probability separates the two paths on input `true`. -/
theorem probability_separates : SeparatesPaths probabilityInterpretation := by
  rw [SeparatesPaths, probability_reversiblePath, probability_erasurePath]
  intro equality
  have entry := congrArg (fun channel ↦ channel.prob true true) equality
  change (1 : ℚ≥0) = 0 at entry
  exact one_ne_zero entry

/-! ## Quantum processes -/

/-- Reuse the abstract zero scalar cost of the quantum slice. -/
local instance quantumZeroCost :
    HasProcessCost Ript.Models.Quantum.Object Nat :=
  Ript.Examples.CommonBitRealizations.quantumZeroCost

/-- Reversible classical-basis negation embedded as a CPTP quantum channel. -/
noncomputable def quantumFlip :
    KrausChannel
      Ript.Examples.OperationalErasureRealizations.classicalQubit
      Ript.Examples.OperationalErasureRealizations.classicalQubit :=
  measurementPreparation Ript.Examples.StochasticBits.deterministicNot

/-- Quantum interpretation of the two paths. -/
noncomputable def quantumInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.Quantum.Object)
      scalarResourceMap where
  obj _ := Ript.Examples.OperationalErasureRealizations.classicalQubit
  mapGen
    | .reversibleFirst => quantumFlip
    | .reversibleSecond => quantumFlip
    | .expose => KrausChannel.identity
        Ript.Examples.OperationalErasureRealizations.classicalQubit
    | .erase => Ript.Examples.OperationalErasureRealizations.quantumReset
  mapGen_cost generator := by
    cases generator <;> exact Nat.zero_le _

/-- Reversible quantum path is Boolean-basis dephasing. -/
theorem quantum_reversiblePath :
    ResourceChangingInterpretation.eval quantumInterpretation reversiblePath =
      dephase Ript.Examples.StochasticBits.bit := by
  change KrausChannel.comp quantumFlip quantumFlip = _
  rw [quantumFlip, ← measurementPreparation_comp]
  congr 1
  exact Ript.Examples.CommonBitRealizations.semanticFlip_involutive

/-- Quantum erasure path is the reset channel. -/
theorem quantum_erasurePath :
    ResourceChangingInterpretation.eval quantumInterpretation erasurePath =
      Ript.Examples.OperationalErasureRealizations.quantumReset := by
  change KrausChannel.comp (KrausChannel.identity _)
    Ript.Examples.OperationalErasureRealizations.quantumReset = _
  apply KrausChannel.ext
  funext ρ
  simp [KrausChannel.comp, KrausChannel.identity,
    KrausChannel.ofOperators]

/-- Quantum theory separates dephasing from reset on the `true` basis state. -/
theorem quantum_separates : SeparatesPaths quantumInterpretation := by
  intro equality
  have explicitEquality :
      dephase Ript.Examples.StochasticBits.bit =
        Ript.Examples.OperationalErasureRealizations.quantumReset :=
    quantum_reversiblePath.symm.trans (equality.trans quantum_erasurePath)
  have classicalEquality :
      FinStoch.identity Ript.Examples.StochasticBits.bit =
        Ript.Examples.OperationalErasureRealizations.eraseBitChannel :=
    measurementPreparation_faithful (by
      simpa [dephase,
        Ript.Examples.OperationalErasureRealizations.quantumReset] using
          explicitEquality)
  have contradiction := congrArg (fun channel ↦ channel.prob true true)
    classicalEquality
  change (1 : ℚ≥0) = 0 at contradiction
  exact one_ne_zero contradiction

/-! ## Causal model -/

/-- Exact copy channel represented by the existing child mechanism. -/
def causalCopyChannel :
    FinStoch Ript.Examples.OperationalErasureRealizations.causalSource
      Ript.Examples.StochasticBits.bit :=
  (Ript.Examples.SimpleCausalModel.chainModel.mechanism
    Ript.Examples.SimpleCausalModel.effect).toFinStoch

/-- Causal diamond: ordinary mechanism along both branches, followed by
identity or erasure. -/
def causalInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.FiniteStochastic.Object)
      scalarResourceMap where
  obj
    | .input => Ript.Examples.OperationalErasureRealizations.causalSource
    | .reversible => Ript.Examples.StochasticBits.bit
    | .irreversible => Ript.Examples.StochasticBits.bit
    | .output => Ript.Examples.StochasticBits.bit
  mapGen
    | .reversibleFirst => causalCopyChannel
    | .reversibleSecond => FinStoch.identity Ript.Examples.StochasticBits.bit
    | .expose => causalCopyChannel
    | .erase => Ript.Examples.OperationalErasureRealizations.eraseBitChannel
  mapGen_cost generator := by
    cases generator <;> exact Nat.zero_le _

/-- The reversible causal branch is exactly the ordinary child mechanism. -/
theorem causal_reversiblePath :
    ResourceChangingInterpretation.eval causalInterpretation reversiblePath =
      causalCopyChannel := by
  change FinStoch.comp causalCopyChannel (FinStoch.identity _) = _
  apply FinStoch.ext
  intro input output
  simp [FinStoch.comp, FinStoch.identity]

/-- The causal erasure branch is the mechanism followed by constant erasure. -/
theorem causal_erasurePath :
    ResourceChangingInterpretation.eval causalInterpretation erasurePath =
      FinStoch.comp causalCopyChannel
        Ript.Examples.OperationalErasureRealizations.eraseBitChannel :=
  rfl

/-- A true parent is copied to a true child with probability one. -/
theorem causal_copy_true :
    causalCopyChannel.prob
      (Ript.Examples.OperationalErasureRealizations.causalParentInput true)
      true = 1 := by
  have hmechanism := Ript.Examples.SimpleCausalModel.chainModel_effect
    (Ript.Examples.OperationalErasureRealizations.causalParentInput true)
  have hentry := congrArg (fun distribution ↦ distribution.prob true) hmechanism
  exact hentry.trans (by rfl)

/-- The same input has zero probability of true after constant erasure. -/
theorem causal_erasure_true_zero :
    (FinStoch.comp causalCopyChannel
      Ript.Examples.OperationalErasureRealizations.eraseBitChannel).prob
        (Ript.Examples.OperationalErasureRealizations.causalParentInput true)
        true = 0 := by
  simp [FinStoch.comp,
    Ript.Examples.OperationalErasureRealizations.eraseBitChannel,
    FinStoch.dirac]

/-- The causal interpretation separates copy from intervention-like erasure. -/
theorem causal_separates : SeparatesPaths causalInterpretation := by
  intro equality
  have pathEquality : causalCopyChannel =
      FinStoch.comp causalCopyChannel
        Ript.Examples.OperationalErasureRealizations.eraseBitChannel :=
    causal_reversiblePath.symm.trans (equality.trans causal_erasurePath)
  have entry := congrArg (fun channel ↦ channel.prob
    (Ript.Examples.OperationalErasureRealizations.causalParentInput true) true)
    pathEquality
  have contradiction : (1 : ℚ≥0) = 0 :=
    causal_copy_true.symm.trans (entry.trans causal_erasure_true_zero)
  exact one_ne_zero contradiction

/-! ## Computation -/

/-- Computation interpretation preserves the exact four-resource map. -/
def computationInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.Computation.Total.Object)
      computationResourceMap where
  obj _ := Ript.Examples.SimpleComputation.totalBit
  mapGen
    | .reversibleFirst => Ript.Examples.SimpleComputation.totalNot
    | .reversibleSecond => Ript.Examples.SimpleComputation.totalNot
    | .expose => Ript.Examples.SimpleComputation.totalQuery
    | .erase => Ript.Examples.OperationalErasureRealizations.computationErase
  mapGen_cost generator := by
    cases generator <;> intro kind <;> fin_cases kind <;> decide

/-- Reversible computation restores every Boolean input. -/
theorem computation_reversible_true :
    (ResourceChangingInterpretation.eval computationInterpretation
      reversiblePath).run true = true := by
  change !(!true) = true
  decide

/-- Erasure computation maps true to false. -/
theorem computation_erasure_true :
    (ResourceChangingInterpretation.eval computationInterpretation
      erasurePath).run true = false :=
  rfl

/-- Executable functions distinguish identity from constant erasure. -/
theorem computation_separates : SeparatesPaths computationInterpretation := by
  intro equality
  have result := congrArg (fun computation ↦ computation.run true) equality
  have contradiction : true = false :=
    computation_reversible_true.symm.trans
      (result.trans computation_erasure_true)
  exact (by decide : true ≠ false) contradiction

/-! ## Semantic information -/

/-- Semantic diamond compares perfect information with constant observation. -/
def semanticInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := Ript.Models.FiniteStochastic.Object)
      scalarResourceMap where
  obj _ := Ript.Examples.SimpleDecision.decisionBit
  mapGen
    | .reversibleFirst =>
        Ript.Examples.CommonBitRealizations.semanticFlipExperiment
    | .reversibleSecond =>
        Ript.Examples.CommonBitRealizations.semanticFlipExperiment
    | .expose => Ript.Examples.SimpleDecision.perfectExperiment
    | .erase => Ript.Examples.OperationalErasureRealizations.constantExperiment
  mapGen_cost generator := by
    cases generator <;> exact Nat.zero_le _

/-- Reversible semantic branch is perfect observation. -/
theorem semantic_reversiblePath :
    ResourceChangingInterpretation.eval semanticInterpretation reversiblePath =
      Ript.Examples.SimpleDecision.perfectExperiment :=
  Ript.Examples.CommonBitRealizations.semanticFlip_involutive

/-- Erasure semantic branch is the constant experiment. -/
theorem semantic_erasurePath :
    ResourceChangingInterpretation.eval semanticInterpretation erasurePath =
      Ript.Examples.OperationalErasureRealizations.constantExperiment :=
  Ript.Examples.OperationalErasureRealizations.semantic_pipeline_eq_constant

/-- Semantic experiments separate perfect information from erased value. -/
theorem semantic_separates : SeparatesPaths semanticInterpretation := by
  intro equality
  have pathEquality : Ript.Examples.SimpleDecision.perfectExperiment =
      Ript.Examples.OperationalErasureRealizations.constantExperiment :=
    semantic_reversiblePath.symm.trans (equality.trans semantic_erasurePath)
  have entry := congrArg (fun channel ↦ channel.prob true true) pathEquality
  change (1 : ℚ≥0) = 0 at entry
  exact one_ne_zero entry

/-! ## Thermodynamics -/

/-- Reuse the abstract zero scalar cost of the thermal slice. -/
local instance thermalZeroCost : HasProcessCost ThermalObject Nat :=
  Ript.Examples.CommonBitRealizations.thermalZeroCost

/-- Free memory flip tensored with an idle work battery. -/
def thermalReversibleFlip :
    GibbsPreserving
      Ript.Examples.OperationalErasureRealizations.thermalMemoryBattery
      Ript.Examples.OperationalErasureRealizations.thermalMemoryBattery :=
  GibbsPreserving.tensor Ript.Examples.SimpleThermalModel.thermalFlip
    (GibbsPreserving.identity
      Ript.Examples.ExactWorkErasure.workBatteryThermal)

/-- Thermal diamond compares a reversible cycle with work-assisted erasure. -/
def thermalInterpretation :
    ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := ThermalObject) scalarResourceMap where
  obj _ := Ript.Examples.OperationalErasureRealizations.thermalMemoryBattery
  mapGen
    | .reversibleFirst => thermalReversibleFlip
    | .reversibleSecond => thermalReversibleFlip
    | .expose => GibbsPreserving.identity
        Ript.Examples.OperationalErasureRealizations.thermalMemoryBattery
    | .erase => Ript.Examples.ExactWorkErasure.exactWorkErasureProcess
  mapGen_cost generator := by
    cases generator <;> exact Nat.zero_le _

/-- The reversible thermal branch is the joint identity process. -/
theorem thermal_reversiblePath :
    ResourceChangingInterpretation.eval thermalInterpretation reversiblePath =
      GibbsPreserving.identity
        Ript.Examples.OperationalErasureRealizations.thermalMemoryBattery := by
  change GibbsPreserving.comp thermalReversibleFlip thermalReversibleFlip = _
  calc
    GibbsPreserving.comp thermalReversibleFlip thermalReversibleFlip =
        GibbsPreserving.tensor
          (GibbsPreserving.comp Ript.Examples.SimpleThermalModel.thermalFlip
            Ript.Examples.SimpleThermalModel.thermalFlip)
          (GibbsPreserving.comp
            (GibbsPreserving.identity
              Ript.Examples.ExactWorkErasure.workBatteryThermal)
            (GibbsPreserving.identity
              Ript.Examples.ExactWorkErasure.workBatteryThermal)) :=
      (GibbsPreserving.tensor_comp _ _ _ _).symm
    _ = GibbsPreserving.tensor
          (GibbsPreserving.identity Ript.Examples.SimpleThermalModel.thermalBit)
          (GibbsPreserving.identity
            Ript.Examples.ExactWorkErasure.workBatteryThermal) := by
      rw [Ript.Examples.SimpleThermalModel.thermalFlip_involutive]
      congr 1
      apply GibbsPreserving.ext
      apply FinStoch.ext
      intro input output
      simp [GibbsPreserving.comp, GibbsPreserving.identity,
        FinStoch.comp, FinStoch.identity]
    _ = GibbsPreserving.identity
        Ript.Examples.OperationalErasureRealizations.thermalMemoryBattery :=
      GibbsPreserving.tensor_id _ _

/-- The thermal erasure branch is the exact work-erasure process. -/
theorem thermal_erasurePath :
    ResourceChangingInterpretation.eval thermalInterpretation erasurePath =
      Ript.Examples.ExactWorkErasure.exactWorkErasureProcess :=
  Ript.Examples.OperationalErasureRealizations.thermal_pipeline_eq_process

/-- Thermal channel entries distinguish the reversible cycle from erasure. -/
theorem thermal_separates : SeparatesPaths thermalInterpretation := by
  intro equality
  have pathEquality : GibbsPreserving.identity
        Ript.Examples.OperationalErasureRealizations.thermalMemoryBattery =
      Ript.Examples.ExactWorkErasure.exactWorkErasureProcess :=
    thermal_reversiblePath.symm.trans (equality.trans thermal_erasurePath)
  have entry := congrArg (fun process ↦
    process.channel.prob (true, true) (true, true)) pathEquality
  change (1 : ℚ≥0) = 0 at entry
  exact one_ne_zero entry

/-! ## Six-model non-thin completeness -/

/-- Every concrete model separates the two paths. -/
theorem sixModelPathSeparation :
    SeparatesPaths probabilityInterpretation ∧
    SeparatesPaths quantumInterpretation ∧
    SeparatesPaths causalInterpretation ∧
    SeparatesPaths computationInterpretation ∧
    SeparatesPaths semanticInterpretation ∧
    SeparatesPaths thermalInterpretation :=
  ⟨probability_separates, quantum_separates, causal_separates,
    computation_separates, semantic_separates, thermal_separates⟩

/-- **Six-model semantic completeness for the non-thin diamond theory.** -/
theorem sixModelSemanticCompleteness :
    SemanticallyComplete probabilityInterpretation ∧
    SemanticallyComplete quantumInterpretation ∧
    SemanticallyComplete causalInterpretation ∧
    SemanticallyComplete computationInterpretation ∧
    SemanticallyComplete semanticInterpretation ∧
    SemanticallyComplete thermalInterpretation :=
  ⟨semanticallyComplete_of_separates _ probability_separates,
    semanticallyComplete_of_separates _ quantum_separates,
    semanticallyComplete_of_separates _ causal_separates,
    semanticallyComplete_of_separates _ computation_separates,
    semanticallyComplete_of_separates _ semantic_separates,
    semanticallyComplete_of_separates _ thermal_separates⟩

/-! ## Generic free-path representation -/

/-- Diamond path separation implies faithfulness for the generic typed
generator-path normal form. -/
theorem genericPathFaithful_of_separates
    {S : Type} {C : Type u} [AddCommMonoid S] [PartialOrder S]
    [Category.{v} C] [HasProcessCost C S] {φ : Resource →+o S}
    (interpretation : ResourceChangingInterpretation.Interpretation
      (signature := signature) (C := C) φ)
    (separates : SeparatesPaths interpretation) :
    Ript.Semantics.SequentialNormalForm.PathFaithful interpretation := by
  intro X Y left right equality
  have derivation := semanticallyComplete_of_separates interpretation separates
    left.toExpr right.toExpr equality
  have normalized :=
    Ript.Semantics.SequentialNormalForm.normalize_eq_of_derives derivation
  simpa using normalized

/-- All six diamond models are faithful on arbitrary typed generator paths. -/
theorem sixModelGenericPathFaithfulness :
    Ript.Semantics.SequentialNormalForm.PathFaithful probabilityInterpretation ∧
    Ript.Semantics.SequentialNormalForm.PathFaithful quantumInterpretation ∧
    Ript.Semantics.SequentialNormalForm.PathFaithful causalInterpretation ∧
    Ript.Semantics.SequentialNormalForm.PathFaithful computationInterpretation ∧
    Ript.Semantics.SequentialNormalForm.PathFaithful semanticInterpretation ∧
    Ript.Semantics.SequentialNormalForm.PathFaithful thermalInterpretation :=
  ⟨genericPathFaithful_of_separates _ probability_separates,
    genericPathFaithful_of_separates _ quantum_separates,
    genericPathFaithful_of_separates _ causal_separates,
    genericPathFaithful_of_separates _ computation_separates,
    genericPathFaithful_of_separates _ semantic_separates,
    genericPathFaithful_of_separates _ thermal_separates⟩

/-- The generic free-path completeness theorem specializes to all six diamond
interpretations. -/
theorem sixModelGenericSemanticCompleteness :
    Ript.Semantics.SequentialNormalForm.SemanticallyComplete
        probabilityInterpretation ∧
    Ript.Semantics.SequentialNormalForm.SemanticallyComplete
        quantumInterpretation ∧
    Ript.Semantics.SequentialNormalForm.SemanticallyComplete
        causalInterpretation ∧
    Ript.Semantics.SequentialNormalForm.SemanticallyComplete
        computationInterpretation ∧
    Ript.Semantics.SequentialNormalForm.SemanticallyComplete
        semanticInterpretation ∧
    Ript.Semantics.SequentialNormalForm.SemanticallyComplete
        thermalInterpretation :=
  ⟨Ript.Semantics.SequentialNormalForm.semanticallyComplete_of_pathFaithful _
      (genericPathFaithful_of_separates _ probability_separates),
    Ript.Semantics.SequentialNormalForm.semanticallyComplete_of_pathFaithful _
      (genericPathFaithful_of_separates _ quantum_separates),
    Ript.Semantics.SequentialNormalForm.semanticallyComplete_of_pathFaithful _
      (genericPathFaithful_of_separates _ causal_separates),
    Ript.Semantics.SequentialNormalForm.semanticallyComplete_of_pathFaithful _
      (genericPathFaithful_of_separates _ computation_separates),
    Ript.Semantics.SequentialNormalForm.semanticallyComplete_of_pathFaithful _
      (genericPathFaithful_of_separates _ semantic_separates),
    Ript.Semantics.SequentialNormalForm.semanticallyComplete_of_pathFaithful _
      (genericPathFaithful_of_separates _ thermal_separates)⟩

/-! ## Six universal free lifts -/

/-- Canonical resource-changing free lift into classical probability. -/
def probabilityFreeLift :
    ResourceChangeFunctor (TermModel signature)
      Ript.Models.FiniteStochastic.Object Resource Nat scalarResourceMap :=
  ResourceChangingSequentialFree.lift probabilityInterpretation

/-- Canonical resource-changing free lift into quantum processes. -/
noncomputable def quantumFreeLift :
    ResourceChangeFunctor (TermModel signature)
      Ript.Models.Quantum.Object Resource Nat scalarResourceMap :=
  ResourceChangingSequentialFree.lift quantumInterpretation

/-- Canonical resource-changing free lift into causal mechanisms. -/
def causalFreeLift :
    ResourceChangeFunctor (TermModel signature)
      Ript.Models.FiniteStochastic.Object Resource Nat scalarResourceMap :=
  ResourceChangingSequentialFree.lift causalInterpretation

/-- Canonical resource-changing free lift into total computation. -/
def computationFreeLift :
    ResourceChangeFunctor (TermModel signature)
      Ript.Models.Computation.Total.Object Resource ComputationResource
        computationResourceMap :=
  ResourceChangingSequentialFree.lift computationInterpretation

/-- Canonical resource-changing free lift into semantic experiments. -/
def semanticFreeLift :
    ResourceChangeFunctor (TermModel signature)
      Ript.Models.FiniteStochastic.Object Resource Nat scalarResourceMap :=
  ResourceChangingSequentialFree.lift semanticInterpretation

/-- Canonical resource-changing free lift into thermal processes. -/
def thermalFreeLift :
    ResourceChangeFunctor (TermModel signature)
      ThermalObject Resource Nat scalarResourceMap :=
  ResourceChangingSequentialFree.lift thermalInterpretation

/-- All six free lifts agree with their supplied interpretations on every
primitive generator. -/
theorem sixModelFreeLiftOnGenerators :
    (∀ {X Y : Interface} (generator : Generator X Y),
      probabilityFreeLift.toFunctor.map
          (TermModel.quote signature (.gen generator)) =
        probabilityInterpretation.mapGen generator) ∧
    (∀ {X Y : Interface} (generator : Generator X Y),
      quantumFreeLift.toFunctor.map
          (TermModel.quote signature (.gen generator)) =
        quantumInterpretation.mapGen generator) ∧
    (∀ {X Y : Interface} (generator : Generator X Y),
      causalFreeLift.toFunctor.map
          (TermModel.quote signature (.gen generator)) =
        causalInterpretation.mapGen generator) ∧
    (∀ {X Y : Interface} (generator : Generator X Y),
      computationFreeLift.toFunctor.map
          (TermModel.quote signature (.gen generator)) =
        computationInterpretation.mapGen generator) ∧
    (∀ {X Y : Interface} (generator : Generator X Y),
      semanticFreeLift.toFunctor.map
          (TermModel.quote signature (.gen generator)) =
        semanticInterpretation.mapGen generator) ∧
    (∀ {X Y : Interface} (generator : Generator X Y),
      thermalFreeLift.toFunctor.map
          (TermModel.quote signature (.gen generator)) =
        thermalInterpretation.mapGen generator) :=
  ⟨ResourceChangingSequentialFree.lift_on_generator probabilityInterpretation,
    ResourceChangingSequentialFree.lift_on_generator quantumInterpretation,
    ResourceChangingSequentialFree.lift_on_generator causalInterpretation,
    ResourceChangingSequentialFree.lift_on_generator computationInterpretation,
    ResourceChangingSequentialFree.lift_on_generator semanticInterpretation,
    ResourceChangingSequentialFree.lift_on_generator thermalInterpretation⟩

/-- All six canonical lifts obey their advertised translated resource bound
on every free-process morphism. -/
theorem sixModelFreeLiftCostBounds :
    (∀ {X Y : TermModel signature} (morphism : X ⟶ Y),
      processCost (R := Nat) (probabilityFreeLift.toFunctor.map morphism) ≤
        scalarResourceMap (processCost (R := Resource) morphism)) ∧
    (∀ {X Y : TermModel signature} (morphism : X ⟶ Y),
      processCost (R := Nat) (quantumFreeLift.toFunctor.map morphism) ≤
        scalarResourceMap (processCost (R := Resource) morphism)) ∧
    (∀ {X Y : TermModel signature} (morphism : X ⟶ Y),
      processCost (R := Nat) (causalFreeLift.toFunctor.map morphism) ≤
        scalarResourceMap (processCost (R := Resource) morphism)) ∧
    (∀ {X Y : TermModel signature} (morphism : X ⟶ Y),
      processCost (R := ComputationResource)
          (computationFreeLift.toFunctor.map morphism) ≤
        computationResourceMap (processCost (R := Resource) morphism)) ∧
    (∀ {X Y : TermModel signature} (morphism : X ⟶ Y),
      processCost (R := Nat) (semanticFreeLift.toFunctor.map morphism) ≤
        scalarResourceMap (processCost (R := Resource) morphism)) ∧
    (∀ {X Y : TermModel signature} (morphism : X ⟶ Y),
      processCost (R := Nat) (thermalFreeLift.toFunctor.map morphism) ≤
        scalarResourceMap (processCost (R := Resource) morphism)) :=
  ⟨probabilityFreeLift.map_cost_le, quantumFreeLift.map_cost_le,
    causalFreeLift.map_cost_le, computationFreeLift.map_cost_le,
    semanticFreeLift.map_cost_le, thermalFreeLift.map_cost_le⟩

end Ript.Examples.DiamondBitRealizations
