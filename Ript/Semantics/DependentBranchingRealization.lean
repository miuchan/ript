import Mathlib.Tactic.FinCases
import Ript.Models.Causal.FinStoch
import Ript.Models.Computation.Randomized
import Ript.Models.Decision.SemanticValue
import Ript.Models.Quantum.ClassicalEmbedding
import Ript.Models.Thermal.GibbsPreserving
import Ript.Syntax.DependentBranching

/-!
# Six-model realizations of dependent branching normal forms

Every finite dependent branching tree has one strictly positive canonical
normal form.  This module interprets an arbitrary such normal form in six
operational theories without inspecting the syntax that produced it:

* an exact finite stochastic channel;
* a measurement--preparation quantum channel;
* a two-node finite causal model with an explicit full-support input prior;
* a randomized program carrying an arbitrary computation-resource vector;
* a task-semantic experiment;
* a Gibbs-preserving process into the induced output equilibrium, together
  with an exact existence-and-uniqueness criterion for any externally supplied
  target equilibrium.

The representation theorem identifies the common stochastic boundary of all
six constructions.  The completeness theorem proves that equality in every
one of the probability, quantum, computation, semantic-experiment, and
thermal-channel presentations reflects equality of normal forms.  A causal
joint distribution is also complete when the input prior has full support.
Compatible externally targeted thermal lifts also reflect normal-form
equality. Thus no model-specific quotient or choice is used to select a
representative.
-/

set_option autoImplicit false

namespace Ript.Semantics.DependentBranchingRealization

open CategoryTheory
open Ript.Models.Causal
open Ript.Models.Computation
open Ript.Models.Computation.Randomized
open Ript.Models.Decision.FiniteRisk
open Ript.Models.Decision.SemanticValue
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic
open Ript.Models.Quantum
open Ript.Models.Quantum.ClassicalEmbedding
open Ript.Models.Thermal
open Ript.Syntax.DependentBranching

universe u

variable {History State Action Baseline : Type u}
  [Fintype History] [DecidableEq History]
  [Fintype State] [DecidableEq State] [Inhabited State]
  [Fintype Action] [DecidableEq Action]
  [Fintype Baseline] [DecidableEq Baseline]

/-- The exact stochastic process represented by a dependent normal form. -/
abbrev probability (normalForm : NormalForm History State) :
    FinStoch (Object.of State) (Object.of (History × State)) :=
  normalForm.toFinStoch

/-- The canonical classical quantum realization of a dependent normal form. -/
noncomputable def quantum (normalForm : NormalForm History State) :
    KrausChannel (classicalObject (Object.of State))
      (classicalObject (Object.of (History × State))) :=
  measurementPreparation normalForm.toFinStoch

omit [Inhabited State] in
/-- On diagonal states, the quantum realization is exactly stochastic
pushforward through the represented normal form. -/
theorem quantum_diagonalDensity (normalForm : NormalForm History State)
    (input : FinDist (Object.of State)) :
    (quantum normalForm).applyDensity (diagonalDensity input) =
      diagonalDensity (input.push normalForm.toFinStoch) :=
  measurementPreparation_diagonalDensity input normalForm.toFinStoch

/-- The tagged homogeneous carrier used to present one arbitrary channel as a
two-node causal model.  The root uses `inl`; the child uses `inr`. -/
abbrev CausalValue (History State : Type u) :=
  State ⊕ (History × State)

/-- The executable two-node DAG `input → recorded output`. -/
def causalDAG : FiniteDAG 2 where
  parents child := if child = 1 then {0} else ∅
  parent_before child parent membership := by
    fin_cases child
    · simp at membership
    · have parent_zero : parent = 0 := by
        simpa using membership
      subst parent
      decide

/-- Embed an input prior into the root tag of the causal carrier. -/
def causalRootDistribution (prior : FinDist (Object.of State)) :
    FinDist (Object.of (CausalValue History State)) where
  prob
    | .inl input => prior.prob input
    | .inr _ => 0
  normalized := by
    simpa using prior.normalized

/-- The unique parent of the second node in `causalDAG`. -/
def causalParent :
    {parent // parent ∈ causalDAG.parents (1 : Fin 2)} :=
  ⟨0, by simp [causalDAG]⟩

/-- Read the causal input tag, using the inhabited default only on malformed
assignments whose root carries an output tag. -/
def causalInput
    (parents : causalDAG.ParentAssignment (CausalValue History State)
      (1 : Fin 2)) : State :=
  match parents causalParent with
  | .inl input => input
  | .inr _ => default

/-- Conditional output distribution of the causal child. -/
def causalOutputDistribution (normalForm : NormalForm History State)
    (parents : causalDAG.ParentAssignment (CausalValue History State)
      (1 : Fin 2)) :
    FinDist (Object.of (CausalValue History State)) where
  prob
    | .inl _ => 0
    | .inr output => normalForm.toFinStoch.prob (causalInput parents) output
  normalized := by
    simpa using normalForm.toFinStoch.normalized (causalInput parents)

/-- Root mechanism of the generic causal realization. -/
def causalRootMechanism (prior : FinDist (Object.of State)) :
    Mechanism causalDAG (CausalValue History State) (0 : Fin 2) where
  run _ := causalRootDistribution prior

/-- Child mechanism of the generic causal realization. -/
def causalOutputMechanism (normalForm : NormalForm History State) :
    Mechanism causalDAG (CausalValue History State) (1 : Fin 2) where
  run := causalOutputDistribution normalForm

/-- Present an arbitrary dependent normal form as an exact finite causal
model. -/
def causal (prior : FinDist (Object.of State))
    (normalForm : NormalForm History State) :
    FiniteCausalModel 2 (CausalValue History State) where
  dag := causalDAG
  mechanism := Fin.cases (causalRootMechanism prior) fun last : Fin 1 ↦ by
    have last_zero : last = 0 := Fin.eq_zero last
    subst last
    exact causalOutputMechanism normalForm

@[simp]
theorem causal_mechanism_zero (prior : FinDist (Object.of State))
    (normalForm : NormalForm History State) :
    (causal prior normalForm).mechanism 0 = causalRootMechanism prior :=
  rfl

@[simp]
theorem causal_mechanism_one (prior : FinDist (Object.of State))
    (normalForm : NormalForm History State) :
    (causal prior normalForm).mechanism 1 =
      causalOutputMechanism normalForm :=
  rfl

/-- The valid two-node assignment associated with one channel entry. -/
def causalAssignment (input : State) (output : History × State) :
    Assignment 2 (CausalValue History State) :=
  ![Sum.inl input, Sum.inr output]

/-- **Causal representation.**  On valid tagged assignments, the causal joint
mass is exactly the input prior times the represented channel entry. -/
theorem causal_joint_representation
    (prior : FinDist (Object.of State))
    (normalForm : NormalForm History State)
    (input : State) (output : History × State) :
    (causal prior normalForm).joint.prob (causalAssignment input output) =
      prior.prob input * normalForm.toFinStoch.prob input output := by
  rw [(causal prior normalForm).observational_factorization]
  simp only [Fin.prod_univ_succ, Fin.succ_zero_eq_one]
  change prior.prob input * _ =
    prior.prob input * normalForm.toFinStoch.prob input output
  congr 1
  rw [causal_mechanism_one]
  simp [causalAssignment, causalOutputMechanism,
    causalOutputDistribution, causalInput, causalParent, causalDAG]

/-- Resource-accounted randomized computation represented by the same exact
channel. -/
def computation (resource : ComputationResource)
    (normalForm : NormalForm History State) :
    Randomized.Object.of State ⟶ Randomized.Object.of (History × State) :=
  Randomized.mk normalForm.toFinStoch resource

/-- Canonical four-coordinate resource declaration extracted from a dependent
tree.  Worst-case path cost controls steps and gates; maximum depth controls
queries and stored history slots. -/
def treeResource {signature : Signature.{u}} (tree : Tree signature) :
    ComputationResource :=
  ComputationResource.of tree.budget tree.height tree.height tree.budget

@[simp]
theorem treeResource_steps {signature : Signature.{u}}
    (tree : Tree signature) :
    treeResource tree .steps = tree.budget :=
  rfl

@[simp]
theorem treeResource_queries {signature : Signature.{u}}
    (tree : Tree signature) :
    treeResource tree .queries = tree.height :=
  rfl

@[simp]
theorem treeResource_storage {signature : Signature.{u}}
    (tree : Tree signature) :
    treeResource tree .storage = tree.height :=
  rfl

@[simp]
theorem treeResource_gates {signature : Signature.{u}}
    (tree : Tree signature) :
    treeResource tree .gates = tree.budget :=
  rfl

/-- Every realized dependent history stays within the step coordinate of the
canonical randomized-computation resource declaration. -/
theorem historyCost_le_treeResource_steps {signature : Signature.{u}}
    (tree : Tree signature) (history : tree.History) :
    tree.historyCost history ≤ treeResource tree .steps := by
  simpa using tree.historyCost_le_budget history

/-- Every realized dependent history fits in the storage coordinate of the
canonical randomized-computation resource declaration. -/
theorem historyLength_le_treeResource_storage {signature : Signature.{u}}
    (tree : Tree signature) (history : tree.History) :
    tree.historyLength history ≤ treeResource tree .storage := by
  simpa using tree.historyLength_le_height history

/-- Canonical resource-accounted randomized realization of a dependent tree. -/
def treeComputation {signature : Signature.{u}}
    (semantics : Semantics signature State) (tree : Tree signature) :
    Randomized.Object.of State ⟶
      Randomized.Object.of (tree.History × State) :=
  computation (treeResource tree) (tree.normalForm semantics)

omit [Inhabited State] in
@[simp]
theorem treeComputation_resource {signature : Signature.{u}}
    (semantics : Semantics signature State) (tree : Tree signature) :
    (treeComputation semantics tree).resource = treeResource tree :=
  rfl

/-- The semantic experiment exposed by a dependent normal form.  Task value
is evaluated separately so the underlying experiment remains available for
representation and completeness. -/
abbrev semanticExperiment (normalForm : NormalForm History State) :
    FinStoch (Object.of State) (Object.of (History × State)) :=
  normalForm.toFinStoch

/-- A fixed decision problem and baseline relative to which observations carry
semantic information. -/
structure SemanticContext (State Action Baseline : Type u)
    [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    [Fintype Baseline] [DecidableEq Baseline] where
  /-- Task whose Bayes risk gives observations their meaning. -/
  problem : DecisionProblem (Object.of State) (Object.of Action)
  /-- Reference experiment used to measure task-relative improvement. -/
  baseline : FinStoch (Object.of State) (Object.of Baseline)

/-- A semantic-information process keeps the full experiment in a fixed task
context.  Its numeric value is derived, not stored independently. -/
structure SemanticRealization (History State Action Baseline : Type u)
    [Fintype History] [DecidableEq History]
    [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    [Fintype Baseline] [DecidableEq Baseline]
    (context : SemanticContext State Action Baseline) where
  /-- Observation channel evaluated by the semantic task. -/
  experiment : FinStoch (Object.of State) (Object.of (History × State))

namespace SemanticRealization

variable {context : SemanticContext State Action Baseline}

/-- Task-relative information value derived from a semantic realization. -/
def value (realization :
    SemanticRealization History State Action Baseline context) : ℚ≥0 :=
  semanticValue context.problem context.baseline realization.experiment

omit [Inhabited State] in
/-- Semantic realizations in one task context are equal when their complete
experiments are equal. -/
@[ext]
theorem ext (first second :
    SemanticRealization History State Action Baseline context)
    (equality : first.experiment = second.experiment) : first = second := by
  cases first
  cases second
  cases equality
  rfl

end SemanticRealization

/-- Interpret a dependent normal form as a task-contextual semantic process. -/
def semantic (context : SemanticContext State Action Baseline)
    (normalForm : NormalForm History State) : ℚ≥0 :=
  semanticValue context.problem context.baseline
    (semanticExperiment normalForm)

/-- The structured semantic realization used by the six-model interface. -/
def semanticRealization (context : SemanticContext State Action Baseline)
    (normalForm : NormalForm History State) :
    SemanticRealization History State Action Baseline context where
  experiment := semanticExperiment normalForm

omit [Inhabited State] in
@[simp]
theorem semanticRealization_experiment
    (context : SemanticContext State Action Baseline)
    (normalForm : NormalForm History State) :
    (semanticRealization context normalForm).experiment =
      normalForm.toFinStoch :=
  rfl

omit [Inhabited State] in
@[simp]
theorem semanticRealization_value
    (context : SemanticContext State Action Baseline)
    (normalForm : NormalForm History State) :
    (semanticRealization context normalForm).value =
      semanticValue context.problem context.baseline normalForm.toFinStoch :=
  rfl

/-- Thermal input system whose equilibrium is the supplied exact prior. -/
def thermalInput (prior : FinDist (Object.of State)) : ThermalObject where
  system := Object.of State
  equilibrium := prior

/-- Thermal output carrier equipped with an externally supplied exact
equilibrium. Unlike `thermalOutput`, this target is not defined by pushing the
input prior through a normal form. -/
def thermalTarget
    (targetEquilibrium : FinDist (Object.of (History × State))) :
    ThermalObject where
  system := Object.of (History × State)
  equilibrium := targetEquilibrium

/-- Intrinsic compatibility of a dependent normal form with an externally
specified thermal target. -/
def IsThermalTargetCompatible
    (prior : FinDist (Object.of State))
    (targetEquilibrium : FinDist (Object.of (History × State)))
    (normalForm : NormalForm History State) : Prop :=
  GibbsPreserving.IsEquilibriumCompatible
    (X := thermalInput prior) (Y := thermalTarget targetEquilibrium)
    normalForm.toFinStoch

/-- A compatible externally specified equilibrium gives a Gibbs-preserving
realization of the normal form into that target. -/
def thermalInto
    (prior : FinDist (Object.of State))
    (targetEquilibrium : FinDist (Object.of (History × State)))
    (normalForm : NormalForm History State)
    (compatible : IsThermalTargetCompatible prior targetEquilibrium
      normalForm) :
    GibbsPreserving (thermalInput prior) (thermalTarget targetEquilibrium) :=
  GibbsPreserving.ofCompatible normalForm.toFinStoch compatible

omit [Inhabited State] in
@[simp]
theorem thermalInto_channel
    (prior : FinDist (Object.of State))
    (targetEquilibrium : FinDist (Object.of (History × State)))
    (normalForm : NormalForm History State)
    (compatible : IsThermalTargetCompatible prior targetEquilibrium
      normalForm) :
    (thermalInto prior targetEquilibrium normalForm compatible).channel =
      normalForm.toFinStoch :=
  rfl

/-- Thermal output system with the equilibrium induced by the represented
channel. -/
def thermalOutput (prior : FinDist (Object.of State))
    (normalForm : NormalForm History State) : ThermalObject where
  system := Object.of (History × State)
  equilibrium := prior.push normalForm.toFinStoch

/-- Gibbs-preserving realization into the induced output equilibrium. -/
def thermal (prior : FinDist (Object.of State))
    (normalForm : NormalForm History State) :
    GibbsPreserving (thermalInput prior) (thermalOutput prior normalForm) where
  channel := normalForm.toFinStoch
  preserves_equilibrium := rfl

omit [Inhabited State] in
/-- Compatibility with an externally supplied target says exactly that its
equilibrium is the equilibrium induced by the represented channel. -/
theorem isThermalTargetCompatible_iff_target_eq_induced
    (prior : FinDist (Object.of State))
    (targetEquilibrium : FinDist (Object.of (History × State)))
    (normalForm : NormalForm History State) :
    IsThermalTargetCompatible prior targetEquilibrium normalForm ↔
      targetEquilibrium = (thermalOutput prior normalForm).equilibrium := by
  change prior.push normalForm.toFinStoch = targetEquilibrium ↔
    targetEquilibrium = prior.push normalForm.toFinStoch
  exact eq_comm

omit [Inhabited State] in
/-- **Non-induced thermal-target representation.** An externally supplied
finite target equilibrium supports the normal-form channel exactly when there
is a unique Gibbs-preserving lift with that underlying channel. -/
theorem isThermalTargetCompatible_iff_existsUnique
    (prior : FinDist (Object.of State))
    (targetEquilibrium : FinDist (Object.of (History × State)))
    (normalForm : NormalForm History State) :
    IsThermalTargetCompatible prior targetEquilibrium normalForm ↔
      ∃! process : GibbsPreserving (thermalInput prior)
          (thermalTarget targetEquilibrium),
        process.channel = normalForm.toFinStoch :=
  GibbsPreserving.isEquilibriumCompatible_iff_existsUnique
    (X := thermalInput prior) (Y := thermalTarget targetEquilibrium)
    normalForm.toFinStoch

/-- Equality of compatible realizations into one externally specified target
is exactly equality of dependent normal forms. -/
theorem thermalInto_eq_iff
    (prior : FinDist (Object.of State))
    (targetEquilibrium : FinDist (Object.of (History × State)))
    {first second : NormalForm History State}
    (firstCompatible : IsThermalTargetCompatible prior targetEquilibrium first)
    (secondCompatible :
      IsThermalTargetCompatible prior targetEquilibrium second) :
    thermalInto prior targetEquilibrium first firstCompatible =
        thermalInto prior targetEquilibrium second secondCompatible ↔
      first = second := by
  constructor
  · intro equality
    apply NormalForm.toFinStoch_injective
    exact congrArg GibbsPreserving.channel equality
  · intro equality
    subst second
    apply GibbsPreserving.ext
    rfl

omit [Inhabited State] in
/-- The former induced-target construction is the canonical special case of
the externally targeted realization. -/
theorem thermal_eq_thermalInto_induced
    (prior : FinDist (Object.of State))
    (normalForm : NormalForm History State) :
    thermal prior normalForm =
      thermalInto prior (prior.push normalForm.toFinStoch) normalForm rfl :=
  rfl

omit [Inhabited State] in
/-- The induced output equilibrium is the prior-weighted branch table. -/
theorem thermalOutput_equilibrium
    (prior : FinDist (Object.of State))
    (normalForm : NormalForm History State)
    (output : History × State) :
    (thermalOutput prior normalForm).equilibrium.prob output =
      ∑ input, prior.prob input * normalForm.toFinStoch.prob input output :=
  rfl

/-- Equality of stochastic realizations is exactly equality of dependent
normal forms. -/
theorem probability_eq_iff
    {first second : NormalForm History State} :
    probability first = probability second ↔ first = second :=
  NormalForm.toFinStoch_eq_iff

/-- Faithfulness of measurement--preparation upgrades stochastic normal-form
completeness to the quantum realization. -/
theorem quantum_eq_iff {first second : NormalForm History State} :
    quantum first = quantum second ↔ first = second := by
  constructor
  · intro equality
    exact NormalForm.toFinStoch_injective
      (measurementPreparation_faithful equality)
  · rintro rfl
    rfl

/-- Equality of randomized programs at one fixed resource declaration is
exactly equality of their dependent normal forms. -/
theorem computation_eq_iff (resource : ComputationResource)
    {first second : NormalForm History State} :
    computation resource first = computation resource second ↔
      first = second := by
  constructor
  · intro equality
    apply NormalForm.toFinStoch_injective
    exact congrArg Randomized.Hom.channel equality
  · rintro rfl
    rfl

/-- Equality of full semantic experiments, before applying a possibly
non-faithful task-value projection, is exactly normal-form equality. -/
theorem semanticExperiment_eq_iff
    {first second : NormalForm History State} :
    semanticExperiment first = semanticExperiment second ↔ first = second :=
  NormalForm.toFinStoch_eq_iff

/-- In one fixed task context, equality of structured semantic-information
processes is exactly equality of dependent normal forms.  Equality of numeric
task value alone is intentionally not claimed to be faithful. -/
theorem semanticRealization_eq_iff
    (context : SemanticContext State Action Baseline)
    {first second : NormalForm History State} :
    semanticRealization context first = semanticRealization context second ↔
      first = second := by
  constructor
  · intro equality
    apply NormalForm.toFinStoch_injective
    exact congrArg SemanticRealization.experiment equality
  · rintro rfl
    rfl

/-- Equality of the underlying thermal channels is exactly normal-form
equality.  The codomain equilibrium is then equal by stochastic pushforward. -/
theorem thermal_channel_eq_iff
    (prior : FinDist (Object.of State))
    {first second : NormalForm History State} :
    (thermal prior first).channel = (thermal prior second).channel ↔
      first = second :=
  NormalForm.toFinStoch_eq_iff

/-- Equality of valid causal joint entries for every input and recorded output. -/
def CausallyEqual (prior : FinDist (Object.of State))
    (first second : NormalForm History State) : Prop :=
  ∀ input output,
    (causal prior first).joint.prob (causalAssignment input output) =
      (causal prior second).joint.prob (causalAssignment input output)

/-- With a full-support prior, the causal joint presentation is faithful to
the entire dependent normal form. -/
theorem causallyEqual_iff
    (prior : FinDist (Object.of State))
    (fullSupport : ∀ input, 0 < prior.prob input)
    {first second : NormalForm History State} :
    CausallyEqual prior first second ↔ first = second := by
  constructor
  · intro equality
    apply NormalForm.toFinStoch_injective
    apply FinStoch.ext
    intro input output
    have jointEquality := equality input output
    rw [causal_joint_representation, causal_joint_representation]
      at jointEquality
    exact mul_left_cancel₀ (ne_of_gt (fullSupport input)) jointEquality
  · rintro rfl
    intro input output
    rfl

/-- Simultaneous equality of the six operational realizations.  For thermal
systems the comparison is made at the common underlying channel, because the
codomain equilibrium is induced from that channel. -/
def AllModelsAgree (context : SemanticContext State Action Baseline)
    (prior : FinDist (Object.of State))
    (resource : ComputationResource)
    (first second : NormalForm History State) : Prop :=
  probability first = probability second ∧
    quantum first = quantum second ∧
    CausallyEqual prior first second ∧
    computation resource first = computation resource second ∧
    semanticRealization context first = semanticRealization context second ∧
    (thermal prior first).channel = (thermal prior second).channel

/-- **Six-model completeness.**  For any full-support exact prior, the six
realizations agree exactly when the canonical dependent normal forms agree. -/
theorem allModelsAgree_iff
    (context : SemanticContext State Action Baseline)
    (prior : FinDist (Object.of State))
    (fullSupport : ∀ input, 0 < prior.prob input)
    (resource : ComputationResource)
    {first second : NormalForm History State} :
    AllModelsAgree context prior resource first second ↔ first = second := by
  constructor
  · intro agreement
    exact probability_eq_iff.mp agreement.1
  · rintro rfl
    exact ⟨rfl, rfl, causallyEqual_iff prior fullSupport |>.2 rfl,
      rfl, rfl, rfl⟩

/-- The proposition that all six constructions expose the same exact
normal-form channel at their operational boundary. -/
def RepresentedInAllModels
    (context : SemanticContext State Action Baseline)
    (prior : FinDist (Object.of State))
    (resource : ComputationResource)
    (normalForm : NormalForm History State) : Prop :=
  probability normalForm = normalForm.toFinStoch ∧
    quantum normalForm = measurementPreparation normalForm.toFinStoch ∧
    (∀ input output,
      (causal prior normalForm).joint.prob (causalAssignment input output) =
        prior.prob input * normalForm.toFinStoch.prob input output) ∧
    ((computation resource normalForm).channel = normalForm.toFinStoch ∧
      (computation resource normalForm).resource = resource) ∧
    ((semanticRealization context normalForm).experiment =
        normalForm.toFinStoch ∧
      (semanticRealization context normalForm).value =
        semanticValue context.problem context.baseline
          normalForm.toFinStoch) ∧
    ((thermal prior normalForm).channel = normalForm.toFinStoch ∧
      (thermalOutput prior normalForm).equilibrium =
        prior.push normalForm.toFinStoch)

/-- **Six-model representation package.**  All six constructions expose the
same exact normal-form channel at their operational boundary, while the causal
and thermal models additionally record the supplied prior. -/
theorem sixModelRepresentation
    (context : SemanticContext State Action Baseline)
    (prior : FinDist (Object.of State))
    (resource : ComputationResource)
    (normalForm : NormalForm History State) :
    RepresentedInAllModels context prior resource normalForm :=
  ⟨rfl, rfl, causal_joint_representation prior normalForm,
    ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- Comparing two dependent trees along an explicit history equivalence is
equivalent to simultaneous equality of all six normal-form realizations. -/
theorem tree_allModelsAgree_iff
    {signature : Signature.{u}}
    (semantics : Semantics signature State)
    (context : SemanticContext State Action Baseline)
    (prior : FinDist (Object.of State))
    (fullSupport : ∀ input, 0 < prior.prob input)
    (resource : ComputationResource)
    (first second : Tree signature)
    (historyEquivalence : first.History ≃ second.History) :
    AllModelsAgree context prior resource
        (first.normalForm semantics)
        ((second.normalForm semantics).reindexHistory historyEquivalence) ↔
      first.normalForm semantics =
        (second.normalForm semantics).reindexHistory historyEquivalence :=
  allModelsAgree_iff context prior fullSupport resource

/-- Operational form of `tree_allModelsAgree_iff`: equality in all six
realizations is equivalent to equality of the history-recording stochastic
processes after the explicit history reindexing. -/
theorem tree_allModelsAgree_iff_run
    {signature : Signature.{u}}
    (semantics : Semantics signature State)
    (context : SemanticContext State Action Baseline)
    (prior : FinDist (Object.of State))
    (fullSupport : ∀ input, 0 < prior.prob input)
    (resource : ComputationResource)
    (first second : Tree signature)
    (historyEquivalence : first.History ≃ second.History) :
    AllModelsAgree context prior resource
        (first.normalForm semantics)
        ((second.normalForm semantics).reindexHistory historyEquivalence) ↔
      first.run semantics =
        ((second.normalForm semantics).reindexHistory
          historyEquivalence).toFinStoch := by
  rw [tree_allModelsAgree_iff semantics context prior fullSupport resource
    first second historyEquivalence]
  exact NormalForm.toFinStoch_eq_iff.symm

end Ript.Semantics.DependentBranchingRealization
