import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Ript.Models.Causal.FinStoch

/-!
# Executable two-node causal model

The root `cause` is a fair Boolean variable and the child `effect` copies its
parent.  Observationally only equal pairs occur.  After `do(effect = true)`,
the cause remains fair while the effect is forced to `true`; this executable
difference is the characteristic mechanism-replacement semantics of an
intervention rather than ordinary conditioning.

The same model also witnesses a genuine stochastic intervention: replacing
the child mechanism by an independent fair coin gives four exact quarter-mass
assignments. A subsequent explicit reinstall of the original child mechanism
normalizes to the empty soft-intervention program and returns the base model.
-/

set_option autoImplicit false

namespace Ript.Examples.SimpleCausalModel

open Ript.Models.Causal
open Ript.Models.FiniteDistribution
open Ript.Models.FiniteStochastic

/-- Node zero is the cause and node one is the effect. -/
def cause : Fin 2 := 0

/-- The child node whose mechanism copies the cause. -/
def effect : Fin 2 := 1

/-- The two-node chain `cause → effect`, with its topological certificate. -/
def chainDAG : FiniteDAG 2 where
  parents child := if child = effect then {cause} else ∅
  parent_before child parent hparent := by
    by_cases hchild : child = effect
    · subst child
      simp [cause, effect] at hparent
      subst parent
      decide
    · simp [hchild] at hparent

/-- Exact uniform distribution on Boolean values. -/
def fairBitDistribution : FinDist (Object.of Bool) where
  prob _ := (1 : ℚ≥0) / 2
  normalized := by
    change (∑ value : Bool, (1 : ℚ≥0) / 2) = 1
    rw [Fintype.sum_bool]
    norm_num

/-- A nontrivial finite causal model: a fair root and a deterministic copy
mechanism at its child. -/
def chainModel : FiniteCausalModel 2 Bool where
  dag := chainDAG
  mechanism node := by
    by_cases hroot : node = cause
    · subst node
      exact { run := fun _ ↦ fairBitDistribution }
    · have heffect : node = effect := by
        rcases Fin.eq_zero_or_eq_succ node with hzero | ⟨remaining, hsucc⟩
        · have : node = cause := by simpa [cause] using hzero
          exact False.elim (hroot this)
        · have hremaining : remaining = 0 := Fin.eq_zero remaining
          subst remaining
          simpa [effect] using hsucc
      subst node
      exact
        { run := fun parents ↦
            FinDist.pure (parents ⟨cause, by simp [chainDAG, cause, effect]⟩) }

/-- The root mechanism ignores its empty parent assignment and returns the
fair Boolean distribution. -/
@[simp]
theorem chainModel_cause
    (parents : chainModel.dag.ParentAssignment Bool cause) :
    (chainModel.mechanism cause).run parents = fairBitDistribution := by
  simp [chainModel, cause]

/-- The effect mechanism is the point distribution at its parent's value. -/
@[simp]
theorem chainModel_effect
    (parents : chainModel.dag.ParentAssignment Bool effect) :
    (chainModel.mechanism effect).run parents =
      FinDist.pure (parents ⟨cause, by
        change cause ∈ chainDAG.parents effect
        simp [chainDAG, cause, effect]⟩) := by
  simp [chainModel, cause, effect]

/-- Numeric-index form of the root mechanism equation, useful for reduction of
closed examples. -/
@[simp]
theorem chainModel_zero
    (parents : chainModel.dag.ParentAssignment Bool (0 : Fin 2)) :
    (chainModel.mechanism 0).run parents = fairBitDistribution := by
  simpa [cause] using chainModel_cause parents

/-- Numeric-index form of the child mechanism equation. -/
@[simp]
theorem chainModel_one
    (parents : chainModel.dag.ParentAssignment Bool (1 : Fin 2)) :
    (chainModel.mechanism 1).run parents =
      FinDist.pure (parents ⟨0, by
        change cause ∈ chainDAG.parents effect
        simp [chainDAG, cause, effect]⟩) := by
  simpa [cause, effect] using chainModel_effect parents

/-- The hard intervention that forces the effect to `true`. -/
def forceEffectTrue : Intervention 2 Bool :=
  Intervention.doAt effect true

/-- The example intervention leaves the root untargeted. -/
@[simp]
theorem forceEffectTrue_cause : forceEffectTrue.setting cause = none := by
  rfl

/-- The example intervention forces the child to `true`. -/
@[simp]
theorem forceEffectTrue_effect : forceEffectTrue.setting effect = some true := by
  rfl

/-- The intervened model retains the fair root mechanism. -/
@[simp]
theorem intervened_chain_zero
    (parents : (chainModel.intervene forceEffectTrue).dag.ParentAssignment
      Bool (0 : Fin 2)) :
    (((chainModel.intervene forceEffectTrue).mechanism 0).run parents) =
      fairBitDistribution := by
  simp [FiniteCausalModel.intervene, forceEffectTrue, Intervention.doAt,
    chainModel_zero, effect]

/-- The intervened child mechanism is the point distribution at `true`. -/
@[simp]
theorem intervened_chain_one
    (parents : (chainModel.intervene forceEffectTrue).dag.ParentAssignment
      Bool (1 : Fin 2)) :
    (((chainModel.intervene forceEffectTrue).mechanism 1).run parents) =
      FinDist.pure true := by
  simp [FiniteCausalModel.intervene, forceEffectTrue, Intervention.doAt,
    effect]

/-- Read one exact observational joint probability. -/
def observationalProbability (causeValue effectValue : Bool) : ℚ≥0 :=
  chainModel.joint.prob ![causeValue, effectValue]

/-- Read one exact interventional joint probability. -/
def interventionalProbability (causeValue effectValue : Bool) : ℚ≥0 :=
  (chainModel.intervene forceEffectTrue).joint.prob ![causeValue, effectValue]

/-- Observationally, the child agrees with its cause almost surely. -/
theorem observational_copy :
    observationalProbability false false = (1 : ℚ≥0) / 2 ∧
    observationalProbability false true = 0 ∧
    observationalProbability true false = 0 ∧
    observationalProbability true true = (1 : ℚ≥0) / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    unfold observationalProbability
    rw [chainModel.observational_factorization]
    norm_num [chainModel, chainDAG, fairBitDistribution, cause, effect,
      FinDist.pure]
  all_goals decide

/-- After `do(effect = true)`, the root stays fair and the effect is forced. -/
theorem intervention_replaces_child_mechanism :
    interventionalProbability false false = 0 ∧
    interventionalProbability false true = (1 : ℚ≥0) / 2 ∧
    interventionalProbability true false = 0 ∧
    interventionalProbability true true = (1 : ℚ≥0) / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    unfold interventionalProbability
    rw [(chainModel.intervene forceEffectTrue).observational_factorization]
    norm_num [FiniteCausalModel.intervene, forceEffectTrue,
      Intervention.doAt, chainModel, chainDAG, fairBitDistribution, cause,
      effect, FinDist.pure]
  all_goals decide

/-! ## Soft and stochastic intervention witness -/

/-- Parent-independent fair replacement mechanism for the child. -/
def fairEffectMechanism : Mechanism chainModel.dag Bool effect where
  run _ := fairBitDistribution

/-- A genuine stochastic intervention replacing the child copy mechanism by
an independent fair coin. -/
def randomizeEffect : SoftIntervention chainModel.dag Bool :=
  SoftIntervention.replaceAt effect fairEffectMechanism

@[simp]
theorem randomizeEffect_cause : randomizeEffect.setting cause = none := by
  rfl

@[simp]
theorem randomizeEffect_effect :
    randomizeEffect.setting effect = some fairEffectMechanism :=
  SoftIntervention.replaceAt_same effect fairEffectMechanism

@[simp]
theorem randomizeEffect_zero : randomizeEffect.setting (0 : Fin 2) = none := by
  simpa [cause] using randomizeEffect_cause

@[simp]
theorem randomizeEffect_one :
    randomizeEffect.setting (1 : Fin 2) = some fairEffectMechanism := by
  simpa [effect] using randomizeEffect_effect

/-- Read one joint probability after the stochastic child intervention. -/
def randomizedEffectProbability (causeValue effectValue : Bool) : ℚ≥0 :=
  (chainModel.softInterventionalChannel randomizeEffect).prob PUnit.unit
    ![causeValue, effectValue]

/-- Randomizing the child makes it independent of the still-fair root, so all
four assignments have exact mass `1/4`. -/
theorem stochastic_intervention_independent_fair :
    randomizedEffectProbability false false = (1 : ℚ≥0) / 4 ∧
    randomizedEffectProbability false true = (1 : ℚ≥0) / 4 ∧
    randomizedEffectProbability true false = (1 : ℚ≥0) / 4 ∧
    randomizedEffectProbability true true = (1 : ℚ≥0) / 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    unfold randomizedEffectProbability
    rw [chainModel.softInterventional_factorization randomizeEffect]
    norm_num [randomizeEffect_zero, randomizeEffect_one,
      fairEffectMechanism, chainModel, chainDAG, fairBitDistribution,
      cause, effect]

/-- Explicitly reinstall the original child mechanism. This write is
semantically meaningful after `randomizeEffect`, but redundant in the final
normal form relative to the original base model. -/
def restoreEffect : SoftIntervention chainModel.dag Bool :=
  SoftIntervention.replaceAt effect (chainModel.mechanism effect)

/-- A two-step stochastic/soft intervention program that randomizes and then
restores the child. -/
def randomizeThenRestore :
    SoftInterventionProgram.Program chainModel.dag Bool :=
  [randomizeEffect, restoreEffect]

/-- Canonical reduction erases the final explicit write of the original
mechanism, yielding the empty intervention. -/
theorem randomizeThenRestore_normalize :
    SoftInterventionProgram.normalize chainModel randomizeThenRestore =
      SoftIntervention.empty := by
  have rawEqual :
      SoftInterventionProgram.rawNormalize randomizeThenRestore =
        restoreEffect := by
    apply SoftIntervention.ext
    intro node
    fin_cases node <;>
      simp [SoftInterventionProgram.rawNormalize, randomizeThenRestore,
        randomizeEffect, restoreEffect, SoftIntervention.thenReplace,
        SoftIntervention.replaceAt,
        SoftIntervention.empty, effect]
  rw [SoftInterventionProgram.normalize, rawEqual]
  apply SoftIntervention.ext
  intro node
  fin_cases node <;>
    simp [restoreEffect, SoftIntervention.reduceAgainst,
      SoftIntervention.replaceAt, SoftIntervention.empty,
      Mechanism.EntrywiseEqual, effect]

/-- The two-step program executes back to the original causal model. -/
theorem randomizeThenRestore_run :
    SoftInterventionProgram.run chainModel randomizeThenRestore = chainModel := by
  rw [SoftInterventionProgram.run_eq_softIntervene_normalize,
    randomizeThenRestore_normalize,
    FiniteCausalModel.softIntervene_empty]

/-- Program completeness recognizes the randomize--restore program as
semantically equal to the empty program exactly through their shared reduced
normal form. -/
theorem randomizeThenRestore_semantically_empty :
    SoftInterventionProgram.SemanticallyEquivalent chainModel
      randomizeThenRestore [] := by
  rw [SoftInterventionProgram.semanticallyEquivalent_iff_normalize_eq,
    randomizeThenRestore_normalize]
  rfl

-- The observational joint is normalized exactly.
#eval decide
  (observationalProbability false false + observationalProbability false true +
    observationalProbability true false + observationalProbability true true = 1)

-- The observational mismatch `cause = false, effect = true` has zero mass.
#eval decide (observationalProbability false true = 0)

-- Intervention creates the previously impossible assignment with mass `1/2`.
#eval decide (interventionalProbability false true = (1 : ℚ≥0) / 2)

-- The forced effect cannot be false under the intervention.
#eval decide (interventionalProbability true false = 0)

-- The intervention leaves the upstream cause marginally fair.
#eval decide
  (interventionalProbability false true =
    interventionalProbability true true)

-- A stochastic child intervention yields the exact independent fair joint.
#eval decide
  (randomizedEffectProbability false false = (1 : ℚ≥0) / 4 ∧
    randomizedEffectProbability false true = (1 : ℚ≥0) / 4 ∧
    randomizedEffectProbability true false = (1 : ℚ≥0) / 4 ∧
    randomizedEffectProbability true true = (1 : ℚ≥0) / 4)

-- The reduced last-write-wins program has no targeted child node.
#eval decide
  ((SoftInterventionProgram.normalize chainModel randomizeThenRestore).setting
    effect).isNone

end Ript.Examples.SimpleCausalModel
