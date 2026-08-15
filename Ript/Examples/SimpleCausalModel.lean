import Mathlib.Tactic.NormNum
import Ript.Models.Causal.FinStoch

/-!
# Executable two-node causal model

The root `cause` is a fair Boolean variable and the child `effect` copies its
parent.  Observationally only equal pairs occur.  After `do(effect = true)`,
the cause remains fair while the effect is forced to `true`; this executable
difference is the characteristic mechanism-replacement semantics of an
intervention rather than ordinary conditioning.
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
    rfl

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
    first
    | rfl
    | intro h
      exact Bool.false_ne_true h.symm

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

end Ript.Examples.SimpleCausalModel
