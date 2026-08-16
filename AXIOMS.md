# Assumption Audit

The core declares no project-specific assumptions. The following table records
the actual output of `lake env lean Ript/Audit/AxiomChecks.lean`.

| Theorem | Kernel output | Source |
| --- | --- | --- |
| `Ript.Resource.budgeted_id` | `[propext]` | `Ript/Resource/Budget.lean` |
| `Ript.Resource.budgeted_comp` | `[propext, Quot.sound]` | `Ript/Resource/Budget.lean` |
| `Ript.Syntax.Expr.syntaxCost_id` | `none` | `Ript/Syntax/Cost.lean` |
| `Ript.Syntax.Expr.syntaxCost_comp` | `none` | `Ript/Syntax/Cost.lean` |
| `Ript.Semantics.eval_id` | `none` | `Ript/Semantics/Eval.lean` |
| `Ript.Semantics.eval_comp` | `none` | `Ript/Semantics/Eval.lean` |
| `Ript.Semantics.eval_cost_le` | `[propext, Quot.sound]` | `Ript/Semantics/Eval.lean` |
| `Ript.Semantics.soundness` | `[propext]` | `Ript/Semantics/Soundness.lean` |
| `Ript.Semantics.complete_via_term_model` | `[propext, Quot.sound]` | `Ript/Semantics/Completeness.lean` |
| `Ript.Semantics.budget_complete_in_free_model` | `[propext, Quot.sound]` | `Ript/Semantics/Completeness.lean` |
| `Ript.Resource.budgeted_tensor` | `[propext, Quot.sound]` | `Ript/Resource/ParallelBudget.lean` |
| `Ript.Semantics.monoidalEval_cost_le` | `[propext, Quot.sound]` | `Ript/Semantics/MonoidalEval.lean` |
| `Ript.Semantics.monoidal_soundness` | `[propext, Quot.sound]` | `Ript/Semantics/MonoidalSoundness.lean` |
| `Ript.Semantics.monoidal_complete_via_term_model` | `[propext, Quot.sound]` | `Ript/Semantics/MonoidalCompleteness.lean` |
| `Ript.Semantics.monoidal_budget_complete_in_free_model` | `[propext, Quot.sound]` | `Ript/Semantics/MonoidalCompleteness.lean` |
| `Ript.Semantics.Free.lift_on_generator` | `[propext, Quot.sound]` | `Ript/Semantics/MonoidalInitiality.lean` |
| `Ript.Semantics.Free.lift_preserves_cost` | `[propext, Quot.sound]` | `Ript/Semantics/MonoidalInitiality.lean` |
| `Ript.Semantics.Free.lift_unique` | `[propext, Quot.sound]` | `Ript/Semantics/MonoidalInitiality.lean` |
| `Ript.Models.FiniteStochastic.FinStoch.id_apply` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteStochastic.lean` |
| `Ript.Models.FiniteStochastic.FinStoch.comp_apply` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteStochastic.lean` |
| `Ript.Models.FiniteStochastic.FinStoch.tensor_apply` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteStochastic.lean` |
| `Ript.Models.FiniteStochastic.FinStoch.dirac_comp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteStochastic.lean` |
| `Ript.Models.FiniteStochastic.FinStoch.dirac_faithful` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteStochastic.lean` |
| `Ript.Models.FiniteStochastic.FinStoch.comp_discard` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteStochastic.lean` |
| `Ript.Models.FiniteDistribution.FinDist.pure_bind` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteDistribution.lean` |
| `Ript.Models.FiniteDistribution.FinDist.bind_pure` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteDistribution.lean` |
| `Ript.Models.FiniteDistribution.FinDist.bind_assoc` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteDistribution.lean` |
| `Ript.Models.FiniteStochastic.kleisliToChannel_channelToKleisli` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteStochastic/Kleisli.lean` |
| `Ript.Models.FiniteStochastic.channelToKleisli_kleisliToChannel` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteStochastic/Kleisli.lean` |
| `Ript.Models.FiniteStochastic.kleisliEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteStochastic/Kleisli.lean` |
| `Ript.Models.Probability.StochFunctor.rowMeasure_singleton` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Probability/StochFunctor.lean` |
| `Ript.Models.Probability.StochFunctor.toKernel_comp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Probability/StochFunctor.lean` |
| `Ript.Models.Probability.StochFunctor.toStoch_map_dirac` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Probability/StochFunctor.lean` |
| `Ript.Models.Probability.StochFunctor.toStoch_map_eq_iff` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Probability/StochFunctor.lean` |
| `Ript.Models.Probability.StochFunctor.productMeasurableSpace_eq_top` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Probability/StochFunctor.lean` |
| `Ript.Models.Probability.StochFunctor.toStoch_map_tensor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Probability/StochFunctor.lean` |
| `Ript.Core.Simulates.trans` | `none` | `Ript/Core/Simulation.lean` |
| `Ript.Core.SimulatesWithin.trans` | `[propext, Quot.sound]` | `Ript/Core/Simulation.lean` |
| `Ript.Models.Decision.Blackwell.dominates_tensor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/Blackwell.lean` |
| `Ript.Models.Decision.Blackwell.semanticBayesRisk_mono` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/Blackwell.lean` |
| `Ript.Models.Decision.FiniteRisk.finiteBayesRisk_le_randomizedDecisionRisk` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/FiniteRisk.lean` |
| `Ript.Models.Decision.FiniteRisk.finiteBayesRisk_mono` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/FiniteRisk.lean` |
| `Ript.Models.Decision.ResourceBounded.resourceBayesRisk_antitone` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/ResourceBounded.lean` |
| `Ript.Models.Decision.ResourceBounded.resourceBayesRisk_le_of_reduction` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/ResourceBounded.lean` |
| `Ript.Models.Decision.SemanticValue.semanticValue_mono` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/SemanticValue.lean` |
| `Ript.Models.Decision.SemanticValue.resourceSemanticValue_mono_reduction` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/SemanticValue.lean` |
| `Ript.Models.Computation.ComputationResource.within_sound` | `[propext]` | `Ript/Models/Computation/Resource.lean` |
| `Ript.Models.Computation.Total.tensor_comp` | `[propext, Quot.sound]` | `Ript/Models/Computation/Total.lean` |
| `Ript.Models.Computation.Partial.tensor_comp` | `[propext, Quot.sound]` | `Ript/Models/Computation/Partial.lean` |
| `Ript.Models.Computation.Partial.ofTotal_resource` | `[propext, Quot.sound]` | `Ript/Models/Computation/Partial.lean` |
| `Ript.Examples.SimpleComputation.total_interpreter_cost_sound` | `[propext, Quot.sound]` | `Ript/Examples/SimpleComputation.lean` |
| `Ript.Examples.SimpleComputation.partial_budget_checker_sound` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleComputation.lean` |
| `Ript.Models.Causal.FiniteDAG.acyclic` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/DAG.lean` |
| `Ript.Models.Causal.FiniteCausalModel.prefixFactorMass_normalized` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/Model.lean` |
| `Ript.Models.Causal.FiniteCausalModel.observational_factorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/Model.lean` |
| `Ript.Models.Causal.FiniteCausalModel.intervene_same` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/Intervention.lean` |
| `Ript.Models.Causal.FiniteCausalModel.intervene_idempotent` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/Intervention.lean` |
| `Ript.Models.Causal.FiniteCausalModel.intervene_comm_of_disjoint` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/Intervention.lean` |
| `Ript.Models.Causal.FiniteCausalModel.intervention_preserves_normalization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/Intervention.lean` |
| `Ript.Models.Causal.FiniteCausalModel.interventional_factorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/FinStoch.lean` |
| `Ript.Examples.SimpleCausalModel.intervention_replaces_child_mechanism` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleCausalModel.lean` |

`propext` and `Quot.sound` are Lean's standard logical and quotient principles;
they are not project-declared assumptions. The quotient dependency is confined
to proof semantics. The stage-1 and stage-2 flagship theorems do not depend on
classical choice. The finite stochastic and finite-distribution representation
theorems report `Classical.choice` through Mathlib's generic
`Fintype` and finite-sum proof infrastructure. Runtime channel data instead
uses explicitly supplied `Fintype` and `DecidableEq` values; no definition in
the executable finite model is `noncomputable`, and the checked `#eval`
examples execute exact rational probabilities. The Stage-5 bridge is
deliberately noncomputable only in its measure-theoretic semantic module:
finite rational rows are interpreted as finite sums of Dirac measures and then
packaged as Mathlib `Stoch` kernels. It does not feed choice-derived data back
into the executable model. Stage 6 adds executable finite minima over explicitly
enumerated deterministic decision rules. Its definitions remain computable;
`Classical.choice` in audited finite-decision theorems comes from Mathlib's
finite-set and category proof infrastructure and, for existence of an optimal
rule, proof-only finite choice. The separate semantic Bayes-risk theorem reuses
Mathlib's noncomputable `bayesRisk` exactly at the measure-theoretic boundary.
The Stage-7 computation slice uses a pointwise `Fin 4 → Nat` resource vector
and executable total and `Option`-partial functions. Its category, tensor
bifunctor, total-to-partial embedding, and resource data are computational.
The specialized partial budget theorem reports `Classical.choice` through the
proof that a Boolean comparison over the finite coordinate type is true; the
checker itself evaluates directly, and `ComputationResource.within_sound`
does not use classical choice.
The finite causal slice is executable over a supplied finite value carrier and
uses a topological numbering certificate rather than a chosen topological
sort. Its definitions of parent-local mechanisms, factor products, hard
interventions, and exact `FinStoch` states are all computational. The audited
causal theorems report `Classical.choice` and `Quot.sound` through Mathlib's
generic finite-set, finite-product, and nonnegative-rational proof
infrastructure; no choice-derived value is used by the evaluator, and the
two-node example reduces to exact rational results under ordinary `#eval`.
In particular,
the braided hexagon soundness cases use the primitive `BraidedCategory`
hexagon laws directly, so the stage-2 flagship results do not acquire that
dependency from derived coherence lemmas.

No audited theorem uses compiler trust or a placeholder-proof assumption.

The `Ript/Univalent/` boundary does not yet exist and is not imported by the core.
