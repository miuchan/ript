# Assumption Audit

The core declares no project-specific assumptions. The following table records
the actual output of `lake env lean Ript/Audit/AxiomChecks.lean`.

| Theorem | Kernel output | Source |
| --- | --- | --- |
| `Ript.Resource.budgeted_id` | `[propext]` | `Ript/Resource/Budget.lean` |
| `Ript.Resource.budgeted_comp` | `[propext, Quot.sound]` | `Ript/Resource/Budget.lean` |
| `Ript.Core.CausalProcess.comp` | `none` | `Ript/Core/Capabilities.lean` |
| `Ript.Core.causal_of_deterministic` | `none` | `Ript/Core/Capabilities.lean` |
| `Ript.Models.FiniteFunction.tensor_apply` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteFunction/Monoidal.lean` |
| `Ript.Models.FiniteFunction.copy_apply` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteFunction/Monoidal.lean` |
| `Ript.Models.FiniteFunction.discard_apply` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteFunction/Monoidal.lean` |
| `Ript.Models.FiniteFunction.copy_natural` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteFunction/Monoidal.lean` |
| `Ript.Models.FiniteFunction.discard_natural` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteFunction/Monoidal.lean` |
| `Ript.Models.FiniteFunction.copy_coassociative` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteFunction/Monoidal.lean` |
| `Ript.Models.FiniteFunction.copy_commutative` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteFunction/Monoidal.lean` |
| `Ript.Models.FiniteFunction.causal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteFunction/Monoidal.lean` |
| `Ript.Examples.ClassicalCopy.negate_copy_natural` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ClassicalCopy.lean` |
| `Ript.Examples.ClassicalCopy.negate_causal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ClassicalCopy.lean` |
| `Ript.Resource.costToFiltration_toCost` | `[propext, Quot.sound]` | `Ript/Resource/Filtration.lean` |
| `Ript.Resource.filtrationToCost_toFiltration_of_attained` | `none` | `Ript/Resource/Filtration.lean` |
| `Ript.Resource.filtrationToCost_comp` | `none` | `Ript/Resource/Filtration.lean` |
| `Ript.Resource.filtrationToCost_tensor` | `none` | `Ript/Resource/Filtration.lean` |
| `Ript.Examples.CostFiltration.declaredUnitsFiltration_attained` | `[propext]` | `Ript/Examples/CostFiltration.lean` |
| `Ript.Examples.CostFiltration.declaredUnitsCost_eq_units` | `[propext]` | `Ript/Examples/CostFiltration.lean` |
| `Ript.Examples.CostFiltration.reconstructedProcessCost_eq_units` | `[propext]` | `Ript/Examples/CostFiltration.lean` |
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
| `Ript.Models.FiniteStochastic.FinStoch.mix_idem` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteStochastic/Convex.lean` |
| `Ript.Models.FiniteStochastic.FinStoch.mix_postcomp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteStochastic/Convex.lean` |
| `Ript.Models.FiniteStochastic.FinStoch.mix_precomp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteStochastic/Convex.lean` |
| `Ript.Models.FiniteStochastic.FinStoch.mix_tensor_left` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteStochastic/Convex.lean` |
| `Ript.Examples.ConvexChannels.fairIdentityOrNot_apply` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ConvexChannels.lean` |
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
| `Ript.Models.Probability.FiniteKL.distributionMeasure_push` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Probability/FiniteKL.lean` |
| `Ript.Models.Probability.FiniteKL.distributionMeasure_absolutelyContinuous_iff` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Probability/FiniteKL.lean` |
| `Ript.Models.Probability.FiniteKL.distributionMeasure_withDensity_densityRatio` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Probability/FiniteKL.lean` |
| `Ript.Models.Probability.FiniteKL.finiteKL_eq_sum_of_absolutelyContinuous` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Probability/FiniteKL.lean` |
| `Ript.Models.Probability.FiniteKL.finiteKL_toReal_eq_sum_of_fullSupport` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Probability/FiniteKL.lean` |
| `Ript.Models.Probability.FiniteKL.finiteKL_eq_zero_iff` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Probability/FiniteKL.lean` |
| `Ript.Models.Probability.FiniteKL.finiteKL_eq_top_of_support_violation` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Probability/FiniteKL.lean` |
| `Ript.Models.Probability.FiniteKL.finiteKL_eq_top_iff_support_violation` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Probability/FiniteKL.lean` |
| `Ript.Models.Probability.FiniteKL.finiteKL_dataProcessing` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Probability/FiniteKL.lean` |
| `Ript.Core.Simulates.trans` | `none` | `Ript/Core/Simulation.lean` |
| `Ript.Core.SimulatesWithin.trans` | `[propext, Quot.sound]` | `Ript/Core/Simulation.lean` |
| `Ript.Models.Decision.Blackwell.dominates_tensor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/Blackwell.lean` |
| `Ript.Models.Decision.Blackwell.semanticBayesRisk_mono` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/Blackwell.lean` |
| `Ript.Models.Decision.FiniteRisk.finiteBayesRisk_le_randomizedDecisionRisk` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/FiniteRisk.lean` |
| `Ript.Models.Decision.FiniteRisk.finiteBayesRisk_mono` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/FiniteRisk.lean` |
| `Ript.Models.Decision.DeterministicBlackwell.reconstruction_deterministicDecisionRisk` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/DeterministicBlackwell.lean` |
| `Ript.Models.Decision.DeterministicBlackwell.target_reconstructionRisk_zero` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/DeterministicBlackwell.lean` |
| `Ript.Models.Decision.DeterministicBlackwell.deterministic_dominates_iff_reconstructionRisk_le` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/DeterministicBlackwell.lean` |
| `Ript.Models.Decision.DeterministicBlackwell.deterministic_dominates_iff_fiber_refines` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/DeterministicBlackwell.lean` |
| `Ript.Examples.DeterministicBlackwell.aligned_reconstructionRisk_zero` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DeterministicBlackwell.lean` |
| `Ript.Examples.DeterministicBlackwell.crossing_reconstructionRisk_half` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DeterministicBlackwell.lean` |
| `Ript.Examples.DeterministicBlackwell.block_dominates_aligned` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DeterministicBlackwell.lean` |
| `Ript.Examples.DeterministicBlackwell.block_not_dominates_crossing` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DeterministicBlackwell.lean` |
| `Ript.Models.Decision.Separation.finiteDecisionOrder_of_dominates` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/Separation.lean` |
| `Ript.Models.Decision.Separation.DecisionSeparationCertificate.not_dominates` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/Separation.lean` |
| `Ript.Models.Decision.Separation.not_finiteDecisionOrder_iff_certificate` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/Separation.lean` |
| `Ript.Models.Decision.Separation.blackwellShermanSteinConverse_iff_separationComplete` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/Separation.lean` |
| `Ript.Models.Decision.Separation.finiteBlackwellShermanStein_iff_certificateComplete` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/Separation.lean` |
| `Ript.Models.Decision.GarblingPolytope.mixedGarbling_independentGarblingLaw` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/GarblingPolytope.lean` |
| `Ript.Models.Decision.GarblingPolytope.deterministicMixtureDominates_iff` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/GarblingPolytope.lean` |
| `Ript.ForMathlib.RationalConvexHull.mem_convexHull_of_ratCastVector_mem_convexHull` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/RationalConvexHull.lean` |
| `Ript.ForMathlib.RationalConvexHull.exists_rational_strictSeparator_of_not_mem_convexHull` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/RationalConvexHull.lean` |
| `Ript.Examples.EmptyParameterBoundary.unit_not_dominates_empty` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/EmptyParameterBoundary.lean` |
| `Ript.Examples.EmptyParameterBoundary.vacuous_finiteDecisionOrder` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/EmptyParameterBoundary.lean` |
| `Ript.Examples.EmptyParameterBoundary.converse_fails_without_nonempty` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/EmptyParameterBoundary.lean` |
| `Ript.Models.Decision.RationalSeparation.RationalGarblingSeparator.toDecisionSeparationCertificate` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/RationalSeparation.lean` |
| `Ript.Models.Decision.RationalSeparation.DecisionSeparationCertificate.toRationalGarblingSeparator` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/RationalSeparation.lean` |
| `Ript.Models.Decision.RationalSeparation.rationalGarblingSeparator_nonempty_iff_certificate` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/RationalSeparation.lean` |
| `Ript.Models.Decision.RationalSeparation.channelVector_mem_convexHull_iff` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/RationalSeparation.lean` |
| `Ript.Models.Decision.RationalSeparation.rationalSeparationComplete` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/RationalSeparation.lean` |
| `Ript.Models.Decision.RationalSeparation.blackwellShermanSteinConverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/RationalSeparation.lean` |
| `Ript.Models.Decision.RationalSeparation.finiteBlackwellShermanStein_iff_rationalSeparationComplete` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/RationalSeparation.lean` |
| `Ript.Models.Decision.RationalSeparation.finiteBlackwellShermanStein` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/RationalSeparation.lean` |
| `Ript.Examples.StochasticSeparation.noisy_information_quarter_risk` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/StochasticSeparation.lean` |
| `Ript.Examples.StochasticSeparation.uninformative_information_half_risk` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/StochasticSeparation.lean` |
| `Ript.Examples.StochasticSeparation.uninformative_not_dominates_noisy` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/StochasticSeparation.lean` |
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
| `Ript.Models.FiniteDistribution.FinDist.push_comp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteDistribution.lean` |
| `Ript.Models.FiniteDistribution.FinDist.push_tensor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteDistribution.lean` |
| `Ript.Models.Thermal.GibbsPreserving.tensor_id` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/GibbsPreserving.lean` |
| `Ript.Models.Thermal.GibbsPreserving.tensor_comp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/GibbsPreserving.lean` |
| `Ript.Models.Thermal.GibbsPreserving.equilibrium_is_free` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/GibbsPreserving.lean` |
| `Ript.Models.Thermal.FiniteClosedProtocol.runSteps_eq_push_composeSteps` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Protocol.lean` |
| `Ript.Models.Thermal.FiniteClosedProtocol.composeSteps_append` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Protocol.lean` |
| `Ript.Models.Thermal.FiniteClosedProtocol.run_equilibrium` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Protocol.lean` |
| `Ript.Models.Thermal.FiniteClosedProtocol.cannot_reach_from_equilibrium` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Protocol.lean` |
| `Ript.Models.Thermal.Divergence.athermality_monotone` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Monotone.lean` |
| `Ript.Models.Thermal.klAthermality_monotone` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/KLDivergence.lean` |
| `Ript.Models.Thermal.FiniteGibbsData.partitionFunction_pos` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Gibbs.lean` |
| `Ript.Models.Thermal.FiniteGibbsData.sum_probability` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Gibbs.lean` |
| `Ript.Models.Thermal.FiniteGibbsData.ofFullSupport_probability` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Gibbs.lean` |
| `Ript.Models.Thermal.FiniteGibbsData.tensor_partitionFunction` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Gibbs.lean` |
| `Ript.Models.Thermal.FiniteGibbsData.probability_ratio` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/RationalGibbs.lean` |
| `Ript.Models.Thermal.FiniteGibbsData.hasRationalProbabilities_iff_hasRationalBoltzmannRatiosAt` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/RationalGibbs.lean` |
| `Ript.Models.Thermal.FiniteGibbsData.ofPositiveRationalWeights_probability` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/RationalGibbs.lean` |
| `Ript.Models.Thermal.FiniteGibbsData.ofPositiveRationalWeights_hasRationalProbabilities` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/RationalGibbs.lean` |
| `Ript.Models.Thermal.GibbsThermalObject.equilibrium_fullSupport` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Gibbs.lean` |
| `Ript.Models.Thermal.GibbsThermalObject.klAthermality_toReal_eq_inverseTemperature_mul_freeEnergyGap` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/FreeEnergy.lean` |
| `Ript.Models.Thermal.GibbsThermalObject.freeEnergyGap_equilibrium` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/FreeEnergy.lean` |
| `Ript.Models.Thermal.GibbsThermalObject.freeEnergyGap_monotone` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/FreeEnergy.lean` |
| `Ript.Models.Thermal.GibbsThermalObject.freeEnergyGap_tensor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/FreeEnergy.lean` |
| `Ript.Models.Thermal.joint_absolutelyContinuous_tensor_marginals` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Correlation.lean` |
| `Ript.Models.Thermal.GibbsThermalObject.mutualInformation_eq_finiteKL_toReal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Correlation.lean` |
| `Ript.Models.Thermal.GibbsThermalObject.mutualInformation_nonneg` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Correlation.lean` |
| `Ript.Models.Thermal.GibbsThermalObject.freeEnergyGap_eq_marginals_add_correlation` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Correlation.lean` |
| `Ript.Models.Thermal.WorkAssistedTransition.landauer_freeEnergy_bound` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Work.lean` |
| `Ript.Models.Thermal.WorkAssistedTransition.landauer_work_bound` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Work.lean` |
| `Ript.Models.Thermal.CorrelatedWorkAssistedTransition.landauer_freeEnergy_bound` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/CorrelatedWork.lean` |
| `Ript.Models.Thermal.CorrelatedWorkAssistedTransition.landauer_work_bound` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/CorrelatedWork.lean` |
| `Ript.Models.Thermal.BathAssistedTransition.landauer_freeEnergy_bound` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Bath.lean` |
| `Ript.Models.Thermal.BathAssistedTransition.landauer_work_bound_of_bath_returns` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Bath.lean` |
| `Ript.Examples.ExplicitBathErasure.bathBatterySwap_erases` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ExplicitBathErasure.lean` |
| `Ript.Examples.ExplicitBathErasure.explicitBathErasure_saturates` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ExplicitBathErasure.lean` |
| `Ript.Examples.ExplicitBathErasure.explicitBathErasure_batteryEntropy_changes` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ExplicitBathErasure.lean` |
| `Ript.Models.Thermal.GibbsThermalObject.meanEnergy_pure` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/FreeEnergy.lean` |
| `Ript.Models.Thermal.GibbsThermalObject.entropy_pure` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/FreeEnergy.lean` |
| `Ript.Examples.ExactWorkErasure.exactWorkErasureChannel_erases` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ExactWorkErasure.lean` |
| `Ript.Examples.ExactWorkErasure.workBattery_low_lt_high` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ExactWorkErasure.lean` |
| `Ript.Examples.ExactWorkErasure.exactWorkErasure_batteryEntropy_neutral` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ExactWorkErasure.lean` |
| `Ript.Examples.ExactWorkErasure.exactWorkErasure_saturates_landauer_work` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ExactWorkErasure.lean` |
| `Ript.Models.Thermal.FiniteClosedProtocol.trace_twoSteps` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Protocol.lean` |
| `Ript.Models.Thermal.FiniteClosedProtocol.run_twoSteps` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Protocol.lean` |
| `Ript.Examples.ExactWorkCycle.exactWorkRechargeChannel_preserves_equilibrium` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ExactWorkCycle.lean` |
| `Ript.Examples.ExactWorkCycle.exactWorkRechargeChannel_recharges` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ExactWorkCycle.lean` |
| `Ript.Examples.ExactWorkCycle.exactWorkRecharge_batteryEntropy_neutral` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ExactWorkCycle.lean` |
| `Ript.Examples.ExactWorkCycle.exactWorkRecharge_saturates_landauer_work` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ExactWorkCycle.lean` |
| `Ript.Examples.ExactWorkCycle.exactWorkCycle_trace` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ExactWorkCycle.lean` |
| `Ript.Examples.ExactWorkCycle.exactWorkCycle_returns` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ExactWorkCycle.lean` |
| `Ript.Examples.ExactWorkCycle.exactWorkCycle_batteryEnergy_balanced` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ExactWorkCycle.lean` |
| `Ript.Examples.ExactWorkCycle.exactWorkCycle_systemFreeEnergy_balanced` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ExactWorkCycle.lean` |
| `Ript.Examples.SimpleThermalModel.thermalFlip_involutive` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleThermalModel.lean` |
| `Ript.Examples.SimpleThermalModel.thermalFlipCycle_process` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleThermalModel.lean` |
| `Ript.Examples.SimpleThermalModel.thermalFlipCycle_erased_trace` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleThermalModel.lean` |
| `Ript.Examples.SimpleThermalModel.thermalFlipCycle_returns` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleThermalModel.lean` |
| `Ript.Examples.SimpleThermalModel.no_finiteClosedProtocol_exact_erasure` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleThermalModel.lean` |
| `Ript.Examples.SimpleThermalModel.klAthermality_toReal_eq_sum` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleThermalModel.lean` |
| `Ript.Examples.SimpleThermalModel.thermalFlip_klAthermality_invariant` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleThermalModel.lean` |
| `Ript.Examples.SimpleThermalModel.thermalBit_kl_freeEnergy_identity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleThermalModel.lean` |
| `Ript.Examples.SimpleThermalModel.thermalFlip_freeEnergyGap_invariant` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleThermalModel.lean` |
| `Ript.Examples.SimpleThermalModel.canonicalGibbsThermalBit_probability` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleThermalModel.lean` |
| `Ript.Examples.RationalGibbsSpectra.twoLevelSpectrum_probability_false` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/RationalGibbsSpectra.lean` |
| `Ript.Examples.RationalGibbsSpectra.threeLevelSpectrum_hasRationalProbabilities` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/RationalGibbsSpectra.lean` |
| `Ript.Examples.RationalGibbsSpectra.irrationalTwoLevelSpectrum_not_hasRationalProbabilities` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/RationalGibbsSpectra.lean` |
| `Ript.Examples.SimpleThermalModel.thermalPair_freeEnergyGap_additive` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleThermalModel.lean` |
| `Ript.Examples.SimpleThermalModel.thermalBitAt_erased_freeEnergyGap` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleThermalModel.lean` |
| `Ript.Examples.SimpleThermalModel.thermalBit_erasure_landauer_work_bound` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleThermalModel.lean` |
| `Ript.Examples.SimpleThermalModel.correlatedBits_freeEnergyGap` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleThermalModel.lean` |
| `Ript.Examples.SimpleThermalModel.thermalBit_correlated_erasure_landauer_work_bound` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleThermalModel.lean` |
| `Ript.Examples.SimpleThermalModel.approximateErasureCost_antitone` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ApproximateErasure.lean` |
| `Ript.Examples.SimpleThermalModel.approximateErasedBit_freeEnergyGap` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ApproximateErasure.lean` |
| `Ript.Examples.SimpleThermalModel.thermalBit_approximate_erasure_landauer_work_bound` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ApproximateErasure.lean` |
| `Ript.Examples.SimpleThermalModel.thermalBit_correlated_approximate_erasure_landauer_work_bound` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ApproximateErasure.lean` |
| `Ript.Models.Quantum.KrausRepresentation.map_posSemidef` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Kraus.lean` |
| `Ript.Models.Quantum.KrausRepresentation.map_trace` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Kraus.lean` |
| `Ript.Models.Quantum.KrausChannel.map_posSemidef` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Kraus.lean` |
| `Ript.Models.Quantum.KrausChannel.map_trace` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Kraus.lean` |
| `Ript.Models.Quantum.KrausChannel.identity_applyDensity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Kraus.lean` |
| `Ript.Models.Quantum.KrausChannel.comp_applyDensity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Kraus.lean` |
| `Ript.Models.Quantum.KrausChannel.tensor_applyDensity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Tensor.lean` |
| `Ript.Models.Quantum.KrausChannel.tensor_identity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Tensor.lean` |
| `Ript.Models.Quantum.KrausChannel.tensor_comp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Tensor.lean` |
| `Ript.Models.Quantum.KrausChannel.basisBra_complete` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Discard.lean` |
| `Ript.Models.Quantum.KrausChannel.eq_discard` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Discard.lean` |
| `Ript.Models.Quantum.KrausChannel.comp_discard` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Discard.lean` |
| `Ript.Models.Quantum.KrausChannel.identity_toLinearMap` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Kraus.lean` |
| `Ript.Models.Quantum.amplification_kronecker` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/CompletePositivity.lean` |
| `Ript.Models.Quantum.KrausChannel.amplification_eq_tensor_identity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/CompletePositivity.lean` |
| `Ript.Models.Quantum.KrausChannel.toLinearMap_isCompletelyPositive` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/CompletePositivity.lean` |
| `Ript.Examples.QubitChannel.bitFlipOperator_complete` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitChannel.lean` |
| `Ript.Examples.QubitChannel.bitFlip_basisDensity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitChannel.lean` |
| `Ript.Examples.QubitChannel.bitFlip_tensor_basisDensity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitChannel.lean` |
| `Ript.Examples.QubitChannel.discard_basisDensity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitChannel.lean` |
| `Ript.Examples.QubitChannel.bellProjector_posSemidef` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitChannel.lean` |
| `Ript.Examples.QubitChannel.bellDensity_trace_one` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitChannel.lean` |
| `Ript.Examples.QubitChannel.bellDensity_cross_term` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitChannel.lean` |
| `Ript.Examples.QubitChannel.bitFlip_amplification_bell_posSemidef` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitChannel.lean` |
| `Ript.Models.Quantum.ClassicalEmbedding.transitionOperator_complete` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/ClassicalEmbedding.lean` |
| `Ript.Models.Quantum.ClassicalEmbedding.measurementPreparation_diagonalDensity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/ClassicalEmbedding.lean` |
| `Ript.Models.Quantum.ClassicalEmbedding.measurementPreparation_comp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/ClassicalEmbedding.lean` |
| `Ript.Models.Quantum.ClassicalEmbedding.measurementPreparation_tensor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/ClassicalEmbedding.lean` |
| `Ript.Models.Quantum.ClassicalEmbedding.measurementPreparation_faithful` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/ClassicalEmbedding.lean` |
| `Ript.Models.Quantum.ClassicalEmbedding.dephase_idempotent` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/ClassicalEmbedding.lean` |
| `Ript.Models.Quantum.ClassicalEmbedding.ClassicalQuantum.embedding_map_tensor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/ClassicalEmbedding.lean` |
| `Ript.Examples.ClassicalQuantum.quantumNoisyNot_false_to_true` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ClassicalQuantum.lean` |
| `Ript.Examples.ClassicalQuantum.dephase_bool_offDiagonal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ClassicalQuantum.lean` |
| `Ript.Higher.ModelTransformation.horizontalComp_interchange` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/Coherence.lean` |
| `Ript.Higher.model_pentagon` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/Coherence.lean` |
| `Ript.Higher.model_triangle` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/Coherence.lean` |
| `Ript.Higher.ModelHom.map_cost_eq` | `none` | `Ript/Higher/Equivalence.lean` |
| `Ript.Higher.ModelHom.map_comp_cost_le` | `none` | `Ript/Higher/Equivalence.lean` |
| `Ript.Higher.ModelHom.map_tensor_cost_le` | `none` | `Ript/Higher/Equivalence.lean` |
| `Ript.Higher.ModelHom.compCostReflecting` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/Equivalence.lean` |
| `Ript.Higher.CostExactModelEquivalence.hom_map_cost_eq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/Equivalence.lean` |
| `CategoryTheory.Bicategory.HomotopyCategory.homMk_eq_iff` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/HomotopyCategory.lean` |
| `CategoryTheory.Bicategory.HomotopyCategory.equivalenceOfIsIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/HomotopyCategory.lean` |
| `Ript.Higher.costExactMorphisms_isMultiplicative` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/Localization.lean` |
| `Ript.Higher.costExactLocalizationFunctor_inverts` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/Localization.lean` |
| `Ript.Higher.costExactLocalizationFunctorEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/Localization.lean` |
| `Ript.Examples.HigherLocalization.unitToNatModelHom_not_isIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/HigherLocalization.lean` |
| `Ript.Univalent.UniverseModel.internalUnivalence` | `[propext, Quot.sound]` | `Ript/Univalent/Soundness.lean` |
| `Ript.Univalent.UniverseModel.identity_eq_iff_interpret_eq` | `[propext, Quot.sound]` | `Ript/Univalent/Soundness.lean` |
| `Ript.Univalent.UniverseModel.path_interpretation_sound` | `[propext, Quot.sound]` | `Ript/Univalent/Soundness.lean` |
| `Ript.Univalent.UniverseModel.InternalPredicate.identity_indistinguishable` | `[propext, Quot.sound]` | `Ript/Univalent/Soundness.lean` |
| `Ript.Univalent.UniverseModel.functionProcessStructureIdentity` | `[propext, Quot.sound]` | `Ript/Univalent/Soundness.lean` |
| `Ript.Univalent.ProcessDerives.soundness` | `[propext, Quot.sound]` | `Ript/Univalent/Process.lean` |
| `Ript.Examples.UnivalentProcessUniverse.bitTensorUnit_ne_unitTensorBit` | `none` | `Ript/Examples/UnivalentProcessUniverse.lean` |
| `Ript.Examples.UnivalentProcessUniverse.swapIdentity_apply` | `[propext, Quot.sound]` | `Ript/Examples/UnivalentProcessUniverse.lean` |
| `Ript.Examples.UnivalentProcessUniverse.reindex_not_sound` | `[propext, Quot.sound]` | `Ript/Examples/UnivalentProcessUniverse.lean` |
| `Ript.Univalent.UniverseModel.ObjectCompletion.ofCode_eq_iff_identity` | `[propext, Quot.sound]` | `Ript/Univalent/Completion.lean` |
| `Ript.Univalent.UniverseModel.ObjectCompletion.tensor_assoc` | `[propext, Quot.sound]` | `Ript/Univalent/Completion.lean` |
| `Ript.Univalent.UniverseModel.objectCompletionUniversal` | `[propext, Quot.sound]` | `Ript/Univalent/Completion.lean` |
| `Ript.Univalent.UniverseModel.internalPredicateCompletionEquiv` | `[propext, Quot.sound]` | `Ript/Univalent/Completion.lean` |
| `Ript.Univalent.UniverseModel.objectCompletionToSkeletal_bijective` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Completion.lean` |
| `Ript.Univalent.UniverseModel.skeletalCompletionUniversal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Completion.lean` |
| `Ript.Examples.UnivalentCompletion.codeCardinality_equiv` | `[propext]` | `Ript/Examples/UnivalentCompletion.lean` |
| `Ript.Examples.UnivalentCompletion.completionDoesNotReflectCodeEquality` | `[propext, Quot.sound]` | `Ript/Examples/UnivalentCompletion.lean` |
| `Ript.Univalent.UniverseModel.yonedaEmbeddingFullyFaithful` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Presheaf.lean` |
| `Ript.Univalent.UniverseModel.representableTransformationEquiv_trans` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Presheaf.lean` |
| `Ript.Univalent.UniverseModel.representableNaturalIsoEquiv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Presheaf.lean` |
| `Ript.Univalent.UniverseModel.representableEquivNaturalIsoEquiv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Presheaf.lean` |
| `Ript.Univalent.UniverseModel.representableTransformation_isIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Presheaf.lean` |
| `Ript.Univalent.UniverseModel.yonedaEnvelopeFactorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Presheaf.lean` |
| `Ript.Univalent.UniverseModel.yonedaEnvelopeEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Presheaf.lean` |
| `Ript.Univalent.UniverseModel.yonedaEnvelopeUniversal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Presheaf.lean` |
| `Ript.Univalent.UniverseModel.interfaceIdentities_eq_isomorphisms` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Localization.lean` |
| `Ript.Univalent.UniverseModel.interfaceIdentities_isInvertedBy` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Localization.lean` |
| `Ript.Univalent.UniverseModel.interfaceIdentityStrictUniversalProperty` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Localization.lean` |
| `Ript.Univalent.UniverseModel.interfaceIdentityLocalizationUniversal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Localization.lean` |
| `Ript.Univalent.UniverseModel.toSkeletalCompletionIsEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Localization.lean` |
| `Ript.Univalent.UniverseModel.toSkeletalCompletionIsLocalization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Localization.lean` |
| `Ript.Univalent.UniverseModel.skeletalCompletionLocalizationUniversal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Localization.lean` |
| `Ript.Univalent.UniverseModel.toYonedaEnvelopeIsLocalization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Localization.lean` |
| `Ript.Univalent.UniverseModel.yonedaEnvelopeLocalizationUniversal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Localization.lean` |
| `Ript.Examples.UnivalentPresheaf.swapTransformation_component` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/UnivalentPresheaf.lean` |
| `Ript.Examples.UnivalentPresheaf.envelopeIsoDoesNotReflectCodeEquality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/UnivalentPresheaf.lean` |
| `Ript.Examples.UnivalentPresheaf.swap_preserves_cardinality` | `[propext]` | `Ript/Examples/UnivalentPresheaf.lean` |
| `Ript.Univalent.UniverseModel.interfaceNerveStrictSegal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Simplicial.lean` |
| `Ript.Univalent.UniverseModel.interfaceNerveSegalEquiv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Simplicial.lean` |
| `CategoryTheory.Nerve.kanComplex` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/GroupoidNerve.lean` |
| `Ript.Univalent.UniverseModel.interfaceNerveKanComplex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Simplicial.lean` |
| `Ript.Univalent.UniverseModel.interfaceNerveHornFiller_restricts` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Simplicial.lean` |
| `Ript.Univalent.UniverseModel.interfaceNerveQuasicategory` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Simplicial.lean` |
| `Ript.Univalent.UniverseModel.interfaceNerveTwoCoskeletal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Simplicial.lean` |
| `Ript.Univalent.UniverseModel.interfaceNerveEquivEdgeEquiv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Simplicial.lean` |
| `Ript.Univalent.UniverseModel.interfaceNerveComposition_composite` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Simplicial.lean` |
| `Ript.Univalent.UniverseModel.interfaceNerveInverseComposition_composite` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Simplicial.lean` |
| `Ript.Univalent.UniverseModel.interfaceNerveHomotopyCategoryIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/Simplicial.lean` |
| `Ript.Examples.UnivalentSimplicial.swapEdge_decodes_equiv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/UnivalentSimplicial.lean` |
| `Ript.Examples.UnivalentSimplicial.swapCancellationKanFiller_restricts` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/UnivalentSimplicial.lean` |
| `Ript.Examples.UnivalentSimplicial.swapCancellation_faces` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/UnivalentSimplicial.lean` |
| `Ript.Examples.UnivalentSimplicial.swapCancellation_segal_roundTrip` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/UnivalentSimplicial.lean` |
| `Ript.Examples.UnivalentSimplicial.simplicialEdgeDoesNotReflectCodeEquality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/UnivalentSimplicial.lean` |
| `Ript.Examples.UnivalentSimplicial.swapEdge_preserves_cardinality` | `[propext]` | `Ript/Examples/UnivalentSimplicial.lean` |
| `SSet.Path.mapIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/StrictSegalIso.lean` |
| `SSet.Path.mapIso_spine` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/StrictSegalIso.lean` |
| `SSet.StrictSegal.ofIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/StrictSegalIso.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramHorizontalSimplexEquiv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramHorizontalRowIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramHorizontalStrictSegal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramHorizontalRowIsStrictSegal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramOuterSegalEquiv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramOuterSegalEquiv_apply` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `CategoryTheory.Groupoid.constantDiagramEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/GroupoidInterval.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramHorizontalArrow_isIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramCompletenessFunctorIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramCompletenessEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramCompletenessEquivalence_functor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramCompletenessFunctorIsEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramCompletenessMap_eq_nerveMap` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `SSet.NerveEquivalenceWitness.ofEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/GroupoidalCompleteSegal.lean` |
| `SSet.KanComplex.ofIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/GroupoidalCompleteSegal.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramCompletenessNerveEquivalenceWitness` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramLevelStrictSegal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramLevelKan` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `SSet.boundaryMatchingMap_fibration` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/ReedyMatching.lean` |
| `SSet.boundaryMatchingConeIsLimit` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/ReedyMatching.lean` |
| `SSet.boundaryMatchingMap_eq_limitLift` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/ReedyMatching.lean` |
| `SSet.nerveFunctorSimplexMappingIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/ReedyMatching.lean` |
| `SSet.functorClassifyingDiagramMappingIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/ReedyMatching.lean` |
| `SSet.BoundaryReedyFibrant.matchingMap_eq_limitLift` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/ReedyMatching.lean` |
| `SSet.BoundaryReedyFibrant.matchingMap_fibration` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/ReedyMatching.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramMappingSpaceNaturalIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramMappingSpaceIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramMappingSpaceIso_naturality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramBoundaryReedyFibrant` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramBoundaryMatchingConeIsLimit` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramBoundaryMatchingMap_eq_limitLift` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramBoundaryMatchingMap_fibration` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `SSet.GroupoidalCompleteSegal.matchingConeIsLimit` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/GroupoidalCompleteSegal.lean` |
| `SSet.GroupoidalCompleteSegal.matchingMap_fibration` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/GroupoidalCompleteSegal.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramHorizontalRowKan` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramGroupoidalCompleteSegal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramVerticalVerticesIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramVerticalEdgeEquiv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramVerticalTransformation_isIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramVerticalTransformation_comp_inverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramVerticalTransformation_inverse_comp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramVerticalEdgeComponent_isIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramVerticalEdgeEquiv_inverseEdge` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |

`propext` and `Quot.sound` are Lean's standard logical and quotient principles;
they are not project-declared assumptions. The quotient dependency is confined
to proof semantics. The stage-1 and stage-2 flagship theorems do not depend on
classical choice. The cost--filtration reconstruction stores the attained least
budget as explicit data, so its round-trip, serial, and tensor proofs require no
choice; the reverse round-trip is therefore constructive for discrete resource
orders such as `Nat` as well as for complete orders. The reported `propext` and
`Quot.sound` on the forward round-trip arise from the existing process-cost
category interface, not from choosing a minimizing budget. The finite
deterministic cartesian layer chooses `PUnit` and ordinary product types
explicitly, and its tensor, copy, and discard functions reduce under ordinary
`#eval`. Its audited categorical laws nevertheless report
`[propext, Classical.choice, Quot.sound]` through Mathlib's generic cartesian
monoidal and commutative-comonoid proof infrastructure; no choice-derived
value is consumed by the executable Boolean example. The weaker generic
causality composition and deterministic-to-causal bridge require no axioms.
The finite stochastic and finite-distribution representation
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
The deterministic finite converse adds one proof-only use of
`Classical.choose` to extend a fiber-constant target from the image of a source
observation to its whole finite observation carrier. The extracted Blackwell
witness, all reconstruction risks, and the four-state aligned/crossing example
remain exact executable data; no choice-derived value is returned by an
evaluator. The converse for arbitrary finite stochastic experiments is proved,
not assumed, for the necessary nonempty hidden-state boundary. The stochastic
separation layer proves it via completeness of concrete finite decision
certificates. Constructing a certificate from failure of the universal risk
order uses an optimal deterministic rule and hence proof-only finite choice.
Certificate checking and the noisy Boolean example remain exact `ℚ≥0`
computations.
The garbling-polytope refinement remains in the same audited footprint. It
constructs an exact product distribution over deterministic post-processings
and proves that its marginals recover the original stochastic channel; this is
executable `ℚ≥0` data, not a chosen convex decomposition. The empty-hidden-state
example is kernel-checked proof data showing why the global converse requires
`Nonempty Θ.carrier`. The rational-separation layer uses proof-only
`Classical.choice` to select a target default action and an optimal finite
decision rule when converting a signed rational separator into a decision
certificate, and in the finite-dimensional geometric proof. That proof reflects
rational points from real convex hulls, applies real Hahn--Banach separation,
and uses density to choose rational coefficients while preserving finitely many
strict inequalities. It is proposition-level and does not expose a separator
algorithm. The reverse certificate conversion is explicit from the prior and
loss. All audited declarations report exactly
`[propext, Classical.choice, Quot.sound]`; no separation axiom is introduced.
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
The finite thermal slice likewise contains executable finite carriers, exact
rational equilibrium states, and exact stochastic channels. Its
Gibbs-preserving category and tensor bifunctor use proof fields only to certify
that channels preserve the distinguished distributions. Its finite closed
protocol layer is an executable list of endomorphisms: stepwise execution,
full traces, and composite-channel semantics are exact rational data. The
audited proofs show that list concatenation agrees with channel composition,
that every such protocol fixes equilibrium, and that the uniform Boolean
equilibrium therefore cannot be exactly erased in the closed model. The
explicit two-flip cycle has the trace `pure false`, `pure true`, `pure false`.
These results use the same standard footprint and introduce no project axiom;
they do not model an external bath or battery. The generic
divergence theorem still requires data processing as an explicit structure
field. The separate finite-KL semantic layer now discharges that field rather
than assuming it: it embeds exact distributions as discrete probability
measures, specializes Mathlib's extended-nonnegative-real KL divergence, and
derives full finite stochastic data processing from Mathlib's Markov-kernel
theorem. It also identifies the discrete Radon--Nikodym density with the exact
rational mass ratio, derives the finite f-divergence and classical logarithmic
sum formulas, and characterizes `∞` exactly by support violation. This confines
logarithms and measure-theoretic noncomputability to the semantic boundary. Its audited
theorems inherit `Classical.choice` and `Quot.sound` from Mathlib's measure,
integration, finite-sum, category, and nonnegative-rational infrastructure;
there is no project axiom and no choice-derived data flows back into the exact
executable model.

The Gibbs refinement adds real energies, positive inverse temperature,
exponentials, and free energy only in that noncomputable analytic layer.
`GibbsThermalObject` carries an explicit equality certificate tying those real
probabilities to the exact rational equilibrium. The full-support constructor
uses the exact equilibrium itself to define a canonical real energy function;
its proof that `Z = 1` and the common-temperature tensor/additivity theorems
stay in the same analytic layer. The audited positivity proof
uses `Classical.choice` only to extract a state from the supplied `Nonempty`
witness; no chosen value becomes executable model data. The KL/free-energy
identity and free-energy-gap monotonicity inherit precisely the existing
`[propext, Classical.choice, Quot.sound]` footprint and introduce no new
assumption. Canonical realization and tensor additivity have the same audited
footprint. The exact rationality refinement proves that an independently
specified finite real spectrum has rational normalized Gibbs probabilities iff
all Boltzmann ratios to any chosen reference state are positive rationals. Its
explicit positive-rational-weight constructor returns exact executable
`FinDist` data; only the logarithmic real spectrum remains analytic. The
two-/three-level checks evaluate exact rational masses, while the `sqrt 2`
counterexample is a proof-only nonexistence theorem. All audited declarations
retain `[propext, Classical.choice, Quot.sound]`; no new axiom and no
choice-derived runtime data are introduced. The work-assisted layer derives its Landauer free-energy balance
from those two theorems and only identifies battery energy decrease with work
under an explicit entropy-neutrality hypothesis. Its generic balance, work
specialization, and Boolean `log 2 / β` bound introduce no additional axiom.
The correlated-endpoint extension proves that Shannon mutual information is
the finite KL divergence to the product of the exact marginals, proves its
nonnegativity, decomposes joint excess free energy, and derives the corrected
Landauer bounds with the same audited footprint. The executable correlated
Boolean pair stores exactly `log 2 / β` of correlation free energy.
The bath-assisted layer adds no assumption: its system--bath--battery balance,
exact-bath-return specialization, and entropy-neutral work form all audit as
`[propext, Classical.choice, Quot.sound]`, inherited from the same analytic
finite KL/free-energy layer. The executable three-bit permutation, exact
erasure equation, free-energy saturation theorem, and battery entropy-change
theorem have that same footprint. The channel and rational endpoint states
still reduce in the kernel; `Classical.choice` is confined to proof and
analytic semantics and does not generate runtime data.
The separate two-level work-battery witness has the same audited footprint.
Its exact rational channel, pure endpoint states, and three regression checks
are executable; its logarithmic energy-gap calculation remains in the analytic
layer. The audit covers the generic pure-state energy and entropy lemmas, exact
erasure, strict battery nondegeneracy, endpoint entropy neutrality, and exact
mechanical Landauer saturation. No new axiom or choice-derived runtime data is
introduced.
The exact recharge and closed-cycle extension retains the same footprint. Its
recharge channel, Gibbs-preservation equation, exact endpoint evolution, and
three trace checks are exact rational data. The analytic proofs show that
memory free-energy release recharges the battery by `log 2 / β`, and that the
signed system and battery changes cancel over the cycle. The generic two-step
trace/run lemmas and every audited cycle theorem depend only on
`[propext, Classical.choice, Quot.sound]`; no runtime choice, new axiom, or net
work assumption is introduced.
The Boolean thermal example still evaluates its rational channel and protocol
trace facts by ordinary kernel reduction, while its no-go, KL, and free-energy
theorems are kernel-checked proof data.
The finite quantum slice is intentionally separate from the classical
stochastic object type. Density matrices are complex positive-semidefinite
matrices of trace one, and every operational map carries the mere existence of
an explicit finite Kraus family with completeness equation
`∑ i, Kᵢᴴ Kᵢ = I`. Operational actions are proved complex-linear; their
canonical tensor is certified by pairwise Kronecker Kraus operators on all
matrices. Basis bras define the trace channel, whose uniqueness proves the
causal discard law without introducing copying. Identity amplification is
defined on every finite auxiliary system, and every Kraus channel is proved
completely positive by identifying that amplification with tensoring by the
auxiliary identity. The normalized Bell-density example checks positivity,
trace one, an off-diagonal coherence entry, and preservation of positivity
under amplified Pauli-X. The audited positivity, trace-preservation, identity,
composition, tensor, discard, complete-positivity, Bell-density, and Pauli-X results
inherit `Classical.choice` and `Quot.sound`
from Mathlib's finite-sum, matrix-order, complex-number, and category proof
infrastructure. No choice-derived data is used in the channel action: the
operational map is stored directly, while its Kraus certificate is proof-only.
The Bell density is noncomputable only at Mathlib's complex operator-order
proof boundary; its matrix entries are explicit. The two `#eval decide`
contracts execute the discrete computational-basis
action; arbitrary complex-matrix equality remains in the kernel proof layer.
The classical-to-quantum layer constructs each transition operator explicitly
as `sqrt(P(y | x)) |y><x|` and proves its Kraus completeness equation. Because
the image of a stochastic identity is basis dephasing rather than the ambient
quantum identity, the faithful functor targets a dephasing-idempotent
Karoubi-style subcategory of Kraus channels. Identity, composition, independent
tensor, diagonal-state evolution, and faithfulness are all compiled theorems.
Their audited assumptions are the same standard Mathlib finite-matrix set
`[propext, Classical.choice, Quot.sound]`; no new project axiom and no
choice-derived operational channel data are introduced.
The higher-categorical layer fixes a resource type and bundles symmetric
monoidal costed process categories as 0-cells, resource-nonincreasing strong
braided monoidal functors as 1-cells, and monoidal natural transformations as
2-cells. Its vertical and horizontal composition, interchange, associator,
unitors, pentagon, and triangle laws reuse Mathlib's functor and bicategory
infrastructure. These coherence theorems report the standard
`[propext, Classical.choice, Quot.sound]` footprint inherited from that
infrastructure. The cost-exact preservation lemmas themselves use no axioms:
cost reflection is an explicit hypothesis, never inferred merely from a
bicategorical equivalence.
The first ordinary localization of that higher layer is now compiled as a
separate, explicitly truncated semantic construction. Its homotopy category
quotients 1-morphisms only by invertible 2-cells; the cost-exact marking is
closed under identity and composition; and Mathlib's Gabriel--Zisman
construction supplies a genuine `Functor.IsLocalization` instance and the
standard functor-category universal property. A zero-cost discrete example
proves that one marked arrow is not invertible before localization, so this
construction adds a genuine formal inverse. All seven audited declarations
for the quotient, multiplicative mark, localization, and example report
exactly `[propext, Classical.choice, Quot.sound]`. These are the standard
quotient and chosen-representative dependencies of the ordinary semantic
layer; they introduce no project axiom and no choice-derived executable data.
Because noninvertible 2-cells are discarded before localization, this result
is not a bicategorical, Dwyer--Kan, simplicial, or Rezk localization.
The internally univalent layer is an axiom-free deep embedding. Interface
codes, structural equivalences, identity expressions, and typed process
expressions are syntax. A small set-level model interprets raw paths and
equivalences as Lean `Equiv` values, then quotients them by equality of that
interpretation. Internal identities form a genuine Mathlib groupoid and are
equivalent to the internal structural equivalences. Process reindexing is
conjugation along those identities, and the explicit process derivation system
is sound for every supplied generator interpretation. These theorems report
only `[propext, Quot.sound]`; there is no project axiom, no `Classical.choice`,
no external univalence assumption, and no map `Equiv α β → α = β`. The
quotient is confined to proof semantics, while the raw syntax and concrete
Boolean interpretation remain executable.
Stage 12 now adds two deliberately distinct truncated completion layers. The
choice-free `ObjectCompletion` quotients codes by mere internal identity. Its
identity/equivalence characterization, structural algebra, invariant-map
universal property, and internal-predicate descent use only `[propext,
Quot.sound]`; executable invariants are supplied before quotient elimination,
so no chosen representative becomes runtime data. The categorical
`SkeletalCompletion` instead reuses Mathlib's skeleton of the internal
groupoid. It preserves every automorphism, is equivalent to the original
groupoid, and induces an equivalence of functor categories. Mathlib's chosen
skeleton representatives explain the additional `Classical.choice` in the
skeletal bijection and categorical universal-property audits. That layer is
explicitly `noncomputable` and cannot flow back into the executable core.
Neither construction is advertised as a Rezk completion: they provide only
0-truncated object identification and a 1-truncated skeletal groupoid, without
presheaf/simplicial localization or higher coherence.
The next presheaf layer reuses Mathlib's ordinary Yoneda embedding and its
essential-image infrastructure. Internal identities correspond exactly to
natural transformations between representables, all such transformations are
invertible because the source is a groupoid, and internal structural
equivalences correspond exactly to natural isomorphisms of representables.
The `YonedaEnvelope` is the full subcategory of presheaves isomorphic to a
representable and is categorically equivalent to the internal groupoid. The
audited footprint `[propext, Classical.choice, Quot.sound]` is already present
on Mathlib's generic `CategoryTheory.yoneda` and
`Yoneda.fullyFaithful`; essential-image witness extraction also uses chosen
representatives. This semantic layer is downstream of the executable syntax,
and no choice-derived object is returned to the computable core. The envelope
is still an ordinary 1-category: it is not a Rezk completion, does not make
isomorphic presheaves externally equal, and supplies no higher path or Segal
coherence.
The localization refinement uses Mathlib's existing
`Functor.IsLocalization` predicate. Since the internal interface category is
already a groupoid, its top morphism property equals its isomorphisms and
every outgoing functor inverts it. The identity, skeletal-completion, and
restricted-Yoneda functors are localization models, and Mathlib's canonical
`Localization.functorEquivalence` supplies their fixed-target universal
properties. All nine audited declarations report exactly `[propext,
Classical.choice, Quot.sound]`; this ordinary semantic theorem introduces no
project axiom and no runtime data. It does not prove localization of any
noninvertible resource process or the full model bicategory.
The simplicial layer then specializes Mathlib's ordinary categorical nerve to
the internal groupoid. Its explicit spine equivalence proves the strict Segal
condition; Mathlib derives a quasicategory instance and 2-coskeletality, and
the homotopy-category/nerve counit recovers the source groupoid. The
ForMathlib extension proves the missing general theorem that the nerve of a
groupoid is Kan: degenerate identities fill dimension one, inverses and
cancellation fill low-dimensional outer horns, strict-Segal quasicategory
structure fills inner horns, and spine reconstruction handles dimension four
and above. The base
Mathlib declarations `CategoryTheory.Nerve.strictSegal`,
`CategoryTheory.Nerve.quasicategory`, `SSet.StrictSegal.isCoskeletal`, and
`CategoryTheory.nerveFunctorCompHoFunctorIso` each audit as `[propext,
Classical.choice, Quot.sound]`, which explains the identical footprint of the
new semantic declarations. The executable syntax remains upstream and does
not consume nerve reconstruction data. The Kan theorem and chosen-filler
restriction theorem audit with the same exact list. This categorical nerve is
not claimed to be a complete Segal space, presheaf localization, or Rezk
completion; those require additional completeness or localization results not
supplied here.
The classifying-diagram layer retains the extra direction omitted by the
ordinary nerve. In outer degree `n` it forms the category of functors
`Fin (n + 1) ⥤ M.Object` and natural transformations, then applies the nerve
vertically. Every such natural transformation is pointwise invertible because
`M.Object` is a groupoid, so every vertical level is itself the nerve of a
groupoid and is proved Kan, strict Segal, quasicategorical, and 2-coskeletal.
Taking vertical vertices naturally recovers the ordinary interface nerve, and
vertical edges decode exactly to invertible natural transformations with
explicit inverse and cancellation laws. All audited declarations in this
layer report `[propext, Classical.choice, Quot.sound]`, inherited from the
quotient interface semantics and generic Mathlib nerve/category machinery.
The project-local transport API `SSet.Path.mapIso` and
`SSet.StrictSegal.ofIso` has that same exact footprint. Flipping the two
finite indexing categories gives a natural isomorphism from every horizontal
row to the ordinary nerve of `ComposableArrows M.Object k`; transporting
strict-Segal reconstruction along it proves that the actual outer spine map
is an equivalence in every bidegree. The row isomorphism, transported
strict-Segal structure, outer equivalence, and theorem identifying its forward
map with the spine all audit as `[propext, Classical.choice, Quot.sound]`.
The construction is downstream of all executable models. It introduces no
project axiom and no choice-derived runtime data. The generic groupoid
equivalence `CategoryTheory.Groupoid.constantDiagramEquivalence`, the theorem
that every represented horizontal arrow is invertible, the natural
comparison with the actual outer zero-degeneracy, the resulting category
equivalence and `Functor.IsEquivalence` instance, and the theorem identifying
the completeness map with its nerve all audit exactly as
`[propext, Classical.choice, Quot.sound]`. Thus the actual Rezk completeness
comparison is proved without a project axiom. The natural simplex-mapping
presentation, density-based matching-limit cone, universal matching map,
matching fibration, and bundled project-local boundary Reedy witness also
audit with exactly `[propext, Classical.choice, Quot.sound]`. The transported
horizontal Kan instances, the categorical nerve witness for the actual
completeness map, and the bundled project-local
`SSet.GroupoidalCompleteSegal` structure have that same exact footprint.
Mathlib-native weak-equivalence/standard complete-Segal-space packaging cannot
yet be stated against the pinned API, and a localization universal property
remains unproved and unclaimed.
In particular,
the braided hexagon soundness cases use the primitive `BraidedCategory`
hexagon laws directly, so the stage-2 flagship results do not acquire that
dependency from derived coherence lemmas.

No audited theorem uses compiler trust or a placeholder-proof assumption.

The `Ript/Univalent/` layer depends on the semantic universe model and is not
imported by `Ript/Core/`, `Ript/Computable/`, or any finite executable model.
