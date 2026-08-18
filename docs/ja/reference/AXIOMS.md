# 仮定監査

[English](../../en/reference/AXIOMS.md) · [简体中文](../../zh-CN/reference/AXIOMS.md) ·
[日本語](AXIOMS.md) · [Esperanto](../../eo/reference/AXIOMS.md)

この表は `lake env lean Ript/Audit/AxiomChecks.lean` の実出力を記録します。
ルートの [`AXIOMS.md`](../../../AXIOMS.md) が検証スクリプトの機械的正本です。宣言名、正確な
カーネル出力、ソースファイルの列は `scripts/sync-doc-reference-tables.sh` によって同期されます。

| 定理または宣言 | カーネル出力 | ソース |
| --- | --- | --- |
<!-- BEGIN GENERATED AXIOM ROWS -->
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
| `Ript.Syntax.Signature.mapCost_comp` | `[propext, Quot.sound]` | `Ript/Syntax/Signature.lean` |
| `Ript.Syntax.Expr.unmapCost_mapCost` | `[propext]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Syntax.Expr.mapCost_unmapCost` | `[propext]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Syntax.Expr.mapCostEquiv` | `[propext]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Syntax.Expr.syntaxCost_mapCost` | `[propext]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Semantics.ResourceChangingInterpretation.equivMappedCostInterpretation` | `none` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Semantics.ResourceChangingInterpretation.eval_cost_le` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Semantics.ResourceChangingInterpretation.mapped_soundness_iff_term_model` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Semantics.ResourceChangingInterpretation.mapped_budget_complete_in_free_model` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Examples.CommonBitRealizations.semanticFlip_blackwellEquivalent_perfect` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/CommonBitRealizations.lean` |
| `Ript.Examples.CommonBitRealizations.semanticFlip_guessing_value` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/CommonBitRealizations.lean` |
| `Ript.Examples.CommonBitRealizations.computation_flip_cost` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/CommonBitRealizations.lean` |
| `Ript.Examples.CommonBitRealizations.sixModelFlipAgreement` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/CommonBitRealizations.lean` |
| `Ript.Syntax.MonoidalSignature.mapCost_comp` | `[propext, Quot.sound]` | `Ript/Syntax/MonoidalSignature.lean` |
| `Ript.Syntax.MonoidalExpr.unmapCost_mapCost` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Syntax.MonoidalExpr.mapCost_unmapCost` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Syntax.MonoidalExpr.mapCostEquiv` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Syntax.MonoidalExpr.syntaxCost_mapCost` | `[propext]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Semantics.ResourceChangingMonoidalInterpretation.equivMappedCostInterpretation` | `none` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Semantics.ResourceChangingMonoidalInterpretation.eval_cost_le` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Semantics.ResourceChangingMonoidalInterpretation.mapped_soundness_iff_term_model` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Semantics.ResourceChangingMonoidalInterpretation.mapped_budget_complete_in_free_model` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
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
| `Ript.Resource.withinBudget_reindex` | `[propext]` | `Ript/Resource/Reindexing.lean` |
| `Ript.Core.ResourceChangeFunctor.comp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Core/ResourceChange.lean` |
| `Ript.Core.ResourceChangeFunctor.map_withinBudget` | `none` | `Ript/Resource/Change.lean` |
| `Ript.Higher.ProcessModel.reindex_cost` | `[propext]` | `Ript/Higher/ResourceChange.lean` |
| `Ript.Higher.ResourceChangeModelHom.comp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/ResourceChange.lean` |
| `Ript.Higher.ResourceChangeModelHom.toReindex_map_cost_eq` | `[propext]` | `Ript/Higher/ResourceChange.lean` |
| `Ript.Higher.ResourceChangeModelHom.map_withinBudget` | `none` | `Ript/Higher/ResourceChange.lean` |
| `Ript.Higher.ResourceChangeModelTransformation.comp_toNatTrans` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/ResourceChange.lean` |
| `Ript.Higher.ResourceModelTransformation.horizontalComp_interchange` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCoherence.lean` |
| `Ript.Higher.totalModel_pentagon` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCoherence.lean` |
| `Ript.Higher.totalModel_triangle` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCoherence.lean` |
| `Ript.Examples.TotalResourceModels.projectToSteps_cost_exact` | `[propext, Quot.sound]` | `Ript/Examples/TotalResourceModels.lean` |
| `Ript.Examples.TotalResourceModels.stepBudgetedNot_cost` | `[propext, Quot.sound]` | `Ript/Examples/TotalResourceModels.lean` |
| `Ript.Models.Computation.ComputationResource.stepsHom_of` | `[propext, Quot.sound]` | `Ript/Models/Computation/Resource.lean` |
| `Ript.Examples.ResourceReindexing.countedNot_twice_step_cost` | `[propext, Quot.sound]` | `Ript/Examples/ResourceReindexing.lean` |
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
| `CategoryTheory.Bicategory.MorphismProperty.toHomotopy_homMk_iff` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MorphismProperty.lean` |
| `CategoryTheory.Bicategory.HomotopyCategory.pithToHomotopy` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/PithToHomotopy.lean` |
| `CategoryTheory.Pseudofunctor.mapEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Bicategory.Equivalence.trans` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Bicategory.Equivalence.symm` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Bicategory.Equivalence.replaceHom` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Bicategory.IsEquivalence.of_iso` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Bicategory.IsEquivalence.comp` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Bicategory.IsEquivalence.of_comp_right` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.FactorsThrough.trans` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.StrongTrans.equivalenceApp` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Bicategory.MorphismProperty.IsInvertedBy.of_equivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.precomposition` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.localPrecomposition` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.idCompEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.localPrecomposition_id_isEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Bicategory.MorphismProperty.equivalences_isBicategoricalLocalization_id` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.LocallyDiscrete.equivalenceOfIsIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Bicategory.MorphismProperty.locallyDiscrete_isInvertedBy` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `Ript.Higher.costExactMorphisms_isMultiplicative` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/Localization.lean` |
| `Ript.Higher.costExactMorphisms_homMk_iff` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/Localization.lean` |
| `Ript.Higher.IsCostExactBicategoricalLocalization.map_isEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/Localization.lean` |
| `Ript.Higher.IsCostExactBicategoricalLocalization.map_costReflecting_isEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/Localization.lean` |
| `Ript.Higher.costExactIdentity_isBicategoricalLocalization_iff` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/Localization.lean` |
| `Ript.Higher.costExactLocalizationFunctor_inverts` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/Localization.lean` |
| `Ript.Higher.costExactLocalizationFunctor_map_isIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/Localization.lean` |
| `Ript.Higher.costExactPithLocalization_map_isIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/Localization.lean` |
| `Ript.Higher.costExactLocalizationFunctorEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/Localization.lean` |
| `Ript.Examples.HigherLocalization.unitToNatModelHom_not_isIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/HigherLocalization.lean` |
| `Ript.Examples.HigherLocalization.unitToNatModelHom_not_isEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/HigherLocalization.lean` |
| `Ript.Examples.HigherLocalization.costExactIdentity_not_isBicategoricalLocalization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/HigherLocalization.lean` |
| `Ript.Examples.WalkingLocalization.inclusionFunctor_isLocalization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/WalkingLocalization.lean` |
| `Ript.Examples.WalkingLocalization.inclusion_map_arrow_comp_inverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/WalkingLocalization.lean` |
| `Ript.Examples.WalkingLocalization.inverse_comp_inclusion_map_arrow` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/WalkingLocalization.lean` |
| `Ript.Examples.WalkingLocalization.arrow_not_isEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/WalkingLocalization.lean` |
| `Ript.Examples.WalkingLocalization.inclusion_genuinely_adds_inverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/WalkingLocalization.lean` |
| `CategoryTheory.Pseudofunctor.prod` | `[propext]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Product.lean` |
| `CategoryTheory.Pseudofunctor.pair` | `[propext]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Product.lean` |
| `CategoryTheory.Pseudofunctor.StrongTrans.pair` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Product.lean` |
| `CategoryTheory.Pseudofunctor.pairEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Product.lean` |
| `CategoryTheory.Bicategory.Equivalence.prod` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Product.lean` |
| `CategoryTheory.Pseudofunctor.fstComp` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Product.lean` |
| `CategoryTheory.Pseudofunctor.prodIdSndCompEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Product.lean` |
| `CategoryTheory.Bicategory.mateEquiv_precomp` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Bicategory.mateEquiv_postcomp` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Bicategory.mateEquiv_precomp_postcomp` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Bicategory.mateEquiv_sliding` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Bicategory.mateEquiv_counit` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Bicategory.mateEquiv_unit` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.map_mateEquiv` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.StrongTrans.mate_naturality` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.StrongTrans.inverseNaturalityIso_hom` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.StrongTrans.inverseNaturalityIso_comp_hom_counit` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.StrongTrans.hom_comp_inverseNaturalityIso_unit` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.StrongTrans.inverseNaturalityIso_sliding` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.StrongTrans.inverseNaturalityIso_eq` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.StrongTrans.naturalityIsoOfIso_refl` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.StrongTrans.naturalityIsoOfIso_naturality` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.StrongTrans.naturalityIsoOfIso_injective` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos_eq_of_coherence` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos_assoc` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos_naturality_left` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos_naturality_right` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.StrongTrans.naturalityCompIsoOfIsos_right_id` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.StrongTrans.naturalityIsoOfIso_comp_left` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.StrongTrans.naturalityIsoOfIso_comp_right` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.StrongTrans.naturalityIsoOfIso_trans` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.StrongTrans.naturalityAt_inv` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `CategoryTheory.Pseudofunctor.localPrecomposition_faithful_of_obj_surjective` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/Localization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.inclusion_inverts` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.markedArrow_not_isEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.inclusion_map_markedArrow_isEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.inclusionMapMarkedArrowCompInverseIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.inverseCompInclusionMapMarkedArrowIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.discardTwoCell_not_isIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.inclusion_map₂_injective` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.inclusion_map₂_discardTwoCell_not_isIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.target_not_isLocallyDiscrete` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.inclusion_adds_inverse_and_retains_noninvertible_twoCell` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.inclusion_obj_surjective` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalCompletionHom_comp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.pathToCompletion_eq_canonicalCompletionHom` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.completion_hom_eq_canonical` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.walkingCompletionIsThin` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.completionCodiscreteEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.inclusion_localPrecomposition_faithful` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.inclusion_localPrecomposition_full` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.inclusionLocalPrecompositionFullyFaithful` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransForwardNaturality_eq_source` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransForwardNaturality_naturality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransGeneratorNaturality_eq_forward` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransGeneratorInverseNaturality_hom` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalRetainedInverseComparison` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalGeneratorRetainedComparison` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalRetainedGeneratorComparison` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalInverseComparison_identity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalInverseComparison_naturality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransRetainedInverseCompositeNaturality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransRetainedInverseNaturality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransInverseCompositeNaturality_naturality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransInverseNaturality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransInverseNaturality_naturality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransEndpointNaturality_inverse_of_not_le` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransEndpointNaturality_inclusion` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransEndpointNaturality_forward` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransEndpointNaturality_inclusion_id` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransEndpointNaturality_naturality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransEndpointNaturality_iso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransEndpointNaturality_inverseComposite` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransEndpointNaturality_comp_inclusion` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransEndpointNaturality_id_inclusion` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransEndpointNaturality_id` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransEndpointNaturality_id_eq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransForwardIdentityNaturality_transport` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_id_eq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_id` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_eq_endpoint` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_forward` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_generator` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_generatorInverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_iso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransGeneratorCancellation_counit` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransGeneratorCancellation_unit` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_compIso_inverseGenerator_generator` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_comp_inverseGenerator_generator` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_compIso_generator_inverseGenerator` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_comp_generator_inverseGenerator` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_inverseComposite` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_naturality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_comp_inclusion` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_comp_forward` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_compIso_forward` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_generatorRetained_transport` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_retainedGenerator_transport` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransRetainedInverse_sliding` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.LiftedStrongTransRetainedInverseCompositionCoherence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_comp_inverseGenerator_retained` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_comp_inverseGenerator_retained_public` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_compIso_inverseGenerator_retained_public` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_inverseGeneratorRetained_transport` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_compIso_retainedInverse_public` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_comp_retainedInverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_compIso_assoc_bootstrap` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_compIso_assoc_unbootstrap` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_compIso_of_iso_left` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_compIso_of_iso_right` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_compIso_inverse_retained` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_compIso_retained_inverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_compIso_canonicalInverse_canonicalForward` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_compIso_canonicalForward_canonicalInverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_compIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransNaturality_comp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTrans` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedStrongTransRestrictionIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.liftedModificationApp_naturality_endpoint` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.inclusion_localPrecomposition_full_endpoint` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.inclusion_localPrecomposition_essSurj` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.inclusion_localPrecomposition_isEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.localizedCoordinateFactorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.localizedCoordinateSource_inverts` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.localizedCoordinateSource_has_factorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.localizedCoordinateLift_map_inverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.localizedCoordinate_inverts_factors_and_maps_inverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.retainedSource_inverts` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.retainedFactorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.retainedSource_has_factorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.retainedCoordinate_map₂_discardTwoCell_not_isIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.retainedCoordinate_inverts_factors_and_retains_discard` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.separableMixedFactorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.separableMixedSource_inverts` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.separableMixedSource_has_factorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.repleteSeparableMixedSource_inverts` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.repleteSeparableMixedSource_has_factorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.repleteSeparableMixedSource_inverts_and_factors` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.separableMixedLift_map_inverse_fst` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.separableMixedIdentity_map₂_discardTwoCell_not_isIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.separableMixedIdentity_inverts_factors_maps_inverse_and_retains_discard` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftSourceEquivalence_hom` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftHomFunctor_zero_zero` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftHomFunctor_zero_one` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftHomFunctor_one_zero` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftHomFunctor_one_one` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftPrelaxFunctor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftPrelaxFunctor_map_forward` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftPrelaxFunctor_map_inverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftPrelaxFunctor_map₂_forward` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftPrelaxFunctor_map₂_inverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapId` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalSourceCompositionComparison_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalSourceCompositionComparison_associativity_inv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalForwardCompositionComparison_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalForwardCompositionComparison_associativity_inv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompTarget_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompTarget_naturality_right` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompTarget_naturality_left` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompSource_naturality_right` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompSource_naturality_left` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompSource_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompTransport_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_iso_right_hom` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_iso_left_hom` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_forward` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_forward_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalInverseRetainedCompositionComparison_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftInverseRetainedMapCompTarget_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftInverseRetainedMapCompSource_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftInverseRetainedMapCompTransport_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_inverseRetained` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_inverseRetained_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompForward` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompForward_naturality_right` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompForward_naturality_left` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompInverseRetained` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompInverseRetained_naturality_right` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompInverseRetained_naturality_left` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompRetainedInverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompRetainedInverse_naturality_right` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompRetainedInverse_naturality_left` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompInverseForward` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompInverseForward_naturality_right` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompInverseForward_naturality_left` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompForwardInverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompForwardInverse_naturality_right` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompForwardInverse_naturality_left` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalEndpointTwoCell` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalEndpointHom_eq_forward` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalEndpointHom_eq_inverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_endpoint` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftEndpointMapComp_naturality_right` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftEndpointMapComp_naturality_left` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_naturality_right` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_naturality_left` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalSourceLeftUnitorFactorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalForwardLeftUnitorFactorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalInverseLeftUnitorFactorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalSourceRightUnitorFactorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalForwardRightUnitorFactorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapIdTail` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalSourceGeneratorRetainedComparison_unit` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalSourceRetainedGeneratorComparison_unit` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftSourceLeftUnitor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftSourceLeftUnitor_afterCompositionComparison` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardSlidingSource_unit` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftInverseSlidingSource_unit` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompForward_leftUnitor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompRetainedInverse_leftUnitor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_forwardIdentity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_inverseLeftIdentity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftLeftUnitor_forward` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftLeftUnitor_inverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftLeftUnitor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalInverseRightUnitorFactorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftSourceRightUnitor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftSourceRightUnitor_afterCompositionComparison` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompForward_rightUnitor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_rightIdentity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRightUnitor_forward` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompInverseRetained_rightUnitor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_inverseRightIdentity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRightUnitor_inverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRightUnitor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.HigherNoninvertibleTwoCell.discardTwoCell_not_isIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/HigherNoninvertibleTwoCell.lean` |
| `Ript.Examples.HigherNoninvertibleTwoCell.homotopy_classes_ne` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/HigherNoninvertibleTwoCell.lean` |
| `Ript.Examples.HigherNoninvertibleTwoCell.locallyDiscrete_map_identifies_discard` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/HigherNoninvertibleTwoCell.lean` |
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
<!-- END GENERATED AXIOM ROWS -->

## 結果の読み方

- `none` は公理に依存しないことを示します。
- `propext` は Lean の命題外延性です。
- `Quot.sound` は商型を使う証明層に由来します。
- `Classical.choice` は主に Mathlib の有限型、圏論、測度、骨格、Yoneda、単体的基盤に由来します。
- プロジェクト独自公理、コンパイラ信頼回避、証明穴はありません。

実行可能な有限コアは、古典選択を必要とする意味論層から分離されています。
`Classical.choice` が表示されても、選択された代表元が実行時データになるとは限りません。

## 更新手順

主要定理を追加・変更した場合は、監査モジュールとルート台帳を更新し、
`./scripts/sync-doc-reference-tables.sh`、続いて `./scripts/quality-gate.sh` を実行してください。
