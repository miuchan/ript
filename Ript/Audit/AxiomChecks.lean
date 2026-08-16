import Ript.Examples.BitProcesses
import Ript.Examples.ClassicalQuantum
import Ript.Examples.ClassicalCopy
import Ript.Examples.ConvexChannels
import Ript.Examples.CostFiltration
import Ript.Examples.HigherModels
import Ript.Examples.QubitChannel
import Ript.Examples.SimpleCausalModel
import Ript.Examples.SimpleComputation
import Ript.Examples.SimpleThermalModel
import Ript.Examples.StochasticBits
import Ript.Examples.UnivalentCompletion
import Ript.Examples.UnivalentPresheaf
import Ript.Examples.UnivalentProcessUniverse
import Ript.Examples.UnivalentSimplicial
import Ript.Models.Decision.SemanticValue
import Ript.Models.Probability.FiniteKL
import Ript.Models.Probability.StochFunctor
import Ript.Models.FiniteStochastic.Kleisli
import Ript.Resource.ParallelBudget
import Ript.Semantics.Completeness
import Ript.Semantics.MonoidalCompleteness
import Ript.Semantics.MonoidalInitiality

/-!
# Kernel assumption checks

This module prints the assumptions used by the current flagship theorems.
Its output is mirrored in `AXIOMS.md` after every audit run.
-/

set_option autoImplicit false

#print axioms Ript.Resource.budgeted_id
#print axioms Ript.Resource.budgeted_comp
#print axioms Ript.Core.CausalProcess.comp
#print axioms Ript.Core.causal_of_deterministic
#print axioms Ript.Models.FiniteFunction.tensor_apply
#print axioms Ript.Models.FiniteFunction.copy_apply
#print axioms Ript.Models.FiniteFunction.discard_apply
#print axioms Ript.Models.FiniteFunction.copy_natural
#print axioms Ript.Models.FiniteFunction.discard_natural
#print axioms Ript.Models.FiniteFunction.copy_coassociative
#print axioms Ript.Models.FiniteFunction.copy_commutative
#print axioms Ript.Models.FiniteFunction.causal
#print axioms Ript.Examples.ClassicalCopy.negate_copy_natural
#print axioms Ript.Examples.ClassicalCopy.negate_causal
#print axioms Ript.Resource.costToFiltration_toCost
#print axioms Ript.Resource.filtrationToCost_toFiltration_of_attained
#print axioms Ript.Resource.filtrationToCost_comp
#print axioms Ript.Resource.filtrationToCost_tensor
#print axioms Ript.Examples.CostFiltration.declaredUnitsFiltration_attained
#print axioms Ript.Examples.CostFiltration.declaredUnitsCost_eq_units
#print axioms Ript.Examples.CostFiltration.reconstructedProcessCost_eq_units
#print axioms Ript.Syntax.Expr.syntaxCost_id
#print axioms Ript.Syntax.Expr.syntaxCost_comp
#print axioms Ript.Semantics.eval_id
#print axioms Ript.Semantics.eval_comp
#print axioms Ript.Semantics.eval_cost_le
#print axioms Ript.Semantics.soundness
#print axioms Ript.Semantics.complete_via_term_model
#print axioms Ript.Semantics.budget_complete_in_free_model
#print axioms Ript.Resource.budgeted_tensor
#print axioms Ript.Semantics.monoidalEval_cost_le
#print axioms Ript.Semantics.monoidal_soundness
#print axioms Ript.Semantics.monoidal_complete_via_term_model
#print axioms Ript.Semantics.monoidal_budget_complete_in_free_model
#print axioms Ript.Semantics.Free.lift_on_generator
#print axioms Ript.Semantics.Free.lift_preserves_cost
#print axioms Ript.Semantics.Free.lift_unique
#print axioms Ript.Models.FiniteStochastic.FinStoch.id_apply
#print axioms Ript.Models.FiniteStochastic.FinStoch.comp_apply
#print axioms Ript.Models.FiniteStochastic.FinStoch.tensor_apply
#print axioms Ript.Models.FiniteStochastic.FinStoch.dirac_comp
#print axioms Ript.Models.FiniteStochastic.FinStoch.dirac_faithful
#print axioms Ript.Models.FiniteStochastic.FinStoch.comp_discard
#print axioms Ript.Models.FiniteStochastic.FinStoch.mix_idem
#print axioms Ript.Models.FiniteStochastic.FinStoch.mix_postcomp
#print axioms Ript.Models.FiniteStochastic.FinStoch.mix_precomp
#print axioms Ript.Models.FiniteStochastic.FinStoch.mix_tensor_left
#print axioms Ript.Examples.ConvexChannels.fairIdentityOrNot_apply
#print axioms Ript.Models.FiniteDistribution.FinDist.pure_bind
#print axioms Ript.Models.FiniteDistribution.FinDist.bind_pure
#print axioms Ript.Models.FiniteDistribution.FinDist.bind_assoc
#print axioms Ript.Models.FiniteStochastic.kleisliToChannel_channelToKleisli
#print axioms Ript.Models.FiniteStochastic.channelToKleisli_kleisliToChannel
#print axioms Ript.Models.FiniteStochastic.kleisliEquivalence
#print axioms Ript.Models.Probability.StochFunctor.rowMeasure_singleton
#print axioms Ript.Models.Probability.StochFunctor.toKernel_comp
#print axioms Ript.Models.Probability.StochFunctor.toStoch_map_dirac
#print axioms Ript.Models.Probability.StochFunctor.toStoch_map_eq_iff
#print axioms Ript.Models.Probability.StochFunctor.productMeasurableSpace_eq_top
#print axioms Ript.Models.Probability.StochFunctor.toStoch_map_tensor
#print axioms Ript.Models.Probability.FiniteKL.distributionMeasure_push
#print axioms Ript.Models.Probability.FiniteKL.distributionMeasure_absolutelyContinuous_iff
#print axioms Ript.Models.Probability.FiniteKL.distributionMeasure_withDensity_densityRatio
#print axioms Ript.Models.Probability.FiniteKL.finiteKL_eq_sum_of_absolutelyContinuous
#print axioms Ript.Models.Probability.FiniteKL.finiteKL_toReal_eq_sum_of_fullSupport
#print axioms Ript.Models.Probability.FiniteKL.finiteKL_eq_zero_iff
#print axioms Ript.Models.Probability.FiniteKL.finiteKL_eq_top_of_support_violation
#print axioms Ript.Models.Probability.FiniteKL.finiteKL_eq_top_iff_support_violation
#print axioms Ript.Models.Probability.FiniteKL.finiteKL_dataProcessing
#print axioms Ript.Core.Simulates.trans
#print axioms Ript.Core.SimulatesWithin.trans
#print axioms Ript.Models.Decision.Blackwell.dominates_tensor
#print axioms Ript.Models.Decision.Blackwell.semanticBayesRisk_mono
#print axioms Ript.Models.Decision.FiniteRisk.finiteBayesRisk_le_randomizedDecisionRisk
#print axioms Ript.Models.Decision.FiniteRisk.finiteBayesRisk_mono
#print axioms Ript.Models.Decision.ResourceBounded.resourceBayesRisk_antitone
#print axioms Ript.Models.Decision.ResourceBounded.resourceBayesRisk_le_of_reduction
#print axioms Ript.Models.Decision.SemanticValue.semanticValue_mono
#print axioms Ript.Models.Decision.SemanticValue.resourceSemanticValue_mono_reduction
#print axioms Ript.Models.Computation.ComputationResource.within_sound
#print axioms Ript.Models.Computation.Total.tensor_comp
#print axioms Ript.Models.Computation.Partial.tensor_comp
#print axioms Ript.Models.Computation.Partial.ofTotal_resource
#print axioms Ript.Examples.SimpleComputation.total_interpreter_cost_sound
#print axioms Ript.Examples.SimpleComputation.partial_budget_checker_sound
#print axioms Ript.Models.Causal.FiniteDAG.acyclic
#print axioms Ript.Models.Causal.FiniteCausalModel.prefixFactorMass_normalized
#print axioms Ript.Models.Causal.FiniteCausalModel.observational_factorization
#print axioms Ript.Models.Causal.FiniteCausalModel.intervene_same
#print axioms Ript.Models.Causal.FiniteCausalModel.intervene_idempotent
#print axioms Ript.Models.Causal.FiniteCausalModel.intervene_comm_of_disjoint
#print axioms Ript.Models.Causal.FiniteCausalModel.intervention_preserves_normalization
#print axioms Ript.Models.Causal.FiniteCausalModel.interventional_factorization
#print axioms Ript.Examples.SimpleCausalModel.intervention_replaces_child_mechanism
#print axioms Ript.Models.FiniteDistribution.FinDist.push_comp
#print axioms Ript.Models.FiniteDistribution.FinDist.push_tensor
#print axioms Ript.Models.Thermal.GibbsPreserving.tensor_id
#print axioms Ript.Models.Thermal.GibbsPreserving.tensor_comp
#print axioms Ript.Models.Thermal.GibbsPreserving.equilibrium_is_free
#print axioms Ript.Models.Thermal.Divergence.athermality_monotone
#print axioms Ript.Models.Thermal.klAthermality_monotone
#print axioms Ript.Examples.SimpleThermalModel.thermalFlip_involutive
#print axioms Ript.Examples.SimpleThermalModel.klAthermality_toReal_eq_sum
#print axioms Ript.Examples.SimpleThermalModel.thermalFlip_klAthermality_invariant
#print axioms Ript.Models.Quantum.KrausRepresentation.map_posSemidef
#print axioms Ript.Models.Quantum.KrausRepresentation.map_trace
#print axioms Ript.Models.Quantum.KrausChannel.map_posSemidef
#print axioms Ript.Models.Quantum.KrausChannel.map_trace
#print axioms Ript.Models.Quantum.KrausChannel.identity_applyDensity
#print axioms Ript.Models.Quantum.KrausChannel.comp_applyDensity
#print axioms Ript.Models.Quantum.KrausChannel.tensor_applyDensity
#print axioms Ript.Models.Quantum.KrausChannel.tensor_identity
#print axioms Ript.Models.Quantum.KrausChannel.tensor_comp
#print axioms Ript.Models.Quantum.KrausChannel.basisBra_complete
#print axioms Ript.Models.Quantum.KrausChannel.eq_discard
#print axioms Ript.Models.Quantum.KrausChannel.comp_discard
#print axioms Ript.Models.Quantum.KrausChannel.identity_toLinearMap
#print axioms Ript.Models.Quantum.amplification_kronecker
#print axioms Ript.Models.Quantum.KrausChannel.amplification_eq_tensor_identity
#print axioms Ript.Models.Quantum.KrausChannel.toLinearMap_isCompletelyPositive
#print axioms Ript.Examples.QubitChannel.bitFlipOperator_complete
#print axioms Ript.Examples.QubitChannel.bitFlip_basisDensity
#print axioms Ript.Examples.QubitChannel.bitFlip_tensor_basisDensity
#print axioms Ript.Examples.QubitChannel.discard_basisDensity
#print axioms Ript.Examples.QubitChannel.bellProjector_posSemidef
#print axioms Ript.Examples.QubitChannel.bellDensity_trace_one
#print axioms Ript.Examples.QubitChannel.bellDensity_cross_term
#print axioms Ript.Examples.QubitChannel.bitFlip_amplification_bell_posSemidef
#print axioms Ript.Models.Quantum.ClassicalEmbedding.transitionOperator_complete
#print axioms Ript.Models.Quantum.ClassicalEmbedding.measurementPreparation_diagonalDensity
#print axioms Ript.Models.Quantum.ClassicalEmbedding.measurementPreparation_comp
#print axioms Ript.Models.Quantum.ClassicalEmbedding.measurementPreparation_tensor
#print axioms Ript.Models.Quantum.ClassicalEmbedding.measurementPreparation_faithful
#print axioms Ript.Models.Quantum.ClassicalEmbedding.dephase_idempotent
#print axioms Ript.Models.Quantum.ClassicalEmbedding.ClassicalQuantum.embedding_map_tensor
#print axioms Ript.Examples.ClassicalQuantum.quantumNoisyNot_false_to_true
#print axioms Ript.Examples.ClassicalQuantum.dephase_bool_offDiagonal
#print axioms Ript.Higher.ModelTransformation.horizontalComp_interchange
#print axioms Ript.Higher.model_pentagon
#print axioms Ript.Higher.model_triangle
#print axioms Ript.Higher.ModelHom.map_cost_eq
#print axioms Ript.Higher.ModelHom.map_comp_cost_le
#print axioms Ript.Higher.ModelHom.map_tensor_cost_le
#print axioms Ript.Higher.CostExactModelEquivalence.hom_map_cost_eq
#print axioms Ript.Univalent.UniverseModel.internalUnivalence
#print axioms Ript.Univalent.UniverseModel.identity_eq_iff_interpret_eq
#print axioms Ript.Univalent.UniverseModel.path_interpretation_sound
#print axioms Ript.Univalent.UniverseModel.InternalPredicate.identity_indistinguishable
#print axioms Ript.Univalent.UniverseModel.functionProcessStructureIdentity
#print axioms Ript.Univalent.ProcessDerives.soundness
#print axioms Ript.Examples.UnivalentProcessUniverse.bitTensorUnit_ne_unitTensorBit
#print axioms Ript.Examples.UnivalentProcessUniverse.swapIdentity_apply
#print axioms Ript.Examples.UnivalentProcessUniverse.reindex_not_sound
#print axioms Ript.Univalent.UniverseModel.ObjectCompletion.ofCode_eq_iff_identity
#print axioms Ript.Univalent.UniverseModel.ObjectCompletion.tensor_assoc
#print axioms Ript.Univalent.UniverseModel.objectCompletionUniversal
#print axioms Ript.Univalent.UniverseModel.internalPredicateCompletionEquiv
#print axioms Ript.Univalent.UniverseModel.objectCompletionToSkeletal_bijective
#print axioms Ript.Univalent.UniverseModel.skeletalCompletionUniversal
#print axioms Ript.Examples.UnivalentCompletion.codeCardinality_equiv
#print axioms Ript.Examples.UnivalentCompletion.completionDoesNotReflectCodeEquality
#print axioms Ript.Univalent.UniverseModel.yonedaEmbeddingFullyFaithful
#print axioms Ript.Univalent.UniverseModel.representableTransformationEquiv_trans
#print axioms Ript.Univalent.UniverseModel.representableNaturalIsoEquiv
#print axioms Ript.Univalent.UniverseModel.representableEquivNaturalIsoEquiv
#print axioms Ript.Univalent.UniverseModel.representableTransformation_isIso
#print axioms Ript.Univalent.UniverseModel.yonedaEnvelopeFactorization
#print axioms Ript.Univalent.UniverseModel.yonedaEnvelopeEquivalence
#print axioms Ript.Univalent.UniverseModel.yonedaEnvelopeUniversal
#print axioms Ript.Examples.UnivalentPresheaf.swapTransformation_component
#print axioms Ript.Examples.UnivalentPresheaf.envelopeIsoDoesNotReflectCodeEquality
#print axioms Ript.Examples.UnivalentPresheaf.swap_preserves_cardinality
#print axioms Ript.Univalent.UniverseModel.interfaceNerveStrictSegal
#print axioms Ript.Univalent.UniverseModel.interfaceNerveSegalEquiv
#print axioms CategoryTheory.Nerve.kanComplex
#print axioms Ript.Univalent.UniverseModel.interfaceNerveKanComplex
#print axioms Ript.Univalent.UniverseModel.interfaceNerveHornFiller_restricts
#print axioms Ript.Univalent.UniverseModel.interfaceNerveQuasicategory
#print axioms Ript.Univalent.UniverseModel.interfaceNerveTwoCoskeletal
#print axioms Ript.Univalent.UniverseModel.interfaceNerveEquivEdgeEquiv
#print axioms Ript.Univalent.UniverseModel.interfaceNerveComposition_composite
#print axioms Ript.Univalent.UniverseModel.interfaceNerveInverseComposition_composite
#print axioms Ript.Univalent.UniverseModel.interfaceNerveHomotopyCategoryIso
#print axioms Ript.Examples.UnivalentSimplicial.swapEdge_decodes_equiv
#print axioms Ript.Examples.UnivalentSimplicial.swapCancellationKanFiller_restricts
#print axioms Ript.Examples.UnivalentSimplicial.swapCancellation_faces
#print axioms Ript.Examples.UnivalentSimplicial.swapCancellation_segal_roundTrip
#print axioms Ript.Examples.UnivalentSimplicial.simplicialEdgeDoesNotReflectCodeEquality
#print axioms Ript.Examples.UnivalentSimplicial.swapEdge_preserves_cardinality
