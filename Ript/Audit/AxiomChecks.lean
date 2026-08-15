import Ript.Examples.BitProcesses
import Ript.Examples.QubitChannel
import Ript.Examples.SimpleCausalModel
import Ript.Examples.SimpleComputation
import Ript.Examples.SimpleThermalModel
import Ript.Examples.StochasticBits
import Ript.Models.Decision.SemanticValue
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
#print axioms Ript.Examples.SimpleThermalModel.thermalFlip_involutive
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
