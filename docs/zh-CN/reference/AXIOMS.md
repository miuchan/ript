# 假设审计

[English](../../en/reference/AXIOMS.md) · [简体中文](AXIOMS.md) ·
[日本語](../../ja/reference/AXIOMS.md) · [Esperanto](../../eo/reference/AXIOMS.md)

本表记录 `lake env lean Ript/Audit/AxiomChecks.lean` 的实际输出。根目录
[`AXIOMS.md`](../../../AXIOMS.md)是验证脚本读取的机器真源；下面的声明名、内核输出和源文件由
`scripts/sync-doc-reference-tables.sh` 同步，不能手工改写。

| 定理或声明 | 内核输出 | 源文件 |
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
| `Ript.Semantics.SequentialFree.lift_on_generator` | `[propext, Quot.sound]` | `Ript/Semantics/SequentialInitiality.lean` |
| `Ript.Semantics.SequentialFree.lift_preserves_cost` | `[propext, Quot.sound]` | `Ript/Semantics/SequentialInitiality.lean` |
| `Ript.Semantics.SequentialFree.lift_unique` | `[propext, Quot.sound]` | `Ript/Semantics/SequentialInitiality.lean` |
| `Ript.Semantics.SequentialFree.strictExtensionEquivPUnit` | `[propext, Quot.sound]` | `Ript/Semantics/SequentialInitiality.lean` |
| `Ript.Semantics.SequentialFree.interpretationEquivResourceMonotoneFunctor` | `[propext, Quot.sound]` | `Ript/Semantics/SequentialInitiality.lean` |
| `Ript.Syntax.Signature.mapCost_comp` | `[propext, Quot.sound]` | `Ript/Syntax/Signature.lean` |
| `Ript.Syntax.Expr.unmapCost_mapCost` | `[propext]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Syntax.Expr.mapCost_unmapCost` | `[propext]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Syntax.Expr.mapCostEquiv` | `[propext]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Syntax.Expr.syntaxCost_mapCost` | `[propext]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Semantics.ResourceChangingInterpretation.equivMappedCostInterpretation` | `none` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Semantics.ResourceChangingInterpretation.eval_cost_le` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Semantics.ResourceChangingInterpretation.mapped_soundness_iff_term_model` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Semantics.ResourceChangingInterpretation.mapped_budget_complete_in_free_model` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Syntax.Derives.mapCost_iff` | `[propext]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Semantics.ResourceChangingInterpretation.soundness` | `[propext]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Semantics.ResourceChangingSequentialFree.lift_on_generator` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingSequentialInitiality.lean` |
| `Ript.Semantics.ResourceChangingSequentialFree.lift_preserves_translated_cost` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingSequentialInitiality.lean` |
| `Ript.Semantics.ResourceChangingSequentialFree.lift_unique` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingSequentialInitiality.lean` |
| `Ript.Semantics.ResourceChangingSequentialFree.strictExtensionEquivPUnit` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingSequentialInitiality.lean` |
| `Ript.Semantics.ResourceChangingSequentialFree.interpretationEquivResourceChangeFunctor` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingSequentialInitiality.lean` |
| `Ript.Examples.CommonBitRealizations.semanticFlip_blackwellEquivalent_perfect` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/CommonBitRealizations.lean` |
| `Ript.Examples.CommonBitRealizations.semanticFlip_guessing_value` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/CommonBitRealizations.lean` |
| `Ript.Examples.CommonBitRealizations.computation_flip_cost` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/CommonBitRealizations.lean` |
| `Ript.Examples.CommonBitRealizations.sixModelFlipAgreement` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/CommonBitRealizations.lean` |
| `Ript.Examples.CompositionalBitRealizations.causal_mechanisms_doubleFlip` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/CompositionalBitRealizations.lean` |
| `Ript.Examples.CompositionalBitRealizations.computation_doubleFlip_cost` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/CompositionalBitRealizations.lean` |
| `Ript.Examples.CompositionalBitRealizations.semantic_doubleFlip_value` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/CompositionalBitRealizations.lean` |
| `Ript.Examples.CompositionalBitRealizations.thermal_protocol_doubleFlip` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/CompositionalBitRealizations.lean` |
| `Ript.Examples.CompositionalBitRealizations.sixModelCompositionAgreement` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/CompositionalBitRealizations.lean` |
| `Ript.Examples.CompositionalBitCompleteness.normalize_derives` | `none` | `Ript/Examples/CompositionalBitCompleteness.lean` |
| `Ript.Examples.CompositionalBitCompleteness.derives_unique` | `none` | `Ript/Examples/CompositionalBitCompleteness.lean` |
| `Ript.Examples.CompositionalBitCompleteness.inImage_iff_eq_canonical` | `[propext]` | `Ript/Examples/CompositionalBitCompleteness.lean` |
| `Ript.Examples.CompositionalBitCompleteness.sixModelSemanticCompleteness` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/CompositionalBitCompleteness.lean` |
| `Ript.Examples.OperationalErasureRealizations.quantum_erases` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/OperationalErasureRealizations.lean` |
| `Ript.Examples.OperationalErasureRealizations.causal_intervention_replaces_mechanism` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/OperationalErasureRealizations.lean` |
| `Ript.Examples.OperationalErasureRealizations.computation_erasure_cost` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/OperationalErasureRealizations.lean` |
| `Ript.Examples.OperationalErasureRealizations.semantic_erasure_value_zero` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/OperationalErasureRealizations.lean` |
| `Ript.Examples.OperationalErasureRealizations.thermal_erases` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/OperationalErasureRealizations.lean` |
| `Ript.Examples.OperationalErasureRealizations.thermal_erasure_landauer_saturation` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/OperationalErasureRealizations.lean` |
| `Ript.Examples.OperationalErasureRealizations.sixModelErasureAgreement` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/OperationalErasureRealizations.lean` |
| `Ript.Examples.DiamondBitTheory.reversiblePath_not_derives_erasurePath` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DiamondBitTheory.lean` |
| `Ript.Examples.DiamondBitTheory.normalize_derives` | `[propext]` | `Ript/Examples/DiamondBitTheory.lean` |
| `Ript.Examples.DiamondBitTheory.derives_iff_normalize_eq` | `[propext, Quot.sound]` | `Ript/Examples/DiamondBitTheory.lean` |
| `Ript.Examples.DiamondBitTheory.inputOutput_inImage_iff` | `[propext, Quot.sound]` | `Ript/Examples/DiamondBitTheory.lean` |
| `Ript.Examples.DiamondBitTheory.semanticallyComplete_of_separates` | `[propext, Quot.sound]` | `Ript/Examples/DiamondBitTheory.lean` |
| `Ript.Examples.DiamondBitRealizations.sixModelPathSeparation` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DiamondBitRealizations.lean` |
| `Ript.Examples.DiamondBitRealizations.sixModelSemanticCompleteness` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DiamondBitRealizations.lean` |
| `Ript.Semantics.SequentialNormalForm.ProcessPath.append_assoc` | `[propext]` | `Ript/Semantics/SequentialNormalForm.lean` |
| `Ript.Semantics.SequentialNormalForm.normalize_toExpr` | `[propext]` | `Ript/Semantics/SequentialNormalForm.lean` |
| `Ript.Semantics.SequentialNormalForm.derives_iff_normalize_eq` | `[propext]` | `Ript/Semantics/SequentialNormalForm.lean` |
| `Ript.Semantics.SequentialNormalForm.termHomEquivPath` | `[propext, Quot.sound]` | `Ript/Semantics/SequentialNormalForm.lean` |
| `Ript.Semantics.SequentialNormalForm.termPathEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Semantics/SequentialNormalForm.lean` |
| `Ript.Semantics.SequentialNormalForm.termToPath_cost_eq` | `[propext, Quot.sound]` | `Ript/Semantics/SequentialNormalForm.lean` |
| `Ript.Semantics.SequentialNormalForm.inImage_iff_exists_path` | `[propext]` | `Ript/Semantics/SequentialNormalForm.lean` |
| `Ript.Semantics.SequentialNormalForm.semanticallyComplete_of_pathFaithful` | `[propext]` | `Ript/Semantics/SequentialNormalForm.lean` |
| `Ript.Examples.DiamondBitRealizations.sixModelGenericPathFaithfulness` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DiamondBitRealizations.lean` |
| `Ript.Examples.DiamondBitRealizations.sixModelGenericSemanticCompleteness` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DiamondBitRealizations.lean` |
| `Ript.Examples.DiamondBitRealizations.sixModelFreeLiftOnGenerators` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DiamondBitRealizations.lean` |
| `Ript.Examples.DiamondBitRealizations.sixModelFreeLiftCostBounds` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DiamondBitRealizations.lean` |
| `Ript.Models.FiniteStochastic.FinStoch.monoidalCategory` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteStochastic/Monoidal.lean` |
| `Ript.Models.FiniteStochastic.FinStoch.symmetricCategory` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteStochastic/Monoidal.lean` |
| `Ript.Models.Computation.Total.monoidalCategory` | `[propext, Quot.sound]` | `Ript/Models/Computation/Total/Monoidal.lean` |
| `Ript.Models.Computation.Total.symmetricCategory` | `[propext, Quot.sound]` | `Ript/Models/Computation/Total/Monoidal.lean` |
| `Ript.Models.Quantum.ClassicalMonoidal.quantumEmbedding_faithful` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/ClassicalMonoidal.lean` |
| `Ript.Models.Quantum.KrausChannel.equivalenceOperator_complete` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Equivalence.lean` |
| `Ript.Models.Quantum.KrausChannel.ofEquiv_comp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Equivalence.lean` |
| `Ript.Models.Quantum.KrausChannel.tensor_ofEquiv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Monoidal.lean` |
| `Ript.Models.Quantum.KrausChannel.monoidalCategory` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Monoidal.lean` |
| `Ript.Models.Quantum.KrausChannel.symmetricCategory` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Monoidal.lean` |
| `Ript.Models.Quantum.KrausOperation.map_posSemidef` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Operation.lean` |
| `Ript.Models.Quantum.KrausOperation.tensor_map_kronecker` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Operation.lean` |
| `Ript.Models.Quantum.KrausOperation.map_real_smul` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Operation.lean` |
| `Ript.Models.Quantum.KrausInstrument.outcomeProbability_normalized` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Instrument.lean` |
| `Ript.Models.Quantum.KrausInstrument.postcompose_outcomeProbability` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Instrument.lean` |
| `Ript.Models.Quantum.KrausInstrument.tensor_outcomeProbability` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Instrument.lean` |
| `Ript.Models.Quantum.KrausInstrument.chosenBranchRepresentation_complete` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Instrument.lean` |
| `Ript.Models.Quantum.KrausInstrument.recordedChannel_map_apply` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Instrument.lean` |
| `Ript.Models.Quantum.KrausInstrument.recordedChannel_injective` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Instrument.lean` |
| `Ript.Models.Quantum.KrausInstrument.recordedChannel_eq_iff` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Instrument.lean` |
| `Ript.Models.Quantum.KrausInstrument.outcomeOperator_complete` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Instrument.lean` |
| `Ript.Models.Quantum.KrausInstrument.extractOperation_map` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Instrument.lean` |
| `Ript.Models.Quantum.KrausInstrument.extractOperations_tracePreserving` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Instrument.lean` |
| `Ript.Models.Quantum.KrausInstrument.extractInstrument_recordedChannel_map_apply` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Instrument.lean` |
| `Ript.Models.Quantum.KrausInstrument.recordedChannel_isClassicallyRecorded` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Instrument.lean` |
| `Ript.Models.Quantum.KrausInstrument.recordedChannel_extractInstrument_eq_iff` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Instrument.lean` |
| `Ript.Models.Quantum.KrausInstrument.isClassicallyRecorded_iff_existsUnique` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Instrument.lean` |
| `Ript.Models.Quantum.KrausInstrument.operationFamily_complete_of_tracePreserving` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Instrument.lean` |
| `Ript.Models.Quantum.KrausInstrument.controlledPostcompose_outcomeProbability` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Instrument.lean` |
| `Ript.Models.Quantum.KrausInstrument.bind_outcomeProbability` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Instrument.lean` |
| `Ript.Models.Quantum.KrausInstrument.relabel_outcomeProbability` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Instrument.lean` |
| `Ript.Models.Quantum.KrausInstrument.bind_assoc` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/Instrument.lean` |
| `Ript.Models.Quantum.InstrumentTree.historyCost_le_budget` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/InstrumentTree.lean` |
| `Ript.Models.Quantum.InstrumentTree.eval_branch_map` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/InstrumentTree.lean` |
| `Ript.Models.Quantum.InstrumentTree.eval_outcomeProbability_normalized` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/InstrumentTree.lean` |
| `Ript.Models.Quantum.InstrumentTree.recordedChannel_history_block` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/InstrumentTree.lean` |
| `Ript.Models.Quantum.InstrumentTree.observationallyEquivalentAlong_iff_branchMap` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/InstrumentTree.lean` |
| `Ript.Models.Quantum.InstrumentTree.observationallyEquivalentAlong_iff_recordedChannel` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/InstrumentTree.lean` |
| `Ript.Models.Quantum.InstrumentTree.eval_ofInstrument_relabel` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/InstrumentTree.lean` |
| `Ript.Models.Quantum.InstrumentTree.isClassicallyRecorded_iff_exists_instrumentTree` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/InstrumentTree.lean` |
| `Ript.Models.Quantum.InstrumentTree.recordedChannel_cost_le_budget` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Quantum/InstrumentTree.lean` |
| `Ript.Examples.QubitInstrument.outcomeProbability_plus` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitInstrument.lean` |
| `Ript.Examples.QubitInstrument.posterior_plus` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitInstrument.lean` |
| `Ript.Examples.QubitInstrument.tensor_outcomeProbability_plus` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitInstrument.lean` |
| `Ript.Examples.QubitInstrument.corrected_branch_plus` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitInstrument.lean` |
| `Ript.Examples.QubitInstrument.corrected_posterior_plus` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitInstrument.lean` |
| `Ript.Examples.QubitInstrument.corrected_total_plus` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitInstrument.lean` |
| `Ript.Examples.QubitInstrument.twoRoundTree_false_probability` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitInstrument.lean` |
| `Ript.Examples.QubitInstrument.twoRoundTree_true_true_probability` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitInstrument.lean` |
| `Ript.Examples.QubitInstrument.twoRoundTree_true_false_probability` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitInstrument.lean` |
| `Ript.Examples.QubitInstrument.twoRoundTree_normalized` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitInstrument.lean` |
| `Ript.Examples.QubitInstrument.recursiveTree_history_card` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitInstrument.lean` |
| `Ript.Examples.QubitInstrument.recursiveTree_budget` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitInstrument.lean` |
| `Ript.Examples.QubitInstrument.recursiveTree_normalized` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitInstrument.lean` |
| `Ript.Examples.QubitInstrument.recursiveTree_history_representation` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/QubitInstrument.lean` |
| `Ript.Examples.InstrumentSyntax.eval_measure_block` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/InstrumentSyntax.lean` |
| `Ript.Examples.InstrumentSyntax.measure_cost_bound` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/InstrumentSyntax.lean` |
| `Ript.Examples.InstrumentSyntax.freeLift_on_measure` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/InstrumentSyntax.lean` |
| `Ript.Examples.InstrumentSyntax.measureCorrect_cost_bound` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/InstrumentSyntax.lean` |
| `Ript.Examples.InstrumentSyntax.freeLift_on_measureCorrect` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/InstrumentSyntax.lean` |
| `Ript.Examples.InstrumentSyntax.measureTree_cost_bound` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/InstrumentSyntax.lean` |
| `Ript.Examples.InstrumentSyntax.freeLift_on_measureTree` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/InstrumentSyntax.lean` |
| `Ript.Models.Computation.Randomized.tensor_comp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Computation/Randomized.lean` |
| `Ript.Models.Computation.Randomized.monoidalCategory` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Computation/Randomized/Monoidal.lean` |
| `Ript.Models.Computation.Randomized.symmetricCategory` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Computation/Randomized/Monoidal.lean` |
| `Ript.Models.Computation.Randomized.withinBudget_sound` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Computation/Randomized.lean` |
| `Ript.Examples.NoisyBitRealizations.quantumNoiseOperator_complete` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/NoisyBitRealizations.lean` |
| `Ript.Examples.NoisyBitRealizations.randomUnitary_ne_measurementPreparation_on_plus` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/NoisyBitRealizations.lean` |
| `Ript.Examples.NoisyBitRealizations.computation_parallel_noise_cost` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/NoisyBitRealizations.lean` |
| `Ript.Examples.NoisyBitRealizations.semanticNoise_quarter_risk` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/NoisyBitRealizations.lean` |
| `Ript.Examples.NoisyBitRealizations.semanticNoise_quarter_value` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/NoisyBitRealizations.lean` |
| `Ript.Examples.NoisyBitRealizations.sixModelNoiseAgreement` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/NoisyBitRealizations.lean` |
| `Ript.Examples.NoisyBitRealizations.sixModelNoiseFreeLiftOnGenerator` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/NoisyBitRealizations.lean` |
| `Ript.Syntax.Branching.Tree.historyCost_le_budget` | `[propext]` | `Ript/Syntax/Branching.lean` |
| `Ript.Syntax.Branching.Tree.historyProbability_normalized` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/Branching.lean` |
| `Ript.Syntax.Branching.NormalForm.toFinStoch_injective` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/Branching.lean` |
| `Ript.Syntax.Branching.Tree.run_comp_dirac_of_decode` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/Branching.lean` |
| `Ript.Syntax.Branching.Tree.observationalCompleteness` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/Branching.lean` |
| `Ript.Examples.AdaptiveNoiseRealizations.probabilityProtocol_representation` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/AdaptiveNoiseRealizations.lean` |
| `Ript.Examples.AdaptiveNoiseRealizations.probabilityProtocol_completeness` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/AdaptiveNoiseRealizations.lean` |
| `Ript.Examples.AdaptiveNoiseRealizations.randomFlipOperator_complete` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/AdaptiveNoiseRealizations.lean` |
| `Ript.Examples.AdaptiveNoiseRealizations.quantumProtocol_basis_block` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/AdaptiveNoiseRealizations.lean` |
| `Ript.Examples.AdaptiveNoiseRealizations.quantumProtocol_ne_measurementPreparation` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/AdaptiveNoiseRealizations.lean` |
| `Ript.Examples.AdaptiveNoiseRealizations.causal_joint_representation` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/AdaptiveNoiseRealizations.lean` |
| `Ript.Examples.AdaptiveNoiseRealizations.semanticProtocol_value` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/AdaptiveNoiseRealizations.lean` |
| `Ript.Examples.AdaptiveNoiseRealizations.adaptiveThermalOutput_equilibrium` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/AdaptiveNoiseRealizations.lean` |
| `Ript.Examples.AdaptiveNoiseRealizations.adaptiveProtocol_run_ne_fixedQuarter` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/AdaptiveNoiseRealizations.lean` |
| `Ript.Examples.AdaptiveNoiseRealizations.sixModelAdaptiveRepresentation` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/AdaptiveNoiseRealizations.lean` |
| `Ript.Syntax.DependentBranching.Tree.historyLength_le_height` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching.lean` |
| `Ript.Syntax.DependentBranching.Tree.historyCost_le_budget` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching.lean` |
| `Ript.Syntax.DependentBranching.Tree.historyProbability_normalized` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching.lean` |
| `Ript.Syntax.DependentBranching.NormalForm.reindexHistory` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching.lean` |
| `Ript.Syntax.DependentBranching.NormalForm.toFinStoch_injective` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching.lean` |
| `Ript.Syntax.DependentBranching.Tree.observationalCompletenessAlong` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching.lean` |
| `Ript.Syntax.DependentBranching.BinaryEmbedding.historyCost_tree` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching.lean` |
| `Ript.Syntax.DependentBranching.BinaryEmbedding.run_tree_apply` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching.lean` |
| `Ript.Examples.DependentBranching.fairTree_representation` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Examples.DependentBranching.fair_normalForm_ne_biased` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Examples.DependentBranching.fair_run_ne_biased_reindexed` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Syntax.DependentBranching.Free.fold_treeAlgebra` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Free.lean` |
| `Ript.Syntax.DependentBranching.Free.treeAlgebraIsInitial` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Free.lean` |
| `Ript.Syntax.DependentBranching.Free.homEquivPUnit` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Free.lean` |
| `Ript.Syntax.DependentBranching.Free.Derives.sound` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Free.lean` |
| `Ript.Syntax.DependentBranching.Free.Derives.complete_via_treeAlgebra` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Free.lean` |
| `Ript.Syntax.DependentBranching.Free.Derives.semanticCompleteness` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Free.lean` |
| `Ript.Syntax.DependentBranching.Free.graft_assoc` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Free.lean` |
| `Ript.Syntax.DependentBranching.Free.fold_graft` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Free.lean` |
| `Ript.Syntax.DependentBranching.Free.fold_height` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Free.lean` |
| `Ript.Syntax.DependentBranching.Free.fold_budget` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Free.lean` |
| `Ript.Syntax.DependentBranching.Free.height_graft_le` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Free.lean` |
| `Ript.Syntax.DependentBranching.Free.budget_graft_le` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Free.lean` |
| `Ript.Examples.DependentBranching.initial_leafCount` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Examples.DependentBranching.graft_associativity_derives` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Examples.DependentBranching.heterogeneous_semanticCompleteness` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Examples.DependentBranching.fairTree_graft_budget` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Syntax.DependentBranching.Free.Cartesian.isTerminalUnit` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Monoidal.lean` |
| `Ript.Syntax.DependentBranching.Free.Cartesian.binaryProductLimit` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Monoidal.lean` |
| `Ript.Syntax.DependentBranching.Free.cartesianMonoidalCategory` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Monoidal.lean` |
| `Ript.Syntax.DependentBranching.Free.braidedCategory` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Monoidal.lean` |
| `Ript.Syntax.DependentBranching.Free.copyDiscardCategory` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Monoidal.lean` |
| `Ript.Syntax.DependentBranching.Free.associator_hom_toFun` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Monoidal.lean` |
| `Ript.Syntax.DependentBranching.Free.braiding_hom_toFun` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Monoidal.lean` |
| `Ript.Syntax.DependentBranching.Free.fold_tensor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Monoidal.lean` |
| `Ript.Syntax.DependentBranching.Free.fold_tensor_eq_iff` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Monoidal.lean` |
| `Ript.Syntax.DependentBranching.Free.foldHom_tensor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Monoidal.lean` |
| `Ript.Syntax.DependentBranching.Free.tree_tensor_reflects_equality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Monoidal.lean` |
| `Ript.Syntax.DependentBranching.Free.jointSemanticCompleteness` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Monoidal.lean` |
| `Ript.Examples.DependentBranching.parallel_leafCount_budget` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Examples.DependentBranching.parallel_interpretation_braiding` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Examples.DependentBranching.heterogeneous_jointSemanticCompleteness` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Syntax.DependentBranching.ParallelProtocol.historyCost_le_budget` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Parallel.lean` |
| `Ript.Syntax.DependentBranching.ParallelProtocol.historyProbability_normalized` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Parallel.lean` |
| `Ript.Syntax.DependentBranching.ParallelProtocol.run_factorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Parallel.lean` |
| `Ript.Syntax.DependentBranching.ParallelProtocol.observationalCompletenessAlong` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Parallel.lean` |
| `Ript.Syntax.DependentBranching.ParallelProtocol.swap_historyCost` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Parallel.lean` |
| `Ript.Syntax.DependentBranching.ParallelProtocol.swap_historyProbability` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Parallel.lean` |
| `Ript.Syntax.DependentBranching.ParallelProtocol.graft_assoc` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Parallel.lean` |
| `Ript.Syntax.DependentBranching.ParallelProtocol.tensor_graft_interchange` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Parallel.lean` |
| `Ript.Syntax.DependentBranching.ParallelProtocol.budget_graft_le` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Parallel.lean` |
| `Ript.Syntax.DependentBranching.ParallelProtocol.height_graft_le` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Parallel.lean` |
| `Ript.Examples.DependentBranching.fairBiasedParallel_run_factorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Examples.DependentBranching.fairBiasedParallel_interchange` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Examples.DependentBranching.fairBiasedParallel_graft_budget` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Examples.DependentBranching.fairFair_run_ne_fairBiased` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Syntax.DependentBranching.LaneProtocol.historyCost_le_budget` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Nary.lean` |
| `Ript.Syntax.DependentBranching.LaneProtocol.historyProbability_normalized` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Nary.lean` |
| `Ript.Syntax.DependentBranching.LaneProtocol.run_factorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Nary.lean` |
| `Ript.Syntax.DependentBranching.LaneProtocol.observationalCompletenessAlong` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Nary.lean` |
| `Ript.Syntax.DependentBranching.LaneProtocol.reindex_budget` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Nary.lean` |
| `Ript.Syntax.DependentBranching.LaneProtocol.reindex_historyProbability` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Nary.lean` |
| `Ript.Syntax.DependentBranching.LaneProtocol.reindex_finalState` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Nary.lean` |
| `Ript.Syntax.DependentBranching.LaneProtocol.reindex_normalForm` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Nary.lean` |
| `Ript.Semantics.DependentBranchingRealization.quantum_diagonalDensity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Semantics/DependentBranchingRealization.lean` |
| `Ript.Semantics.DependentBranchingRealization.causal_joint_representation` | `[propext, Classical.choice, Quot.sound]` | `Ript/Semantics/DependentBranchingRealization.lean` |
| `Ript.Semantics.DependentBranchingRealization.historyCost_le_treeResource_steps` | `[propext, Classical.choice, Quot.sound]` | `Ript/Semantics/DependentBranchingRealization.lean` |
| `Ript.Semantics.DependentBranchingRealization.historyLength_le_treeResource_storage` | `[propext, Classical.choice, Quot.sound]` | `Ript/Semantics/DependentBranchingRealization.lean` |
| `Ript.Semantics.DependentBranchingRealization.quantum_eq_iff` | `[propext, Classical.choice, Quot.sound]` | `Ript/Semantics/DependentBranchingRealization.lean` |
| `Ript.Semantics.DependentBranchingRealization.computation_eq_iff` | `[propext, Classical.choice, Quot.sound]` | `Ript/Semantics/DependentBranchingRealization.lean` |
| `Ript.Semantics.DependentBranchingRealization.semanticRealization_eq_iff` | `[propext, Classical.choice, Quot.sound]` | `Ript/Semantics/DependentBranchingRealization.lean` |
| `Ript.Semantics.DependentBranchingRealization.thermal_channel_eq_iff` | `[propext, Classical.choice, Quot.sound]` | `Ript/Semantics/DependentBranchingRealization.lean` |
| `Ript.Semantics.DependentBranchingRealization.isThermalTargetCompatible_iff_target_eq_induced` | `[propext, Classical.choice, Quot.sound]` | `Ript/Semantics/DependentBranchingRealization.lean` |
| `Ript.Semantics.DependentBranchingRealization.isThermalTargetCompatible_iff_existsUnique` | `[propext, Classical.choice, Quot.sound]` | `Ript/Semantics/DependentBranchingRealization.lean` |
| `Ript.Semantics.DependentBranchingRealization.thermalInto_eq_iff` | `[propext, Classical.choice, Quot.sound]` | `Ript/Semantics/DependentBranchingRealization.lean` |
| `Ript.Semantics.DependentBranchingRealization.causallyEqual_iff` | `[propext, Classical.choice, Quot.sound]` | `Ript/Semantics/DependentBranchingRealization.lean` |
| `Ript.Semantics.DependentBranchingRealization.allModelsAgree_iff` | `[propext, Classical.choice, Quot.sound]` | `Ript/Semantics/DependentBranchingRealization.lean` |
| `Ript.Semantics.DependentBranchingRealization.sixModelRepresentation` | `[propext, Classical.choice, Quot.sound]` | `Ript/Semantics/DependentBranchingRealization.lean` |
| `Ript.Semantics.DependentBranchingRealization.tree_allModelsAgree_iff_run` | `[propext, Classical.choice, Quot.sound]` | `Ript/Semantics/DependentBranchingRealization.lean` |
| `Ript.Syntax.DependentBranching.LaneProtocol.graft_assoc` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Nary.lean` |
| `Ript.Syntax.DependentBranching.LaneProtocol.tensor_graft_interchange` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Nary.lean` |
| `Ript.Syntax.DependentBranching.LaneProtocol.budget_graft_le` | `[propext, Classical.choice, Quot.sound]` | `Ript/Syntax/DependentBranching/Nary.lean` |
| `Ript.Examples.DependentBranching.tripleProtocol_short_probability` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Examples.DependentBranching.tripleProtocol_run_factorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Examples.DependentBranching.tripleProtocol_interchange` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Examples.DependentBranching.tripleProtocol_graft_budget` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Examples.DependentBranching.tripleProtocol_swap_normalForm` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Examples.DependentBranching.fairTree_sixModelRepresentation` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Examples.DependentBranching.fair_biased_not_allModelsAgree` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Examples.DependentBranching.tripleAllFair_run_ne_triple` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/DependentBranching.lean` |
| `Ript.Models.Thermal.GibbsPreserving.monoidalCategory` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Monoidal.lean` |
| `Ript.Models.Thermal.GibbsPreserving.symmetricCategory` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/Monoidal.lean` |
| `Ript.Examples.ParallelBitRealizations.computation_parallel_cost` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ParallelBitRealizations.lean` |
| `Ript.Examples.ParallelBitRealizations.quantum_parallel_product` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ParallelBitRealizations.lean` |
| `Ript.Examples.ParallelBitRealizations.quantum_parallel_basis` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ParallelBitRealizations.lean` |
| `Ript.Examples.ParallelBitRealizations.sixModelParallelAgreement` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ParallelBitRealizations.lean` |
| `Ript.Examples.ParallelBitRealizations.sixModelMonoidalFreeLiftOnGenerator` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ParallelBitRealizations.lean` |
| `Ript.Examples.ParallelBitHigherModels.sixModelResourceMaps` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ParallelBitHigherModels.lean` |
| `Ript.Examples.ParallelBitHigherModels.sixModelOneCellsOnGenerator` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ParallelBitHigherModels.lean` |
| `Ript.Examples.ParallelBitHigherModels.computationOneCell_parallel_cost` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/ParallelBitHigherModels.lean` |
| `Ript.Syntax.MonoidalSignature.mapCost_comp` | `[propext, Quot.sound]` | `Ript/Syntax/MonoidalSignature.lean` |
| `Ript.Syntax.MonoidalExpr.unmapCost_mapCost` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Syntax.MonoidalExpr.mapCost_unmapCost` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Syntax.MonoidalExpr.mapCostEquiv` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Syntax.MonoidalExpr.syntaxCost_mapCost` | `[propext]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Syntax.MonoidalDerives.mapCost_iff` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Semantics.ResourceChangingMonoidalInterpretation.equivMappedCostInterpretation` | `none` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Semantics.ResourceChangingMonoidalInterpretation.eval_cost_le` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Semantics.ResourceChangingMonoidalInterpretation.soundness` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Semantics.ResourceChangingMonoidalInterpretation.mapped_soundness_iff_term_model` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Semantics.ResourceChangingMonoidalInterpretation.mapped_budget_complete_in_free_model` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingInterpretation.lean` |
| `Ript.Semantics.ResourceChangingMonoidalFree.lift_on_generator` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingMonoidalInitiality.lean` |
| `Ript.Semantics.ResourceChangingMonoidalFree.lift_preserves_translated_cost` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingMonoidalInitiality.lean` |
| `Ript.Semantics.ResourceChangingMonoidalFree.lift_unique` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingMonoidalInitiality.lean` |
| `Ript.Semantics.ResourceChangingMonoidalFree.strictExtensionEquivPUnit` | `[propext, Quot.sound]` | `Ript/Semantics/ResourceChangingMonoidalInitiality.lean` |
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
| `Ript.Models.FiniteDistribution.FinDist.pure_injective` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteDistribution.lean` |
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
| `Ript.Models.Decision.SemanticValue.dominates_noInformation` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/SemanticValue.lean` |
| `Ript.Models.Decision.SemanticValue.universalSemanticOrder_iff_finiteDecisionOrder` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/SemanticValue.lean` |
| `Ript.Models.Decision.SemanticValue.blackwellDominates_iff_universalSemanticOrder` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/SemanticValue.lean` |
| `Ript.Models.Decision.SemanticValue.finiteBayesRisk_eq_of_noInformationSemanticValue_eq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/SemanticValue.lean` |
| `Ript.Models.Decision.SemanticValue.blackwellEquivalent_iff_universalSemanticValueProfileEqual` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Decision/SemanticValue.lean` |
| `Ript.Examples.SimpleDecision.perfect_not_blackwellEquivalent_uninformative` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleDecision.lean` |
| `Ript.Examples.SimpleDecision.singleSemanticValue_not_complete` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleDecision.lean` |
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
| `Ript.Higher.TotalModelSimplicial.objectNerveEdgeEquiv_equivalenceEdge` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSimplicial.lean` |
| `Ript.Higher.TotalModelSimplicial.objectNerveEdgeToEquivalence_hom` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSimplicial.lean` |
| `Ript.Higher.TotalModelSimplicial.objectNerveEquivalenceEdge_edgeToEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSimplicial.lean` |
| `Ript.Higher.TotalModelSimplicial.InternalEquivalence.toEdge_ofEdge` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSimplicial.lean` |
| `Ript.Higher.TotalModelSimplicial.InternalEquivalence.ofEdge_toEdge` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSimplicial.lean` |
| `Ript.Higher.TotalModelSimplicial.InternalEquivalence.edgeEquiv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSimplicial.lean` |
| `Ript.Higher.TotalModelSimplicial.objectNerveStrictSegal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSimplicial.lean` |
| `Ript.Higher.TotalModelSimplicial.mappingNerveEdgeEquiv_transformationEdge` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSimplicial.lean` |
| `Ript.Higher.TotalModelSimplicial.mappingNerveVerticalComposition_composite` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSimplicial.lean` |
| `Ript.Higher.TotalModelSimplicial.mappingNerveStrictSegal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSimplicial.lean` |
| `Ript.Higher.TotalModelSimplicial.Triangle.composition_cell` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSimplicial.lean` |
| `Ript.Higher.TotalModelSimplicial.Tetrahedron.existsUnique_over_iff_coherent` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSimplicial.lean` |
| `Ript.Higher.TotalModelSimplicial.Tetrahedron.composition_cell023` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSimplicial.lean` |
| `Ript.Higher.TotalModelSemiSimplicial.Simplex.pullback_refl` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSemiSimplicial.lean` |
| `Ript.Higher.TotalModelSemiSimplicial.Simplex.pullback_trans` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSemiSimplicial.lean` |
| `Ript.Higher.TotalModelSemiSimplicial.nerve` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSemiSimplicial.lean` |
| `Ript.Higher.TotalModelSemiSimplicial.nerve_map_apply` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSemiSimplicial.lean` |
| `Ript.Higher.TotalModelSemiSimplicial.Simplex.toTriangle_cell` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSemiSimplicial.lean` |
| `Ript.Higher.TotalModelSemiSimplicial.Simplex.toTetrahedron_cell023` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSemiSimplicial.lean` |
| `Ript.Higher.TotalModelSemiSimplicial.Simplex.extensionality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSemiSimplicial.lean` |
| `Ript.Higher.TotalModelDuskinNerve.ordinalLaxFunctor_id` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinNerve.lean` |
| `Ript.Higher.TotalModelDuskinNerve.ordinalLaxFunctor_comp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinNerve.lean` |
| `Ript.Higher.TotalModelDuskinNerve.Simplex.pullback_trans` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinNerve.lean` |
| `Ript.Higher.TotalModelDuskinNerve.nerve` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinNerve.lean` |
| `Ript.Higher.TotalModelDuskinNerve.Simplex.pullback_comparison` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinNerve.lean` |
| `Ript.Higher.TotalModelDuskinNerve.Simplex.zeroDegeneracy_edge` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinNerve.lean` |
| `Ript.Higher.TotalModelDuskinNerve.Simplex.tetrahedral_coherence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinNerve.lean` |
| `Ript.Higher.TotalModelDuskinNerve.Simplex.toSemiSimplex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinNerve.lean` |
| `Ript.Higher.TotalModelDuskinNerve.Simplex.toSemiSimplex_pullback` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinNerve.lean` |
| `Ript.Higher.TotalModelDuskinNerve.forgetToSemi` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinNerve.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.Ordinal.toFin` | `[propext]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.Ordinal.fromFin` | `[propext]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.Ordinal.equivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.normalToFiniteOrdinal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.finiteToNormalOrdinalCore` | `[propext]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.finiteToNormalOrdinal` | `[propext]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.CoordinateSimplex.mapHom_refl` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.CoordinateSimplex.mapComp_refl_left` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.CoordinateSimplex.mapComp_strict_refl` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.CoordinateSimplex.mapComp_strict_strict` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.CoordinateSimplex.strictTetrahedralCoherence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.CoordinateSimplex.identityRightUnitEquation` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.CoordinateSimplex.constructorTetrahedralCoherence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.CoordinateSimplex.sourceLeftUnitEquation` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.CoordinateSimplex.sourceRightUnitEquation` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.CoordinateSimplex.sourceTetrahedralCoherence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.CoordinateSimplex.toCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.CoordinateSimplex.toNormalOrdinalSimplex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.CoordinateSimplex.fromNormalOrdinalSimplex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.CoordinateSimplex.fromNormalOrdinalSimplex_toNormalOrdinalSimplex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.CoordinateSimplex.toNativeSimplex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.CoordinateSimplex.toNativeSimplex_comparison` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.CoordinateSimplex.toNativeSimplex_toSemiSimplex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.CoordinateSimplex.toSemiSimplex_toNativeSimplex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.CoordinateSimplex.nativeCoordinateEquiv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.CoordinateSimplex.coordinateNerve` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.CoordinateSimplex.coordinateNerveIsoNative` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.RezkCore.diagram` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.diagramCatMap` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.diagramMap` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.diagramMap_arrowVertex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.actualEquivalenceObjectOfIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.actualEquivalenceSpaceInclusion_vertexOfIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeOneMatchingFunctor_obj_fst_obj` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeOneMatchingFunctor_obj_snd_obj` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeOneMatchingFunctor_map_fst_app` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeOneMatchingFunctor_map_snd_app` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeOneMatchingFunctorIsIsofibration` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeOneMatchingNerveMap_fibration` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeOneMatchingNerveMap_comp_fst` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeOneMatchingNerveMap_comp_snd` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeOneMatchingCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeZeroTypeProductIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeZeroNerveProductIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeZeroNerveProductIso_hom_fst` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeZeroNerveProductIso_hom_snd` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeOneMatchingMap` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeOneMatchingMap_fibration` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeOneMatchingMap_eq_faces` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeOneReedyCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeTwoBoundaryMap_fibration` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeTwoAbstractMatchingMap_eq_limitLift` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeTwoBoundaryToAbstractMatching_fac` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeTwoMatchingMap_factorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeTwoBoundaryToAbstractMatching_comp_faceProjection` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeTwoBoundaryToAbstractMatching_comp_vertexProjection` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeTwoAbstractFaceProjection_comp_incidence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeTwoMatchingCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.abstractMatchingMap_eq_limitLift` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.abstractMatchingMap_fac` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.abstractMatchingBoundaryMap` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.abstractMatchingElement_ext` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.abstractMatchingBoundaryMap_injective` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.abstractMatchingBoundaryMap_matchingMap` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.abstractMatchingMap_app_injective` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.abstractMatchingMap_app_surjective_high` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.abstractMatchingMap_app_bijective_high` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.abstractMatchingMapHighIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.higherMatchingCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.triangleBoundaryEquivalenceStringEquiv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.equivalenceStringToCoreString_coreStringToEquivalenceString` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.coreStringToEquivalenceString_equivalenceStringToCoreString` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeTwoAbstractMatchingBoundaryMap` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeTwoBoundaryComparisonInverseApp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeTwoMatchingElement_ext` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeTwoAbstractMatchingBoundaryMap_injective` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeTwoAbstractMatchingBoundaryMap_comparison` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeTwoBoundaryComparisonInverseApp_comparison` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeTwoBoundaryToAbstractMatching_inverseApp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeTwoBoundaryToAbstractMatching_app_bijective` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeTwoBoundaryAbstractMatchingIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.degreeTwoReedyCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.fromEquivalenceStringDiagram_toEquivalenceStringDiagram` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.toEquivalenceStringDiagram_fromEquivalenceStringDiagram` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.horizontalSimplexEquiv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.horizontalRowIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.horizontalStrictSegal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.outerSegalEquiv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.outerSegalEquiv_apply` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.equivalenceStringCoreEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.objectSpaceWitness` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.completenessWitness` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.selectedIdentityFunctor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.completenessFunctorIsoSelected` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.selectedCompletenessEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.selectedCompletenessWitness` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.equivalenceSpaceInclusion` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.selectedActualInclusionFunctor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.selectedToActualEquivalenceWitness` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.selectedToActualEquivalenceMap_comp_inclusion` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.actualCompletenessWitness` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.actualCompletenessHomotopyEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.constantToDegeneracyIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.selectedCompletenessFunctorIsoDegeneracy` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.completenessFunctorIsoDegeneracy` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.completenessFactorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.completenessNerveHomotopy` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.actualCompletenessNerveHomotopy` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.nerveCompletenessFactorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.completenessHomotopyCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.actualCompletenessCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.RezkCore.segalCompletenessCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.objectCoreEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.completenessWitness` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.equivalenceSpaceInclusion` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.selectedToActualEquivalenceWitness` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.actualCompletenessWitness` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.actualCompletenessHomotopyEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.completenessFunctorIsoDegeneracy` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.completenessFactorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.completenessNerveHomotopy` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.actualCompletenessNerveHomotopy` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.nerveCompletenessFactorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.completenessCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.completenessHomotopyCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.actualCompletenessCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.degreeOneMatchingCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.degreeOneReedyCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.degreeTwoMatchingCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.degreeTwoReedyCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.higherMatchingCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.rezkObjectVertex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.higherCompleteSegalCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.horizontalRowIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.horizontalStrictSegal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.outerSegalEquiv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.outerSegalEquiv_apply` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelCompleteSegal.segalCompletenessCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelCompleteSegal.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.DegenerateCoherence.allIdentity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.DegenerateCoherence.leftLeft` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.DegenerateCoherence.leftRight` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.DegenerateCoherence.leftNaturality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.DegenerateCoherence.rightRight` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.DegenerateCoherence.middleIdentity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelDuskinRepresentation.DegenerateCoherence.rightNaturality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelDuskinRepresentation.lean` |
| `Ript.Higher.TotalModelSimplicial.horizontalCompositionFunctor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSimplicial.lean` |
| `Ript.Higher.TotalModelSimplicial.horizontalCompositionNerveMap_transformation` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSimplicial.lean` |
| `Ript.Higher.TotalModelSimplicial.horizontalAssociatorNatIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSimplicial.lean` |
| `Ript.Higher.TotalModelSimplicial.horizontalAssociatorNerveHomotopy` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSimplicial.lean` |
| `Ript.Higher.TotalModelSimplicial.horizontalLeftUnitorNatIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSimplicial.lean` |
| `Ript.Higher.TotalModelSimplicial.horizontalLeftUnitorNerveHomotopy` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSimplicial.lean` |
| `Ript.Higher.TotalModelSimplicial.horizontalRightUnitorNatIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSimplicial.lean` |
| `Ript.Higher.TotalModelSimplicial.horizontalRightUnitorNerveHomotopy` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/TotalModelSimplicial.lean` |
| `Ript.Examples.HigherNoninvertibleTwoCell.totalDiscardMappingEdge_decodes` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/HigherNoninvertibleTwoCell.lean` |
| `Ript.Examples.HigherNoninvertibleTwoCell.totalDiscardTwoCell_not_isIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/HigherNoninvertibleTwoCell.lean` |
| `Ript.Examples.HigherNoninvertibleTwoCell.totalDiscardMappingEdge_decodes_noninvertible` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/HigherNoninvertibleTwoCell.lean` |
| `Ript.Examples.TotalResourceModels.projectToSteps_cost_exact` | `[propext, Quot.sound]` | `Ript/Examples/TotalResourceModels.lean` |
| `Ript.Examples.TotalResourceModels.stepBudgetedNot_cost` | `[propext, Quot.sound]` | `Ript/Examples/TotalResourceModels.lean` |
| `Ript.Models.Computation.ComputationResource.stepsHom_of` | `[propext, Quot.sound]` | `Ript/Models/Computation/Resource.lean` |
| `Ript.Examples.ResourceReindexing.countedNot_twice_step_cost` | `[propext, Quot.sound]` | `Ript/Examples/ResourceReindexing.lean` |
| `Ript.Models.Causal.FiniteDAG.acyclic` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/DAG.lean` |
| `Ript.Models.Causal.FiniteCausalModel.prefixFactorMass_normalized` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/Model.lean` |
| `Ript.Models.Causal.FiniteCausalModel.observational_factorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/Model.lean` |
| `Ript.Models.Causal.FiniteCausalModel.intervene_same` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/Intervention.lean` |
| `Ript.Models.Causal.FiniteCausalModel.intervene_idempotent` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/Intervention.lean` |
| `Ript.Models.Causal.Intervention.thenDo_assoc` | `[propext, Quot.sound]` | `Ript/Models/Causal/Intervention.lean` |
| `Ript.Models.Causal.FiniteCausalModel.interventionSemantics_injective` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/Intervention.lean` |
| `Ript.Models.Causal.FiniteCausalModel.intervene_thenDo` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/Intervention.lean` |
| `Ript.Models.Causal.InterventionProgram.run_eq_intervene_normalize` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/Intervention.lean` |
| `Ript.Models.Causal.InterventionProgram.semanticallyEquivalent_iff_normalize_eq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/Intervention.lean` |
| `Ript.Models.Causal.FiniteCausalModel.intervene_comm_of_disjoint` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/Intervention.lean` |
| `Ript.Models.Causal.FiniteCausalModel.intervention_preserves_normalization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/Intervention.lean` |
| `Ript.Models.Causal.FiniteCausalModel.interventional_factorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/FinStoch.lean` |
| `Ript.Models.Causal.InterventionProgram.programChannel_eq_interventionalChannel_normalize` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/FinStoch.lean` |
| `Ript.Examples.SimpleCausalModel.intervention_replaces_child_mechanism` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleCausalModel.lean` |
| `Ript.Models.Causal.Mechanism.entrywiseEqual_iff_eq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/SoftIntervention.lean` |
| `Ript.Models.Causal.SoftIntervention.thenReplace_assoc` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/SoftIntervention.lean` |
| `Ript.Models.Causal.SoftIntervention.reduceAgainst_reduced` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/SoftIntervention.lean` |
| `Ript.Models.Causal.SoftIntervention.reduceAgainst_eq_self_iff` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/SoftIntervention.lean` |
| `Ript.Models.Causal.SoftIntervention.reduceAgainst_idempotent` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/SoftIntervention.lean` |
| `Ript.Models.Causal.FiniteCausalModel.softIntervene_ofHard` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/SoftIntervention.lean` |
| `Ript.Models.Causal.FiniteCausalModel.softIntervene_thenReplace` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/SoftIntervention.lean` |
| `Ript.Models.Causal.FiniteCausalModel.softIntervene_reduceAgainst` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/SoftIntervention.lean` |
| `Ript.Models.Causal.FiniteCausalModel.softInterventionSemantics_injective_of_reduced` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/SoftIntervention.lean` |
| `Ript.Models.Causal.SoftInterventionProgram.run_cons` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/SoftIntervention.lean` |
| `Ript.Models.Causal.SoftInterventionProgram.run_eq_softIntervene_normalize` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/SoftIntervention.lean` |
| `Ript.Models.Causal.SoftInterventionProgram.semanticallyEquivalent_iff_normalize_eq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/SoftIntervention.lean` |
| `Ript.Models.Causal.FiniteCausalModel.softInterventional_factorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/FinStoch.lean` |
| `Ript.Models.Causal.FiniteCausalModel.softInterventionalChannel_ofHard` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/FinStoch.lean` |
| `Ript.Models.Causal.SoftInterventionProgram.programChannel_eq_softInterventionalChannel_normalize` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Causal/FinStoch.lean` |
| `Ript.Examples.SimpleCausalModel.stochastic_intervention_independent_fair` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleCausalModel.lean` |
| `Ript.Examples.SimpleCausalModel.randomizeThenRestore_normalize` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleCausalModel.lean` |
| `Ript.Examples.SimpleCausalModel.randomizeThenRestore_run` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleCausalModel.lean` |
| `Ript.Examples.SimpleCausalModel.randomizeThenRestore_semantically_empty` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/SimpleCausalModel.lean` |
| `Ript.Models.FiniteDistribution.FinDist.push_comp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteDistribution.lean` |
| `Ript.Models.FiniteDistribution.FinDist.push_tensor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/FiniteDistribution.lean` |
| `Ript.Models.Thermal.GibbsPreserving.channel_injective` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/GibbsPreserving.lean` |
| `Ript.Models.Thermal.GibbsPreserving.isEquilibriumCompatible_iff_exists` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/GibbsPreserving.lean` |
| `Ript.Models.Thermal.GibbsPreserving.isEquilibriumCompatible_iff_existsUnique` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/GibbsPreserving.lean` |
| `Ript.Models.Thermal.GibbsPreserving.not_exists_channel_iff_not_isEquilibriumCompatible` | `[propext, Classical.choice, Quot.sound]` | `Ript/Models/Thermal/GibbsPreserving.lean` |
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
| `Ript.Higher.CostExactRezkComparison.smallLocalizationFunctor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.CostExactRezkComparison.comparison` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.CostExactRezkComparison.smallLocalizationInverts` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.CostExactRezkComparison.markedTargetVertex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.CostExactRezkComparison.markedArrowFactorsThroughActualEquivalences` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.CostExactRezkComparison.core` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.Presented.wordAssociatorIso` | `[Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.Word.length_append` | `none` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.InversionData.ofIsInvertedBy` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.InversionData.evalAppendIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.InversionData.evalForwardBackwardCancellation` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.InversionData.evalBackwardForwardCancellation` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.InversionData.evalCell` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.InversionData.evalCell_respects` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.InversionData.evalHomFunctor` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.InversionData.lift` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.InversionData.restrictedLift_map₂` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.InversionData.restrictedLift_mapId` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.InversionData.restrictedLift_mapComp` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.InversionData.factorizationHom` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.InversionData.factorizationInv` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.InversionData.factorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.InversionData.factorsThrough` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.InversionData.interpretationCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.LocalExtension.naturalityCell` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzagLocalization.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.LocalExtension.naturalityHom` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzagLocalization.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.LocalExtension.extension` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzagLocalization.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.LocalExtension.restrictionExtensionIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzagLocalization.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.LocalExtension.modificationExtension` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzagLocalization.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.LocalExtension.restrictionModificationExtension` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzagLocalization.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.LocalExtension.localPrecomposition_isEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzagLocalization.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.LocalExtension.inclusion_isBicategoricalLocalization` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzagLocalization.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.Presented.forwardHomFunctor` | `[Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.Presented.sourceIdIso` | `[Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.Presented.sourceCompIso` | `[Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.Presented.markedUnitIso` | `[Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.Presented.markedCounitIso` | `[Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.Presented.localizationBicategory` | `[Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.Presented.inclusion` | `[Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.Presented.markedEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `CategoryTheory.Bicategory.MarkedZigzag.Presented.inclusion_inverts` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/MarkedZigzag.lean` |
| `Ript.Higher.CostExactZigzag.backwardCostReflecting` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzag.lean` |
| `Ript.Higher.CostExactZigzag.unitCellCostReflecting` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzag.lean` |
| `Ript.Higher.CostExactZigzag.counitCellCostReflecting` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzag.lean` |
| `Ript.Higher.CostExactZigzag.forwardHomFunctor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzag.lean` |
| `Ript.Higher.CostExactZigzag.sourceIdIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzag.lean` |
| `Ript.Higher.CostExactZigzag.sourceCompIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzag.lean` |
| `Ript.Higher.CostExactZigzag.markedUnitIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzag.lean` |
| `Ript.Higher.CostExactZigzag.markedCounitIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzag.lean` |
| `Ript.Higher.CostExactZigzag.inclusion` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzag.lean` |
| `Ript.Higher.CostExactZigzag.inclusion_inverts` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzag.lean` |
| `Ript.Higher.CostExactZigzag.markedEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzag.lean` |
| `Ript.Higher.CostExactZigzag.liftOfInverts` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzag.lean` |
| `Ript.Higher.CostExactZigzag.factorizationOfInverts` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzag.lean` |
| `Ript.Higher.CostExactZigzag.factorsThrough` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzag.lean` |
| `Ript.Higher.CostExactZigzag.inclusion_isBicategoricalLocalization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzag.lean` |
| `Ript.Higher.CostExactZigzag.interpretationCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzag.lean` |
| `Ript.Higher.CostExactZigzag.forwardBackwardCancellation` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzag.lean` |
| `Ript.Higher.CostExactZigzag.backwardForwardCancellation` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzag.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonAsSmallFunctor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonNerveMap` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonNerveMap_vertex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonNerveMap_edge` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `CategoryTheory.nerveMap_app_mk₂` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/NerveHomotopy.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonNerveMap_twoSimplex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonNerveHomotopy` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonLocalMap` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonLocalMap_twoCell` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonLocalMap_twoSimplex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.BicategoricalNerveComparison.horizontalCompositionSquare` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.BicategoricalNerveComparison.horizontalTwoCell_comp` | `[propext, Quot.sound]` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.BicategoricalNerveComparison.horizontalCompositionPastedSquare` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.BicategoricalNerveComparison.horizontalCompositionPastingCoherence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.horizontalCompositionSquare` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.horizontalTwoCell_comp` | `[propext, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.horizontalCompositionPastedSquare` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.horizontalCompositionPastingCoherence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonComposeThenMap_edge` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonMapThenCompose_edge` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonComposeThenMap_twoSimplex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonMapThenCompose_twoSimplex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonHorizontalCompositionSquare` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonHorizontalCompositionGlue` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonHorizontalCompositionPastedSquare` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonHorizontalCompositionPastingGlue` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonCompositionPrismSimplex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonCompositionPrism_zeroFace` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonCompositionPrism_lastFace` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonCompositionPrismGlue` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonCompositionPrismSimplexAt` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonCompositionPrismCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.identityComparisonNatIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonIdentityComparisonNatIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonIdentityComparisonHomotopy` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonCompositionComparisonHomotopy` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonAssociatorCompatibility` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonLeftUnitorCompatibility` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonRightUnitorCompatibility` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.pseudofunctorNerveCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.higherLocalizationNerveCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.CostExactZigzagNerveComparison.core` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagNerveComparison.lean` |
| `Ript.Higher.CostExactZigzagNerveComparison.markedVertex_mapsToEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagNerveComparison.lean` |
| `Ript.Higher.CostExactZigzagNerveComparison.twoCell_edge_mapsExactly` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagNerveComparison.lean` |
| `Ript.Higher.CostExactZigzagNerveComparison.twoCell_twoSimplex_mapsExactly` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagNerveComparison.lean` |
| `Ript.Higher.CostExactZigzagNerveComparison.horizontalTwoCell_compositionGlue` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagNerveComparison.lean` |
| `Ript.Higher.CostExactZigzagNerveComparison.horizontalTwoCell_compositorSquare` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagNerveComparison.lean` |
| `Ript.Higher.CostExactZigzagNerveComparison.horizontalTwoCell_pastingGlue` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagNerveComparison.lean` |
| `Ript.Higher.CostExactZigzagNerveComparison.horizontalTwoCell_pastedCompositorSquare` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagNerveComparison.lean` |
| `Ript.Higher.CostExactZigzagNerveComparison.horizontalTwoCellCompositionPrismSimplex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagNerveComparison.lean` |
| `Ript.Higher.CostExactZigzagNerveComparison.horizontalTwoCell_compositionPrismGlue` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagNerveComparison.lean` |
| `Ript.Higher.CostExactZigzagNerveComparison.compositionPrismSimplexAt` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagNerveComparison.lean` |
| `Ript.Higher.CostExactZigzagNerveComparison.compositionPrismCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagNerveComparison.lean` |
| `Ript.Higher.CostExactZigzagNerveComparison.associatorEdgeCoherence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagNerveComparison.lean` |
| `Ript.Higher.CostExactZigzagNerveComparison.leftUnitorEdgeCoherence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagNerveComparison.lean` |
| `Ript.Higher.CostExactZigzagNerveComparison.rightUnitorEdgeCoherence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagNerveComparison.lean` |
| `Ript.Higher.CostExactZigzagNerveComparison.identityHomotopy` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagNerveComparison.lean` |
| `Ript.Higher.CostExactZigzagNerveComparison.compositionHomotopy` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagNerveComparison.lean` |
| `CategoryTheory.Pseudofunctor.homotopyFunctor` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/PseudofunctorHomotopy.lean` |
| `CategoryTheory.Pseudofunctor.homotopyFunctor_map_homMk` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/PseudofunctorHomotopy.lean` |
| `CategoryTheory.Pseudofunctor.homotopyFunctor_inverts_toHomotopy` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Bicategory/PseudofunctorHomotopy.lean` |
| `Ript.Higher.RelativeRezk.diagramCat` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/RelativeRezk.lean` |
| `Ript.Higher.RelativeRezk.comparison` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/RelativeRezk.lean` |
| `Ript.Higher.RelativeRezk.comparison_arrowVertex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/RelativeRezk.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonRezkDiagramMap` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.UniverseLiftedNerve.commonRezkDiagramMap_arrowVertex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/UniverseLiftedLocalizationCompleteSegal.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.smallHomotopyLocalizationFunctor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.homotopyLocalizationFunctor_invertsCostExactMorphisms` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.smallHomotopyLocalization_invertsRelativeMarking` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.relativeOuterComparison` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.relativeOuterComparison_sourceArrow` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.mappedLocalVertexObject_eq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.mappedLocalEdge_eq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.relativeOuter_mappedLocalVertex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.relativeLocal_twoCellOneSkeleton` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.mappedLocalTwoSimplex_eq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.mappedLocalTwoSimplex_diagonal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.relativeLocal_twoSimplexGlue` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.mappedCompositeVertex_outerComposition` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.relativeLocal_horizontalTwoCellGlue` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.sourceHorizontalTwoCell_comp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.relativeLocal_horizontalPastingGlue` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.mappedCompositionPrismSimplex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.relativeLocal_horizontalPrismGlue` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.mappedCompositionPrismSimplexAt` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.relativeLocal_allDegreePrismCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.outerComparison` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.sourceCompletenessHomotopyEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.targetCompletenessHomotopyEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.localVertex_outerArrow` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.localComposite_outerComposition` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.localIdentity_outerIdentity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.outerComposition_sourceComposite` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.localAssociator_outerArrow` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.localLeftUnitor_outerArrow` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.localRightUnitor_outerArrow` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.localIsoToOuterEquality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.localIsoToOuterEquality_trans` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.localPentagon_outerEquality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.localTriangle_outerEquality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.smallHomotopyLocalization_map_marked_isIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.markedArrowFactorsThroughActualEquivalences` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Higher.CostExactZigzagGlobalComparison.core` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/CostExactZigzagGlobalComparison.lean` |
| `Ript.Examples.CostExactFormalInverse.unitToNatFormalReverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/CostExactFormalInverse.lean` |
| `Ript.Examples.CostExactFormalInverse.unitCancellationWord_length` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/CostExactFormalInverse.lean` |
| `Ript.Examples.CostExactFormalInverse.rawCancellationGenerators_exist` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/CostExactFormalInverse.lean` |
| `Ript.Examples.CostExactFormalInverse.presentedCancellationIsos_exist` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/CostExactFormalInverse.lean` |
| `Ript.Examples.CostExactFormalInverse.unitToNatLocalizedEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/CostExactFormalInverse.lean` |
| `Ript.Examples.CostExactFormalInverse.inclusion_genuinely_inverts_unitToNat` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/CostExactFormalInverse.lean` |
| `Ript.Examples.CostExactFormalInverse.formalReverse_exists_beyond_sourceEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/CostExactFormalInverse.lean` |
| `Ript.Higher.BicategoricalNerveComparison.horizontalCompositionFunctor` | `[propext, Quot.sound]` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.BicategoricalNerveComparison.localMap_twoCell` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.BicategoricalNerveComparison.localMap_twoSimplex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.BicategoricalNerveComparison.identityComparisonNatIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.BicategoricalNerveComparison.identityComparisonNerveHomotopy` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.BicategoricalNerveComparison.compositionComparisonNatIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.BicategoricalNerveComparison.compositionComparisonNerveHomotopy` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.BicategoricalNerveComparison.associatorCompatibility` | `none` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.BicategoricalNerveComparison.leftUnitorCompatibility` | `none` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.BicategoricalNerveComparison.rightUnitorCompatibility` | `none` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.BicategoricalNerveComparison.markedEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.BicategoricalNerveComparison.localMap_markedVertex` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.BicategoricalNerveComparison.pseudofunctorNerveCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Higher.BicategoricalNerveComparison.higherLocalizationNerveCore` | `[propext, Classical.choice, Quot.sound]` | `Ript/Higher/LocalizationCompleteSegal.lean` |
| `Ript.Examples.WalkingLocalizationNerveComparison.core` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/WalkingLocalizationNerveComparison.lean` |
| `Ript.Examples.WalkingLocalizationNerveComparison.markedArrowVertex_mapsToEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/WalkingLocalizationNerveComparison.lean` |
| `Ript.Examples.WalkingLocalizationNerveComparison.discardTwoCell_edge_mapsExactly` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/WalkingLocalizationNerveComparison.lean` |
| `Ript.Examples.WalkingLocalizationNerveComparison.mappedDiscardTwoCell_remainsNoninvertible` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/WalkingLocalizationNerveComparison.lean` |
| `Ript.Examples.WalkingLocalizationNerveComparison.compositionHomotopy` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/WalkingLocalizationNerveComparison.lean` |
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
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalSourceTwoCell_rightIdentities_heq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMap₂SourceTwoCell_rightIdentities_heq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompSource_rightIdentities_heq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompSource_firstRightIdentity_heq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalSourceTwoCell_leftIdentities_heq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMap₂SourceTwoCell_leftIdentities_heq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompSource_leftIdentities_heq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompSource_secondLeftIdentity_heq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalSourceTwoCell_leftRightIdentities_heq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMap₂SourceTwoCell_leftRightIdentities_heq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompSource_secondRightIdentity_heq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompSource_firstLeftIdentity_heq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompSourceRightIdentity_hom` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompSourceRightIdentity_naturality_left` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompSourceRightIdentity_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompSourceLeftIdentity_hom` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompSourceLeftIdentity_naturality_right` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompSourceLeftIdentity_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompSourceMixedIdentity_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompSource_identityNormalizations_eq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardMapCompSourceIdentity_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
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
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalRetainedInverseCompositionComparison_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedInverseMapCompTarget_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalRetainedInverseRetainedComparison_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedInverseRetainedMapCompTarget_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalForwardRetainedInverseComparison_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardRetainedInverseMapCompTarget_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalRetainedForwardInverseComparison_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedForwardInverseMapCompTarget_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalForwardInverseRetainedComparison_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardInverseRetainedMapCompTarget_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalInverseForwardRetainedComparison_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftInverseForwardRetainedMapCompTarget_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalInverseRetainedForwardComparison_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftInverseRetainedForwardMapCompTarget_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalRetainedInverseForwardComparison_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedInverseForwardMapCompTarget_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalForwardInverseForwardComparison_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardInverseForwardMapCompTarget_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalInverseForwardInverseComparison_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftInverseForwardInverseMapCompTarget_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftInverseSlidingSource_hom_directMate` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftEquivalenceUnitInsertion_inverseSliding` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardInverseUnitFactorization_compositor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardInverseMapCompSourceNormalized_hom` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftInverseForwardMapCompSourceNormalized_hom` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardRetainedInverseMapCompSource_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardRetainedInverseMapCompTransport_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedForwardInverseMapCompSource_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedForwardInverseMapCompTransport_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardInverseRetainedMapCompSource_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardInverseRetainedMapCompTransport_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftInverseForwardRetainedMapCompSource_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftInverseForwardRetainedMapCompTransport_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftInverseRetainedForwardMapCompSource_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftInverseRetainedForwardMapCompTransport_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedInverseForwardMapCompSource_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedInverseForwardMapCompTransport_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardInverseForwardMapCompSource_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardInverseForwardMapCompTransport_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftInverseForwardInverseMapCompSource_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftInverseForwardInverseMapCompTransport_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedInverseMapCompSource_hom` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedInverseMapCompSource_naturality_right` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedInverseMapCompSource_naturality_left` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedInverseMapCompSourceNormalized_hom` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedInverseMapCompSourceNormalized_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedInverseMapCompSource_eq_normalized` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedInverseMapCompSource_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedInverseMapCompTransport_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftInverseRetainedMapCompSourceNormalized_hom` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedInverseRetainedMapCompSource_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedInverseRetainedMapCompTransport_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompForward` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompForward_naturality_right` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompForward_naturality_left` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompInverseRetained` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompInverseRetained_naturality_right` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompInverseRetained_naturality_left` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompRetainedInverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompRetainedInverse_naturality_right` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapCompRetainedInverse_naturality_left` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_retainedInverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_forwardInverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_inverseForward` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_retainedRetainedInverse_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_retainedInverseRetained_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_forwardRetainedInverse_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_retainedForwardInverse_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_forwardInverseRetained_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_inverseForwardRetained_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_inverseRetainedForward_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_retainedInverseForward_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_forwardInverseForward_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_inverseForwardInverse_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
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
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalSourceGeneratorRetainedComparison_factorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalSourceGeneratorRetainedComparison_factorization_inv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalSourceRetainedGeneratorComparison_factorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalSourceRetainedGeneratorComparison_factorization_inv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftSourceGeneratorRetainedComparison_factorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftSourceGeneratorRetainedComparison_factorization_inv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftSourceRetainedGeneratorComparison_factorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftSourceRetainedGeneratorComparison_factorization_inv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalSourceLeftUnitor_tensor_inv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalSourceRightUnitor_tensor_inv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftSourceLeftUnitor_tensor_inv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftSourceRightUnitor_tensor_inv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalSourceGeneratorRetainedComparison_tensor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalSourceRetainedGeneratorComparison_tensor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftSourceGeneratorRetainedComparison_tensor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftSourceRetainedGeneratorComparison_tensor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalSourceGeneratorRetainedComparison_tensor_inv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.canonicalSourceRetainedGeneratorComparison_tensor_inv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftSourceGeneratorRetainedComparison_tensor_inv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftSourceRetainedGeneratorComparison_tensor_inv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardFactorizationSource_hom_unitor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardFactorizationSource_hom_normalized` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardFactorizationSource_tensor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardFactorizationSource_inv_normalized` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardFactorizationSource_tensor_inv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedForwardFactorizationSource_hom_unitor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedForwardFactorizationSource_hom_normalized` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedForwardFactorizationSource_tensor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftRetainedForwardFactorizationSource_tensor_inv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardFactorizationSource_interchange` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardFactorizationSource_interchange_inv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardSlidingSource_tensor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftForwardSlidingSource_tensor_inv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftInverseSlidingSource_tensor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
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
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftEndpointMapComp_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_associativity` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftPseudofunctor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftPseudofunctor_map_inclusion` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftFactorizationNaturalityOfHEq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftFactorizationNaturalityOfHEq_naturality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftPseudofunctor_map_inclusion_heq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftPseudofunctor_map₂_inclusion_heq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftFactorizationObjEq` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftFactorizationApp` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftFactorizationNaturality` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftFactorizationHom` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftFactorizationObjEqInv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftFactorizationAppInv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftFactorizationNaturalityInv` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftFactorizationInverse` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftFactorization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftFactorsThrough` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.inclusion_isBicategoricalLocalization` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TotalModelWalkingLocalization.lift` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TotalModelWalkingLocalization.lean` |
| `Ript.Examples.TotalModelWalkingLocalization.restrictionEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TotalModelWalkingLocalization.lean` |
| `Ript.Examples.TotalModelWalkingLocalization.factorsThrough` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TotalModelWalkingLocalization.lean` |
| `Ript.Examples.TotalModelWalkingLocalization.localPrecompositionIsEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TotalModelWalkingLocalization.lean` |
| `Ript.Examples.TotalModelWalkingLocalization.universalProperty` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TotalModelWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftMapComp_associativity_of_locallyThin` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftLocallyThinPseudofunctor` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
| `Ript.Examples.TwoDimensionalWalkingLocalization.generalLiftLocallyThinPseudofunctor_map_inclusion` | `[propext, Classical.choice, Quot.sound]` | `Ript/Examples/TwoDimensionalWalkingLocalization.lean` |
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
| `CategoryTheory.Nerve.two_simplex_eq_of_faces_except` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/GroupoidNerve.lean` |
| `CategoryTheory.Nerve.simplex_eq_of_all_faces` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/GroupoidNerve.lean` |
| `CategoryTheory.Nerve.simplex_eq_of_faces_except_high` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/GroupoidNerve.lean` |
| `CategoryTheory.Nerve.boundaryRestriction` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/GroupoidNerve.lean` |
| `CategoryTheory.Nerve.boundaryRestriction_injective` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/GroupoidNerve.lean` |
| `SSet.hornToBoundary` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/GroupoidNerve.lean` |
| `SSet.hornFaceToBoundary` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/GroupoidNerve.lean` |
| `CategoryTheory.Nerve.boundaryRestriction_surjective` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/GroupoidNerve.lean` |
| `CategoryTheory.Nerve.boundaryRestriction_bijective` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/GroupoidNerve.lean` |
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
| `SSet.HomotopyEquivalenceWitness.ofCategoryEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/SSetHomotopyEquivalence.lean` |
| `SSet.HomotopyEquivalenceWitness.transportIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/SSetHomotopyEquivalence.lean` |
| `SSet.NerveEquivalenceWitness.homotopyEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/GroupoidalCompleteSegal.lean` |
| `CategoryTheory.NerveHomotopy.nerveCylinder` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/NerveHomotopy.lean` |
| `CategoryTheory.NerveHomotopy.ofNatTrans` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/NerveHomotopy.lean` |
| `CategoryTheory.SimplicialObject.Homotopy.prismSimplex` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/NerveHomotopy.lean` |
| `CategoryTheory.SimplicialObject.Homotopy.prismSimplex_succ_face_middle` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/NerveHomotopy.lean` |
| `SSet.Homotopy.prismSimplex` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/NerveHomotopy.lean` |
| `SSet.Homotopy.prismSimplex_degeneracy_castSucc_of_le` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/NerveHomotopy.lean` |
| `SSet.Homotopy.AllPrismCoherence` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/NerveHomotopy.lean` |
| `SSet.Homotopy.allPrismCoherence` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/NerveHomotopy.lean` |
| `SSet.Homotopy.degreeTwoPrismFaces` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/NerveHomotopy.lean` |
| `CategoryTheory.Functor.isIsofibrationId` | `[propext]` | `Ript/ForMathlib/CategoryTheory/Isofibration.lean` |
| `CategoryTheory.Functor.coreInclusionIsIsofibration` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Isofibration.lean` |
| `CategoryTheory.Functor.isIsofibrationComp` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Isofibration.lean` |
| `CategoryTheory.Functor.coreArrowEndpointsIsIsofibration` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Isofibration.lean` |
| `CategoryTheory.Functor.exists_lift_iso_hom` | `none` | `Ript/ForMathlib/CategoryTheory/Isofibration.lean` |
| `CategoryTheory.Functor.exists_lift_iso_inv` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Isofibration.lean` |
| `CategoryTheory.Functor.nerveMap_mk₁_isoLift` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Isofibration.lean` |
| `CategoryTheory.Functor.nerveMap_hornOne_lift` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Isofibration.lean` |
| `CategoryTheory.Functor.nerveMap_hornTwo_lift` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Isofibration.lean` |
| `CategoryTheory.Functor.nerveMap_hornHigh_lift` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Isofibration.lean` |
| `SSet.fibration_iff_hornFamily` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Isofibration.lean` |
| `CategoryTheory.Functor.nerveMap_fibration` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Isofibration.lean` |
| `CategoryTheory.Functor.nerveMap_coreArrowEndpoints_fibration` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/Isofibration.lean` |
| `CategoryTheory.TriangleBoundary.isoMk` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/TriangleBoundary.lean` |
| `CategoryTheory.TriangleBoundary.functorBoundaryEquiv` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/TriangleBoundary.lean` |
| `CategoryTheory.TriangleBoundary.restrictAlongFunctor_comp` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/TriangleBoundary.lean` |
| `CategoryTheory.TriangleBoundary.restrictionFunctor_comp_restrictAlongFunctor` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/TriangleBoundary.lean` |
| `CategoryTheory.TriangleBoundary.toBoundaryNerveMap` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/TriangleBoundary.lean` |
| `CategoryTheory.TriangleBoundary.boundaryNerveFace_endpoint` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/TriangleBoundary.lean` |
| `CategoryTheory.TriangleBoundary.ofBoundaryNerveMap` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/TriangleBoundary.lean` |
| `CategoryTheory.TriangleBoundary.boundaryNerveVertexObject_toBoundaryNerveMap` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/TriangleBoundary.lean` |
| `CategoryTheory.TriangleBoundary.cofaceFactorization_nonempty` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/TriangleBoundary.lean` |
| `CategoryTheory.TriangleBoundary.boundarySimplex_eq_coface_map` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/TriangleBoundary.lean` |
| `CategoryTheory.TriangleBoundary.restrictAlong_ofBoundaryNerveMap_coface` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/TriangleBoundary.lean` |
| `CategoryTheory.TriangleBoundary.ofBoundaryNerveMap_toBoundaryNerveMap` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/TriangleBoundary.lean` |
| `CategoryTheory.TriangleBoundary.toBoundaryNerveMap_ofBoundaryNerveMap` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/TriangleBoundary.lean` |
| `CategoryTheory.TriangleBoundary.boundaryNerveEquiv` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/TriangleBoundary.lean` |
| `CategoryTheory.TriangleBoundary.fillable_iff_exists_extension` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/TriangleBoundary.lean` |
| `CategoryTheory.TriangleBoundary.fillable_of_iso_restriction` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/TriangleBoundary.lean` |
| `CategoryTheory.TriangleBoundary.coreRestrictionFunctorIsIsofibration` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/TriangleBoundary.lean` |
| `CategoryTheory.TriangleBoundary.nerveMap_coreRestrictionFunctor_fibration` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/CategoryTheory/TriangleBoundary.lean` |
| `SSet.KanComplex.ofIso` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/GroupoidalCompleteSegal.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramCompletenessNerveEquivalenceWitness` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramLevelStrictSegal` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `Ript.Univalent.UniverseModel.interfaceClassifyingDiagramLevelKan` | `[propext, Classical.choice, Quot.sound]` | `Ript/Univalent/ClassifyingDiagram.lean` |
| `SSet.boundaryMatchingMap_fibration` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/ReedyMatching.lean` |
| `SSet.boundaryMatchingIndexProjection` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/ReedyMatching.lean` |
| `SSet.boundaryMatchingIndexMap` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/ReedyMatching.lean` |
| `SSet.simplicialSpaceBoundaryMatchingDiagram` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/ReedyMatching.lean` |
| `SSet.simplicialSpaceBoundaryMatchingConeIsLimit` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/ReedyMatching.lean` |
| `SSet.boundaryMatchingSimplex_naturality` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/ReedyMatching.lean` |
| `SSet.boundaryMatchingSimplex_not_surjective` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/ReedyMatching.lean` |
| `SSet.boundaryMatchingSimplex_degreeTwoBoundaryFaceElement` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/ReedyMatching.lean` |
| `SSet.boundaryMatchingSimplex_degreeTwoBoundaryVertexElement` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/ReedyMatching.lean` |
| `SSet.degreeTwoBoundaryFaceToVertex` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/ReedyMatching.lean` |
| `SSet.simplicialSpaceBoundaryRestrictionCone` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/ReedyMatching.lean` |
| `SSet.simplicialSpaceBoundaryMatchingMap` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/ReedyMatching.lean` |
| `SSet.simplicialSpaceBoundaryMatchingMap_eq_limitLift` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/ReedyMatching.lean` |
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
| `SSet.GroupoidalCompleteSegal.completenessHomotopyEquivalence` | `[propext, Classical.choice, Quot.sound]` | `Ript/ForMathlib/AlgebraicTopology/GroupoidalCompleteSegal.lean` |
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

## 如何理解这些结果

- `none` 表示声明不依赖任何公理；
- `propext` 是 Lean 的命题外延性；
- `Quot.sound` 来自商类型证明层；
- `Classical.choice` 主要来自 Mathlib 的有限类型、范畴、测度、骨架、Yoneda 与单纯基础设施；
- 表中没有项目自定义公理、编译器信任逃逸或证明占位符。

可执行有限核心与需要经典选择的语义层保持分离。出现 `Classical.choice` 并不意味着选择得到的代表元
进入运行时数据；应结合“源文件”和[项目范围](../PROJECT_SCOPE.md)判断边界。

## 更新规则

新增或改变旗舰定理时：

1. 更新 `Ript/Audit/AxiomChecks.lean`；
2. 运行 `#print axioms` 并更新根 `AXIOMS.md`；
3. 运行 `./scripts/sync-doc-reference-tables.sh`；
4. 运行 `./scripts/quality-gate.sh`。
