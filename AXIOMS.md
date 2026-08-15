# Assumption Audit

The core declares no project-specific assumptions. The following table records
the actual output of `lake env lean Ript/Audit/AxiomChecks.lean`.

| Theorem | Kernel output | Source |
| --- | --- | --- |
| `Ript.Resource.budgeted_id` | `[propext]` | `Ript/Resource/Budget.lean` |
| `Ript.Resource.budgeted_comp` | `[propext, Quot.sound]` | `Ript/Resource/Budget.lean` |
| `Ript.Syntax.Expr.syntaxCost_id` | none | `Ript/Syntax/Cost.lean` |
| `Ript.Syntax.Expr.syntaxCost_comp` | none | `Ript/Syntax/Cost.lean` |
| `Ript.Semantics.eval_id` | none | `Ript/Semantics/Eval.lean` |
| `Ript.Semantics.eval_comp` | none | `Ript/Semantics/Eval.lean` |
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

`propext` and `Quot.sound` are Lean's standard logical and quotient principles;
they are not project-declared assumptions. The quotient dependency is confined
to proof semantics. No flagship theorem depends on classical choice or compiler
trust, and the audit reports no placeholder proof assumption. In particular,
the braided hexagon soundness cases use the primitive `BraidedCategory`
hexagon laws directly, so the stage-2 flagship results do not acquire a
`Classical.choice` dependency from derived coherence lemmas.

The `Ript/Univalent/` boundary does not yet exist and is not imported by the core.
