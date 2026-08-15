import Ript.Examples.BitProcesses
import Ript.Examples.StochasticBits
import Ript.Resource.ParallelBudget
import Ript.Semantics.Completeness
import Ript.Semantics.MonoidalCompleteness
import Ript.Semantics.MonoidalInitiality

/-!
# Kernel assumption checks

This module prints the assumptions used by the stage-1 through stage-3 flagship theorems.
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
