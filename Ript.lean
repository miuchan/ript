import Ript.Audit.AxiomChecks
import Ript.Core.CostedProcess
import Ript.Core.ParallelCost
import Ript.Core.StructuralCost
import Ript.Examples.BitProcesses
import Ript.Models.FiniteFunction
import Ript.Resource.Basic
import Ript.Resource.Budget
import Ript.Resource.ParallelBudget
import Ript.Semantics.Eval
import Ript.Semantics.Completeness
import Ript.Semantics.Interpretation
import Ript.Semantics.MonoidalEval
import Ript.Semantics.MonoidalInterpretation
import Ript.Semantics.MonoidalSoundness
import Ript.Semantics.MonoidalTermModel
import Ript.Semantics.MonoidalCompleteness
import Ript.Semantics.Soundness
import Ript.Semantics.TermModel
import Ript.Syntax.Cost
import Ript.Syntax.Derivation
import Ript.Syntax.Monoidal
import Ript.Syntax.MonoidalCost
import Ript.Syntax.MonoidalDerivation
import Ript.Syntax.MonoidalSignature
import Ript.Syntax.Sequential
import Ript.Syntax.Signature

/-!
# Ript

Root module for Resource-Indexed Information Process Theory.
-/

set_option autoImplicit false
