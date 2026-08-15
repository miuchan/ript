import Mathlib.Tactic.Linter.Lint
import Ript.Audit.AxiomChecks

/-!
# Project lint gate

This module runs Mathlib's default declaration linters over every declaration in
the `Ript` package. The silent form produces no output on success and exits with
an error as soon as a lint violation is found.
-/

set_option autoImplicit false

#lint- in Ript
