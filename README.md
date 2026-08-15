# Ript

Ript is a Lean 4 formalization of **Resource-Indexed Information Process Theory**.
The project is being built from a small, auditable process core before adding
probabilistic, causal, thermal, quantum, and higher-categorical layers.

Stages 1 and 2 are now kernel-checked. They contain:

- ordered additive resource bounds and lax process costs;
- zero-budget identities, additive serial budgets, and budget weakening;
- executable typed syntax for generators, identities, and composition;
- cost-respecting interpretations and semantic cost soundness;
- an explicit equational derivation system with semantic soundness;
- a quotient term model and relative completeness;
- optional parallel-cost and free-structural-cost capabilities;
- typed tensor, associator, unitor, and symmetric-braiding syntax;
- additive parallel budgets and monoidal semantic cost soundness;
- an explicit symmetric monoidal derivation system with semantic soundness;
- a distinct-carrier symmetric monoidal quotient model and relative completeness;
- zero-cost and explicitly metered finite deterministic models;
- executable Boolean examples.

## Trust and build policy

- Every library result must be accepted by Lean's kernel.
- Unproved research statements are tracked in `CONJECTURES.md`, not declared as
  library theorems.
- New assumptions are forbidden in the core and computable dependency graph.
- Executable examples demonstrate computation but never replace general proofs.
- The project pins Lean and mathlib to matching `v4.33.0` releases.

Build the project with:

```bash
lake build
```

Before submitting a change, run the complete code-quality gate:

```bash
./scripts/quality-gate.sh
```

This verifies source hygiene, root-module coverage, a warning-free kernel build,
Mathlib declaration lint, exact executable-example output, and the documented
axiom allowlist. GitHub Actions runs the same checks for every pull request and
every push to `main`.

The focused executable example and assumption audit remain available with:

```bash
lake env lean Ript/Examples/BitProcesses.lean
lake env lean Ript/Audit/AxiomChecks.lean
```

The current implementation status and theorem dependencies are maintained in
`BLUEPRINT.md`; assumption audit results are maintained in `AXIOMS.md`.

## Dependency boundary

Executable syntax and finite functions do not depend on either quotient term
model. Quotients occur only in `Ript/Semantics/TermModel.lean` and
`Ript/Semantics/MonoidalTermModel.lean`, where they prove relative
completeness. No univalent or higher-categorical layer is imported by the
stage-1 or stage-2 core.
