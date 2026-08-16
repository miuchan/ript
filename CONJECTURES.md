# Conjectures and Unproved Research Statements

Only unresolved mathematical statements are listed here. Each entry uses the
required marker `FORMALIZED_BUT_UNPROVED` once its exact Lean proposition has
been checked but no kernel proof is available.

## Exact finite stochastic Blackwell converse

Status: `FORMALIZED_BUT_UNPROVED`.

The exact proposition is now checked by Lean as
`Ript.Models.Decision.Separation.FiniteBlackwellShermanStein`:

```lean
universe u

def FiniteBlackwellShermanStein : Prop :=
  ∀ (Θ X Y : Object.{u}) (P : FinStoch Θ X) (Q : FinStoch Θ Y),
    FiniteDecisionOrder P Q → BlackwellDominates P Q
```

Here `FiniteDecisionOrder P Q` quantifies over every finite action carrier,
exact prior, and exact nonnegative-rational loss. The compiled theorem
`finiteBlackwellShermanStein_iff_certificateComplete` reduces this conjecture
exactly to the claim that every non-garbling pair admits a concrete finite
decision-separation certificate. Certificates are already proved sound, and a
genuinely stochastic Boolean pair has an executable certificate with risks
`1/4 < 1/2`.

The missing implication is geometric: derive an exact rational certificate
from failure of an exact rational stochastic garbling. Mathlib supplies real
locally convex Hahn--Banach/Farkas separation, but the project still needs a
finite garbling-polytope construction and a proof that the resulting strict
separator can be represented by exact nonnegative-rational decision data.

The deterministic finite Blackwell converse is proved, not conjectural: under
any exact full-support prior, target-reconstruction risk recovers an exact
post-processing witness, equivalently the target is constant on every source
fiber.

Apart from that registered converse, the canonical
Gibbs realization of every full-support exact finite equilibrium and the
common-temperature tensor/additivity laws are proved declarations, not
conjectural placeholders. The exact product-endpoint Landauer free-energy
balance, its entropy-neutral battery work form, and the Boolean `log 2 / β`
erasure bound are also proved declarations. The arbitrary-joint marginal
decomposition, mutual-information KL identity and nonnegativity,
correlation-corrected Landauer bounds, and correlated Boolean example are
proved as well. Exact rational-error Boolean approximate erasure, its binary-
entropy free-energy identity and monotonicity law, and its product-endpoint and
correlation-corrected Landauer bounds are proved declarations too. Explicit
finite closed protocols, their composite semantics, the two-flip Boolean
cycle, and the closed exact-erasure no-go are now proved declarations too.
Bath-resolved Landauer accounting and an executable exact-erasure protocol are
also proved: the three-bit permutation returns the bath, consumes information-
battery purity, and saturates the free-energy balance. Its battery entropy
changes, so it is not a mechanical-work witness. A separate two-level
nondegenerate battery now gives an exact entropy-neutral mechanical-work
protocol: it discharges pure high to pure low, erases the fair bit, supplies
`log 2 / β`, and saturates the work bound. A matched exact recharge channel
randomizes the erased memory back to equilibrium, raises the pure battery from
low to high by the same `log 2 / β`, and closes the executable three-state
trace. Both signed balances cancel, so no net work is claimed. Rational-weight
classification for independently specified finite real spectra is now proved:
exact rational Gibbs probabilities exist iff every Boltzmann ratio to any
chosen reference microstate is a positive rational number. Positive rational
weights construct executable two- and three-level examples, while a spectrum
with relative factor `sqrt 2` is proved to have no rational Gibbs distribution.
What remains unsupported is a general algorithm deciding equality of arbitrary
real exponential expressions; no unproved Lean proposition is registered for
that algorithmic boundary.
