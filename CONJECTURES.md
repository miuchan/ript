# Conjectures and Unproved Research Statements

Only unresolved mathematical statements are listed here. Each entry uses the
required marker `FORMALIZED_BUT_UNPROVED` once its exact Lean proposition has
been checked but no kernel proof is available.

There are currently no registered conjectures. The deterministic finite
Blackwell converse is now proved, not conjectural: under any exact full-support
prior, comparison on the zero-one target-reconstruction task recovers an exact
post-processing witness, equivalently the target is constant on every source
fiber. The general converse for arbitrary finite stochastic experiments still
requires a finite-dimensional convex-separation or linear-programming duality
development. Its exact Lean proposition has not yet been registered, so it is
a documented research boundary rather than a `FORMALIZED_BUT_UNPROVED` entry.

In particular, the canonical
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
