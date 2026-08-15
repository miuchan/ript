# Model Capability Matrix

Only implemented and compiled capabilities are marked as supported.

| Model | Sequential | Tensor | Discard | Copy | Convex | Causal | Thermal | Computable |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| FiniteFunction (zero cost) | Yes | No | No | No | No | No | No | Yes |
| FiniteFunction.Metered | Yes | No | No | No | No | No | No | Yes |
| Sequential term model | Yes | No | No | No | No | No | No | Proof layer |
| Symmetric monoidal term model | Yes | Yes | No | No | No | No | No | Proof layer |
| FiniteStochastic (exact `ℚ≥0`) | Yes | Yes | Yes | Yes | No | Yes | No | Yes |
| Finite-distribution Kleisli | Yes | No | No | No | No | No | No | Yes |
| Mathlib `Stoch` bridge (finite discrete image) | Yes | Yes | Via `Stoch` | Via `Stoch` | No | Via `Stoch` | No | Semantic layer |
| QuantumChannel | Planned | No | No | No | No | No | No | No |
