# Model Capability Matrix

Only implemented and compiled capabilities are marked as supported.

| Model | Sequential | Tensor | Discard | Copy | Convex | Causal | Decision | Thermal | Computable |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| FiniteFunction (zero cost) | Yes | No | No | No | No | No | No | No | Yes |
| FiniteFunction.Metered | Yes | No | No | No | No | No | No | No | Yes |
| Sequential term model | Yes | No | No | No | No | No | No | No | Proof layer |
| Symmetric monoidal term model | Yes | Yes | No | No | No | No | No | No | Proof layer |
| FiniteStochastic (exact `ℚ≥0`) | Yes | Yes | Yes | Yes | No | Yes | No | No | Yes |
| Finite-distribution Kleisli | Yes | No | No | No | No | No | No | No | Yes |
| Mathlib `Stoch` bridge (finite discrete image) | Yes | Yes | Via `Stoch` | Via `Stoch` | No | Via `Stoch` | Via Mathlib Bayes risk | No | Semantic layer |
| Exact finite decision layer | Via `FinStoch` | No | No | No | No | Via `FinStoch` | Yes | No | Yes |
| Total computation (`Fin 4 → Nat` resources) | Yes | Bifunctor | No | No | No | No | No | No | Yes |
| Partial computation (`Option` Kleisli) | Yes | Bifunctor | No | No | No | No | No | No | Yes |
| Finite causal DAG (exact `ℚ≥0`) | Topological generation | Via `FinStoch` states | No | No | No generic interface | Yes | No | No | Yes |
| QuantumChannel | Planned | No | No | No | No | No | No | No | No |
