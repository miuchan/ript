# Model Capability Matrix

Only implemented and compiled capabilities are marked as supported.

| Model | Sequential | Tensor | Discard | Copy | Convex | Causal | Thermal | Computable |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| FiniteFunction (zero cost) | Yes | No | No | No | No | No | No | Yes |
| FiniteFunction.Metered | Yes | No | No | No | No | No | No | Yes |
| Sequential term model | Yes | No | No | No | No | No | No | Proof layer |
| Symmetric monoidal term model | Yes | Yes | No | No | No | No | No | Proof layer |
| FiniteStochastic | Planned | No | No | No | No | No | No | Planned |
| Stoch | Planned | No | No | No | No | No | No | No |
| QuantumChannel | Planned | No | No | No | No | No | No | No |
