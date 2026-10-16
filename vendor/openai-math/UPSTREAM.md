Vendored divisor bound `exists_divisors_power_bound` (`τ(n)^k ≤ C_k n`) from
https://github.com/openai/math at commit `1581d4cbdd69a0faf34b2089614fe2a814316a6a`:
`OAI/NumberTheory/Ostmann/Preliminaries/DivisorPowerBound.lean`.

The file is distributed under the included Apache-2.0 license. It is unchanged
apart from its import lines. Upstream imports
`OAI.NumberTheory.Ostmann.Arithmetic.SquareRootProbability`, which pulls in seven
further modules. The proof needs none of them, so that import is replaced by
`Mathlib.Data.Nat.Factorization.Basic` and `Mathlib.NumberTheory.ArithmeticFunction.Misc`.

This is a parent-project-only Lake package: run builds from the repository root.
It uses the parent's pinned Lean `v4.35.0` and Mathlib `v4.35.0`, rather than the
upstream Lean 4.34.1 toolchain. It has no separate toolchain or Mathlib dependency
and does not support standalone builds.
