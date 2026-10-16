# `P(a, b) ≪ a^{3/10 + ε}` for the iteration `x ↦ a mod x`

For integers `a > b > 0` let `b₁ = b`, `b_{i+1} = a mod bᵢ`, and let `P(a, b)` be the number of
positive terms ([Open Problem Garden](https://www.openproblemgarden.org/op/a_discrete_iteration_related_to_pierce_expansions)).
Shallit asked whether `P(a, b) = O((log a)²)`. That question is **still open**. This repository
proves the weaker bound

    P(a, b) ≤ C_ε · a^{3/10 + ε}   for all 0 < b < a,

which improves on Chase–Pandey's `a^{1/3 − 2/177 + ε}`. It has the same exponent as the
unpublished `n^{3/10}` bound reported on Shallit's talks page.

* `paper/pierce_bound.tex` (and `.pdf`): the paper.
* `PierceBound/`: Lean 4 / Mathlib formalisation of the whole proof, with no `sorry`.

## Lean

Build with `lake build` (Lean `v4.35.0`, Mathlib `v4.35.0`). The main theorem is

```lean
theorem PierceBound.P_le : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((3 : ℝ) / 10 + ε)
```

and `#print axioms PierceBound.P_le` gives only `propext`, `Classical.choice`, `Quot.sound`.

| File | Contents |
|---|---|
| `Defs.lean` | `P`, the orbit `orb`; check `P 35 22 = 7` |
| `Block.lean` | curvature `D = dv − eu`: identity `Dz = df + ude + (u−1)e²`, `D ≥ 1`, fiber equation `x M(q) = a N(q) + D`, size bounds |
| `Fiber.lean` | a fixed `(u, v, D)` allows at most `max_{n ≤ 32a⁷} τ(n)` starting points |
| `Window.lean` | for a run of `T` terms in `[A, 2A)`: `T(T−1) ≤ 4AΔ`, `T⁶A² ≤ 995328 a³Δ`, hence `T¹⁰ ≤ 63700992 a³Δ³` |
| `Main.lean` | dyadic decomposition and the final theorem `P_le` |

## Vendored code

`vendor/openai-math/` is a path-required Lake package. It contains a single file from
[openai/math](https://github.com/openai/math) (Apache-2.0): the divisor bound
`τ(n)^k ≤ C_k n` (`exists_divisors_power_bound`). The file is unchanged except for its import
lines; the upstream commit is recorded in [UPSTREAM.md](vendor/openai-math/UPSTREAM.md).
