# Bounds for the iteration `x ↦ a mod x`

For integers `a > b > 0` let `b₁ = b`, `b_{i+1} = a mod bᵢ`, and let `P(a, b)` be the number of
positive terms ([Open Problem Garden](https://www.openproblemgarden.org/op/a_discrete_iteration_related_to_pierce_expansions)).
Shallit asked whether `P(a, b) = O((log a)²)`. That question is **still open**. This repository
proves, uniformly in `0 < b < a`:

* **Unconditionally:** `P(a, b) ≤ C_ε · a^{3/10 + ε}`. This improves on Chase–Pandey's
  `a^{1/3 − 2/177 + ε}`, and has the same exponent as the unpublished `n^{3/10}` bound reported on
  Shallit's talks page.
* **Assuming two published theorems:** `P(a, b) ≪ a^{3/10} √(log log 3a)`. The theorems are
  Nair–Tenenbaum, Acta Math. 180 (1998), on short sums of the Erdős–Hooley `Δ`-function, and
  de la Bretèche–Tenenbaum, Acta Arith. 219 (2025), Thm 1.1, `∑_{n≤x} Δ(n) ≪ x (log log x)^{5/2}`.
  Both are stated in Lean as explicit hypotheses. Their proofs are not formalised.

The main ingredients are two exact identities. The first, for three consecutive steps, shows
that the curvature `D = dv − eu` is a positive integer. The second, for six consecutive steps,
produces a further positive integer `L` with `q w L = J E + S F`. That gives the local bound
`T⁶ A² ≤ 96·10⁶ a³` for the number `T` of remainders in `[A, 2A)`, with no divisor-function loss.

* `paper/pierce_bound.tex` (and `.pdf`): the paper.
* `PierceBound/`: Lean 4 / Mathlib formalisation of all of the above, with no `sorry`.

## Lean

Build with `lake build` (Lean `v4.35.0`, Mathlib `v4.35.0`). The main theorems are

```lean
theorem PierceBound.P_le : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((3 : ℝ) / 10 + ε)

theorem PierceBound.P_le_loglog (hNT : NairTenenbaumDelta) (hBT : BretecheTenenbaumMean) :
    ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ (3 / 10 : ℝ) * √(Real.log (Real.log (3 * a)))
```

`#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound` for both. The second
theorem's dependence on the two papers is entirely through its hypotheses.

| File | Contents |
|---|---|
| `Defs.lean` | `P`, the orbit `orb`; check `P 35 22 = 7` |
| `Block.lean` | curvature `D = dv − eu`: identity `Dz = df + ude + (u−1)e²`, `D ≥ 1`, fiber equation `x M(q) = a N(q) + D`, size bounds |
| `Fiber.lean` | a fixed `(u, v, D)` allows at most `max_{n ≤ 32a⁷} τ(n)` starting points |
| `Window.lean` | for a run of `T` terms in `[A, 2A)`: `T(T−1) ≤ 4AΔ`, `T⁶A² ≤ 995328 a³Δ`, hence `T¹⁰ ≤ 63700992 a³Δ³` |
| `Main.lean` | dyadic decomposition and the unconditional theorem `P_le` |
| `SixStep.lean` | the six-step identity `q w L = J E + S F`, `L ≥ 1`, and `six_step_bound`: `T⁶A² ≤ 96·10⁶ a³` |
| `ShortSum.lean` | the drop count `T ≤ 2 ∑_{a<n≤a+Y} #{d ∣ n : A ≤ d < 2A}` |
| `Geometric.lean` | `∑_k min(α 2^{−k/3}, β 2^{k/2}) ≤ 9 α^{3/5} β^{2/5}` |
| `Conditional.lean` | any short-interval divisor bound `≪ y G(x)` gives `P ≪ a^{3/10} G(a)^{1/5}` (`P_le_of_shortDivisorBound`) |
| `Hooley.lean` | Erdős–Hooley `Δ`, the hypotheses `NairTenenbaumDelta` and `BretecheTenenbaumMean`, partial summation, and `P_le_loglog` |

## Vendored code

`vendor/openai-math/` is a path-required Lake package. It contains a single file from
[openai/math](https://github.com/openai/math) (Apache-2.0): the divisor bound
`τ(n)^k ≤ C_k n` (`exists_divisors_power_bound`). The file is unchanged except for its import
lines; the upstream commit is recorded in [UPSTREAM.md](vendor/openai-math/UPSTREAM.md).
