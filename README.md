# Bounds for the iteration `x ↦ a mod x`

For integers `a > b > 0` let `b₁ = b`, `b_{i+1} = a mod bᵢ`, and let `P(a, b)` be the number of
positive terms ([Open Problem Garden](https://www.openproblemgarden.org/op/a_discrete_iteration_related_to_pierce_expansions)).
Shallit asked whether `P(a, b) = O((log a)²)`. That question is **still open**. This repository
proves, uniformly in `0 < b < a`:

* **Strongest bound:** `P(a, b) ≤ C_ε · a^{45/152 + ε}`, where `45/152 = 0.29605…`. This goes below
  the exponent `3/10` of the unpublished `n^{3/10}` bound reported on Shallit's talks page.
* **Earlier steps:** `P(a, b) ≤ C_ε · a^{8/27 + ε}`, before that `a^{11/37 + ε}`, and before
  that `a^{23/77 + ε}`.
* **The `3/10` bound:** `P(a, b) ≤ C_ε · a^{3/10 + ε}`, improving Chase–Pandey's
  `a^{1/3 − 2/177 + ε}`. Its six-step identity is an ingredient of the main theorem.
* **Assuming two published theorems:** `P(a, b) ≪ a^{3/10} √(log log 3a)`. The theorems are
  Nair–Tenenbaum, Acta Math. 180 (1998), on short sums of the Erdős–Hooley `Δ`-function, and
  de la Bretèche–Tenenbaum, Acta Arith. 219 (2025), Thm 1.1, `∑_{n≤x} Δ(n) ≪ x (log log x)^{5/2}`.
  Both are stated in Lean as explicit hypotheses. Their proofs are not formalised.
* **Structured trajectories:** `P(a, b) ≪ a^{1/4} √R`, where `R − 1` is the number of rises
  `kᵢ < k_{i+1}` in the quotient increments. In particular nonincreasing increments give
  `P(a, b) ≪ a^{1/4}`.
* **The Hankel hierarchy:** an exact positive moment model of the orbit gives positive integer
  invariants `I_r(i)` (Hankel determinants) for every `r`, with `I₁ = bᵢ`, `I₂ = dᵢ`, `I₃ = D`
  and `I₄ = L` in the nonterminal ranges specified in the paper. In particular the last two
  identities require `i + 3 < P(a,b)` and `i + 5 < P(a,b)`, respectively, with zero-based indexing.

The `3/10` bound rests on two exact identities. The first, for three consecutive steps, shows
that the curvature `D = dv − eu` is a positive integer. The second, for six consecutive steps,
produces a further positive integer `L` with `q w L = J E + S F`. That gives the local bound
`T⁶ A² ≤ 96·10⁶ a³` for the number `T` of remainders in `[A, 2A)`, with no divisor-function loss.

The bounds below `3/10` use `L = I₄` as an integer, not just as a positive number. A 3×4 integer matrix
built from four drops and five increments has cofactors `(-L(i+1), U₁, U₂, L(i))`. The seven
integers `L(i), L(i+1), L(i+2), U₁(i), U₂(i), U₁(i+1), U₂(i+1)` form a *pattern*. Its size is
bounded via Hadamard's inequality on the moment model. States with a given pattern satisfy:

* two linear equations and one quadratic in five consecutive increments, with leading
  coefficient `L(i)L(i+1)(L(i)+L(i+1)) > 0`;
* the quartic identity `I₄(i) pᵢ(-qᵢ) = a det(μᵢ(x^{j+l}))`, so at most four states share a point.

So each pattern covers `O(H²)` states, giving `T ≪ X⁷H²` and hence `T⁷⁷ ≪ Δ²²a²³` (exponent 23/77).

For `11/37`, exact Cramer identities give `U₁ > 0 > U₂`, so the quadratic part in `(k₁, k₂, k₃)` is
nondegenerate with an indefinite binary restriction. Apart from at most two exceptional slices,
each slice is a norm equation `x² − δy² = m` with `m ≠ 0`, which
has `≤ 2τ(|m|)³(log₃((B(⌊√δ⌋ + 2))²) + 1)` solutions in `[−B, B]²`, uniformly in the
coefficients. This is proved in
full: square roots modulo prime powers, CRT, and the separation `ε ≥ 3` of norm-one numbers. So
each pattern covers `O(H a^η)` states, `T ≪ a^η X⁷ H`, and `T⁷⁴ ≪ a^{22+O(η)}`.

For `8/27`, the seven pattern integers are signed `3×3` minors of one `3×5` integer matrix. An exact
expansion of `b/a` with a positive remainder bounds all ten minors by `X`. Minor vectors of height `≤ Y`
number `≤ 1 + 20 ∑_{m≤Y} 729 m⁴ τ(m)`, via a maximal pivot, the Plücker relations, and the congruence
`v ≡ μu₀ (mod m/g)`. So `T ≪ a^η X⁵ H` and `T⁵⁴ ≪ a^{16+O(η)}`.

For `45/152`, the pivot gaps `k'` of a state lie in the lattice
`Λ_p = {x ∈ ℤ³ : m ∣ u·x, m ∣ v·x}` of its minor vector, and `m kᶜ = Lᶜ · k'` recovers all five gaps.
The cross relation makes the index `≤ |m|`, so `Λ_p` has a vector of length `λ(p) ≤ X^{1/3}`
(pigeonhole). A reduced basis with `27|b₁|²|b₂|²|b₃|² ≤ 64 det²`, built by minimising the
determinant, then `|b₁|²`, then a Gram determinant (integer arithmetic only), gives coordinates
`λ(p)|yᵢ| ≤ 3H`. After a plane choice the slice count applies to `F_θ` in those coordinates,
with definite slices handled by a definite norm count. So one minor vector covers
`O((H/λ(p) + 1) a^η)` gap vectors. Only `≪ R³X⁴τ²` minor vectors have `λ(p) ≤ R`, and partial
summation gives `T ≪ a^η (H X^{14/3} + X⁵)`, hence `T¹⁵² ≪ a^{45+O(η)}`.

* `paper/pierce_length_bound.tex` (and `.pdf`): the paper.
* `PierceLengthBound/`: Lean 4 / Mathlib formalisation of all of the above, with no `sorry`.

## Lean

Build with `lake exe cache get` (to download the compiled Mathlib) and then `lake build`
(Lean `v4.35.0`, Mathlib `v4.35.0`). The build runs Mathlib's standard linters
(`weak.linter.mathlibStandardSet`). It also builds the independent Palomar Challenge
and Solution modules and runs the eight-theorem axiom audit. The eight `sorry` warnings
in `Challenge.lean` are deliberate statement holes; the proof development has none.
The main theorems are

```lean
theorem PierceLengthBound.P_le_45_152 : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((45 : ℝ) / 152 + ε)

theorem PierceLengthBound.P_le_8_27 : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((8 : ℝ) / 27 + ε)

theorem PierceLengthBound.P_le_11_37 : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((11 : ℝ) / 37 + ε)

theorem PierceLengthBound.P_le_23_77 : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((23 : ℝ) / 77 + ε)

theorem PierceLengthBound.P_le : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((3 : ℝ) / 10 + ε)

theorem PierceLengthBound.P_le_loglog (hNT : NairTenenbaumDelta) (hBT : BretecheTenenbaumMean) :
    ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ (3 / 10 : ℝ) * √(Real.log (Real.log (3 * a)))

theorem PierceLengthBound.P_le_rises : ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ (1 / 4 : ℝ) * √(rises a b + 1)

theorem PierceLengthBound.hankelInv_pos_int (hba : b < a) (hi : i < P a b) (hr : r ≤ P a b - i) :
    ∃ n : ℕ, 0 < n ∧ hankelInv a b i r = n
```

`#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound` for all eight;
`Axioms.lean` checks this with `#guard_msgs` as part of `lake build`; it can also be run
with `lake env lean Axioms.lean`. `P_le_loglog` depends on the two
papers only through its hypotheses.

| File | Contents |
|---|---|
| `Defs.lean` | `P`, the orbit `orb`; check `P 35 22 = 7` |
| `Block.lean` | curvature `D = dv − eu`: identity `Dz = df + ude + (u−1)e²`, `D ≥ 1`, fiber equation `x M(q) = a N(q) + D`, size bounds |
| `Fiber.lean` | a fixed `(u, v, D)` allows at most `max_{n ≤ 32a⁷} τ(n)` starting points |
| `Window.lean` | for a run of `T` terms in `[A, 2A)`: `T(T−1) ≤ 4AΔ` (`T ≥ 2`), `T⁶A² ≤ 995328 a³Δ` (`T ≥ 12`), hence `T¹⁰ ≤ 63700992 a³Δ³` |
| `Main.lean` | dyadic decomposition, `P_le_of_visits` (window bounds `T^N ≤ K S(a) aʳ` with `S(a) ≪ a^η` give `P ≪ a^{r/N+ε}`), and the unconditional theorem `P_le` |
| `SixStep.lean` | the six-step identity `q w L = J E + S F`, `L ≥ 1` (exported as `Lz_pos` in `TwentyThreeMain.lean`), and `six_step_bound`: `T⁶A² ≤ 96·10⁶ a³` for `T ≥ 10` |
| `ShortSum.lean` | the drop count `T ≤ 2 ∑_{a<n≤a+Y} #{d ∣ n : A ≤ d < 2A}` |
| `Geometric.lean` | `∑_k min(α 2^{−k/3}, β 2^{k/2}) ≤ 9 α^{3/5} β^{2/5}`, and the general form `∑_k min(α 2^{−sk}, β 2^{tk}) ≪ α^{t/(s+t)} β^{s/(s+t)}` (`sum_min_le_gen`) |
| `Conditional.lean` | any short-interval divisor bound `≪ y G(x)` for `x^{1/4} ≤ y ≤ x`, with `1 ≤ G(x) ≪ x^{1/40}`, gives `P ≪ a^{3/10} G(a)^{1/5}` (`P_le_of_shortDivisorBound`) |
| `Rises.lean` | the arithmetic-progression bound `q⁴ ≤ 324 h³ a`, runs, the multiplicity lemma, and the three window bounds |
| `RisesMain.lean` | `P_le_rises`: `P ≪ a^{1/4} √R` |
| `Hankel.lean` | the moment model, `I_r(i) ∈ ℤ_{>0}` (`hankelInv_pos_int`), and `I₁ = b`, `I₂ = d`, `I₃ = D`, `I₄ = L` |
| `Hadamard.lean` | Hadamard's inequality `det G ≤ ∏ Gᵢᵢ` for positive definite real matrices |
| `Functional.lean` | the moment functionals `μᵢ`, `νᵢ` on polynomials, the Newton basis, shift rules, `νᵢ(f²) ≤ μᵢ(f²)/qᵢ` |
| `Gram.lean` | `Iᵣ(i) ≤ a ∏ⱼ μᵢ(Fⱼ²)/qᵢʳ`, and the label bound `L(i) qᵢ⁴ ≤ a · gramP` |
| `TwoState.lean` | the cofactors, null relations, reduced quadratic, the multiplicity identity, root counting |
| `PatternBound.lean` | the seven pattern integers are `≤ 172032 A⁴H⁶/a³` under the scale condition |
| `PatternCount.lean` | the counting lemma `#G ≤ 8 (2M+1)⁷ H²` |
| `TwentyThreeMain.lean` | good starts, the window theorem, `T⁷⁷ ≤ C Δ²² a²³`, and `P_le_23_77` |
| `NormCount.lean` | the norm-equation lemma: square roots mod `m` (`≤ τ(m)²`), norm-one separation, and `norm_count` |
| `SliceCount.lean` | the slice lemma: slices of a ternary quadratic via completing squares, for either sign of the binary discriminant (`slice_count_ne`, `slice_count`) |
| `ElevenCount.lean` | the sign identities, the ternary relation `F_θ(k₁,k₂,k₃) = 0`, and the refined count |
| `ElevenMain.lean` | the window bound, `T⁷⁴ ≤ C Δ¹⁹ Ξ¹⁹ a²²`, slack factors `≪ a^η`, and `P_le_11_37` |
| `MinorCount.lean` | the Plücker relations, the congruence count `27 m g²`, and `minor_vector_count` |
| `MinorHeight.lean` | the expansion of `b/a` (`nu_expand`) and the uniform bound on all ten minors |
| `EightMain.lean` | the pattern as signed minors, the window bound, `T⁵⁴ ≤ C Δ¹⁴ Ξ²⁸ a¹⁶`, and `P_le_8_27` |
| `DefiniteNorm.lean` | the definite norm count: `x² + δy² = m` has `≤ 4τ(|m|)³` solutions |
| `Reduce3.lean` | reduced bases of lattices in `ℤ³`: `27 |b₁|²|b₂|²|b₃|² ≤ 64 det²`, and coordinate bounds |
| `TernComp.lean` | ternary quadratics under substitution, the plane choice, and the slice count for a coefficient vector |
| `ShortVec.lean` | the lifting identities, the lattice `Λ_p`, the pigeonhole bound, and `short_count` |
| `LatticeCount.lean` | coordinates in a reduced basis (`ycoord_spec`), the gap vectors of one minor vector (`lattice_fiber_count`), and `pattern_count_lattice` |
| `FortyFiveMain.lean` | partial summation, the window bound `T³ ≤ C Ξ⁹ (H³X¹⁴ + X¹⁵)`, `T¹⁵² ≤ C Δ³⁹ Ξ¹¹⁷ a⁴⁵`, and `P_le_45_152` |
| `Hooley.lean` | Erdős–Hooley `Δ`, the hypotheses `NairTenenbaumDelta` and `BretecheTenenbaumMean`, partial summation, and `P_le_loglog` |

## Vendored code

`vendor/openai-math/` is a path-required Lake package. It contains a single file from
[openai/math](https://github.com/openai/math) (Apache-2.0): the divisor bound
`τ(n)^k ≤ C_k n` (`exists_divisors_power_bound`). Proof bodies are unchanged; imports and
module visibility are adapted. The upstream commit and changes are recorded in
[UPSTREAM.md](vendor/openai-math/UPSTREAM.md).

## Palomar submission

[Challenge.lean](Challenge.lean) independently states all eight main results using only
Mathlib imports and complete mathematical definitions. Its eight theorem proofs are
deliberate holes. [Solution.lean](Solution.lean) exposes the original proved declarations;
neither module imports the other. [comparator.json](comparator.json) selects the results,
and [formalization.yaml](formalization.yaml) records their scope, provenance, automation,
and review status. This repository is the substantive development, not a thin wrapper.

Run the local preparation checks:

```sh
python3 scripts/check-lean-sources.py
python3 scripts/check-math.py
lake exe cache get
lake build
```

On Linux with `bubblewrap` installed, run `bash scripts/verify-comparator.sh` to compare
the statements and proofs using Lean's kernel, NanoDa, and con-ron. The GitHub Actions
workflow runs these checks. The standard sandboxed Comparator needs Linux; a successful
macOS Lean build alone does not establish a Palomar verification pass.

The intended public repository is `jasondavies/pierce-length-bound`. Before submission,
confirm the automation and review account in `formalization.yaml`, push all intended
changes there, and obtain the full commit SHA with `git rev-parse HEAD`.
Run **Full Palomar mechanical preflight** from the repository's Actions tab on that
revision. It uses Palomar's pinned reusable workflow in `full` mode with the
`palomar-standard-v1` execution profile. Require `status: pass` in its mechanical report;
the ordinary CI build and standalone Comparator are not a substitute for this check.
This preflight does not perform editorial review or register the result.

`scripts/check-math.py` independently checks the moment construction and local identities using
exact rational arithmetic on 2,274 deterministic sample orbits. It supplements the formal proof;
finite numerical checks do not establish the asymptotic bounds.

Submit that immutable revision with the repository root as the
project and the default `comparator.json` and `formalization.yaml` paths. See
[Palomar's requirements](https://palomar-registry.org/how-to-submit) and the
[submission form](https://submit.palomar-registry.org/). Agents should use the
[documented HTTPS protocol](https://submit.palomar-registry.org/llms.txt), not drive the form.
Repository preparation does not itself submit or register a result.

## Hexagon submission

After Palomar registration, cite the versioned Palomar record in the paper and rebuild the PDF.
[Hexagon](https://hexagonmath.org/about) accepts TeX source and links to formalization artifacts;
it does not accept Lean code in the upload. This paper is self-contained in
`paper/pierce_length_bound.tex`, including its bibliography, so that file alone is the source package.
The contributor must sign in with an ORCID iD, select the distribution license, and complete
the AI-use and human-understanding disclosures. The paper and metadata identify GPT-6-Astra;
the contributor should describe their own understanding and review accurately.

## Licence

Copyright 2026 Jason Davies. Licensed under the Apache License, Version 2.0; see
[LICENSE](LICENSE). The vendored file keeps its own Apache-2.0 licence
([vendor/openai-math/LICENSE](vendor/openai-math/LICENSE)).
