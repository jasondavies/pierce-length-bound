# Hankel determinants and the length of finite Pierce expansions

Paper: [`paper/pierce_length_bound.pdf`](paper/pierce_length_bound.pdf). This repository
contains the paper and its complete Lean formalization.

For integers `a > b > 0` let `b₀ = b` and `b_{i+1} = a mod bᵢ` until zero.
Let `P(a, b)` be the number of positive terms
([Open Problem Garden](https://www.openproblemgarden.org/op/a_discrete_iteration_related_to_pierce_expansions)).
Shallit asked whether `P(a, b) = O((log a)²)`. That question is **still open**. This repository
proves, uniformly in `0 < b < a`:

* **Strongest unconditional bound:** `P(a, b) ≤ C_ε · a^{β* + ε}`, where
  `β* = (41301 − 3√82849)/137480 = 0.2941336553…`, and its rational instance `4317/14677 + ε`.
  The coefficient-uniform affine-curve theorem and the effective Hilbert specialization
  sieve are both proved inputs.
* **Exterior-lattice bounds:** `γ* = 471/1559 − 6√105/7795 = 0.2942294157…`,
  and its rational instance `153/520 + ε`.
* **Joint-invariant bounds:** `α* = (1310 − √655)/4365 = 0.2942513246…`, and the rational
  versions `2201/7480 + ε` and `128/435 + ε`.
* **Earlier lattice bound:** `45/152 + ε`.
* **Earlier steps:** `P(a, b) ≤ C_ε · a^{8/27 + ε}`, before that `a^{11/37 + ε}`, and before
  that `a^{23/77 + ε}`.
* **The `3/10` bound:** `P(a, b) ≤ C_ε · a^{3/10 + ε}`, improving Chase–Pandey's
  `a^{1/3 − 2/177 + ε}`. Its six-step identity is an ingredient of the main theorem.
* **Assuming two published theorems:** `P(a, b) ≪ a^{3/10} √(log log 3a)`. The theorems are
  Nair–Tenenbaum, Acta Math. 180 (1998), on short sums of the Erdős–Hooley `Δ`-function, and
  de la Bretèche–Tenenbaum, Acta Arith. 219 (2025), Thm 1.1, `∑_{n≤x} Δ(n) ≪ x (log log x)^{5/2}`.
  Both are stated in Lean as explicit hypotheses. Their proofs are not formalized.
* **Structured trajectories:** `P(a, b) ≪ a^{1/4} √R`, where `R − 1` is the number of rises
  `kᵢ < k_{i+1}` in the quotient increments. In particular nonincreasing increments give
  `P(a, b) ≪ a^{1/4}`.
* **The Hankel hierarchy:** an exact positive moment model of the orbit gives positive integer
  invariants `I_r(i)` (Hankel determinants) for every `r`, with `I₁ = bᵢ`, `I₂ = dᵢ`, `I₃ = D`
  and `I₄ = L` in the nonterminal ranges specified in the paper. In particular the last two
  identities require `i + 3 < P(a,b)` and `i + 5 < P(a,b)`, respectively, with zero-based indexing.

## Polar projection and the arithmetic sieve

[`PolarProjectionMain.lean`](PierceLengthBound/PolarProjectionMain.lean) proves the polar exponent
`β*` and its rational instance `4317/14677`. The exact orbit identity `Ψ W = N₀ V`, with
`V = Gk + ℓ` (rank-five form `J W = N₀² V`), identifies the projective curvature
coordinates with linear forms. Their residue-weighted common-base contribution is at
most four. On the good degree-24 components this gives
the powered graph degree bound `60n+56m`.

The branch condition comes from an explicit degree-12 polynomial whose roots specialize
to labels in the residue fields at infinity. A coefficient-uniform effective
Hilbert irreducibility theorem is proved in
[`BranchSieveMultivariateHilbert.lean`](PierceLengthBound/BranchSieveMultivariateHilbert.lean),
using CCDN, integer factor-height bounds, universal resolvents, integral specialization,
Kronecker substitution and induction over the parameters. It bounds the bad four-label
vertices uniformly in the dividend and their common divisor. The completion count
transfers this saving to full patterns: they are covered by eight signed pivot charts on
the first-four-column minors, and common divisors enter through the dilation.
The [reusable Hilbert irreducibility entry points](#reusable-hilbert-irreducibility)
are listed separately below.

A fixed proper exceptional polynomial handles the local geometric exclusions. Its
pattern count is `K (1 + τ_max(X)²) X^(14/3)`, hence `O(X^(14/3+ε))`. Summing the curve
estimates proves the six-term window bound and hence the polar exponents.
The paper's section “Exact polar projection and the branch sieve” presents the argument.

## Repository layout

* `PierceLengthBound/` and `PierceLengthBound.lean`: the Lean 4 / Mathlib proofs of the results
  and explicitly conditional reductions above, with no `sorry`. The [module maps](#module-maps) below locate each step.
* `Challenge.lean`, `Solution.lean`, `comparator.json`: the independent statements, the proved
  declarations, and the Comparator configuration for [Palomar](#palomar-submission).
* `Axioms.lean`: the axiom audit, built by `lake build`.
* `formalization.yaml`: Palomar metadata (scope, provenance, automation, and review status).
* `paper/pierce_length_bound.tex` (and `.pdf`): the paper.
* `scripts/`: source, metadata, dependency, and exact-arithmetic checks.
* `.github/workflows/`: `ci.yml` checks metadata, builds and audits the proofs, and runs
  Comparator on pushes and pull requests; `palomar-preflight.yml` runs the manual
  Full Palomar mechanical preflight (see
  [Palomar submission](#palomar-submission)).
* `vendor/openai-math/`: one vendored file, described under [Dependencies](#dependencies).

## Main theorem statements

```lean
theorem PierceLengthBound.P_le_polar_optimal : ∀ ε > (0 : ℝ), ∃ C > 0,
    ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ (((41301 : ℝ) - 3 * Real.sqrt 82849) / 137480 + ε)

theorem PierceLengthBound.P_le_4317_14677 : ∀ ε > (0 : ℝ), ∃ C > 0,
    ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((4317 : ℝ) / 14677 + ε)

theorem PierceLengthBound.P_le_lattice_optimal : ∀ ε > (0 : ℝ), ∃ C > 0,
    ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((471 : ℝ) / 1559 - 6 * Real.sqrt 105 / 7795 + ε)

theorem PierceLengthBound.P_le_153_520 : ∀ ε > (0 : ℝ), ∃ C > 0,
    ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((153 : ℝ) / 520 + ε)

theorem PierceLengthBound.P_le_joint_optimal : ∀ ε > (0 : ℝ), ∃ C > 0,
    ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ (((1310 : ℝ) - Real.sqrt 655) / 4365 + ε)

theorem PierceLengthBound.P_le_2201_7480 : ∀ ε > (0 : ℝ), ∃ C > 0,
    ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((2201 : ℝ) / 7480 + ε)

theorem PierceLengthBound.P_le_128_435 : ∀ ε > (0 : ℝ), ∃ C > 0,
    ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((128 : ℝ) / 435 + ε)

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

## Building and checking

The project uses Lean `v4.35.0` and Mathlib `v4.35.0`. The curve-counting library is the Lake
package `ccdn_dimension_growth`, a Git dependency on
[`jasondavies/ccdn-linear-growth`](https://github.com/jasondavies/ccdn-linear-growth) pinned in
`lakefile.toml` to commit `9ade6200d053ceef5f6ccc4154ae30c6056be150`. The package name differs
from the repository name because CCDN's own `lakefile.toml` still declares its original name,
which the requirement must match. `lakefile.toml` is the source of truth for the pin:
`scripts/check-curve-counting-dependency.py` checks that `lake-manifest.json`, this README,
`formalization.yaml` and the paper agree with it, and with `--checkout` that the fetched checkout
uses the same Lean toolchain and Mathlib revision as this project. Lake fetches the dependency into
`.lake/packages`.

The check scripts require Python 3.11+ (standard library only, except the three SymPy scripts
marked below). CI runs the source and metadata checks, Lean build and axiom audit,
dependency checks, and the fifteen-statement Comparator check. The supplementary polar
replay, exact-arithmetic checks, and paper build are manual release checks.

Build and check, in order:

```sh
python3 scripts/check-lean-sources.py                       # source layout
python3 scripts/check-theorem-lists.py                      # selected theorem lists agree
python3 scripts/check-curve-counting-dependency.py          # CCDN pin metadata
lake exe cache get                                          # download compiled Mathlib
lake build
python3 scripts/check-curve-counting-dependency.py --checkout
python3 scripts/check-weighted-count-dependencies.py
bash scripts/verify-comparator.sh                           # Linux with bubblewrap only
python3 scripts/verify-polar-kernels.py                     # manual: additional polar proof replays
```

* `lake build` runs Mathlib's standard linters (`weak.linter.mathlibStandardSet`) and builds the
  Palomar `Challenge` and `Solution` modules. The `sorry` warnings in `Challenge.lean`, one per
  selected theorem, are deliberate statement holes; the proof development has none.
* `lake build` also builds `Axioms.lean` (or run `lake env lean Axioms.lean`). Its `#guard_msgs`
  checks show that every theorem in `comparator.json` depends only on `propext`,
  `Classical.choice` and `Quot.sound`, and it audits every exported declaration of
  `PierceLengthBound`, of CCDN, and of CCDN's vendored Bombieri–Vaaler development
  (`ArithmeticHeights`) for nonstandard axioms. `P_le_loglog` depends on the two analytic papers
  only through its hypotheses.
* `scripts/check-theorem-lists.py` checks that `comparator.json`, `Challenge.lean`,
  `Axioms.lean`, `formalization.yaml` and the Lean block under
  [Main theorem statements](#main-theorem-statements) list the same theorems in the same order.
* `scripts/check-weighted-count-dependencies.py` checks which weighted lattice counts the main
  bounds reach; the audited roots and the banned and required declarations are listed in the
  `AUDIT` Lean block of the script.
* `scripts/verify-comparator.sh` compares the statements and proofs with Lean's kernel, NanoDa
  and con-ron, as Palomar does. The sandboxed Comparator needs Linux; a successful macOS Lean
  build alone does not establish a Palomar verification pass.

`scripts/verify-polar-kernels.py` exports thirty-two additional principal polar results,
including the common-base bound, pattern count, effective Hilbert theorem,
arithmetic sieve, graph-degree reduction and global reductions, and replays their proofs with Lean,
NanoDa and con-ron at their standard settings.
This is an additional proof check; these statements are not compared with an independent
Challenge and remain outside the fifteen selected Comparator statements.

Exact-arithmetic checks supplement the formal proof; finite numerical checks do not establish
the asymptotic bounds. `scripts/check-math.py` (standard library only) checks the moment
construction and local identities with exact rational arithmetic on 2,274 deterministic sample
orbits. Three further scripts require SymPy:

```sh
python3 scripts/check-math.py
python3 scripts/check-fixed-dividend.py                     # requires SymPy
python3 scripts/check-fixed-dividend-lines.py               # requires SymPy
python3 scripts/check-polar-projection.py                    # requires SymPy
```

Rebuild the paper with a TeX installation that provides `latexmk` and `pdflatex`,
keeping intermediate files outside `paper/`:

```sh
latexmk -pdf -outdir=/tmp/pierce-paper -interaction=nonstopmode -halt-on-error paper/pierce_length_bound.tex
```

Inspect `/tmp/pierce-paper/pierce_length_bound.pdf`, then copy it to
`paper/pierce_length_bound.pdf` for the release.

The latest verification run is recorded in `review.notes` of
[formalization.yaml](formalization.yaml). It is an agent review, not an independent human
review, and the full Palomar mechanical preflight is still outstanding.

## Proof outlines

### The `3/10` bound and the pattern bounds

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
(pigeonhole). A reduced basis with `27|b₁|²|b₂|²|b₃|² ≤ 64 det²`, built by minimizing the
determinant, then `|b₁|²`, then a Gram determinant (integer arithmetic only), gives coordinates
`λ(p)|yᵢ| ≤ 3H`. After a plane choice the slice count applies to `F_θ` in those coordinates,
with definite slices handled by a definite norm count. So one minor vector covers
`O((H/λ(p) + 1) a^η)` gap vectors. Only `≪ R³X⁴τ²` minor vectors have `λ(p) ≤ R`, and partial
summation gives `T ≪ a^η (H X^{14/3} + X⁵)`, hence `T¹⁵² ≪ a^{45+O(η)}`.

### Exterior-lattice refinement

The drop and gap rows of a start lie in the rank-three lattice `Λ_p` of its pattern. In a
reduced basis the nodes have coordinates of size `H/λ(p)`, and the curvature coordinates, as
`2×2` minors, have integer exterior coordinates of size `S/λ(p)²`. These are constant invertible
linear changes of the old coordinates, so the joint graph keeps its degree `≥ 10n + 7m`. Summing
over patterns with `∑_p λ(p)^{-t} ≪ a^{o(1)} X^{5-t/3}` (`0 ≤ t ≤ 1`) gives a five-term window
bound with exponents `5/17`, `45h/(153h−1)`, `(45h−3m)/(153h−11m)` and `(15h+6n)/(51h+20n)`,
`h = 10n + 7m`, where `m` and `n` are the powers of the curvature coordinates and of the
rank-five invariant. The choice `(m, n) = (3, 2)` gives `153/520`, and optimizing `n/m` at
`√105/15` gives `γ*`.

Unlike the joint-invariant bounds, these use weighted lattice counts: the short-vector count
`short_count` and the reciprocal weight bound `reciprocal_sum_bound`. The weighted-count
dependency audit checks that these are the only weighted counts they reach.

### Joint-invariant refinement

The joint lift adjoins three integer curvature minors `W` and the positive integer rank-five
invariant `I₅ = I₄ Ψ` (`J = N₀ Ψ`) to the three gap coordinates of a pattern. Over each prime component of the
pattern curve these seven coordinates define a graph, and all selected states with the same
minor pattern are integer points of that graph in a uniform box. The ordinary `X⁵` pattern
count suffices, with subpolynomial divisor slack; no weighted-lattice count is used.

The geometric core is a lower bound for the graph degree `δ`. Over a nonexceptional component
of Hilbert degree `d`, exact orders on the normalization give the rank-five coordinate poles of
order `5e/2` at the old infinity branches. A transcendental curvature combination has an extra
finite zero, which forces its pole envelope to have degree at least `(3d + 2)/2`, and these
curvature poles lie on branches distinct from the old infinity poles. Together they give
`4d + 1 ≤ δ ≤ 247d`, hence `δ ≥ 17` when `d ≥ 4`. Lines are excluded at the window scale,
conics and bounded polynomial cuts are counted separately, and exceptional patterns contribute
`O(X⁴ log 2X)`. The affine-curve count on these graphs gives `128/435 = 0.2942528735…`.

Raising the curvature coordinates to a power `m` and the rank-five invariant to a power `n`
gives a graph of degree `δ ≥ 10n + 7m` when `d ≥ 4`. Optimizing the two resulting exponents
gives `α* = (1310 − √655)/4365 = 0.2942513246…`, and `m = 50`, `n = 51` gives `2201/7480`.

### External curve counting

The coefficient-uniform affine-curve theorem is proved in
[`ccdn-linear-growth`](https://github.com/jasondavies/ccdn-linear-growth). `CCDN.affineCurveBound`
gives `C(n) * d³ * B^(1/d) * (log B + d)` for every prime affine curve over `ℚ` in ambient
dimension `n ≥ 2`, using its affine Hilbert degree and every real `B ≥ 1`. Its proof
includes the plane theorem, bounded degree-preserving projections, and uniform box rescaling.
There is no external counting hypothesis.

## Module maps

All modules are in `PierceLengthBound/`; the `.lean` extension is omitted.

### Reusable Hilbert irreducibility

These theorems apply to general monic integer polynomial families, without orbit or
branch assumptions. Their constants depend only on the degree bounds and number of
parameters. They live in the namespace `PierceLengthBound.FixedDividend`.

| Entry point | Module |
|---|---|
| `branch_uniform_monic_hilbert_bound`: one integer parameter, uniform total-degree bound | [`BranchSieveMonicHilbert`](PierceLengthBound/BranchSieveMonicHilbert.lean) |
| `branch_multivariate_monic_hilbert_bound`: any fixed number of integer parameters, bounded root degree and coefficient total degrees | [`BranchSieveMultivariateHilbert`](PierceLengthBound/BranchSieveMultivariateHilbert.lean) |

The application to Pierce patterns starts in
[`BranchSieveVertexMonic`](PierceLengthBound/BranchSieveVertexMonic.lean), which constructs
the monic family and proves its generic irreducibility.
[`BranchSieveArithmeticVertexCount`](PierceLengthBound/BranchSieveArithmeticVertexCount.lean)
then applies the general estimate uniformly in the dividend and common divisor.

### Core and earlier bounds

| Module | Contents |
|---|---|
| `Defs` | `P`, the orbit `orb`, `P ≤ b` (`P_le_self`), the quotients `qq` with `bᵢqᵢ + bᵢ₊₁ = a` and strict monotonicity (`qq_lt`, `qq_strictMono`); check `P 35 22 = 7` |
| `Block` | curvature `D = dv − eu`: identity `Dz = df + ude + (u−1)e²`, `D ≥ 1`, fiber equation `x M(q) = a N(q) + D`, size bounds |
| `Fiber` | a fixed `(u, v, D)` allows at most `max_{n ≤ 32a⁷} τ(n)` starting points |
| `Window` | for a run of `T` terms in `[A, 2A)`: its quotient increments and drops and their telescoping sums, the shared estimates `le_four_mul`, `lt_three_mul`, `drop_bound_sq` and `gap_height_mul_le`, `T(T−1) ≤ 4AΔ` (`T ≥ 2`), `T⁶A² ≤ 995328 a³Δ` (`T ≥ 12`), hence `T¹⁰ ≤ 63700992 a³Δ³` |
| `Main` | dyadic decomposition (`visits_run`), `P_le_of_real_visits` and `P_le_of_visits` (window bounds `T ≤ S(a) a^α`, or `T^N ≤ K S(a) aʳ`, with `S(a) ≪ a^η` give `P ≪ a^{α+ε}`, resp. `a^{r/N+ε}`), and the unconditional theorem `P_le` |
| `PolarProjectionMain` | the optimized polar bound and `4317/14677`; assembles the arithmetic sieve, geometry and six-term window estimate |
| `PolarProjectionWindow`, `PolarProjectionBound` | the six-term window reduction and the global polar bounds |
| `PolarProjectionRetainedBase`, `PolarProjectionRetainedDegree` | common-base contribution at most four and the retained powered graph degree bound `60n+56m` |
| `PolarProjectionGeometryGoodPattern` | explicit branch irreducibility and the fixed proper exceptional polynomial imply the good-pattern geometric estimate |
| `BranchSieveVertexMonic`, `BranchSieveArithmeticVertexCount` | the integer degree-12 family, generic irreducibility, specialization compatibility and uniform scaled-vertex sieve |
| `BranchSievePatternCount`, `BranchSievePatternCountSlow` | completion to full minor patterns with all common divisors and the slow-growth bound on selected orbit windows |
| `HypersurfacePatternCount`, `HypersurfacePatternCountSlow` | proper algebraic exceptional loci have pattern count `K (1 + τ_max(X)²) X^(14/3)`, hence exponent `14/3 + ε` |
| `SixStep` | the six-step identity `q w L = J E + S F`, `L ≥ 1`, the window preamble `window_facts`, and `six_step_bound`: `T⁶A² ≤ 96·10⁶ a³` for `T ≥ 10`, hence `T⁴ ≤ 122449 a` when `AT > 28a` (`window_large_mean_gap`) |
| `ShortSum` | the drop count `T ≤ 2 ∑_{a<n≤a+Y} #{d ∣ n : A ≤ d < 2A}` |
| `Geometric` | `∑_k min(α 2^{−k/3}, β 2^{k/2}) ≤ 9 α^{3/5} β^{2/5}`, and the general form `∑_k min(α 2^{−sk}, β 2^{tk}) ≪ α^{t/(s+t)} β^{s/(s+t)}` (`sum_min_le_gen`) |
| `Conditional` | any short-interval divisor bound `≪ y G(x)` for `x^{1/4} ≤ y ≤ x`, with `1 ≤ G(x) ≪ x^{1/40}`, gives `P ≪ a^{3/10} G(a)^{1/5}` (`P_le_of_shortDivisorBound`) |
| `Rises` | the arithmetic-progression bound `q⁴ ≤ 324 h³ a`, runs, the multiplicity lemma, and the three window bounds |
| `RisesMain` | `P_le_rises`: `P ≪ a^{1/4} √R` |
| `Hankel` | the moment model, `I_r(i) ∈ ℤ_{>0}` (`hankelInv_pos_int`), the real increments `kk` (with `kv a b i j = kk a b (i + j)`), and `I₁ = b`, `I₂ = d`, `I₃ = D`, `I₄ = L` |
| `Hadamard` | Hadamard's inequality `det G ≤ ∏ Gᵢᵢ` for positive definite real matrices |
| `Functional` | the moment functionals `μᵢ`, `νᵢ` on polynomials, the Newton basis, shift rules, `νᵢ(f²) ≤ μᵢ(f²)/qᵢ` |
| `Gram` | `Iᵣ(i) ≤ a ∏ⱼ μᵢ(Fⱼ²)/qᵢʳ`, and the label bound `L(i) qᵢ⁴ ≤ a · gramP` |
| `TwoState` | the cofactors, null relations, reduced quadratic, the multiplicity identity, root counting |
| `PatternBound` | `state_bound`: the four pattern integers of a state are `≤ 172032 A⁴H⁶/a³` under the scale condition (applied at `i` and `i+1` for all seven) |
| `PatternCount` | the counting lemma `#G ≤ 8 (2M+1)⁷ H²` |
| `OrbitPattern` | the orbit-state vocabulary: the integer increments and drops `kq`, `dq`, the six-step integer `Lz` (`Lz_pos`), the cofactors `U1z`, `U2z`, the pattern `theta` and gaps `kap` with their identities (`e0_at`, `e3_at`, `mult_at`), the good starts (`good_card`, `goodStarts`) and their pattern hypotheses (`PatternHyps`, `goodStarts_patternHyps`), and the matrix `𝓜ᵢ` (`Mi`) with the pattern as signed minors (`projθ`, `theta_eq`, `orbit_pattern_first`) |
| `TwentyThreeMain` | the label bound in window form, the pattern height at good starts, the window theorem, `T⁷⁷ ≤ C Δ²² a²³`, and `P_le_23_77` |
| `NormCount` | the norm-equation lemma: square roots mod `m` (`≤ τ(m)²`), norm-one separation, and `norm_count` |
| `SliceCount` | the slice lemma: slices of a ternary quadratic via completing squares, for either sign of the binary discriminant (`slice_count_ne`, `slice_count`) |
| `ElevenCount` | the sign identities, the ternary relation `F_θ(k₁,k₂,k₃) = 0`, and the refined count |
| `ElevenMain` | the slack factor `XiOf c e ≪ a^η` of a polynomial range, the window bound, `T⁷⁴ ≤ C Δ¹⁹ Ξ¹⁹ a²²`, and `P_le_11_37` |
| `MinorCount` | the Plücker relations (over any commutative ring, with Mathlib's `⨯₃`), the cross congruence (`cross_cong`), the congruence count `27 m g²`, and `minor_vector_count` |
| `MinorHeight` | the expansion of `b/a` (`nu_expand`) and the uniform bound on all ten minors |
| `EightMain` | the window bound with minor vectors, `T⁵⁴ ≤ C Δ¹⁴ Ξ²⁸ a¹⁶`, and `P_le_8_27` |
| `DefiniteNorm` | the definite norm count: `x² + δy² = m` has `≤ 4τ(\|m\|)³` solutions |
| `Reduce3` | reduced bases of lattices in `ℤ³`: `27 \|b₁\|²\|b₂\|²\|b₃\|² ≤ 64 det²`, and coordinate bounds |
| `TernComp` | ternary quadratics under substitution, the plane choice, and the slice count for a coefficient vector |
| `ShortVec` | the lifting identities, the lattice `Λ_p`, the pigeonhole bound, and `short_count` |
| `LatticeCount` | coordinates in a reduced basis, the gap vectors of one minor vector (`lattice_fiber_count`), and `pattern_count_lattice` |
| `CubeRoot` | a cube root `X ≤ L³ ≤ 8X` (`exists_cube_root`) and the telescope `1/r = 1/L + ∑_{r≤j<L} 1/(j(j+1))` (`inv_telescope`) |
| `FortyFiveMain` | partial summation, the window bound `T³ ≤ C Ξ⁹ (H³X¹⁴ + X¹⁵)`, `T¹⁵² ≤ C Δ³⁹ Ξ¹¹⁷ a⁴⁵`, and `P_le_45_152` |
| `Hooley` | Erdős–Hooley `Δ`, the hypotheses `NairTenenbaumDelta` and `BretecheTenenbaumMean`, partial summation, and `P_le_loglog` |

### Exterior-lattice chain

[`LatticeJointMain`](PierceLengthBound/LatticeJointMain.lean) exports `P_le_lattice_optimal` and
`P_le_153_520`. The chain also uses `short_count` (`ShortVec`), `reciprocal_sum_bound`
(`FixedDividendWeights`), and the joint-invariant graph, component and curve-counting modules
below.

| Module | Contents |
|---|---|
| `LatticeExterior` | integer exterior coordinates in a reduced basis: `bᵢ·(x×y) = Δcᵢ`, `27λ⁴cᵢ² ≤ 64\|x×y\|²` (`wcoord_spec`) |
| `LatticeCurvature` | all ten curvature minors `≤ 9472A³H³/a²`, and `c = G W` with `det G ≠ 0` (`lattice_curvature_coordinates`) |
| `LinearJointGraph` | invertible constant matrices preserve pole envelopes; the graph of `(nodes, (GW)ᵐ, Jⁿ)` keeps degree `≥ 10n + 7m` (the powered graph is the case `G = 1`) |
| `LatticeJointPointCount` | the points `(y, cᵐ, Jⁿ)` in the pattern box `max(3H/λ, (8S'/3λ²)ᵐ, Yⁿ)`, and the curve count there |
| `LatticeJointPatternCount` | the component count in the lattice box; pattern counts from `JointPatternCount` |
| `LatticeJointWeights` | `∑_p λ(p)^{-t} ≤ 3163861 τ² X^{5-t/3}` for `0 ≤ t ≤ 1` |
| `LatticeJointLocalEstimate` | the five-term local estimate; its lattice-weight summation is shared with the polar six-term estimate |
| `LatticeJointWindow` | integer-power branches and the window exponents |
| `LatticeJointBound` | `P_le_lattice_joint` for all powers, and `P_le_153_520` |
| `LatticeJointOptimization` | the crossing `15r² = 7` and `P_le_lattice_optimal` |

### Joint-invariant chain

[`JointLiftMain`](PierceLengthBound/JointLiftMain.lean) exports `P_le_joint_optimal`,
`P_le_2201_7480` and `P_le_128_435`.

| Module | Contents |
|---|---|
| `JointLiftAlgebra` | curvature reconstruction and dot-product identities; `I₅ = I₄ Ψ`, with positivity and integrality |
| `JointLiftCurvatureHeight` | first-order reciprocal expansion; `\|W_j\| q³ ≤ 68 a H³` for all three curvature coordinates |
| `JointLiftRankFiveHeight` | the Newton Gram product bound `1230460 H¹⁰`, the rank-five height, and its floored selected box |
| `JointLiftCoordinates`, `JointLiftFieldCoordinates` | polynomial graph coordinates with a common denominator, agreeing with the rational curvature formulas |
| `JointLiftGraph` | the prime ideal of a rational graph; its contraction to the old coordinates is the original prime |
| `JointLiftGraphDegree` | upper Hilbert-degree bounds (at most `247d`) from common-denominator formulas |
| `JointLiftPointBox` | selected states with one minor pattern as integer points of the graph in a uniform box |
| `JointLiftDirection` | nonconstancy of the projective curvature direction on components of degree at least three of an irreducible quadric |
| `JointLiftCurvatureNonvanishing` | the extra finite zero of a curvature combination |
| `FixedDividendPolynomialSection` | at most `m·d` points on a proper degree-`m` polynomial cut |
| `JointLiftNormalizationCut`, `JointLiftResolventCut`, `JointLiftRetainedIdentities` | the normalization and raw-resolvent cuts, of degrees at most 166 and 404, and the identities they impose on retained components |
| `JointLiftInfinityOrder` | rank-five pole order `5e/2` and even infinity multiplicity at every valuation centered on the nonexceptional chart |
| `JointLiftQuotientOrder`, `JointLiftLocalOrders` | quotient, resolvent and curvature orders from their local inputs |
| `ChartNodeUnits`, `ChartRawDeterminantOrders` | exact node-difference orders from the resultant unit; orders `−3e` for both consecutive cubic determinants and `−6e` for the fourth |
| `JointLiftRetainedOrders` | quotient and rank-three orders from the retained normalization and resolvent equations |
| `JointLiftChartOrders` | orders `3t`, `≥ 3t`, `3t` and `−5t` of the four graph coordinates (`e = 2t`) |
| `AffineNormalization` | finite Dedekind normalization of the affine chart ring |
| `JointLiftNormalizedOrders` | normalized integer-valued branch orders, with the coordinate order calculations applied to them |
| `NormalizationInfinityDegree`, `NormalizedFiberOrders` | in a normalized parameter fiber, multiplicities times residue degrees sum to the fiber dimension and equal the canonical branch orders |
| `FunctionParameterNormalization`, `FunctionParameterChange` | the weighted zero fiber degree of a transcendental function is its field degree, and its reciprocal generates the same field; finite curve fraction fields are finite over every transcendental function |
| `IntegralBranchOrders`, `BranchValuationComparison`, `BranchResidueComparison` | centers on parameter normalizations; branch transport preserves normalized orders and residue degrees |
| `BranchZeroDegree` | the weighted zero-count inequality, including the extra degree from one additional zero |
| `JointLiftPoleCoverage`, `JointLiftPoleDegree` | every pole of a curvature combination lies on the affine normalization; its degree is bounded by the curvature pole envelope |
| `JointLiftFiniteZero` | the extra normalized zero, outside the old infinity fiber |
| `JointLiftCurvatureDegree` | `3d + 2 ≤ 2 deg(F)` for the curvature pole envelope on a retained component |
| `GraphFunctionField`, `ValuationLinearCombination`, `GraphPoleDegree` | the coordinate pole envelope is bounded by the graph Hilbert degree |
| `JointLiftGraphLowerDegree` | `4d + 1 ≤ δ` on retained graphs (the case `G = 1`, `m = n = 1` of `LinearJointGraph`), and `17 ≤ δ ≤ 247d` when `d ≥ 4` |
| `CurveCounting`, `CurveCountingDegreeRange`, `CurveCountingCoordinates` | the CCDN theorem on Pierce coordinate rings: bounded-degree factors and arbitrary finite index types (including `Fin 3 ⊕ Fin 4`) |
| `OrbitGapCoordinates` | the three node coordinates distinguish complete gap vectors within a pattern |
| `JointLiftPointCount`, `JointLiftCountingSlack` | the curve count on seven-coordinate integer points; the logarithm absorbed via the polynomial box bound |
| `OrbitConicGapCount` | the conic divisor estimate applied directly to distinct gap vectors |
| `OrbitCurveGapCount`, `OrbitPatternCurveCount` | the square-root count after excluding lines at the window scale |
| `JointLiftComponentCount` | conics, the two bounded cuts and retained graphs, in the unpowered box; used by the polar chain |
| `JointLiftExponent` | the selected curvature and rank-five boxes, and their products with powers of the window length |
| `JointLiftOptimization` | rational approximation of a crossing (`exists_rat_max_lt_of_crossing`), the optimal crossing, the minimum of the two exponent functions, and approximation by fixed integer powers |
| `PoweredJointGraph`, `PoweredPoleOrder` | the graph with coordinates `W_jᵐ` and `Jⁿ`, of degree at most `((m+n)·247+1)d`; powers multiply pole orders |
| `PoweredJointGraphLowerDegree` | `δ ≥ 10n + 7m` for `d ≥ 4`, the case `G = 1` of `LinearJointGraph` |
| `PoweredJointPointBox`, `PoweredJointPointCount` | integer points in the box `max(3H, Sᵐ, Yⁿ)` and the curve count there |
| `PoweredJointCountingSlack`, `PoweredJointComponentCount`, `PoweredJointLocalEstimate` | the powered logarithmic and counting inputs |
| `JointPatternCount` | from component counts to nonexceptional and per-pattern estimates, for any box and exponent; shared by the powered, lattice and polar chains |
| `JointPatternAssembly` | the window length bounded by the per-pattern estimate summed over the selected patterns, shared by the local estimates |
| `OrdinaryPatternCount` | the ordinary minor-pattern count `O(τ X⁵)`, the two-class pattern sum and the pattern slack, shared by the local estimates |
| `PoweredJointExponent`, `PoweredJointWindow`, `WindowRealReduction` | window ranges; `window_real_large_mean_gap`, `window_branch_exponent` and the window-constant bookkeeping `window_real_of_branch_power` are the window lemmas shared by the powered, lattice and polar chains (the earlier chains use `window_large_mean_gap` and `window_real_bound_of_power`) |
| `RealPowerBounds` | elementary real-power inequalities: concavity over a finite sum, powers of maxima, one dominant term among five |
| `PoweredJointBound` | the optimized exponent and its rational versions `m = 50`, `n = 51` (`2201/7480`) and `m = n = 1` (`128/435`) |

### Shared and supporting modules

| Modules | Contents |
|---|---|
| `FixedDividend*` | the fixed-dividend resultant identity, quadratic irreducibility, relative primality, a rational component cover of total degree at most 24, even degree of nonexceptional components, line exclusion, conic plane models, and filtered Hilbert-degree infinity charts |
| `Exceptional*` | the exceptional-pattern count `O(X⁴ log 2X)` |
| `IntegralLift*` | reconstruction of `I₃` from the cofactors of the eight-row moment system, the resolvent identities, monic quotient normalization, cubic quotient degree, and properness of the `I₃` lift after at most 492 exceptional points |
| `Conic*` | conic arithmetic, integer values of rational functions, and coefficient heights |
| `Chart*`, `Branch*` (other than `BranchSieve*`), `Normalization*`, `NormalizedBranchValuation`, `CurveNormalization`, `ParameterFiberDegree`, `LinearFunctionDegree` | chart and normalization infrastructure for branch orders and function-field degrees |
| `RationalNeighborhood`, `RationalNeighborhoodJet` | rational expressions cleared on a principal neighborhood of a rational point (`RationalNear`), and rational dependence of the first two coefficients of formal paths; used to build the exceptional polynomial `Θ` |
| `NewtonCoefficientDegrees`, `RawDeterminantTotalDegree`, `OrbitPatternGeometry` | coefficient degrees of the Newton quartic and raw determinants; transport of component data within a pattern |

## Dependencies

* [Mathlib](https://github.com/leanprover-community/mathlib4) `v4.35.0`.
* CCDN (`ccdn-linear-growth`), the curve-counting library described above and pinned as described
  under [Building and checking](#building-and-checking). It vendors the Bombieri–Vaaler
  development of `rwst/Subspace-Theorems` (as `ArithmeticHeights`) and adapts Mertens' first
  theorem, with provenance recorded in its vendor directory.
* `vendor/openai-math/` is a path-required Lake package. It contains a single file from
  [openai/math](https://github.com/openai/math) (Apache-2.0): the divisor bound
  `τ(n)^k ≤ C_k n` (`exists_divisors_power_bound`). Proof bodies are unchanged; imports and
  module visibility are adapted. The upstream commit and changes are recorded in
  [UPSTREAM.md](vendor/openai-math/UPSTREAM.md).

## Palomar submission

[Challenge.lean](Challenge.lean) independently states every theorem selected in
[comparator.json](comparator.json), using only Mathlib imports and complete mathematical
definitions; their proofs are deliberate holes. [Solution.lean](Solution.lean) exposes the
original proved declarations; neither module imports the other.
[formalization.yaml](formalization.yaml) records their scope, provenance, automation, and review
status. This repository is the substantive development, not a thin wrapper.

The intended public repository is `jasondavies/pierce-length-bound`. Before submission:

1. Run the [checks above](#building-and-checking), and confirm the automation and review account
   in `formalization.yaml`.
2. Push all intended changes, and obtain the full commit SHA with `git rev-parse HEAD`.
3. Run **Full Palomar mechanical preflight** from the repository's Actions tab on that revision.
   It uses Palomar's pinned reusable workflow in `full` mode with the `palomar-standard-v1`
   execution profile. Require `status: pass` in its mechanical report; the ordinary CI build and
   standalone Comparator are not a substitute. This preflight does not perform editorial review
   or register the result.
4. Submit that immutable revision with the repository root as the project and the default
   `comparator.json` and `formalization.yaml` paths. See
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

## License

Copyright 2026 Jason Davies. Licensed under the Apache License, Version 2.0; see
[LICENSE](LICENSE). The vendored file keeps its own Apache-2.0 license
([vendor/openai-math/LICENSE](vendor/openai-math/LICENSE)).
