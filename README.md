# Bounds for the iteration `x ↦ a mod x`

For integers `a > b > 0` let `b₁ = b`, `b_{i+1} = a mod bᵢ`, and let `P(a, b)` be the number of
positive terms ([Open Problem Garden](https://www.openproblemgarden.org/op/a_discrete_iteration_related_to_pierce_expansions)).
Shallit asked whether `P(a, b) = O((log a)²)`. That question is **still open**. This repository
proves, uniformly in `0 < b < a`:

* **Strongest bound:** `P(a, b) ≤ C_ε · a^{α* + ε}`, where
  `α* = (1310 − √655)/4365 = 0.2942513246…`. This is proved unconditionally,
  including the external coefficient-uniform affine-curve counting theorem.
* **Rational joint-lift bounds:** `2201/7480 + ε` and `128/435 + ε`.
* **Earlier lattice bound:** `45/152 + ε`.
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

## Joint-invariant refinement

The [original proof candidate](paper/pierce_joint_lift_proof_candidate.txt) proposed
`128/435 = 0.2942528735…`, followed by the powered-coordinate optimization
`(1310 − √655)/4365 = 0.2942513246…` and its rational approximation `2201/7480`.
It extends the [151/513 candidate](paper/pierce_151_513_proof_candidate.txt).
All three bounds are now proved unconditionally, including external curve counting.
[`JointLiftMain.lean`](PierceLengthBound/JointLiftMain.lean) exports the public
statements `P_le_joint_optimal`, `P_le_2201_7480` and `P_le_128_435`.
The manuscript and submission statements include these results.

The new joint lift adjoins three integer curvature minors and the positive
integer rank-five invariant `I₅ = A D` to the three gap coordinates. It uses
the ordinary `X^5` pattern count, with proved subpolynomial divisor slack.
No weighted-lattice counting estimate is used by any of the three joint-lift proofs.

`JointLiftAlgebra` proves the curvature reconstruction and dot-product identities
and the actual identity `I₅ = A D`, including positivity and integrality.
`JointLiftCurvatureHeight` proves the first-order reciprocal expansion and the
uniform bound `|W_j| q³ ≤ 68 a H³` for all three actual curvature coordinates.
`JointLiftRankFiveHeight` proves the Newton Gram product bound `1230460 H^10`,
the actual rank-five height, and its exact floored selected box.
`JointLiftCoordinates`, `JointLiftGraph`, `JointLiftGraphDegree` and
`JointLiftPointBox` construct the actual prime seven-dimensional graph, prove
its degree exists and is at most `247d`, and place all selected states with the
same minor pattern on that graph as integer points in a uniform box.
`JointLiftDirection` proves the algebraic nonconstancy of the projective
curvature direction on degree-at-least-three components of an irreducible quadric,
with an actual rational joint-graph specialization.
`JointLiftCurvatureNonvanishing` proves the curvature coordinates have no common
zero on the affine graph and constructs the extra finite zero of a nonzero
curvature combination. `FixedDividendPolynomialSection` proves the general
bound of `m*d` points for a proper degree-`m` polynomial cut. The actual
normalization and raw-resolvent cuts now have proved degrees at most 166 and
404, respectively, with corresponding bounds on supported states.
`JointLiftPatternCount` exports `P_le_128_435_of_pattern_estimate`, with the
ordinary and exceptional pattern sums, multiplicity bound, all window ranges,
rounding, divisor slack and dyadic summation proved. `JointLiftBound` discharges
both per-pattern estimates and exports the unconditional `P_le_128_435`.

`JointLiftOptimization` proves the exact optimal crossing, the minimum of the
two displayed exponent functions, rational approximation by fixed positive
integer powers, and the `m=50, n=51` calculation. `PoweredJointBound` applies
these results to the completed geometric and analytic estimates and proves
the optimized global Pierce bound.

The shared `FixedDividend*.lean` development proves the resultant identity,
quadratic irreducibility, relative primality, a rational component cover of total
degree at most 24, and even degree for nonexceptional components. The complete
exceptional-pattern count `O(X^4 log(2X))` is proved. The conic development now
derives bounded integer parameters, monic quotient normalization, cubic quotient
degree, and properness of the actual `I₃` function after at most 492 exceptional
points. The conic height and divisor-count development is recorded in the
[formalization status](paper/pierce_joint_lift_status.txt).

`IntegralLiftGraph` constructs the prime ideal of a rational graph, proves its
old-coordinate contraction is the original prime ideal, and places actual
orbit `I₃` points on that graph. The newer general `JointLiftGraphDegree`
development supplies upper Hilbert-degree bounds from common-denominator formulas.
`JointLiftInfinityOrder` now proves the rank-five pole order `5e/2` and even
infinity multiplicity for every discrete valuation centered on the actual
nonexceptional chart. `JointLiftQuotientOrder` and `JointLiftLocalOrders` prove
the quotient, resolvent and curvature order calculations from their local
inputs. `ChartNodeUnits` and `ChartNodeOrders` derive exact node-difference
orders from the actual resultant unit. `ChartRawDeterminantOrders` proves
orders `−3e` for both consecutive cubic determinants and `−6e` for the fourth
determinant on the actual components. `JointLiftRetainedOrders` now derives the
quotient and rank-three orders from the retained normalization and resolvent
equations, with all coefficient bounds proved. `JointLiftChartOrders` connects
these calculations to the actual four graph coordinates: their orders are
`3t`, at least `3t`, `3t`, and `−5t`, where `e = 2t`. It also proves that the
curvature coordinates cannot all have positive order over the original affine
part. `ChartNormalization` and `AffineNormalization` now prove finite Dedekind
normalization of both chart rings. `JointLiftNormalizedOrders` and
`JointLiftNormalizedFiniteOrders` construct normalized integer-valued branch
orders and apply these coordinate calculations to them. `NormalizationFiberDegree`
proves that normalization preserves the infinity fiber dimension.
`NormalizationInfinityDegree` identifies all normalized infinity branches and
proves that the sum of their multiplicities times their residue-field degrees
equals the original Hilbert degree `d`. `NormalizedFiberOrders` identifies those
multiplicities with the canonical branch orders. `FunctionParameterNormalization`
proves equality of the weighted zero and pole fiber degrees by normalizing the
parameter lines for a transcendental function and its reciprocal. It constructs
the associated canonical orders and identifies their parameter and inverse orders.
`FunctionParameterChange` and `ChartFunctionParameters` prove that every
transcendental function on the actual curve gives a finite field extension.
`JointLiftCurvatureTranscendence` proves that the curvature combination giving
the extra finite zero is transcendental. `IntegralBranchOrders` constructs centers
on parameter normalizations and proves regularity of integral elements.
`BranchValuationComparison` and `BranchResidueComparison` prove that this transport
preserves the exact normalized order and residue degree. `BranchZeroDegree`
proves the weighted zero-count inequality, including the extra degree from one
additional zero. `JointLiftPoleCoverage` and `JointLiftPoleDegree` locate every
pole of a curvature combination on the affine normalization and bound its
function-field degree by the curvature pole-envelope degree.
`JointLiftFiniteZero` constructs the actual extra normalized zero outside the
old infinity fiber. `JointLiftCurvatureDegree` combines it with the weighted
infinity orders to prove `3*d + 2 ≤ 2*deg(F)` for the curvature pole envelope
on a retained component. `GraphFunctionField`, `ValuationLinearCombination`, and
`GraphPoleDegree` compare the coordinate pole envelope with graph Hilbert degree.
`JointLiftGraphLowerDegree` proves `4*d + 1 ≤ δ` for the actual retained graph,
and the range `17 ≤ δ ≤ 247*d` when the component degree is at least four.
The earlier `151/513` conditional reduction remains available.

The external coefficient-uniform affine-curve theorem is proved in
`ccdn-dimension-growth`. `AffineCurveCounting.affineCurveBound` gives
`C(n) * d³ * B^(1/d) * (log B + d)` for every prime affine curve over `ℚ`
in ambient dimension `n ≥ 2`, using its actual affine Hilbert degree and every
real `B ≥ 1`. Its proof includes the plane theorem, bounded degree-preserving
projections, and uniform box rescaling. There is no external counting hypothesis.
The theorem is imported through the Lake package `ccdn_dimension_growth`,
using the local sibling path `../ccdn-dimension-growth`. A checkout of that
library must be present beside this repository.

`CurveCounting` identifies the coordinate-ring and point-count interfaces;
`CurveCountingDegreeRange` absorbs bounded-degree factors, and
`CurveCountingCoordinates` handles arbitrary finite index types, including
`Fin 3 ⊕ Fin 4`. `CurveCountingCover` sums over finite prime-component covers.

`OrbitGapCoordinates` proves that the three node coordinates distinguish
complete gap vectors within a fixed pattern. `JointLiftPointCount` applies the
proved counting theorem to actual seven-coordinate integer points.
`JointLiftCountingSlack` absorbs the logarithm using the proved polynomial box
bound, and `JointLiftCoverCount` counts gap vectors over at most 24 components
with a proved `SlowGrowth` coefficient. `OrbitConicGapCount` similarly applies
the conic divisor estimate directly to distinct gap vectors. The graph-degree
range needed for the seventeenth-root term is now proved on retained components.
`JointLiftComponentCount` combines conics, the two bounded cuts, and retained
graphs. `JointLiftNonexceptionalCount` sums their actual prime-component cover.
`OrbitCurveGapCount` and `OrbitPatternCurveCount` prove the ordinary square-root
count after excluding lines at the actual window scale. `JointLiftBound`
combines these to prove the full pattern estimate and the `128/435` length bound.

`PoweredJointGraph` constructs the graph with coordinates `W_j^m` and `J^n`,
proving its upper degree bound `((m+n)*247+1)*d`. `PoweredPoleOrder` proves that
powers multiply pole orders and envelopes. `PoweredJointGraphLowerDegree`
proves `(5*n+3*m)*d+2*m ≤ 2*δ`, hence `δ ≥ 10*n+7*m` for `d≥4`.
`PoweredJointPointBox` supplies actual integer points in `max(3H,S^m,Y^n)`,
and `PoweredJointPointCount` applies the curve theorem to this box.
`PoweredJointCountingSlack`, `PoweredJointComponentCount`, and
`PoweredJointPatternCount` discharge the powered logarithmic and counting inputs.
`PoweredJointExponent`, `PoweredJointWindow` and `WindowRealReduction` prove
all window ranges and dyadic summation. `PoweredJointBound` concludes the
optimized algebraic exponent and its explicit rational version.

The local-dependency build passes (9558 jobs). Its axiom audit covers 2551
Pierce, 1145 counting and 555 curve-vendor declarations, allowing only
`propext`, `Classical.choice` and `Quot.sound`. The weighted-counting
independence audit also passes. This check used CCDN commit
`642822b5d2db7035e625a9f32b0af205a276b2fb`; the path dependency itself is not pinned.
The previous vendored checkpoint passed the full sandboxed Comparator for all
eleven public results with Lean, NanoDa and con-ron. That historical result
does not validate the changed dependency; a fresh Comparator run remains
outstanding. The [status record](paper/pierce_joint_lift_status.txt) distinguishes
the two configurations.
After building, `python3 scripts/check-integral-lift-dependencies.py` checks the optimized and
both rational joint-lift bounds, the powered graph degree and point count, and both the `151/513`
and `128/435` pattern reductions, the actual joint-cover and conic gap counts,
the local-order developments, normalized infinity degree, and function-parameter
zero/pole fiber comparisons, branch transport, the actual extra normalized zero,
the curvature pole-degree lower bound, and the retained graph-degree range for
independence from weighted counting. See the
[current status](paper/pierce_joint_lift_status.txt) and the
[151/513 record](paper/pierce_151_513_status.txt) for precise scopes.

For reproducible exact checks (requires SymPy):

```sh
python3 scripts/check-fixed-dividend.py
python3 scripts/check-fixed-dividend-lines.py
```

## Lean

Place the existing `ccdn-dimension-growth` checkout beside this repository,
so that its `lakefile.toml` is at `../ccdn-dimension-growth/lakefile.toml`.
The local Lake dependency uses that working tree, including any uncommitted
changes; it is not an immutable version pin.

The public repository `jasondavies/ccdn-dimension-growth` has not been created
yet. A checkout of this repository alone therefore cannot fetch the counting
dependency. After publishing the CCDN repository, replace the local path with
a Git dependency pinned to a full commit SHA and rerun verification.

Build with `lake exe cache get` (to download the compiled Mathlib) and then `lake build`
(Lean `v4.35.0`, Mathlib `v4.35.0`). The build runs Mathlib's standard linters
(`weak.linter.mathlibStandardSet`). It also builds the independent Palomar Challenge
and Solution modules and audits every exported declaration from the
`PierceLengthBound` modules for nonstandard axioms.
The eleven `sorry` warnings
in `Challenge.lean` are deliberate statement holes; the proof development has none.
The main theorems are

```lean
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

`#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound` for all eleven;
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

[Challenge.lean](Challenge.lean) independently states all eleven main results using only
Mathlib imports and complete mathematical definitions. Its eleven theorem proofs are
deliberate holes. [Solution.lean](Solution.lean) exposes the original proved declarations;
neither module imports the other. [comparator.json](comparator.json) selects the results,
and [formalization.yaml](formalization.yaml) records their scope, provenance, automation,
and review status. This repository is the substantive development, not a thin wrapper.

With the sibling CCDN checkout in place, run the local preparation checks:

```sh
python3 scripts/check-lean-sources.py
python3 scripts/check-curve-counting-dependency.py --checkout
python3 scripts/check-math.py
lake exe cache get
lake build
```

On Linux with `bubblewrap` installed, run `bash scripts/verify-comparator.sh` to compare
the statements and proofs using Lean's kernel, NanoDa, and con-ron. The standard
sandboxed Comparator needs Linux; a successful macOS Lean build alone does not
establish a Palomar verification pass. The sibling dependency must also be
available to the verifier. The current local-path setup is not portable to a
clean hosted checkout.

The intended public repository is `jasondavies/pierce-length-bound`. Before submission,
publish and pin the CCDN dependency, confirm the automation and review account
in `formalization.yaml`, push all intended changes there, and obtain the full
commit SHA with `git rev-parse HEAD`.
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
