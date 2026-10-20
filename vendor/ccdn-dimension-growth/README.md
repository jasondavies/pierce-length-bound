# CCDN Dimension Growth

A Lean 4 development of coefficient-uniform bounds for integral points on affine curves.

**Status: the full affine curve counting bound is proved in Lean.**
`AffineCurveCounting.affineCurveBound` proves `AffineCurveBound`, including all
ambient dimensions n>=2, with no external counting hypothesis. The proof
includes the plane theorem, bounded degree-preserving projections and the
uniform height/count assembly. There are no counting axioms.

The proved theorem is Castryck–Cluckers–Dittmann–Nguyen (2020), Theorem 3,
with curve degree represented by the slope of the affine Hilbert function:
for each ambient dimension `n ≥ 2`, there is a constant `C(n)` such that every integral
affine curve over `ℚ` of degree `d ≥ 1` satisfies, for every real `B ≥ 1`,

```text
N_aff(X, B) ≤ C(n) d³ B^(1/d) (log B + d).
```

The constant is independent of the curve's coefficients. The project supplies the external
counting input for the Pierce-length refinements.
The current joint-lift candidate proposes `128/435 + ε`, then the optimization
`(1310 − √655)/4365 + ε`. It needs ambient dimension seven: unpowered graph degrees
17 through 5928, and degrees bounded in terms of the fixed powers for the optimized
version. Exceptional curves still use dimension three in degrees 2 through 24.
The new route uses ordinary pattern counting. The external counting theorem
is now proved; the application still requires its own graph-degree and
retained-component geometry and final integration.

## Build and audit

The toolchain is Lean `v4.35.0`; Mathlib is pinned to
`56a005855ea17e0b0958f73ec801ae140b0a1679`, matching `pierce-length-bound`.

With Elan, Python 3, and Git installed:

```sh
lake exe cache get
bash scripts/check.sh
```

The check verifies vendored source hashes and import coverage, builds every library module,
and audits the transitive axioms of exported declarations in both the new mathematics and
the vendored dependency. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
The audit is not an independent kernel implementation and does not replace mathematical
review of theorem statements.

## Implemented mathematics

| Module | Checked content |
| --- | --- |
| `Box` | Exact integral-point counting at real radii; monotonicity, union bounds, injective transport. |
| `Plane` | Explicit plane-curve target; a coordinate-count bound for nonvertical affine lines. |
| `Curve` | Finite-dimensional filtered coordinate spaces, degree via eventual affine Hilbert growth, uniqueness of degree, full-dimensional target. |
| `Interpolation` | Evaluation matrices, nonzero coefficient vectors giving nonzero polynomials, degree and monomial-height bounds. |
| `RowSpan` | Vanishing transfers from selected evaluation rows to all rows in their rational span. |
| `AuxiliaryPolynomial` | Bombieri–Vaaler gives a nonzero vanishing polynomial with an explicit bound on every coefficient. |
| `Nondivisibility` | Leading coefficients obstruct divisibility; an explicit determinant threshold produces an auxiliary polynomial not divisible by the defining polynomial. |
| `Determinant` | Gram determinant upper bound; row-factor divisibility; determinant divisibility from congruent rows. |
| `LocalDeterminant` | Weighted factorizations over commutative rings, multiplicity exponents, quadratic determinant and maximal-minor-gcd divisibility for univariate polynomial evaluations in a residue class. |
| `BlockDeterminant` | Integer column-lattice factorization; residue-block maximal-minor divisors multiply and their prime exponents add, including deficient and empty blocks. |
| `SmoothLocalDeterminant`, `SmoothPlaneChart` | Finite polynomial Newton approximation proves the triangular local determinant exponent for actual smooth plane-curve residue classes, in either coordinate direction. |
| `SingularTangent`, `OriginLayerGenerators`, `OriginTruncationGenerators` | Actual origin-adic layers have dimension at most the plane-curve multiplicity; homogeneous generators span every finite truncation. |
| `ModularPolynomialLift`, `ModularOriginGenerators`, `SingularApproximation` | Lift the local generators to integer polynomials and prove uniform approximation modulo every prime power at actual integral zeros. |
| `SingularLocalDeterminant`, `SingularPlaneChart` | Actual singular residue classes contribute exponent `sum(i < s, floor(i / multiplicity))` to evaluation determinants and maximal-minor gcds; translation and residue-block assembly are proved. |
| `PlaneMultiplicity`, `SingularReduction` | Actual reduced points determine positive multiplicities bounded by the equation degree, the complete residue partition, and the quadratic exponent bound using their total multiplicity; no smoothness or supplied partition is required. |
| `PlaneMultiplicitySmooth` | Actual multiplicity greater than one forces singularity; total multiplicity is at most the point count plus `d²(d−1)` for an irreducible reduction below the characteristic. |
| `SmoothReduction`, `SmoothDeterminant` | Construct the actual smooth residue partition and prove the global logarithmic maximal-minor-gcd bound; finite-field point bounds and excluded primes remain explicit inputs. |
| `SingularDeterminant` | Global logarithmic maximal-minor-gcd bounds for arbitrary reduced points, including singular points, using actual point counts and the proved multiplicity correction; the prime-sum form retains explicit sharp point-count and good-prime hypotheses. |
| `PrimeCutoff`, `SingularDeterminantCutoff` | A prime-weighted tail bound of order `1/sqrt(L)` gives the `27d⁴` cutoff and a global rank-level determinant bound with `4 log(d)` loss and degree-independent error; sharp point counts and good reductions remain explicit inputs. |
| `BadPrimeCharge` | A nonzero integer witness bounds the sum of log(p)/p over its prime divisors; splitting at the logarithmic height gives the exponential bad-prime factor linear in scaled logarithmic height. The geometric input is supplied for plane equations by `GeneralBadReduction` and `PlaneBadPrimes`. |
| `AlgebraicDifferentialConstants`, `RationalDifferential` | Formal differentiation on F(t), its characteristic-zero constant field, and descent of constants through algebraic differential extensions over an algebraically closed constant base. |
| `DifferentialResidue`, `RationalClosedForms`, `BivariateClosedForms` | A simple-root residue of a closed form is constant; for monic irreducible bivariate equations over an algebraically closed characteristic-zero field, every form within the strict outer-degree bounds is a constant multiple of the gradient. |
| `BivariateFactorForms` | Explicit closed forms from factors and repeated factors, with polynomial divisibility obstructions to their being scalar multiples of the whole gradient under stated coprimality hypotheses. |
| `BivariateCoefficientMatrix`, `ClosedFormBaseChange` | Actual integer coefficient matrix on 2d² unknowns, exact kernel encoding, and compatibility with arbitrary coefficient ring maps. |
| `ClosedFormRank`, `FiniteRowMinor`, `ClosedFormIntegerMinor` | Monic absolute irreducibility in characteristic zero forces rank at least 2d²−1, yielding a nonzero integer minor; rank drop in characteristic p forces p to divide it. |
| `ClosedFormHeight`, `ClosedFormMinorCharge` | Each entry is bounded by 2dH and each r-minor by r!(2dH)^r. The logarithmic bound fits the 27d⁴ cutoff and bounds the charge of primes with rank drop by log(1+log(H)/d²)+O(1). |
| `ClosedFormKernelWitness` | Every polynomial pair supported on the grid reconstructs as a coefficient vector; two independent closed forms force rank drop by two. |
| `BivariateTotalDegree` | Total degree transported from the multivariate ring, exact product degrees, derivative bounds, and actual grid support for factor forms of every multiplicity. |
| `ClosedFormFactorRank`, `ClosedFormReducibility` | Below the characteristic, every reducible monic equation of full outer degree forces rank drop by two; monic primary-factor extraction and all multiplicities are proved. |
| `MonicBadReduction` | For monic absolutely irreducible integer equations of full outer degree, constructs a positive height-controlled integer divisible by every geometric bad prime above the degree, and proves the geometric prime-charge bound. |
| `ClosedFormScaling`, `ConstantLeadingBadReduction` | Nonzero constant scaling preserves matrix rank. For integer equations of full outer degree, leading coefficient times minor detects geometric reducibility and degree drops, with the required scaled-height charge; integer monicity is unnecessary. |
| `PlaneShear`, `LeadingDirection`, `ShearNormalization` | Integral shears preserve irreducibility and total degree and commute with coefficient maps. A parameter in 0,...,d gives full outer degree, and the actual bad-prime set is preserved. |
| `ShearHeight` | A bounded integral shear increases coefficient height by at most (d+1)^(d+2). |
| `GeneralBadReduction`, `PlaneBadPrimes` | For every absolutely irreducible integer plane equation, construct a positive integer witness and the actual finite set of geometric bad primes above 27d⁴. Its charge is at most log(1+log(H)/d²)+O(1), including degree drops. |
| `HeightDeterminant`, `PlaneChartHeight` | Discharge the bad-prime assumptions in the determinant lower bound and actual affine-chart comparison using the equation's coefficient height. The sharp finite-field point count remains an explicit hypothesis. |
| `ResidueAggregation` | Cauchy–Schwarz aggregation of local multiplicity exponents with the leading constant preserved; global logarithmic lower bound from explicit local divisibilities. |
| `PrimeProduct` | Combine divisibility at distinct primes into a product and a logarithmic lower bound. |
| `MertensFirst` | First Mertens theorem: a uniform bounded error for the prime sum of log(p)/p, with convergent prime-power error. |
| `PrimeSums` | Weighted good-prime sums, charges for excluded primes, and analytic determinant lower bound from explicit local divisibility and finite-field point estimates. |
| `FilteredIntersection`, `MonomialDimension` | Filtered multiples, kernel dimension bounds, and exact monomial-space dimensions, adapted from the Pierce development. |
| `PlaneHilbert` | Exact principal-plane Hilbert function; polynomial total degree equals the degree used by the counting target. |
| `PointSeparation`, `PolynomialSection`, `Bezout` | A proper degree-`m` section of an actual degree-`d` prime curve has at most `dm` distinct points; sharp plane intersection and integer-box counting forms. |
| `FormalImplicitRoot`, `FormalPlaneBranch` | Construct the unique formal power-series branch at a point with a nonzero partial derivative, in arbitrary characteristic. |
| `SectionImageRank`, `FormalBranchFaithful`, `FormalBranchOrder` | A proper section bounds independent polynomial images; the actual formal branch is faithful, and a degree-m section has local order at most dm. |
| `PowerSeriesOrderIndependence`, `PowerSeriesFrobenius` | Distinct orders and injective finite jets prevent Frobenius cancellation; the plane-curve condition is dD<p. |
| `FormalBranchMultiplicity`, `FormalPlaneDifferentiation`, `PlaneTangentMultiplicity` | Prove N times the number of distinct selected points is at most dm when a proper section's first N tangent derivatives vanish, with N at most the characteristic. All formal branches are constructed. |
| `PlaneFrobeniusAuxiliary`, `PlaneFrobeniusSystem`, `PlaneStepanovBound` | Construct nontrivial auxiliary coefficients from a strict finite-dimensional inequality and prove the resulting prime-field point count, including the d(d-1) critical-point correction. The numerical choice and sharp estimate are supplied by the next row. |
| `StepanovParameters`, `PlaneStepanovDimension`, `StepanovRealBound`, `SharpPlaneCount` | Choose integer degrees above 27d⁴, verify the exact dimension inequality, prove the prime-field bound p+161d² sqrt(p), and discharge the full coefficient-uniform rational-plane integral-point theorem. |
| `FunctionFieldRank`, `CurveFunctionField` | Hilbert growth bounds independent polynomial classes over a transcendental parameter field; common denominators prove the actual function-field extension is finite of degree at most d. |
| `CurveParameter`, `CurveRationalParameter` | Positive affine Hilbert degree supplies a transcendental original coordinate and a constructed embedding K(t) into the fraction field. |
| `BoundedLinearSeparation`, `BoundedPrimitiveElement`, `CurvePrimitivePair` | Construct an integer linear form with moment-curve coefficients (1,k,...) and k<=n*d² which, together with an original coordinate, generates the function field. |
| `BoundedProjectionCoordinates` | The pair maps integer points to integer points with box factor 1+n*(n*d²+1)^n. Preservation of curve degree and exceptional-fiber control are not asserted. |
| `PlaneSingularities` | Nonzero partial derivative below the characteristic and the `d(d-1)` bound for distinct singular points of an irreducible plane equation. |
| `RowSelection` | Independent spanning rows selected from a finite matrix, with strict rank deficiency from a nonzero annihilator. |
| `HomogeneousMonomials`, `HomogeneousHilbert` | Complete homogeneous monomial indexing, binomial dimensions, homogeneous-factor extraction, and the exact principal homogeneous Hilbert function. |
| `HomogeneousEvaluation`, `HomogeneousRank`, `HomogeneousAuxiliary` | An actual homogeneous equation supplies independent spanning evaluation rows with the full binomial rank deficit; Bombieri–Vaaler then produces a small homogeneous polynomial vanishing on the entire supplied point set. |
| `HomogeneousRankDichotomy` | Clearing denominators transfers absence of integer auxiliary polynomials to rational relations; exact evaluation rank and the plane identity 2s+d²=d(2M+3). |
| `HomogeneousDeterminantComparison`, `PlaneChartDeterminant` | Exact-rank Bombieri–Vaaler and coefficient obstruction give the logarithmic Gram/gcd upper bound; actual affine-chart rows combine it with the singular determinant lower bound. |
| `PlaneAuxiliaryDegree`, `PlaneAuxiliaryLargeHeight`, `PlaneAuxiliarySelection` | Derive explicit integer auxiliary degrees from the determinant comparison in both height ranges. The small-height bound retains B^(2/d) and the leading-coefficient saving L^(-1/d²); the large-height bound is O(d³). Sharp finite-field counts and coefficient positioning remain hypotheses. |
| `PrimitiveIntegerPolynomial`, `PrimitiveNormalization` | Extract primitive integer models of rational equations, preserving degree and homogeneous grading. Removing integer content does not increase coefficient height. Rational divisibility reflects to integer divisibility for every primitive equation. |
| `HomogeneousChart` | Restriction to x₀=1 is injective on each homogeneous degree. Explicit bounded homogenization inverts it; full chart degree transfers affine divisibility back to homogeneous divisibility. |
| `PlaneAuxiliaryCount` | The actual primitive auxiliary nonmultiples give proper rational affine sections. Bézout yields distinct-point bounds and bounds in the integer-box counting interface in both height ranges, still conditional on sharp finite-field counting and the stated coefficient-position hypotheses. |
| `IntegerGridInterpolation`, `PlaneGridHeight` | Integer-grid values control every coefficient, with factor (d+1)^(d+1) in one variable and (d+1)^(2(d+1)) in two. A bounded plane grid point supplies a nonzero height witness. |
| `HomogeneousTranslation`, `AffineTranslation` | Integral chart translations lift to homogeneous automorphisms. They preserve primitive equations, homogeneity, chart degree and irreducibility under coefficient maps; the point box grows by at most d+1. |
| `HomogeneousLeadingCoefficient`, `HomogeneousEvaluationHeight`, `LeadingPositionHeight` | A translation with parameters in 0,...,d gives a lexicographic leading coefficient L and an actual transformed-chart coefficient bound H with 1≤H and log L≤log H≤log L+14d². |
| `Analytic` | Elimination of coefficient height, absorption of additive errors, degree-2-through-24 square-root estimate, logarithm absorption. |

`PlaneCurveBound` and `AffineCurveBound` are definitions of propositions, not proved theorems.
The homogeneous auxiliary-polynomial theorem derives its monomial list, rank deficit,
and spanning rows from an actual nonzero homogeneous equation and its integral zeros.
The determinant comparison now gives an actual nonmultiple with an explicit degree
in each coefficient-height range, conditional on the sharp finite-field estimate
and, in the large-height case, a suitable leading-coefficient position.
The position is now supplied by a proved bounded integer translation. The
sharp finite-field estimate remains unproved; applying the translation and
absorbing its height and box costs in the final count still needs assembly.

## Reused proof

The exact Bombieri–Vaaler theorem cited in CCDN §3.3 is taken from
[Ralf Stephan's Subspace-Theorems](https://github.com/rwst/Subspace-Theorems/tree/09835cb23557ae5ae0cf55a9c4ab9055f5d60338).
Only its 25-module transitive dependency is vendored. Source attribution, original hashes,
local hashes, and the two compatibility changes are recorded under `vendor/bombieri-vaaler/`.
The code is rebuilt against this project's pinned Mathlib; upstream verification claims
are not a substitute for that build.

The first Mertens theorem is adapted from [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/c39a751132c88b6e8080b74c74023fd95b3d8be0/PrimeNumberTheoremAnd/IEANTN/Mertens.lean).
The extracted proof uses only Mathlib. Its source revision, hashes, adaptation notes, and
Apache license are recorded under `vendor/mertens/`.

## Remaining work

The central unfinished input is the global determinant lower bound for curves, CCDN Proposition 3.2.6.
The local plane estimate now includes singular residue classes: the multiplicity
is the order of the actual translated reduction, and the local exponent is
`sum(i < s, floor(i / multiplicity))`, at least `s²/(2*multiplicity) - s`.
The full reduced-point partition and its positive total multiplicity are now
constructed from the actual equation. Residue-block aggregation and prime sums
are also proved. The sharp finite-field point bound remains open. The coefficient-controlled
bad-prime estimate for plane equations is now proved. The multiplicity correction is proved: it adds at most
`d²(d−1)` to the point count for irreducible reductions below the characteristic.
`SingularDeterminant` now combines this correction with the actual local
divisibilities into a global logarithmic gcd bound. Its exact-denominator form
needs no point-count estimate; its prime-sum form assumes the sharp point-count
bound and an explicit set of good primes. The cutoff refinement in `SingularDeterminantCutoff` removes the polynomial
degree error: primes above `27d⁴` yield a `4 log(d)` loss and an error independent
of `d`. The required sharp point-count bound remains unproved. `HeightDeterminant`
discharges the bad-prime charge using the actual coefficient height.
`PlaneChartDeterminant` combines the singular lower bound with the actual
exact-rank homogeneous upper bound on the chart x₀=1.
The bad-prime witness construction now has a proved differential core: formal
rational differentiation, algebraic constant descent, simple-root residue
constancy, and the characteristic-zero monic bivariate closed-form
classification. Factor forms and their divisibility obstructions are also
proved. The actual integer matrix, characteristic-zero rank bound, nonzero
integer minor, coefficient-height bound and prime charge are now checked.
The full reducibility-to-rank-drop implication is proved for monic equations
of full outer degree below the characteristic, including repeated factors.
In this monic case the minor now detects every geometric bad prime above the
degree, with the required height and charge. The extension to non-monic equations of full outer degree is now proved,
including reductions whose degree drops. Bounded integral shears now supply
full outer degree and preserve the actual bad-prime set. The coefficient-height
cost is now bounded by (d+1)^(d+2). This completes the required uniform
bad-prime charge for plane equations in arbitrary coordinates. `PlaneBadPrimes`
constructs the finite excluded set, and `PlaneChartHeight` incorporates its
charge into the actual affine-chart determinant comparison.
`PlaneAuxiliarySelection` now chooses an integer degree and constructs a nonmultiple
in both height ranges. Writing L for the leading coefficient's absolute value and
K for the determinant error, the small-height degree is at most
`d + log(B) + 2 exp(K+23) d³ (1+log(H)/d²) B^(2/d) / L^(1/d²) + 2`.
When `log(H) ≥ 4d log(B)` and `log(H) ≤ log(L)+Td²`, the degree is at most
`(34+8 exp(K+6+T))d³`. The finite-field estimate is explicit in both theorems.
Primitive normalization and rational nondivisibility are now proved.
`HomogeneousChart` supplies the chart transfer, and `PlaneAuxiliaryCount`
applies Bézout to the actual integer points and to the real-radius counting
interface. In the small-height range its bound is d times the displayed
auxiliary-degree bound; in the large-height range it is
`(34+8 exp(K+6+T))d⁴`. These are conditional bounds preceding the affine scaling
step: this earlier chart bound has exponent 2/d. The scaled-model result below
obtains exponent 1/d under an explicit scaling-prime hypothesis.
Coefficient positioning is now proved: a translation with parameters in 0,...,d
preserves the primitive equation, homogeneous degree, chart degree and
irreducibility, and increases the point-box radius by at most d+1. For the
actual transformed equation it supplies H with `log(L)≤log(H)≤log(L)+14d²`.
The scaled-model translation and height elimination are now assembled.
`PolynomialMapAuxiliary` applies the determinant argument to polynomial
coordinates of the original curve. `ScaledHomogenization` constructs the
integral model with points `(p,x,y)` and a coefficient of size at least `p^d`.
It is primitive when the prime p does not divide the original constant term.
`HomogeneousSlice` and `ScaledAuxiliaryCount` transfer nonmultiples to proper
sections on x₀=p. The actual bounded translation has point radius `(d+1)B`,
and `ScaledModelPosition` supplies H≥p^d with the position loss 14d².
`ScaledPlaneCount` combines both auxiliary-degree branches with Bézout;
`scaled_plane_finite_count_one_over_degree` in `ScaledBoxExponent` gives
`K(C,A) d³ B^(1/d) (log B+d)` for actual distinct integer points when
`B/A≤p≤B`, p does not divide the constant term, and the stated sharp
finite-field estimate holds with constant C. The constant is explicit and
independent of the equation's coefficients. `ScalingPrime` constructs a suitable
prime with the absolute ratio `A=exp(2*mertensError+2)` when `B≥A` and the
nonzero constant term has `log|f(0)|<B/A`. `ScaledPlaneSmallCoefficient`
therefore removes the prime hypothesis in that branch. The complementary height and box cases are now covered by `UnscaledModelCount`,
`AffineBoxRanges` and `AffineNonzeroConstant`: large coefficients give O(d⁴),
and small boxes use the coefficient-uniform 2/d fallback. `AffineTranslationCount`
removes a zero constant term by a bounded integer translation, preserving
primitivity, degree, irreducibility and the actual residue count.
`AffinePlaneAssembly` therefore proves the target 1/d count for primitive
absolutely irreducible integer plane equations at every B≥1, conditional only
on the stated sharp finite-field estimate. `RationalPlaneAssembly` extends it
to rational absolutely irreducible equations with one coefficient-independent
constant. `SharpPlaneResidueBound` names the remaining finite-field obligation;
it is discharged with constant 161 by `SharpPlaneCount.sharpPlaneResidueBound`.
`PolynomialLinearDescent` and `NonabsolutePlaneCount` now handle rational
irreducible equations that split over an extension: each factor's base-field
zeros lie on a nonzero base-field polynomial of no larger degree, and Bézout
gives at most d² points in total. `PlaneCurveAssembly` therefore proves
`SharpPlaneResidueBound C → PlaneCurveBound` for C≥0. The finite-field
nongeometric case also costs at most d²; `GeometricResidueReduction` reduces
the missing point estimate to geometrically irreducible equations alone.
The local Stepanov machinery is now proved: formal branches, local and summed
multiplicity bounds, tangent differentiation, and Frobenius noncancellation.
`PlaneFrobeniusSystem` constructs actual auxiliary coefficients from a strict
dimension inequality. `PlaneStepanovBound` proves
`#S * N <= d*(D+p*A) + d*(d-1)*N` provided `d*D<p`, `N<=p`, and
`sum(r<N, H(D+A+r*d)) < H(D)*H(A)`, where H is the actual filtered
coordinate-ring dimension. It constructs polynomial bases, the nontrivial
auxiliary and every formal branch. `StepanovParameters` now chooses
`A=floor(sqrt(p)/d)`, `D=floor((p-1)/d)` and `N=d*A-4*d²`.
`PlaneStepanovDimension` proves the dimension inequality above `27d⁴`;
`StepanovRealBound` handles all rounding and proves the explicit error constant
161. Thus `SharpPlaneCount` proves `p+161d² sqrt(p)` for every irreducible
prime-field equation above the cutoff, discharges `SharpPlaneResidueBound 161`,
and proves `PlaneCurveBound` unconditionally. The next projection steps now
construct a transcendental original coordinate, prove its function-field
extension has degree at most d, and produce a primitive linear form with
integer moment-curve coefficients and k<=n*d². This actual pair has integral
coordinates and box factor `1+n*(n*d²+1)^n`. It generates the function field;
`PlaneProjectionDegree` now constructs its irreducible image equation and proves
that its degree is at most d. `PlaneIdealCount` proves the complete prime-ideal
counting interface in dimension two. `ProjectionFieldDegree` proves degree
preservation when the parameter extension has degree d.
`BoundedBirationalProjection` constructs polynomial reconstruction identities
with a proper common denominator Q. `ProjectionExceptionalCount` proves that
a finite source set loses at most d*deg(Q) points under projection.
`CurveProjectionDeformation` now constructs a polynomial family of plane
relations. Differentiating it in `CurveDerivativeReconstruction` reconstructs
every linear source coordinate using the same partial-derivative denominator,
provided the projection preserves degree. Its degree is at most d-1, so
`DegreePreservingProjectionCount` proves an actual point-count error of
at most d(d-1). This includes geometrically reducible prime curves and uses no
normalization or exceptional-fiber assumption.
`BoundedDegreePreservingProjection` now constructs such a pair unconditionally.
The first moment parameter satisfies `k₀<=n²*d`, and the second `k₁<=n*d²`.
The proof bounds geometric infinity points using the actual infinity Hilbert
pieces, chooses a bounded form avoiding them, and uses the Nullstellensatz to
generate the eventual coordinate filtration. This forces the parameter-field
extension to have degree exactly d. No geometric-integrality or supplied
parameter-field hypothesis remains. The two moment forms have integral
coefficients, preserve degree, and incur at most d(d-1) exceptional points.
`DegreePreservingProjectionBox` now bounds the actual integral projection in
a box enlarged by `(n+1)*((n+1)*(d+1))^(2*n)`. `ProjectionScaleAbsorption`
proves its logarithm is at most `(2*n²+3*n)*d`, retaining the exact exponent
1/d and the d³ factor after rescaling. `AffineProjectionCount` transports
actual integral points to the plane image. `AffineCurveBound.affineCurveBound`
assembles these proved inputs and the d(d-1) error into the full theorem.
The constant depends only on n; the ideal, degree, coefficients and real radius
are universally quantified afterward.
See [the proof roadmap](docs/roadmap.txt).

## References

- W. Castryck, R. Cluckers, P. Dittmann, K. H. Nguyen,
  *The dimension growth conjecture, polynomial in the degree and without logarithmic factors*,
  Algebra & Number Theory 14 (2020), 2261–2294.
  [DOI](https://doi.org/10.2140/ant.2020.14.2261),
  [author PDF](https://rcluckers.perso.math.cnrs.fr/prints/Cast-Cl-Ditt-Nguy.pdf).
- The same counting input appears as Corollary 2.2 in
  [Cluckers–Dèbes–Hendel–Nguyen–Vermeulen (2025)](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/improvements-on-dimension-growth-results-and-effective-hilberts-irreducibility-theorem/A7BCAEBF00B8B165D6DDB3FFB9B40B97).

The new source and documentation were developed with AI assistance. This repository makes
no claim of independent human review or of a new mathematical counting theorem.
