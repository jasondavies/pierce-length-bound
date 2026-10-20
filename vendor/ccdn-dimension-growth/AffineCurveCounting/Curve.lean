module

public import AffineCurveCounting.Plane

/-!
# Affine curves and the full counting target

An affine algebraic set is represented by an ideal in `ℚ[x₁,…,xₙ]`. For an integral curve,
its degree is the slope of the eventually linear affine Hilbert function: the dimension
of polynomials of total degree at most `M` in its coordinate ring is `d*M + c` for large `M`.

`AffineCurveBound` records the full target, with constants depending only on the ambient
dimension. It is proved by `affineCurveBound` in the `AffineCurveBound` module.
`PlaneHilbert` proves the passage from a plane defining
polynomial to this Hilbert-function degree. `PlaneIdealCount` proves the full
prime-ideal counting interface in dimension two. `BoundedDegreePreservingProjection`
constructs bounded integral projections preserving degree in every dimension.
The general integer-height and counting assembly is completed in
`AffineProjectionCount`, `ProjectionScaleAbsorption` and `AffineCurveBound`.
-/

@[expose] public section

namespace AffineCurveCounting

abbrev CoordinatePolynomial (n : ℕ) := MvPolynomial (Fin n) ℚ

def idealZeroLocus {n : ℕ} (I : Ideal (CoordinatePolynomial n)) : Set (RatPoint n) :=
  {x | ∀ f ∈ I, MvPolynomial.eval x f = 0}

noncomputable def coordinateSpace {n : ℕ} (I : Ideal (CoordinatePolynomial n)) (M : ℕ) :
    Submodule ℚ (CoordinatePolynomial n ⧸ I) :=
  (MvPolynomial.restrictTotalDegree (Fin n) ℚ M).map (Ideal.Quotient.mkₐ ℚ I).toLinearMap

instance coordinateSpace_finite {n : ℕ} (I : Ideal (CoordinatePolynomial n)) (M : ℕ) :
    Module.Finite ℚ (coordinateSpace I M) := by
  unfold coordinateSpace
  infer_instance

noncomputable def affineHilbertFunction {n : ℕ} (I : Ideal (CoordinatePolynomial n))
    (M : ℕ) : ℕ := Module.finrank ℚ (coordinateSpace I M)

/-- Degree via the eventual affine Hilbert polynomial. This condition is mathematical
data about the coordinate ring, and contains no point-counting estimate. -/
def HasAffineCurveDegree {n : ℕ} (I : Ideal (CoordinatePolynomial n)) (d : ℕ) : Prop :=
  ∃ N : ℕ, ∃ c : ℤ, ∀ M : ℕ, N ≤ M →
    (affineHilbertFunction I M : ℤ) = (d : ℤ) * M + c

theorem affineCurveDegree_unique {n : ℕ} {I : Ideal (CoordinatePolynomial n)} {d e : ℕ}
    (hd : HasAffineCurveDegree I d) (he : HasAffineCurveDegree I e) : d = e := by
  obtain ⟨N, c, hN⟩ := hd
  obtain ⟨P, k, hP⟩ := he
  have hN0 := hN (max N P) (le_max_left _ _)
  have hP0 := hP (max N P) (le_max_right _ _)
  have hN1 := hN (max N P + 1) (by omega)
  have hP1 := hP (max N P + 1) (by omega)
  push_cast at hN0 hP0 hN1 hP1
  have hde : (d : ℤ) = e := by nlinarith
  exact_mod_cast hde

/-- CCDN (2020), Theorem 3, using the affine Hilbert function to specify degree.
The constant is chosen before the ideal, degree, and real box radius. -/
def AffineCurveBound : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ I : Ideal (CoordinatePolynomial n), I.IsPrime →
      ∀ d : ℕ, 0 < d → HasAffineCurveDegree I d →
        ∀ B : ℝ, 1 ≤ B → (count (idealZeroLocus I) B : ℝ) ≤ C * curveBound d B

end AffineCurveCounting
