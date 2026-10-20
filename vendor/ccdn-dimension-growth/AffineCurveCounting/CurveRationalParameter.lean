module

public import AffineCurveCounting.CurveParameter

/-! Construct the rational-function field embedding from a transcendental
coordinate, and prove the degree bound for the resulting field extension. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section

/-- Send the rational-function variable to an actual transcendental element. -/
def transcendentalRatFuncMap {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u : F) (hu : Transcendental K u) : RatFunc K →ₐ[K] F :=
  RatFunc.liftAlgHom (Polynomial.aeval u)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (transcendental_iff_injective.mp hu))

lemma transcendentalRatFuncMap_X {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u : F) (hu : Transcendental K u) : transcendentalRatFuncMap u hu RatFunc.X = u := by
  change RatFunc.liftRingHom (Polynomial.aeval u).toRingHom _ RatFunc.X = u
  exact (RatFunc.liftRingHom_X (Polynomial.aeval u).toRingHom _).trans (Polynomial.aeval_X u)

/-- Every actual positive-degree affine curve has a coordinate parameter and
a constructed embedding K(t) into its function field. The corresponding
extension is finite, with degree at most the affine Hilbert degree. -/
theorem exists_curve_rational_parameter {K F σ : Type*} [Field K] [Field F]
    [Fintype σ] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    [Algebra (MvPolynomial σ K ⧸ I) F] [IsScalarTower K (MvPolynomial σ K ⧸ I) F]
    [IsFractionRing (MvPolynomial σ K ⧸ I) F]
    (d : ℕ) (hd : 0 < d)
    (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c) :
    ∃ (j : σ) (φ : RatFunc K →ₐ[K] F),
      φ RatFunc.X = algebraMap (MvPolynomial σ K ⧸ I) F ((Ideal.Quotient.mk I) (MvPolynomial.X j)) ∧
      let : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
      Module.Finite (RatFunc K) F ∧ Module.finrank (RatFunc K) F ≤ d := by
  obtain ⟨j, hj⟩ := affine_degree_fraction_transcendental_coordinate (F := F) I d hd hdegree
  let u := algebraMap (MvPolynomial σ K ⧸ I) F ((Ideal.Quotient.mk I) (MvPolynomial.X j))
  let φ := transcendentalRatFuncMap u hj
  refine ⟨j, φ, transcendentalRatFuncMap_X u hj, ?_⟩
  let : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
  let : IsScalarTower K (RatFunc K) F := IsScalarTower.of_algHom φ
  apply curve_functionField_finite_rank_le I d hdegree (MvPolynomial.X j)
    (by simp) RatFunc.X RatFunc.transcendental_X
  exact (transcendentalRatFuncMap_X u hj).symm

end
end AffineCurveCounting
