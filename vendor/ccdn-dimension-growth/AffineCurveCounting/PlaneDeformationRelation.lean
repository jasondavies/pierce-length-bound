module

public import AffineCurveCounting.CurveProjectionDeformation

/-! The constant and first-order equations of a polynomial family of plane
relations, expressed as equations in the target algebra. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma plane_deformation_relation_coefficients {K A ι : Type*}
    [Field K] [CommRing A] [Algebra K A] [Fintype ι]
    (a : Fin 2 → A) (k : Fin 2) (w : A)
    (r : ι → MvPolynomial (Fin 2) K) (v : ι → Polynomial K)
    (hv : ∑ j, (v j).map (algebraMap K A) * planeLinearDeformation a k w (r j) = 0) :
    aeval a (∑ j, (v j).coeff 0 • r j) = 0 ∧
    aeval a (∑ j, (v j).coeff 1 • r j) +
      aeval a (pderiv k (∑ j, (v j).coeff 0 • r j)) * w = 0 := by
  have h0 := congrArg (fun p : Polynomial A => p.coeff 0) hv
  have h1 := congrArg (fun p : Polynomial A => p.coeff 1) hv
  simp only [Polynomial.finsetSum_coeff, Polynomial.mul_coeff_zero, Polynomial.coeff_map,
    planeLinearDeformation_coeff_zero, Polynomial.coeff_zero] at h0
  simp only [Polynomial.finsetSum_coeff, Polynomial.mul_coeff_one, Polynomial.coeff_map,
    planeLinearDeformation_coeff_zero, planeLinearDeformation_coeff_one,
    Polynomial.coeff_zero, Finset.sum_add_distrib] at h1
  constructor
  · simp only [map_sum, map_smul]
    simpa only [Algebra.smul_def] using h0
  · simp only [map_sum, Derivation.map_smul, map_smul]
    simp only [Algebra.smul_def, Finset.sum_mul]
    simpa only [mul_assoc, add_comm] using h1

end
end AffineCurveCounting
