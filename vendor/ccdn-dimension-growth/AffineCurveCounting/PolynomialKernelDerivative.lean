module

public import AffineCurveCounting.PolynomialKernelOrigin

/-! Differentiate a polynomial family of linear relations at zero. If the
specialized kernel is one-dimensional, its prescribed generator extends to
first order, giving the reconstruction equation needed for a plane projection. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Polynomial Matrix

lemma polynomial_matrix_kernel_coeff_zero {K ι κ : Type*} [Field K] [Fintype κ]
    (A : Matrix ι κ (Polynomial K)) (v : κ → Polynomial K) (hv : A *ᵥ v = 0) :
    (A.map (fun p => p.coeff 0)) *ᵥ (fun j => (v j).coeff 0) = 0 := by
  funext i
  have hh := congrArg (fun p : Polynomial K => p.coeff 0) (congrFun hv i)
  simpa only [mulVec, dotProduct, finsetSum_coeff, mul_coeff_zero,
    Pi.zero_apply, coeff_zero, Matrix.map_apply] using hh

lemma polynomial_matrix_kernel_coeff_one {K ι κ : Type*} [Field K] [Fintype κ]
    (A : Matrix ι κ (Polynomial K)) (v : κ → Polynomial K) (hv : A *ᵥ v = 0) :
    (A.map (fun p => p.coeff 0)) *ᵥ (fun j => (v j).coeff 1) +
      (A.map (fun p => p.coeff 1)) *ᵥ (fun j => (v j).coeff 0) = 0 := by
  funext i
  have hh := congrArg (fun p : Polynomial K => p.coeff 1) (congrFun hv i)
  simpa only [mulVec, dotProduct, finsetSum_coeff, mul_coeff_one,
    Pi.zero_apply, coeff_zero, Matrix.map_apply, Pi.add_apply, Finset.sum_add_distrib] using hh

/-- Persistent dependence and a one-dimensional specialized kernel imply the
first-order relation A(0)*g + A'(0)*f = 0 for its generator f. -/
theorem polynomial_matrix_kernel_first_order {K ι κ : Type*} [Field K] [CharZero K]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ (Polynomial K))
    (hA : ∀ k : ℕ, ¬ Function.Injective (A.map (Polynomial.evalRingHom (k : K))).mulVecLin)
    (f : κ → K)
    (hker : ∀ v : κ → K, (A.map (fun p => p.coeff 0)) *ᵥ v = 0 →
      ∃ c : K, v = c • f) :
    ∃ g : κ → K, (A.map (fun p => p.coeff 0)) *ᵥ g +
      (A.map (fun p => p.coeff 1)) *ᵥ f = 0 := by
  obtain ⟨v, hv, j, hj⟩ := polynomial_matrix_kernel_nonzero_at_zero A hA
  obtain ⟨c, hc⟩ := hker _ (polynomial_matrix_kernel_coeff_zero A v hv)
  have hcn : c ≠ 0 := by
    intro hz
    have hh := congrFun hc j
    rw [hz, zero_smul, Pi.zero_apply, coeff_zero_eq_eval_zero] at hh
    exact hj hh
  have hh := polynomial_matrix_kernel_coeff_one A v hv
  rw [hc, Matrix.mulVec_smul] at hh
  refine ⟨c⁻¹ • (fun j => (v j).coeff 1), ?_⟩
  rw [Matrix.mulVec_smul]
  have he := congrArg (fun w : ι → K => c⁻¹ • w) hh
  simpa only [smul_add, smul_smul, inv_mul_cancel₀ hcn, one_smul, smul_zero] using he

end
end AffineCurveCounting
