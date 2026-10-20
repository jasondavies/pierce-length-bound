module

public import AffineCurveCounting.InfinityEvaluationSpan

/-! Homogeneous polynomials with extension-field coefficients contribute no
new directions beyond the extension-field span of ground-field monomials. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma homogeneous_extension_evaluation_mem {K L σ ι : Type*} [Field K] [Field L]
    [Algebra K L] (z : ι → σ → L) (m : ℕ) (p : MvPolynomial σ L)
    (hp : p.IsHomogeneous m) :
    (fun i => MvPolynomial.eval (z i) p) ∈
      Submodule.span L (Set.range (homogeneousPointEvaluation (K := K) z m)) := by
  classical
  let W := Submodule.span L (Set.range (homogeneousPointEvaluation (K := K) z m))
  have hdeg (e : σ →₀ ℕ) (he : e ∈ p.support) : e.degree = m :=
    by
      rw [Finsupp.degree_eq_weight_one, ← Pi.one_def]
      exact hp (mem_support_iff.mp he)
  have hmono (e : σ →₀ ℕ) (he : e ∈ p.support) :
      (fun i => MvPolynomial.eval (z i) (monomial e (p.coeff e))) ∈ W := by
    let q : homogeneousSubmodule σ K m := ⟨monomial e 1, isHomogeneous_monomial 1 (hdeg e he)⟩
    have hq : homogeneousPointEvaluation (K := K) z m q ∈ W := Submodule.subset_span ⟨q, rfl⟩
    have hval : (fun i => MvPolynomial.eval (z i) (monomial e (p.coeff e))) =
        p.coeff e • homogeneousPointEvaluation (K := K) z m q := by
      funext i
      simp [homogeneousPointEvaluation, q, MvPolynomial.eval_monomial, aeval_monomial]
    rw [hval]
    exact W.smul_mem _ hq
  have hsum : (fun i => MvPolynomial.eval (z i) p) =
      ∑ e ∈ p.support, (fun i => MvPolynomial.eval (z i) (monomial e (p.coeff e))) := by
    funext i
    simpa only [Finset.sum_apply, map_sum] using congrArg (MvPolynomial.eval (z i)) p.as_sum
  rw [hsum]
  exact W.sum_mem hmono

end
end AffineCurveCounting
