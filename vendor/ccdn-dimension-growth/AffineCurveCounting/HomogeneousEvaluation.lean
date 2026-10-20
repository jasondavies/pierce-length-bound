module

public import AffineCurveCounting.HomogeneousMonomials
public import AffineCurveCounting.RowSelection

/-! Actual homogeneous equations give nonzero relations on the complete
homogeneous evaluation matrix and hence strictly deficient row rank. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Matrix

lemma homogeneous_eq_sum_coeff {K : Type*} [CommSemiring K] {n M : ℕ}
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous M) :
    f = ∑ j, monomial (homogeneousMonomials n M j) (f.coeff (homogeneousMonomials n M j)) := by
  classical
  ext p
  by_cases hp : p.sum (fun _ e => e) = M
  · obtain ⟨j, rfl⟩ := homogeneousMonomials_surjective n M p hp
    simp [coeff_monomial, (homogeneousMonomials_injective n M).eq_iff]
  · have hc := hf.coeff_eq_zero hp
    rw [hc, coeff_sum]
    symm
    apply Finset.sum_eq_zero
    intro j _
    rw [coeff_monomial, ite_eq_right]
    intro h
    apply hp
    rw [← h]
    exact homogeneousMonomials_degree n M j

lemma homogeneous_coefficients_ne_zero {n M : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous M) (hf0 : f ≠ 0) :
    (fun j => f.coeff (homogeneousMonomials n M j)) ≠ 0 := by
  intro h
  apply hf0
  rw [homogeneous_eq_sum_coeff f hf]
  have hz : ∀ j, f.coeff (homogeneousMonomials n M j) = 0 := fun j => congrFun h j
  simp only [hz, monomial_zero, Finset.sum_const_zero]

lemma homogeneous_evaluation_kernel {n M t : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous M)
    (points : Fin t → (Fin (n + 1) → ℤ)) (hzero : ∀ i, eval (points i) f = 0) :
    evaluationMatrix (homogeneousMonomials n M) points *ᵥ
      (fun j => f.coeff (homogeneousMonomials n M j)) = 0 := by
  have he : polynomialOfCoefficients (homogeneousMonomials n M)
      (fun j => f.coeff (homogeneousMonomials n M j)) = f :=
    (homogeneous_eq_sum_coeff f hf).symm
  ext i
  rw [← eval_polynomialOfCoefficients, he]
  exact hzero i

/-- Select an actual spanning family of independent evaluation rows. The
homogeneous equation, padded to degree `M`, proves strict rank deficiency. -/
theorem homogeneous_independent_evaluation_rows {n d M t : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hdM : d ≤ M)
    (points : Fin t → (Fin (n + 1) → ℤ)) (hzero : ∀ i, eval (points i) f = 0) :
    ∃ (s : ℕ) (a : Fin s → Fin t), Function.Injective a ∧
      LinearIndependent ℚ
        ((evaluationMatrix (homogeneousMonomials n M) (points ∘ a)).map ((↑) : ℤ → ℚ)).row ∧
      Submodule.span ℚ (Set.range
        ((evaluationMatrix (homogeneousMonomials n M) (points ∘ a)).map ((↑) : ℤ → ℚ)).row) =
      Submodule.span ℚ (Set.range
        ((evaluationMatrix (homogeneousMonomials n M) points).map ((↑) : ℤ → ℚ)).row) ∧
      s < (n + M).choose M := by
  let F := f * X (0 : Fin (n + 1)) ^ (M - d)
  have hF : F.IsHomogeneous M := by
    simpa only [Nat.add_sub_of_le hdM] using hf.mul (isHomogeneous_X_pow (0 : Fin (n + 1)) (M - d))
  have hF0 : F ≠ 0 := mul_ne_zero hf0 (pow_ne_zero _ (X_ne_zero _))
  have hFzero : ∀ i, eval (points i) F = 0 := by
    intro i
    simp only [F, eval_mul, hzero i, zero_mul]
  let v := fun j => F.coeff (homogeneousMonomials n M j)
  have hv : (fun j => (v j : ℚ)) ≠ 0 := by
    intro h
    apply homogeneous_coefficients_ne_zero F hF hF0
    funext j
    have hj := congrFun h j
    change (v j : ℚ) = 0 at hj
    change v j = 0
    exact_mod_cast hj
  have hk := homogeneous_evaluation_kernel F hF points hFzero
  have hkQ : ((evaluationMatrix (homogeneousMonomials n M) points).map ((↑) : ℤ → ℚ)) *ᵥ
      (fun j => (v j : ℚ)) = 0 := by
    ext i
    have hi := congrFun hk i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at hi ⊢
    dsimp only [v]
    exact_mod_cast hi
  obtain ⟨s, a, ha, hli, hspan, hs⟩ := exists_independent_spanning_rows_lt _ _ hv hkQ
  exact ⟨s, a, ha, hli, hspan, hs⟩

end
end AffineCurveCounting
