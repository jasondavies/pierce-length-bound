module

public import AffineCurveCounting.HomogeneousRankDichotomy

/-! Coefficient height controls homogeneous evaluations, uniformly on the
integer point box, with the exact number of monomials. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem homogeneous_integer_evaluation_bound {n d : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d)
    {H R : ℝ} (hH : 0 ≤ H) (hR : 1 ≤ R) (hcoeff : ∀ m, |(f.coeff m : ℝ)| ≤ H)
    (x : Fin (n + 1) → ℤ) (hx : ∀ j, |(x j : ℝ)| ≤ R) :
    |(eval x f : ℝ)| ≤ ((n + d).choose d : ℝ) * H * R ^ d := by
  classical
  conv_lhs => rw [homogeneous_eq_sum_coeff f hf]
  simp only [map_sum, eval_monomial, Int.cast_sum, Int.cast_mul]
  calc
    _ ≤ ∑ j, |(f.coeff (homogeneousMonomials n d j) : ℝ) *
      (((homogeneousMonomials n d j).prod (fun i k => x i ^ k) : ℤ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin ((n + d).choose d), H * R ^ d := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hcoeff _) (abs_monomial_value_le _ x hR hx
        (homogeneousMonomials_degree n d j).le) (abs_nonneg _) hH
    _ = _ := by simp [mul_assoc]

lemma ternary_homogeneous_dimension_le_square (d : ℕ) :
    ((2 + d).choose d : ℝ) ≤ ((d : ℝ) + 2) ^ 2 := by
  have h : 2 * ((2 + d).choose d : ℝ) = ((d : ℝ) + 2) * (d + 1) := by
    exact_mod_cast ternary_homogeneous_dimension d
  nlinarith [show (0 : ℝ) ≤ d by positivity]

end
end AffineCurveCounting
