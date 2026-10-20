module

public import AffineCurveCounting.HomogeneousRank
public import AffineCurveCounting.Nondivisibility

/-! Bombieri--Vaaler for complete homogeneous evaluation matrices. The defining
equation supplies rank deficiency, and selected rows span the whole point set. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Matrix

/-- An actual homogeneous equation yields a small homogeneous polynomial
vanishing at every given integral point. No monomial list, selected rows,
rank deficiency, or spanning hypothesis is supplied by the caller. -/
theorem exists_small_homogeneous_vanishing_polynomial {n d M t : ℕ}
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hdM : d ≤ M)
    (points : Fin t → (Fin (n + 1) → ℤ)) (hzero : ∀ i, eval (points i) f = 0) :
    ∃ (s : ℕ) (a : Fin s → Fin t), Function.Injective a ∧ s < (n + M).choose M ∧
      s + (n + (M - d)).choose (M - d) ≤ (n + M).choose M ∧
      LinearIndependent ℚ
        ((evaluationMatrix (homogeneousMonomials n M) (points ∘ a)).map ((↑) : ℤ → ℚ)).row ∧
      ∃ g : MvPolynomial (Fin (n + 1)) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
        (∀ i, eval (points i) g = 0) ∧ ∀ e, |(g.coeff e : ℝ)| ≤
          (Real.sqrt (((evaluationMatrix (homogeneousMonomials n M) (points ∘ a) *
            (evaluationMatrix (homogeneousMonomials n M) (points ∘ a))ᵀ).det : ℤ) : ℝ) /
            (Int.Matrix.minorGcd (evaluationMatrix (homogeneousMonomials n M) (points ∘ a)) : ℝ)) ^
              ((((n + M).choose M : ℝ) - s)⁻¹) := by
  classical
  obtain ⟨s, a, ha, hli, hspan, hs⟩ := homogeneous_independent_evaluation_rows f hf hf0 hdM points hzero
  have hdeficit := integer_homogeneous_rows_hilbert_bound f hf hf0 hdM (points ∘ a)
    (fun i => hzero (a i)) hli
  let mon := homogeneousMonomials n M
  let A := evaluationMatrix mon (points ∘ a)
  obtain ⟨v, hv, hAv, hsmall⟩ :=
    Int.Matrix.exists_ne_zero_mulVec_eq_zero_iSup_abs_le_det_rpow A hli (by simpa using hs)
  simp only [Fintype.card_fin] at hsmall
  refine ⟨s, a, ha, hs, hdeficit, hli, polynomialOfCoefficients mon v,
    polynomialOfCoefficients_ne_zero mon (homogeneousMonomials_injective n M) hv,
    polynomialOfCoefficients_homogeneous n M v, ?_, ?_⟩
  · intro i
    apply vanishes_of_evaluation_row_mem_span mon (points ∘ a) v hAv (points i)
    rw [hspan]
    exact Submodule.subset_span ⟨i, rfl⟩
  · apply abs_coefficient_polynomialOfCoefficients_le mon (homogeneousMonomials_injective n M) v
    · apply Real.rpow_nonneg
      have hD := Int.Matrix.one_le_minorGcd hli
      exact div_nonneg (Real.sqrt_nonneg _) (by exact_mod_cast (show (0 : ℤ) ≤ _ by omega))
    · intro j
      have hj : |v j| ≤ ⨆ k, |v k| := le_ciSup (Set.finite_range (fun k => |v k|)).bddAbove j
      have hjR : |(v j : ℝ)| ≤ ((⨆ k, |v k| : ℤ) : ℝ) := by exact_mod_cast hj
      exact hjR.trans hsmall

end
end AffineCurveCounting
