module

public import AffineCurveCounting.Interpolation
public import ArithmeticHeights.BombieriVaaler

/-!
# Bombieri–Vaaler applied to polynomial interpolation

This is the small-coefficient auxiliary-polynomial step of the determinant method.
It does not yet ensure nondivisibility by a defining polynomial. Establishing that property
requires the global determinant lower bound and the Hilbert-function argument in CCDN §3.3.
-/

@[expose] public section

namespace AffineCurveCounting

open Matrix

theorem abs_coefficient_polynomialOfCoefficients_le {n N : ℕ}
    (mon : Fin N → (Fin n →₀ ℕ)) (hmon : Function.Injective mon)
    (v : Fin N → ℤ) {R : ℝ} (hR : 0 ≤ R) (hv : ∀ j, |(v j : ℝ)| ≤ R)
    (e : Fin n →₀ ℕ) :
    |((polynomialOfCoefficients mon v).coeff e : ℝ)| ≤ R := by
  classical
  by_cases he : ∃ j, mon j = e
  · obtain ⟨j, rfl⟩ := he
    rw [coefficient_polynomialOfCoefficients mon hmon]
    exact hv j
  · have hz : (polynomialOfCoefficients mon v).coeff e = 0 := by
      simp [polynomialOfCoefficients, MvPolynomial.coeff_monomial, not_exists.mp he]
    simpa [hz] using hR

/-- A rank-`s` evaluation matrix on `N > s` distinct monomials admits a nonzero
vanishing polynomial with the exact Bombieri–Vaaler coefficient bound.
Every coefficient is bounded, including coefficients outside the specified monomial list. -/
theorem exists_small_vanishing_polynomial {n N s M : ℕ}
    (mon : Fin N → (Fin n →₀ ℕ)) (hmon : Function.Injective mon)
    (points : Fin s → (Fin n → ℤ)) (hsN : s < N)
    (hdeg : ∀ j, (mon j).sum (fun _ e => e) ≤ M)
    (hrank : LinearIndependent ℚ
      ((evaluationMatrix mon points).map ((↑) : ℤ → ℚ)).row) :
    ∃ g : MvPolynomial (Fin n) ℤ, g ≠ 0 ∧ g.totalDegree ≤ M ∧
      (∀ i, MvPolynomial.eval (points i) g = 0) ∧
      ∀ e, |(g.coeff e : ℝ)| ≤
        (Real.sqrt (((evaluationMatrix mon points * (evaluationMatrix mon points)ᵀ).det : ℤ) : ℝ) /
          ((Int.Matrix.minorGcd (evaluationMatrix mon points) : ℤ) : ℝ)) ^
            (((N : ℝ) - s)⁻¹) := by
  classical
  let A := evaluationMatrix mon points
  obtain ⟨v, hv, hAv, hsmall⟩ :=
    Int.Matrix.exists_ne_zero_mulVec_eq_zero_iSup_abs_le_det_rpow A hrank
      (by simpa using hsN)
  simp only [Fintype.card_fin] at hsmall
  refine ⟨polynomialOfCoefficients mon v, polynomialOfCoefficients_ne_zero mon hmon hv,
    totalDegree_polynomialOfCoefficients_le mon v hdeg,
    vanishes_of_evaluationMatrix_mulVec_eq_zero mon points v hAv, ?_⟩
  apply abs_coefficient_polynomialOfCoefficients_le mon hmon v
  · apply Real.rpow_nonneg
    have hD : 1 ≤ Int.Matrix.minorGcd A := Int.Matrix.one_le_minorGcd hrank
    have hDR : (0 : ℝ) ≤ (Int.Matrix.minorGcd A : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ Int.Matrix.minorGcd A)
    exact div_nonneg (Real.sqrt_nonneg _) hDR
  · intro j
    have hj : |v j| ≤ ⨆ k, |v k| := le_ciSup (Set.finite_range (fun k => |v k|)).bddAbove j
    have hjR : |(v j : ℝ)| ≤ ((⨆ k, |v k| : ℤ) : ℝ) := by exact_mod_cast hj
    exact hjR.trans hsmall

end AffineCurveCounting
