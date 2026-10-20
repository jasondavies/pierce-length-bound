module

public import AffineCurveCounting.AuxiliaryPolynomial

/-!
# Small coefficients exclude polynomial multiples

The arithmetic point is that a nonzero integer multiplier has a leading coefficient of
absolute value at least one. This is the coefficient obstruction used in CCDN §3.3.
The determinant bound needed to make the auxiliary polynomial small enough remains separate.
-/

@[expose] public section

namespace AffineCurveCounting

theorem abs_leadingCoeff_le_of_dvd {n : ℕ} (order : MonomialOrder (Fin n))
    {f g : MvPolynomial (Fin n) ℤ} (hg : g ≠ 0) (hfg : f ∣ g) :
    |order.leadingCoeff f| ≤ |order.leadingCoeff g| := by
  obtain ⟨q, rfl⟩ := hfg
  have hq : q ≠ 0 := by intro h; simp [h] at hg
  have hq1 := Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hq)
  rw [MonomialOrder.leadingCoeff_mul, abs_mul]
  nlinarith [abs_nonneg (order.leadingCoeff f)]

theorem not_dvd_of_coefficients_lt_leadingCoeff {n : ℕ}
    (order : MonomialOrder (Fin n)) {f g : MvPolynomial (Fin n) ℤ}
    (hg : g ≠ 0) {R : ℝ} (hcoeff : ∀ e, |(g.coeff e : ℝ)| ≤ R)
    (hR : R < |((order.leadingCoeff f : ℤ) : ℝ)|) : ¬ f ∣ g := by
  intro hfg
  have hle := abs_leadingCoeff_le_of_dvd order hg hfg
  have hleR : |((order.leadingCoeff f : ℤ) : ℝ)| ≤ |((order.leadingCoeff g : ℤ) : ℝ)| := by
    exact_mod_cast hle
  have hgc : |((order.leadingCoeff g : ℤ) : ℝ)| ≤ R := hcoeff (order.degree g)
  linarith

/-- The auxiliary polynomial is not a multiple of `f` when the determinant estimate gives
the strict coefficient threshold. The threshold is an explicit numerical inequality. -/
theorem exists_auxiliary_not_dvd {n N s M : ℕ}
    (order : MonomialOrder (Fin n)) (f : MvPolynomial (Fin n) ℤ)
    (mon : Fin N → (Fin n →₀ ℕ)) (hmon : Function.Injective mon)
    (points : Fin s → (Fin n → ℤ)) (hsN : s < N)
    (hdeg : ∀ j, (mon j).sum (fun _ e => e) ≤ M)
    (hrank : LinearIndependent ℚ
      ((evaluationMatrix mon points).map ((↑) : ℤ → ℚ)).row)
    (hthreshold :
      (Real.sqrt (((evaluationMatrix mon points * (evaluationMatrix mon points).transpose).det : ℤ) : ℝ) /
        ((Int.Matrix.minorGcd (evaluationMatrix mon points) : ℤ) : ℝ)) ^
          (((N : ℝ) - s)⁻¹) < |((order.leadingCoeff f : ℤ) : ℝ)|) :
    ∃ g : MvPolynomial (Fin n) ℤ, g ≠ 0 ∧ g.totalDegree ≤ M ∧
      (∀ i, MvPolynomial.eval (points i) g = 0) ∧ ¬ f ∣ g := by
  obtain ⟨g, hg, hdegG, hvan, hcoeff⟩ :=
    exists_small_vanishing_polynomial mon hmon points hsN hdeg hrank
  exact ⟨g, hg, hdegG, hvan,
    not_dvd_of_coefficients_lt_leadingCoeff order hg hcoeff hthreshold⟩

end AffineCurveCounting
