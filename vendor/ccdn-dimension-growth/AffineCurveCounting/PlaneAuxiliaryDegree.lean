module

public import AffineCurveCounting.PlaneChartHeight

/-! Quantitative degree control from the plane determinant comparison.
The finite-field estimate remains an explicit input through PlaneChartHeight. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Real

lemma plane_rank_ge_degree_parameter {s d M : ℕ} (hd : 0 < d) (hdM : d ≤ M)
    (hr : 2 * s + d ^ 2 = d * (2 * M + 3)) : M ≤ s := by
  have h := Nat.mul_le_mul_left (d - 1) hdM
  have he : d - 1 + 1 = d := Nat.sub_add_cancel hd
  nlinarith

lemma plane_rank_archimedean_error {s d M : ℕ} (hd : 0 < d) (hdM : d ≤ M)
    (hr : 2 * s + d ^ 2 = d * (2 * M + 3)) :
    Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) ≤
      5 * (s : ℝ) ^ 2 / 2 := by
  have hMs := plane_rank_ge_degree_parameter hd hdM hr
  have hs : 0 < s := lt_of_lt_of_le (lt_of_lt_of_le hd hdM) hMs
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hMsR : (M : ℝ) ≤ s := by exact_mod_cast hMs
  have hl := (Real.log_le_sub_one_of_pos hsR).trans (by linarith : (s : ℝ) - 1 ≤ s)
  have hf : Real.log (s.factorial : ℝ) ≤ (s : ℝ) * Real.log s := by
    have hp : (s.factorial : ℝ) ≤ (s : ℝ) ^ s := by exact_mod_cast Nat.factorial_le_pow s
    simpa only [Real.log_pow] using Real.log_le_log (by positivity) hp
  have hn : (0 : ℝ) < (2 + M).choose M := by
    exact_mod_cast Nat.choose_pos (show M ≤ 2 + M by omega)
  have hdim : 2 * ((2 + M).choose M : ℝ) = ((M : ℝ) + 2) * (M + 1) := by
    exact_mod_cast ternary_homogeneous_dimension M
  have hbound : ((2 + M).choose M : ℝ) ≤ ((M : ℝ) + 2) ^ 2 := by nlinarith
  have hlog : Real.log ((2 + M).choose M) ≤ 4 * s := by
    have h := Real.log_le_log hn hbound
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    have h' := Real.log_le_sub_one_of_pos (show (0 : ℝ) < M + 2 by positivity)
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hl hsR.le,
    mul_le_mul_of_nonneg_left hlog hsR.le]

/-- The small-height case of the plane auxiliary-degree calculation. The
coefficient obstruction is retained with its exact exponent 1/d². -/
theorem plane_auxiliary_log_degree_bound {s d M : ℕ} {B L A K : ℝ}
    (hd : 0 < d) (hdM : d ≤ M)
    (hr : 2 * s + d ^ 2 = d * (2 * M + 3))
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hML : Real.log B ≤ M)
    (hheight : Real.log L ≤ 4 * d * Real.log B)
    (hcomparison : (s : ℝ) ^ 2 / 2 *
        (Real.log s - 4 * Real.log d - Real.log A - K) ≤
      Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) +
        s * M * Real.log B - (((2 + M).choose M : ℝ) - s) * Real.log L) :
    Real.log M ≤ K + 23 + Real.log 2 + 3 * Real.log d + Real.log A +
      2 / d * Real.log B - Real.log L / (d : ℝ) ^ 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hMR : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le hd hdM
  have hdMR : (d : ℝ) ≤ M := by exact_mod_cast hdM
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hMs := plane_rank_ge_degree_parameter hd hdM hr
  have hsR : (0 : ℝ) < s := by exact_mod_cast lt_of_lt_of_le (lt_of_lt_of_le hd hdM) hMs
  have he : 2 * (s : ℝ) + (d : ℝ) ^ 2 = d * (2 * M + 3) := by exact_mod_cast hr
  have hslo : (d : ℝ) * M ≤ 2 * s := by nlinarith
  have hshi : (s : ℝ) ≤ d * (M + 1) := by nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hdim : 2 * ((2 + M).choose M : ℝ) = ((M : ℝ) + 2) * (M + 1) := by
    exact_mod_cast ternary_homogeneous_dimension M
  have hsquare : (s : ℝ) ^ 2 ≤ 2 * (d : ℝ) ^ 2 * ((2 + M).choose M) := by
    have hsq := pow_le_pow_left₀ hsR.le hshi 2
    nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) (show 0 ≤ (M : ℝ) + 1 by positivity)]
  have hlogB := Real.log_nonneg hB
  have hlogL := Real.log_nonneg hL
  have harch := plane_rank_archimedean_error hd hdM hr
  have hbasic : Real.log s - 4 * Real.log d - Real.log A - K ≤
      5 + 2 * M / s * Real.log B -
        2 * (((2 + M).choose M : ℝ) - s) / (s : ℝ) ^ 2 * Real.log L := by
    have hc : Real.log s - 4 * Real.log d - Real.log A - K ≤
        (Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) +
          s * M * Real.log B - (((2 + M).choose M : ℝ) - s) * Real.log L) /
            ((s : ℝ) ^ 2 / 2) := (le_div_iff₀ (show (0 : ℝ) < (s : ℝ) ^ 2 / 2 by positivity)).mpr
      (by simpa only [mul_comm] using hcomparison)
    calc
      _ ≤ _ := hc
      _ ≤ (5 * (s : ℝ) ^ 2 / 2 + s * M * Real.log B -
          (((2 + M).choose M : ℝ) - s) * Real.log L) / ((s : ℝ) ^ 2 / 2) := by
        gcongr
      _ = _ := by field_simp
  have hbox : 2 * (M : ℝ) / s * Real.log B ≤ 2 / d * Real.log B + 2 := by
    have hrat : 2 * (M : ℝ) / s ≤ 2 / d + 2 / M := by
      apply (div_le_iff₀ hsR).mpr
      field_simp
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hrat hlogB
    have hrem : 2 / (M : ℝ) * Real.log B ≤ 2 := by
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hMR).mpr (by linarith)
    nlinarith
  have hcoef : Real.log L / (d : ℝ) ^ 2 - 16 ≤
      2 * (((2 + M).choose M : ℝ) - s) / (s : ℝ) ^ 2 * Real.log L := by
    have hrat : 1 / (d : ℝ) ^ 2 - 2 / s ≤
        2 * (((2 + M).choose M : ℝ) - s) / (s : ℝ) ^ 2 := by
      apply (le_div_iff₀ (show (0 : ℝ) < (s : ℝ) ^ 2 by positivity)).mpr
      field_simp
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hrat hlogL
    have hrem : 2 / (s : ℝ) * Real.log L ≤ 16 := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hsR).mpr
      have hh := mul_le_mul_of_nonneg_left hML hdR.le
      nlinarith
    simp only [sub_mul, one_div, inv_mul_eq_div] at hh
    linarith
  have hlogs : Real.log d + Real.log M - Real.log 2 ≤ Real.log s := by
    have h := Real.log_le_log (show (0 : ℝ) < d * M / 2 by positivity)
      (show (d : ℝ) * M / 2 ≤ s by linarith)
    rwa [Real.log_div (by positivity) (by norm_num), Real.log_mul hdR.ne' hMR.ne'] at h
  linarith

/-- Exponentiation of the logarithmic degree bound, keeping the coefficient
saving and the leading box exponent unchanged. -/
lemma plane_degree_bound_of_log_bound {d M : ℕ} {B L A K : ℝ}
    (hd : 0 < d) (hM : 0 < M) (hB : 0 < B) (hL : 0 < L) (hA : 0 < A)
    (hlog : Real.log M ≤ K + 23 + Real.log 2 + 3 * Real.log d + Real.log A +
      2 / d * Real.log B - Real.log L / (d : ℝ) ^ 2) :
    (M : ℝ) ≤ 2 * Real.exp (K + 23) * (d : ℝ) ^ 3 * A * B ^ (2 / (d : ℝ)) /
      L ^ (1 / (d : ℝ) ^ 2) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  apply (Real.log_le_log_iff hMR (by positivity)).mp
  rw [Real.log_div (by positivity) (by positivity)]
  simp only [Real.log_mul (by positivity : (2 : ℝ) ≠ 0) (Real.exp_pos _).ne',
    Real.log_mul (by positivity : 2 * Real.exp (K + 23) ≠ 0) (by positivity : (d : ℝ) ^ 3 ≠ 0),
    Real.log_mul (by positivity : 2 * Real.exp (K + 23) * (d : ℝ) ^ 3 ≠ 0) hA.ne',
    Real.log_mul (by positivity : 2 * Real.exp (K + 23) * (d : ℝ) ^ 3 * A ≠ 0)
      (Real.rpow_pos_of_pos hB _).ne', Real.log_exp, Real.log_pow, Real.log_rpow hB,
    Real.log_rpow hL]
  convert hlog using 1
  push_cast
  ring

/-- A degree exceeding the proved small-height threshold gives an actual
integer homogeneous auxiliary polynomial. The sharp finite-field count is
still required, explicitly, as in the determinant theorem. -/
theorem plane_chart_exists_auxiliary_small_height
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d M t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d) (hdM : d ≤ M)
    (hdchart : (planeAffineChart f).totalDegree = d)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) (planeAffineChart f)))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : ∀ m, |((planeAffineChart f).coeff m : ℝ)| ≤ H)
    (z : Fin t → Fin 2 → ℤ) (hz : ∀ i, MvPolynomial.eval (z i) (planeAffineChart f) = 0)
    {B C : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(z i j : ℝ)| ≤ B) (hC : 0 ≤ C)
    (hML : Real.log B ≤ M)
    (hheight : Real.log |((order.leadingCoeff f : ℤ) : ℝ)| ≤ 4 * d * Real.log B)
    (hthreshold : 2 * Real.exp (heightDeterminantError C + 23) * (d : ℝ) ^ 3 *
      (1 + Real.log H / (d : ℝ) ^ 2) * B ^ (2 / (d : ℝ)) /
        |((order.leadingCoeff f : ℤ) : ℝ)| ^ (1 / (d : ℝ) ^ 2) < M)
    (hcount : ∀ p : ℕ, p.Prime → 27 * (d : ℝ) ^ 4 < (p : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod p)) (planeAffineChart f)) →
      (Nat.card (PlaneResidue (planeAffineChart f) p) : ℝ) ≤
        p + C * (d : ℝ) ^ 2 * Real.sqrt p) :
    ∃ g : MvPolynomial (Fin 3) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
      (∀ i, MvPolynomial.eval (Fin.cons 1 (z i)) g = 0) ∧ ¬ f ∣ g := by
  classical
  by_contra hnone
  have hrel : ∀ g : MvPolynomial (Fin 3) ℤ, g.IsHomogeneous M →
      (∀ i, MvPolynomial.eval (Fin.cons 1 (z i)) g = 0) → f ∣ g := by
    intro g hg hv
    by_cases hg0 : g = 0
    · simp [hg0]
    · by_contra hnd
      exact hnone ⟨g, hg0, hg, hv, hnd⟩
  have hdchart' : 0 < (planeAffineChart f).totalDegree := by simpa only [hdchart] using hd
  have hcount' := hcount
  rw [← hdchart] at hcount'
  obtain ⟨s, _, _, hr, hc⟩ := plane_chart_no_auxiliary_height_comparison
    order f hf hf0 hd hdM hdchart' hir H hH hcoeff z hz hB hbox hC hrel hcount'
  rw [hdchart] at hc
  have hL : 1 ≤ |((order.leadingCoeff f : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (order.leadingCoeff_ne_zero_iff.mpr hf0)
  have hlog := plane_auxiliary_log_degree_bound hd hdM hr hB hL hML hheight hc
  have hA : 0 < 1 + Real.log H / (d : ℝ) ^ 2 := by
    have := Real.log_nonneg hH
    positivity
  have hbound := plane_degree_bound_of_log_bound hd (lt_of_lt_of_le hd hdM)
    (by linarith) (by linarith) hA hlog
  exact (not_lt_of_ge hbound) hthreshold

end
end AffineCurveCounting
