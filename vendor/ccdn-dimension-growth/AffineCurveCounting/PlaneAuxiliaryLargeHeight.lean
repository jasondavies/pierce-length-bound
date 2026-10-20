module

public import AffineCurveCounting.PlaneAuxiliaryDegree

/-! The complementary large-coefficient-height auxiliary-degree estimate. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Real

lemma log_one_add_sub_quarter_le {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) - x / 4 ≤ Real.log 4 + 1 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (1 + x) / 4 by positivity)
  rw [Real.log_div (by positivity) (by norm_num)] at h
  linarith

set_option maxHeartbeats 800000 in
/-- When the coefficient height exceeds B^(4d), a degree at least 32d
satisfying the no-auxiliary comparison is bounded by a constant times d³.
The constant includes the loss in positioning the leading coefficient. -/
theorem plane_auxiliary_large_height_log_bound {s d M : ℕ} {B L H T K : ℝ}
    (hd : 0 < d) (hMlarge : 32 * d ≤ M)
    (hr : 2 * s + d ^ 2 = d * (2 * M + 3))
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hH : 1 ≤ H) (hT : 0 ≤ T)
    (hheight : 4 * d * Real.log B ≤ Real.log H)
    (hposition : Real.log H ≤ Real.log L + T * (d : ℝ) ^ 2)
    (hcomparison : (s : ℝ) ^ 2 / 2 *
        (Real.log s - 4 * Real.log d - Real.log (1 + Real.log H / (d : ℝ) ^ 2) - K) ≤
      Real.log (s.factorial : ℝ) / 2 + (s : ℝ) / 2 * Real.log ((2 + M).choose M) +
        s * M * Real.log B - (((2 + M).choose M : ℝ) - s) * Real.log L) :
    Real.log M ≤ K + 6 + Real.log 2 + Real.log 4 + T + 3 * Real.log d := by
  let A := 1 + Real.log H / (d : ℝ) ^ 2
  change _ ≤ _ at hcomparison
  have hdM : d ≤ M := by omega
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

  have hMlargeR : 32 * (d : ℝ) ≤ M := by exact_mod_cast hMlarge
  have hslarge : 16 * (d : ℝ) ^ 2 ≤ s := by nlinarith
  have hboxrat : 2 * (M : ℝ) / s ≤ (5 / 2 : ℝ) / d := by
    apply (div_le_iff₀ hsR).mpr
    field_simp
    nlinarith
  have hcoefrat : (7 / 8 : ℝ) / (d : ℝ) ^ 2 ≤
      2 * (((2 + M).choose M : ℝ) - s) / (s : ℝ) ^ 2 := by
    have hrat : 1 / (d : ℝ) ^ 2 - 2 / s ≤
        2 * (((2 + M).choose M : ℝ) - s) / (s : ℝ) ^ 2 := by
      apply (le_div_iff₀ (show (0 : ℝ) < (s : ℝ) ^ 2 by positivity)).mpr
      field_simp
      nlinarith
    have hrem : 2 / (s : ℝ) ≤ (1 / 8 : ℝ) / (d : ℝ) ^ 2 := by
      apply (div_le_iff₀ hsR).mpr
      field_simp
      nlinarith
    have hid : (7 / 8 : ℝ) / (d : ℝ) ^ 2 =
        1 / (d : ℝ) ^ 2 - (1 / 8 : ℝ) / (d : ℝ) ^ 2 := by ring
    linarith only [hrat, hrem, hid]
  have hbox : 2 * (M : ℝ) / s * Real.log B ≤
      5 / 8 * (Real.log H / (d : ℝ) ^ 2) := by
    have hh := mul_le_mul_of_nonneg_right hboxrat hlogB
    have hh' : (5 / 2 : ℝ) / d * Real.log B ≤
        5 / 8 * (Real.log H / (d : ℝ) ^ 2) := by
      field_simp
      nlinarith
    exact hh.trans hh'
  have hcoef : 7 / 8 * (Real.log H / (d : ℝ) ^ 2) - 7 / 8 * T ≤
      2 * (((2 + M).choose M : ℝ) - s) / (s : ℝ) ^ 2 * Real.log L := by
    have hh := mul_le_mul_of_nonneg_right hcoefrat hlogL
    have hh' : 7 / 8 * (Real.log H / (d : ℝ) ^ 2) - 7 / 8 * T ≤
        (7 / 8 : ℝ) / (d : ℝ) ^ 2 * Real.log L := by
      field_simp
      nlinarith
    exact hh'.trans hh
  have hlogs : Real.log d + Real.log M - Real.log 2 ≤ Real.log s := by
    have h := Real.log_le_log (show (0 : ℝ) < d * M / 2 by positivity)
      (show (d : ℝ) * M / 2 ≤ s by linarith)
    rwa [Real.log_div (by positivity) (by norm_num), Real.log_mul hdR.ne' hMR.ne'] at h
  have hlogH := Real.log_nonneg hH
  have hlogA := log_one_add_sub_quarter_le (show 0 ≤ Real.log H / (d : ℝ) ^ 2 by positivity)
  dsimp only [A] at hbasic
  linarith

lemma plane_large_degree_bound_of_log_bound {d M : ℕ} {T K : ℝ}
    (hd : 0 < d) (hM : 0 < M)
    (hlog : Real.log M ≤ K + 6 + Real.log 2 + Real.log 4 + T + 3 * Real.log d) :
    (M : ℝ) ≤ 8 * Real.exp (K + 6 + T) * (d : ℝ) ^ 3 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  apply (Real.log_le_log_iff hMR (by positivity)).mp
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp, Real.log_pow]
  have h8 : Real.log 8 = Real.log 2 + Real.log 4 := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
    norm_num
  rw [h8]
  convert hlog using 1
  push_cast
  ring

/-- Large coefficient height forces an actual auxiliary polynomial of degree
O(d³), under the explicit sharp finite-field and leading-position inputs. -/
theorem plane_chart_exists_auxiliary_large_height
    {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {d M t : ℕ}
    (order : MonomialOrder (Fin 3)) (f : MvPolynomial (Fin 3) ℤ)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (hd : 0 < d) (hMlarge : 32 * d ≤ M)
    (hdchart : (planeAffineChart f).totalDegree = d)
    (hir : Irreducible (MvPolynomial.map (Int.castRingHom F) (planeAffineChart f)))
    (H : ℝ) (hH : 1 ≤ H) (hcoeff : ∀ m, |((planeAffineChart f).coeff m : ℝ)| ≤ H)
    (z : Fin t → Fin 2 → ℤ) (hz : ∀ i, MvPolynomial.eval (z i) (planeAffineChart f) = 0)
    {B C : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(z i j : ℝ)| ≤ B) (hC : 0 ≤ C)
    (T : ℝ) (hT : 0 ≤ T)
    (hheight : 4 * d * Real.log B ≤ Real.log H)
    (hposition : Real.log H ≤ Real.log |((order.leadingCoeff f : ℤ) : ℝ)| + T * (d : ℝ) ^ 2)
    (hthreshold : 8 * Real.exp (heightDeterminantError C + 6 + T) * (d : ℝ) ^ 3 < M)
    (hcount : ∀ p : ℕ, p.Prime → 27 * (d : ℝ) ^ 4 < (p : ℝ) →
      Irreducible (MvPolynomial.map (Int.castRingHom (ZMod p)) (planeAffineChart f)) →
      (Nat.card (PlaneResidue (planeAffineChart f) p) : ℝ) ≤
        p + C * (d : ℝ) ^ 2 * Real.sqrt p) :
    ∃ g : MvPolynomial (Fin 3) ℤ, g ≠ 0 ∧ g.IsHomogeneous M ∧
      (∀ i, MvPolynomial.eval (Fin.cons 1 (z i)) g = 0) ∧ ¬ f ∣ g := by
  classical
  have hdM : d ≤ M := by omega
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
  have hlog := plane_auxiliary_large_height_log_bound hd hMlarge hr hB hL hH hT
    hheight hposition hc
  have hbound := plane_large_degree_bound_of_log_bound hd (lt_of_lt_of_le hd hdM) hlog
  exact (not_lt_of_ge hbound) hthreshold

end
end AffineCurveCounting
