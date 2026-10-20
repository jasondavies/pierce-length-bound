module

public import AffineCurveCounting.Analytic

/-! A monotone scaled logarithmic-height ratio. A lower bound for the scaled
model height yields the saving needed to change the box exponent 2/d to 1/d. -/

@[expose] public section
namespace AffineCurveCounting
open Real

lemma log_height_ratio_antitone {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    (1 + v) / Real.exp v ≤ (1 + u) / Real.exp u := by
  have he : 1 + (v - u) ≤ Real.exp (v - u) := by
    simpa only [add_comm] using Real.add_one_le_exp (v - u)
  have hh : 1 + v ≤ (1 + u) * Real.exp (v - u) := by
    have hmul := mul_le_mul_of_nonneg_left he (show 0 ≤ 1 + u by linarith)
    nlinarith [mul_nonneg hu (sub_nonneg.mpr huv)]
  apply (div_le_div_iff₀ (Real.exp_pos _) (Real.exp_pos _)).mpr
  have hp := mul_le_mul_of_nonneg_right hh (Real.exp_pos u).le
  rw [mul_assoc, ← Real.exp_add, sub_add_cancel] at hp
  exact hp

/-- Eliminate an upper coefficient height in favor of any lower model height,
retaining the exact exponent 1/d² and the position loss exp(T). -/
theorem positioned_height_ratio_le {d H L Y T : ℝ}
    (hd : 0 < d) (hY : 1 ≤ Y) (hYH : Y ≤ H) (hL : 0 < L)
    (hposition : Real.log H ≤ Real.log L + T * d ^ 2) :
    (1 + Real.log H / d ^ 2) / L ^ (1 / d ^ 2) ≤
      Real.exp T * ((1 + Real.log Y / d ^ 2) / Y ^ (1 / d ^ 2)) := by
  have hY0 : 0 < Y := by linarith
  have hH0 : 0 < H := by linarith
  have hds : 0 < d ^ 2 := by positivity
  have hu : 0 ≤ Real.log Y / d ^ 2 := div_nonneg (Real.log_nonneg hY) hds.le
  have huv : Real.log Y / d ^ 2 ≤ Real.log H / d ^ 2 :=
    div_le_div_of_nonneg_right (Real.log_le_log hY0 hYH) hds.le
  have hmono := log_height_ratio_antitone hu huv
  have hpos : Real.log H / d ^ 2 ≤ Real.log L / d ^ 2 + T := by
    apply (div_le_iff₀ hds).mpr
    field_simp
    nlinarith only [hposition]
  have hexp : Real.exp (Real.log H / d ^ 2) ≤
      Real.exp T * Real.exp (Real.log L / d ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hnum : 0 ≤ 1 + Real.log H / d ^ 2 := by linarith
  have hstep : (1 + Real.log H / d ^ 2) / Real.exp (Real.log L / d ^ 2) ≤
      Real.exp T * ((1 + Real.log H / d ^ 2) / Real.exp (Real.log H / d ^ 2)) := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    rw [← mul_div_assoc, div_mul_eq_mul_div]
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hexp hnum]
  have hh := hstep.trans (mul_le_mul_of_nonneg_left hmono (Real.exp_pos T).le)
  rw [Real.rpow_def_of_pos hL, Real.rpow_def_of_pos hY0]
  simpa only [mul_one_div] using hh

end AffineCurveCounting
