module

public import AffineCurveCounting.DegreePreservingProjectionBox
public import AffineCurveCounting.SharpPlaneCount

/-! Absorb the degree-dependent projection box factor into a constant depending
only on ambient dimension, retaining the exact exponent 1/d and d³ factor. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section

def projectionLogConstant (n : ℕ) : ℝ := 2 * (n : ℝ) ^ 2 + 3 * n

lemma projectionLogConstant_nonneg (n : ℕ) : 0 ≤ projectionLogConstant n := by
  unfold projectionLogConstant
  positivity

lemma projectionBoxFactor_log_le (n : ℕ) {d : ℕ} (hd : 0 < d) :
    Real.log (projectionBoxFactor n d) ≤ projectionLogConstant n * d := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  have hd0 : (0 : ℝ) < d + 1 := by positivity
  have hln : Real.log ((n : ℝ) + 1) ≤ n := by
    simpa only [add_sub_cancel_right] using Real.log_le_sub_one_of_pos hn0
  have hld : Real.log ((d : ℝ) + 1) ≤ d := by
    simpa only [add_sub_cancel_right] using Real.log_le_sub_one_of_pos hd0
  unfold projectionBoxFactor
  rw [Real.log_mul hn0.ne' (pow_pos (pow_pos (mul_pos hn0 hd0) _) _).ne',
    Real.log_pow, Real.log_pow, Real.log_mul hn0.ne' hd0.ne']
  unfold projectionLogConstant
  have hh := mul_le_mul_of_nonneg_left (add_le_add hln hld) (show 0 ≤ 2 * (n : ℝ) by positivity)
  have hh₂ := mul_le_mul_of_nonneg_left hd1 (show 0 ≤ 2 * (n : ℝ) ^ 2 + n by positivity)
  norm_num only [Nat.cast_ofNat]
  nlinarith

lemma curveBound_scale_of_log_le {d : ℕ} (hd : 0 < d) {A B C : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 0 ≤ C) (hlog : Real.log A ≤ C * d) :
    curveBound d (A * B) ≤ Real.exp C * (C + 1) * curveBound d B := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hlogB := Real.log_nonneg hB
  have hlogA := Real.log_nonneg hA
  have hpow : A ^ (1 / (d : ℝ)) ≤ Real.exp C := by
    rw [Real.rpow_def_of_pos hA0, Real.exp_le_exp, ← div_eq_mul_one_div]
    exact (div_le_iff₀ hd0).mpr hlog
  have hlog₂ : Real.log A + Real.log B + d ≤ (C + 1) * (Real.log B + d) := by
    nlinarith [mul_nonneg hC hlogB]
  unfold curveBound
  rw [Real.mul_rpow hA0.le hB0.le, Real.log_mul hA0.ne' hB0.ne']
  calc
    _ ≤ (d : ℝ) ^ 3 * (Real.exp C * B ^ (1 / (d : ℝ))) *
        ((C + 1) * (Real.log B + d)) := by gcongr
    _ = _ := by ring

/-- A uniform scale constant, chosen before degree, ideal and radius. -/
theorem projection_curveBound_scale (n : ℕ) {d : ℕ} (hd : 0 < d)
    {B : ℝ} (hB : 1 ≤ B) :
    curveBound d (projectionBoxFactor n d * B) ≤
      (Real.exp (projectionLogConstant n) * (projectionLogConstant n + 1)) * curveBound d B :=
  curveBound_scale_of_log_le hd (projectionBoxFactor_one_le n d) hB
    (projectionLogConstant_nonneg n) (projectionBoxFactor_log_le n hd)

end
end AffineCurveCounting
