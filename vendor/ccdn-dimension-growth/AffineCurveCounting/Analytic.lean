module

public import AffineCurveCounting.Plane

/-!
# Uniform estimates and bounded-degree consequences

These are proved real inequalities. Their use with a point count still requires proving
the geometric/determinant estimate. No counting conjecture is assumed as a global axiom.
-/

@[expose] public section

namespace AffineCurveCounting

/-- Eliminate the leading-coefficient height from CCDN Corollary 4.2.4.
This is the explicit inequality used in their proof of Theorem 3. -/
theorem coefficient_height_elimination {d H B : ℝ} (hd : 1 ≤ d) (hH : 1 ≤ H)
    (hB : 1 ≤ B) :
    (d ^ 2 * Real.log H + d ^ 3 * Real.log B + d ^ 4) / H ^ (1 / d ^ 2) ≤
      d ^ 3 * Real.log B + 2 * d ^ 4 := by
  have hd0 : 0 < d := by linarith
  have ht : 0 < 1 / d ^ 2 := by positivity
  have hp : 0 < H ^ (1 / d ^ 2) := Real.rpow_pos_of_pos (by linarith) _
  have hp1 : 1 ≤ H ^ (1 / d ^ 2) := Real.one_le_rpow hH ht.le
  have hl := Real.log_le_rpow_div (show 0 ≤ H by linarith) ht
  have hl' : Real.log H ≤ H ^ (1 / d ^ 2) * d ^ 2 := by
    simpa only [div_div_eq_mul_div, div_one] using hl
  have hlogB := Real.log_nonneg hB
  apply (div_le_iff₀ hp).mpr
  have h1 := mul_le_mul_of_nonneg_left hl' (sq_nonneg d)
  have h2 := mul_le_mul_of_nonneg_left hp1 (show 0 ≤ d ^ 3 * Real.log B by positivity)
  have h3 := mul_le_mul_of_nonneg_left hp1 (show 0 ≤ d ^ 4 by positivity)
  nlinarith

/-- Absorb both additive error terms of Corollary 4.2.4 into the uniform expression,
with an explicit factor `3`. This is a numerical implication, not the corollary itself. -/
theorem refined_estimate_le_uniform {C d H B : ℝ} (hC : 0 ≤ C) (hd : 1 ≤ d)
    (hH : 1 ≤ H) (hB : 1 ≤ B) :
    C * B ^ (1 / d) *
        ((d ^ 2 * Real.log H + d ^ 3 * Real.log B + d ^ 4) / H ^ (1 / d ^ 2)) +
        C * d * Real.log B + C * d ^ 4 ≤
      3 * C * d ^ 3 * B ^ (1 / d) * (Real.log B + d) := by
  have hd0 : 0 ≤ d := by linarith
  have hpow0 : 0 ≤ B ^ (1 / d) := Real.rpow_nonneg (by linarith) _
  have hpow1 : 1 ≤ B ^ (1 / d) := Real.one_le_rpow hB (by positivity)
  have hlog := Real.log_nonneg hB
  have hdsq : 1 ≤ d ^ 2 := one_le_pow₀ hd
  have hd3 : d ≤ d ^ 3 := by nlinarith
  have hmain := mul_le_mul_of_nonneg_left (coefficient_height_elimination hd hH hB)
    (mul_nonneg hC hpow0)
  have htail1 : C * d * Real.log B ≤ C * B ^ (1 / d) * d ^ 3 * Real.log B := by
    calc
      _ = C * 1 * d * Real.log B := by ring
      _ ≤ _ := by gcongr
  have htail2 : C * d ^ 4 ≤ C * B ^ (1 / d) * d ^ 4 := by
    calc
      _ = C * 1 * d ^ 4 := by ring
      _ ≤ _ := by gcongr
  have hpos : 0 ≤ C * B ^ (1 / d) * d ^ 3 * Real.log B := by positivity
  nlinarith

theorem curveBound_nonneg {d : ℕ} {B : ℝ} (hB : 1 ≤ B) : 0 ≤ curveBound d B := by
  unfold curveBound
  have := Real.log_nonneg hB
  positivity

/-- The precise bounded-degree consequence used by the Pierce application. -/
theorem curveBound_le_sqrt {d D : ℕ} (hd : 2 ≤ d) (hD : d ≤ D) {B : ℝ}
    (hB : 1 ≤ B) :
    curveBound d B ≤ (D : ℝ) ^ 3 * B ^ (1 / 2 : ℝ) * (Real.log B + D) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hDR : (d : ℝ) ≤ D := by exact_mod_cast hD
  have hpow : B ^ (1 / (d : ℝ)) ≤ B ^ (1 / 2 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hB
    exact one_div_le_one_div_of_le (by norm_num) hdR
  have hlog := Real.log_nonneg hB
  unfold curveBound
  gcongr

theorem curveBound_le_sqrt_24 {d : ℕ} (hd : 2 ≤ d) (hD : d ≤ 24) {B : ℝ}
    (hB : 1 ≤ B) :
    curveBound d B ≤ 13824 * B ^ (1 / 2 : ℝ) * (Real.log B + 24) := by
  convert curveBound_le_sqrt hd hD hB using 1
  norm_num

/-- Absorb the logarithm with a specified positive exponent loss and an explicit constant. -/
theorem sqrt_log_le_rpow {B ε D : ℝ} (hB : 1 ≤ B) (hε : 0 < ε) (hD : 0 ≤ D) :
    B ^ (1 / 2 : ℝ) * (Real.log B + D) ≤
      (1 / ε + D) * B ^ (1 / 2 + ε : ℝ) := by
  have hB0 : 0 < B := by linarith
  have hp1 : 1 ≤ B ^ ε := Real.one_le_rpow hB hε.le
  have hl := Real.log_le_rpow_div hB0.le hε
  have hd := mul_le_mul_of_nonneg_left hp1 hD
  have hsum : Real.log B + D ≤ (1 / ε + D) * B ^ ε := by
    rw [div_eq_mul_inv] at hl
    simp only [one_div]
    nlinarith
  calc
    _ ≤ B ^ (1 / 2 : ℝ) * ((1 / ε + D) * B ^ ε) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hB0.le _)
    _ = _ := by rw [Real.rpow_add hB0]; ring

end AffineCurveCounting
