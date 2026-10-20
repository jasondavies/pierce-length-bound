/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ConicWindow

/-! Exponent arithmetic for a general higher-degree local count and the new
180/611 specialization. These implications do not assert the local count. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend

/-- A general higher-degree branch, in actual remainder-window coordinates. -/
theorem remainder_window_degree_exponent {T H X A a C E D K n m : ℕ}
    (ha : 0 < a) (hA : 0 < A) (hcount : T ^ n ≤ K * H ^ 3 * X ^ m)
    (hgap : H * (A * T) ≤ C * a) (hheight : X * a ^ 3 ≤ E * A ^ 4 * H ^ 6)
    (hdrop : T ^ 2 ≤ D * A) :
    T ^ (n + 10 * m + 9) ≤ K * E ^ m * C ^ (6 * m + 3) *
      D ^ (2 * m + 3) * a ^ (3 * m + 3) := by
  have h1 : T ^ n * a ^ (3 * m) ≤ K * E ^ m * A ^ (4 * m) * H ^ (6 * m + 3) := by
    calc T ^ n * a ^ (3 * m) ≤ (K * H ^ 3 * X ^ m) * a ^ (3 * m) := by gcongr
      _ = K * H ^ 3 * (X * a ^ 3) ^ m := by simp only [mul_pow, pow_mul]; ring
      _ ≤ K * H ^ 3 * (E * A ^ 4 * H ^ 6) ^ m := by gcongr
      _ = _ := by simp only [mul_pow, pow_add, pow_mul]; ring
  have h2 : (T ^ (n + 6 * m + 3) * A ^ (2 * m + 3)) * (A ^ (4 * m) * a ^ (3 * m)) ≤
      (K * E ^ m * C ^ (6 * m + 3) * a ^ (3 * m + 3)) * (A ^ (4 * m) * a ^ (3 * m)) := by
    calc _ = (T ^ n * a ^ (3 * m)) * (A * T) ^ (6 * m + 3) := by
          simp only [mul_pow, pow_add, pow_mul]; ring
      _ ≤ (K * E ^ m * A ^ (4 * m) * H ^ (6 * m + 3)) * (A * T) ^ (6 * m + 3) := by gcongr
      _ = K * E ^ m * A ^ (4 * m) * (H * (A * T)) ^ (6 * m + 3) := by rw [mul_pow]; ring
      _ ≤ K * E ^ m * A ^ (4 * m) * (C * a) ^ (6 * m + 3) := by gcongr
      _ = _ := by simp only [mul_pow, pow_add, pow_mul]; ring
  have h3 := Nat.le_of_mul_le_mul_right h2 (by positivity : 0 < A ^ (4 * m) * a ^ (3 * m))
  calc T ^ (n + 10 * m + 9) = T ^ (n + 6 * m + 3) * (T ^ 2) ^ (2 * m + 3) := by
        simp only [pow_add, pow_mul]; ring
    _ ≤ T ^ (n + 6 * m + 3) * (D * A) ^ (2 * m + 3) := by gcongr
    _ = (T ^ (n + 6 * m + 3) * A ^ (2 * m + 3)) * D ^ (2 * m + 3) := by rw [mul_pow]; ring
    _ ≤ (K * E ^ m * C ^ (6 * m + 3) * a ^ (3 * m + 3)) * D ^ (2 * m + 3) := by gcongr
    _ = _ := by ring

set_option exponentiation.threshold 1000 in
/-- The degree-four local branch gives the new exponent exactly. -/
theorem remainder_window_quarter_curve_exponent {T H X A a C E D K : ℕ}
    (ha : 0 < a) (hA : 0 < A) (hcount : T ^ 12 ≤ K * H ^ 3 * X ^ 59)
    (hgap : H * (A * T) ≤ C * a) (hheight : X * a ^ 3 ≤ E * A ^ 4 * H ^ 6)
    (hdrop : T ^ 2 ≤ D * A) :
    T ^ 611 ≤ K * E ^ 59 * C ^ 357 * D ^ 121 * a ^ 180 :=
  remainder_window_degree_exponent ha hA hcount hgap hheight hdrop

/-- A general degree threshold gives the family 45d/(153d-1) appearing in
the candidate. This remains an implication from the corresponding local count. -/
theorem remainder_window_degree_threshold {T H X A a C E D K d : ℕ}
    (hd : 1 ≤ d) (ha : 0 < a) (hA : 0 < A)
    (hcount : T ^ (3 * d) ≤ K * H ^ 3 * X ^ (15 * d - 1))
    (hgap : H * (A * T) ≤ C * a) (hheight : X * a ^ 3 ≤ E * A ^ 4 * H ^ 6)
    (hdrop : T ^ 2 ≤ D * A) :
    T ^ (153 * d - 1) ≤ K * E ^ (15 * d - 1) * C ^ (90 * d - 3) *
      D ^ (30 * d + 1) * a ^ (45 * d) := by
  have h := remainder_window_degree_exponent ha hA hcount hgap hheight hdrop
  have h1 : 3 * d + 10 * (15 * d - 1) + 9 = 153 * d - 1 := by omega
  have h2 : 6 * (15 * d - 1) + 3 = 90 * d - 3 := by omega
  have h3 : 2 * (15 * d - 1) + 3 = 30 * d + 1 := by omega
  have h4 : 3 * (15 * d - 1) + 3 = 45 * d := by omega
  rwa [h1, h2, h3, h4] at h

lemma parity_exponent_comparison :
    (135 : ℚ) / 458 - 180 / 611 = 45 / 279838 ∧
    (180 : ℚ) / 611 - 5 / 17 = 5 / 10387 ∧
    (180 : ℚ) / 611 < 135 / 458 := by norm_num

/-- For every proposed degree threshold, the resulting exponent remains above 5/17. -/
lemma degree_threshold_exponent_gap {d : ℚ} (hd : 1 ≤ d) :
    45 * d / (153 * d - 1) - 5 / 17 = 5 / (17 * (153 * d - 1)) := by
  have hne : 153 * d - 1 ≠ 0 := by linarith
  have he := mul_inv_cancel₀ hne
  field_simp
  linear_combination 5 * he

/-- Degree improvements in this unchanged framework remain strictly above 5/17. -/
lemma degree_threshold_exponent_gt {d : ℚ} (hd : 1 ≤ d) :
    5 / 17 < 45 * d / (153 * d - 1) := by
  have he := degree_threshold_exponent_gap hd
  have hdpos : 0 < 153 * d - 1 := by linarith
  have hpos : 0 < 5 / (17 * (153 * d - 1)) := by positivity
  linarith

lemma parity_critical_balance :
    (251 : ℚ) / 611 - 180 / 611 = 71 / 611 ∧
    1 + 2 * ((251 : ℚ) / 611) - 6 * (180 / 611) = 33 / 611 ∧
    4 * ((251 : ℚ) / 611) - 1 - 5 * (71 / 611) = 38 / 611 ∧
    (38 : ℚ) / 611 - 33 / 611 = 5 / 611 := by norm_num

end PierceLengthBound.FixedDividend
