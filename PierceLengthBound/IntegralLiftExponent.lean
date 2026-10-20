/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ConicWindow
public import PierceLengthBound.FixedDividendSelection

/-! Exact exponent arithmetic for the additional integral Hankel coordinate.
These implications retain the geometric graph-count estimate as a premise. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend

/-- The graph box bound and degree-ten count give exponent `151/513`. -/
theorem remainder_window_integral_lift_exponent {T H X B A a C E D F K : ℕ}
    (ha : 0 < a) (hA : 0 < A) (hcount : T ^ 10 ≤ K * X ^ 50 * B)
    (hgap : H * (A * T) ≤ C * a) (hheight : X * a ^ 3 ≤ E * A ^ 4 * H ^ 6)
    (hbox : B * T ^ 3 ≤ F * a) (hdrop : T ^ 2 ≤ D * A) :
    T ^ 513 ≤ K * E ^ 50 * C ^ 300 * F * D ^ 100 * a ^ 151 := by
  have h1 : T ^ 10 * a ^ 150 ≤ K * E ^ 50 * A ^ 200 * H ^ 300 * B := by
    calc T ^ 10 * a ^ 150 ≤ (K * X ^ 50 * B) * a ^ 150 := by gcongr
      _ = K * B * (X * a ^ 3) ^ 50 := by ring
      _ ≤ K * B * (E * A ^ 4 * H ^ 6) ^ 50 := by gcongr
      _ = _ := by ring
  have h2 : (T ^ 313 * A ^ 100) * (A ^ 200 * a ^ 150) ≤
      (K * E ^ 50 * C ^ 300 * F * a ^ 151) * (A ^ 200 * a ^ 150) := by
    calc _ = (T ^ 10 * a ^ 150) * (A * T) ^ 300 * T ^ 3 := by ring
      _ ≤ (K * E ^ 50 * A ^ 200 * H ^ 300 * B) * (A * T) ^ 300 * T ^ 3 := by gcongr
      _ = K * E ^ 50 * A ^ 200 * (H * (A * T)) ^ 300 * (B * T ^ 3) := by ring
      _ ≤ K * E ^ 50 * A ^ 200 * (C * a) ^ 300 * (F * a) := by gcongr
      _ = _ := by ring
  have h3 := Nat.le_of_mul_le_mul_right h2 (by positivity : 0 < A ^ 200 * a ^ 150)
  calc T ^ 513 = T ^ 313 * (T ^ 2) ^ 100 := by ring
    _ ≤ T ^ 313 * (D * A) ^ 100 := by gcongr
    _ = (T ^ 313 * A ^ 100) * D ^ 100 := by ring
    _ ≤ (K * E ^ 50 * C ^ 300 * F * a ^ 151) * D ^ 100 := by gcongr
    _ = _ := by ring

/-- The selected integral-coordinate height in remainder-window notation. -/
def selectedLiftHeight (a A T : ℕ) : ℕ :=
  896 * A ^ 3 * selectedGapHeight a A T ^ 3 / a ^ 2

/-- Flooring the invariant height introduces no additive rounding loss. -/
lemma lift_height_times_cube {a A T C S H : ℕ} (ha : 0 < a) (hA : 0 < A)
    (hgap : H * (A * T) ≤ C * a) (hS : S * a ^ 2 ≤ 896 * A ^ 3 * H ^ 3) :
    S * T ^ 3 ≤ 896 * C ^ 3 * a := by
  apply Nat.le_of_mul_le_mul_right (c := A ^ 3 * a ^ 2) ?_ (by positivity)
  calc _ = (S * a ^ 2) * A ^ 3 * T ^ 3 := by ring
    _ ≤ (896 * A ^ 3 * H ^ 3) * A ^ 3 * T ^ 3 := by gcongr
    _ = 896 * A ^ 3 * (H * (A * T)) ^ 3 := by ring
    _ ≤ 896 * A ^ 3 * (C * a) ^ 3 := by gcongr
    _ = _ := by ring

/-- The drop estimate absorbs the original gap radius into the lifted box. -/
lemma max_lift_height_times_cube {a A T C S H D : ℕ} (hA : 0 < A) (hD : 1 ≤ D)
    (hgap : H * (A * T) ≤ C * a) (hS : S * T ^ 3 ≤ 896 * C ^ 3 * a)
    (hdrop : T ^ 2 ≤ D * A) :
    max H S * T ^ 3 ≤ (896 * C ^ 3 + C) * D * a := by
  have hH : H * T ^ 3 ≤ C * D * a := by
    apply Nat.le_of_mul_le_mul_right (c := A) ?_ hA
    calc H * T ^ 3 * A = (H * (A * T)) * T ^ 2 := by ring
      _ ≤ (C * a) * (D * A) := by gcongr
      _ = _ := by ring
  rcases le_total H S with h | h
  · rw [max_eq_right h]
    calc S * T ^ 3 ≤ 896 * C ^ 3 * a := hS
      _ = 896 * C ^ 3 * 1 * a := by ring
      _ ≤ (896 * C ^ 3 + C) * D * a := by gcongr; omega
  · rw [max_eq_left h]
    exact hH.trans (by gcongr; omega)

lemma integral_lift_exponent_comparison :
    (180 : ℚ) / 611 - 151 / 513 = 79 / 313443 ∧
    (151 : ℚ) / 513 - 5 / 17 = 2 / 8721 ∧
    (151 : ℚ) / 513 < 180 / 611 := by norm_num

lemma integral_lift_critical_balance :
    (211 : ℚ) / 513 - 151 / 513 = 60 / 513 ∧
    1 - 3 * ((151 : ℚ) / 513) = 60 / 513 ∧
    1 + 2 * ((211 : ℚ) / 513) - 6 * (151 / 513) = 29 / 513 ∧
    4 * ((211 : ℚ) / 513) - 1 - 5 * (60 / 513) = 31 / 513 ∧
    5 * ((29 : ℚ) / 513) + (60 / 513) / 10 = 151 / 513 := by norm_num

end PierceLengthBound.FixedDividend
