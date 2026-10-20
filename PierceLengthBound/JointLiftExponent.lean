/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftExponent

/-! Exact exponent arithmetic for the joint curvature/rank-five lift.
The graph count and the invariant height bounds remain explicit premises. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend

/-- A degree-seventeen graph bound with a box of controlled scaled height. -/
theorem remainder_window_joint_box_exponent {T H X B A a C E D F K u v : ℕ}
    (ha : 0 < a) (hA : 0 < A) (hcount : T ^ 17 ≤ K * X ^ 85 * B)
    (hgap : H * (A * T) ≤ C * a) (hheight : X * a ^ 3 ≤ E * A ^ 4 * H ^ 6)
    (hbox : B * T ^ u ≤ F * a ^ v) (hdrop : T ^ 2 ≤ D * A) :
    T ^ (867 + u) ≤ K * E ^ 85 * C ^ 510 * F * D ^ 170 * a ^ (255 + v) := by
  have h1 : T ^ 17 * a ^ 255 ≤ K * E ^ 85 * A ^ 340 * H ^ 510 * B := by
    calc T ^ 17 * a ^ 255 ≤ (K * X ^ 85 * B) * a ^ 255 := by gcongr
      _ = K * B * (X * a ^ 3) ^ 85 := by ring
      _ ≤ K * B * (E * A ^ 4 * H ^ 6) ^ 85 := by gcongr
      _ = _ := by ring
  have h2 : (T ^ (527 + u) * A ^ 170) * (A ^ 340 * a ^ 255) ≤
      (K * E ^ 85 * C ^ 510 * F * a ^ (255 + v)) * (A ^ 340 * a ^ 255) := by
    calc _ = (T ^ 17 * a ^ 255) * (A * T) ^ 510 * T ^ u := by
          simp only [pow_add]; ring
      _ ≤ (K * E ^ 85 * A ^ 340 * H ^ 510 * B) * (A * T) ^ 510 * T ^ u := by gcongr
      _ = K * E ^ 85 * A ^ 340 * (H * (A * T)) ^ 510 * (B * T ^ u) := by ring
      _ ≤ K * E ^ 85 * A ^ 340 * (C * a) ^ 510 * (F * a ^ v) := by gcongr
      _ = _ := by simp only [pow_add]; ring
  have h3 := Nat.le_of_mul_le_mul_right h2 (by positivity : 0 < A ^ 340 * a ^ 255)
  calc T ^ (867 + u) = T ^ (527 + u) * (T ^ 2) ^ 170 := by
        simp only [pow_add]; ring
    _ ≤ T ^ (527 + u) * (D * A) ^ 170 := by gcongr
    _ = (T ^ (527 + u) * A ^ 170) * D ^ 170 := by ring
    _ ≤ (K * E ^ 85 * C ^ 510 * F * a ^ (255 + v)) * D ^ 170 := by gcongr
    _ = _ := by ring

/-- The curvature box uses the uniform 68/q^3 bound and q >= a/(4A). -/
def selectedCurvatureHeight (a A T : ℕ) : ℕ :=
  4352 * A ^ 3 * selectedGapHeight a A T ^ 3 / a ^ 2

/-- The proposed rank-five box from the explicit Newton Gram bound. -/
def selectedRankFiveHeight (a A T : ℕ) : ℕ :=
  1259991040 * A ^ 5 * selectedGapHeight a A T ^ 10 / a ^ 4

lemma curvature_height_times_cube {a A T C S H : ℕ} (ha : 0 < a) (hA : 0 < A)
    (hgap : H * (A * T) ≤ C * a) (hS : S * a ^ 2 ≤ 4352 * A ^ 3 * H ^ 3) :
    S * T ^ 3 ≤ 4352 * C ^ 3 * a := by
  apply Nat.le_of_mul_le_mul_right (c := A ^ 3 * a ^ 2) ?_ (by positivity)
  calc _ = (S * a ^ 2) * A ^ 3 * T ^ 3 := by ring
    _ ≤ (4352 * A ^ 3 * H ^ 3) * A ^ 3 * T ^ 3 := by gcongr
    _ = 4352 * A ^ 3 * (H * (A * T)) ^ 3 := by ring
    _ ≤ 4352 * A ^ 3 * (C * a) ^ 3 := by gcongr
    _ = _ := by ring

lemma max_curvature_height_times_cube {a A T C S H D : ℕ} (hA : 0 < A) (hD : 1 ≤ D)
    (hgap : H * (A * T) ≤ C * a) (hS : S * T ^ 3 ≤ 4352 * C ^ 3 * a)
    (hdrop : T ^ 2 ≤ D * A) :
    max H S * T ^ 3 ≤ (4352 * C ^ 3 + C) * D * a := by
  have hH : H * T ^ 3 ≤ C * D * a := by
    apply Nat.le_of_mul_le_mul_right (c := A) ?_ hA
    calc H * T ^ 3 * A = (H * (A * T)) * T ^ 2 := by ring
      _ ≤ (C * a) * (D * A) := by gcongr
      _ = _ := by ring
  rcases le_total H S with h | h
  · rw [max_eq_right h]
    calc S * T ^ 3 ≤ 4352 * C ^ 3 * a := hS
      _ = 4352 * C ^ 3 * 1 * a := by ring
      _ ≤ (4352 * C ^ 3 + C) * D * a := by gcongr; omega
  · rw [max_eq_left h]
    exact hH.trans (by gcongr; omega)

/-- The rank-five height introduces a twentieth power of the window length. -/
lemma rank_five_height_times_twenty {a A T C Y H D J : ℕ} (ha : 0 < a) (hA : 0 < A)
    (hgap : H * (A * T) ≤ C * a) (hY : Y * a ^ 4 ≤ J * A ^ 5 * H ^ 10)
    (hdrop : T ^ 2 ≤ D * A) :
    Y * T ^ 20 ≤ J * C ^ 10 * D ^ 5 * a ^ 6 := by
  have h1 : (Y * A ^ 5 * T ^ 10) * (a ^ 4 * A ^ 5) ≤
      (J * C ^ 10 * a ^ 6) * (a ^ 4 * A ^ 5) := by
    calc _ = (Y * a ^ 4) * (A * T) ^ 10 := by ring
      _ ≤ (J * A ^ 5 * H ^ 10) * (A * T) ^ 10 := by gcongr
      _ = J * A ^ 5 * (H * (A * T)) ^ 10 := by ring
      _ ≤ J * A ^ 5 * (C * a) ^ 10 := by gcongr
      _ = _ := by ring
  have h2 := Nat.le_of_mul_le_mul_right h1 (by positivity : 0 < a ^ 4 * A ^ 5)
  calc Y * T ^ 20 = Y * T ^ 10 * (T ^ 2) ^ 5 := by ring
    _ ≤ Y * T ^ 10 * (D * A) ^ 5 := by gcongr
    _ = (Y * A ^ 5 * T ^ 10) * D ^ 5 := by ring
    _ ≤ (J * C ^ 10 * a ^ 6) * D ^ 5 := by gcongr
    _ = _ := by ring

lemma joint_lift_exponent_comparisons :
    (151 : ℚ) / 513 - 128 / 435 = 7 / 74385 ∧
    (128 : ℚ) / 435 - 5 / 17 = 1 / 7395 ∧
    (128 : ℚ) / 435 - 261 / 887 = 1 / 385845 ∧
    (128 : ℚ) / 435 - 2201 / 7480 = 1 / 650760 ∧
    (1295 : ℚ) / 4401 < 2201 / 7480 := by norm_num

lemma joint_lift_critical_balance :
    (179 : ℚ) / 435 - 128 / 435 = 51 / 435 ∧
    1 - 3 * ((128 : ℚ) / 435) = 51 / 435 ∧
    1 + 5 * ((179 : ℚ) / 435) - 10 * (128 / 435) = 50 / 435 ∧
    1 + 2 * ((179 : ℚ) / 435) - 6 * (128 / 435) = 25 / 435 ∧
    4 * ((179 : ℚ) / 435) - 1 - 5 * (51 / 435) = 26 / 435 ∧
    5 * ((25 : ℚ) / 435) + (51 / 435) / 17 = 128 / 435 := by norm_num

end PierceLengthBound.FixedDividend
