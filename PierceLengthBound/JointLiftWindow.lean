/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftExponent

/-! The joint-lift count branches in actual remainder-window coordinates.
All geometric counting assertions remain explicit hypotheses. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend

/-- An absolute constant covering the five local ranges. -/
def jointLiftWindowBase : ℕ :=
  122449 + 3609600 ^ 5 * 56 ^ 30 * 8 ^ 10 +
    3609600 ^ 8 * 56 ^ 49 * 8 ^ 17 +
    3609600 ^ 85 * 56 ^ 510 * (4352 * 56 ^ 3 + 56) * 8 ^ 171 +
    3609600 ^ 85 * 56 ^ 520 * 1259991040 * 8 ^ 175 +
    124928 * 3609600 * 56 ^ 11 * 8 ^ 3

/-- The three proposed joint-lift local terms, as an integer-power disjunction. -/
def JointLiftCountBranches (K T H X S Y : ℕ) : Prop :=
  T ≤ K * X ^ 5 ∨ T ^ 2 ≤ K * H * X ^ 8 ∨ T ^ 17 ≤ K * X ^ 85 * max (max H S) Y

set_option exponentiation.threshold 1000 in
/-- Exact full-window reduction, conditional on the three-branch local count.
The larger common power avoids losing any of the target exponent to rounding. -/
theorem window_227070_of_joint_lift_count {a A T Δ K : ℕ}
    (hT : 36 ≤ T) (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3)
    (hdrop : T * (T - 1) ≤ 4 * A * Δ)
    (hlocal : let H := 28 * a / (A * T) + 1
      let X := 3609600 * A ^ 4 * H ^ 6 / a ^ 3
      let S := 4352 * A ^ 3 * H ^ 3 / a ^ 2
      let Y := 1259991040 * A ^ 5 * H ^ 10 / a ^ 4
      124928 * A ^ 4 * H ^ 5 * X < a ^ 3 → JointLiftCountBranches K T H X S Y) :
    T ^ 227070 ≤ (jointLiftWindowBase * (K + 1) * Δ ^ 175) ^ 56768 * a ^ 66816 := by
  have hA : 1 ≤ A := by
    by_contra h
    have hz : A = 0 := by omega
    simp [hz] at hdrop
    omega
  have hΔ : 1 ≤ Δ := by
    by_contra h
    have hz : Δ = 0 := by omega
    simp [hz] at hdrop
    omega
  have ha : 1 ≤ a := by
    by_contra h
    have hz : a = 0 := by omega
    simp [hz] at hsix
    omega
  let B := jointLiftWindowBase * (K + 1) * Δ ^ 175
  have hc : 1 ≤ jointLiftWindowBase := by unfold jointLiftWindowBase; omega
  have hB : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr (by dsimp [B]; positivity)
  have hbase : jointLiftWindowBase ≤ B := by
    calc jointLiftWindowBase = jointLiftWindowBase * 1 * 1 := by ring
      _ ≤ B := by
        dsimp [B]
        gcongr
        · omega
        · exact Nat.one_le_pow 175 Δ hΔ
  have hT2 : T ^ 2 ≤ (8 * Δ) * A := by
    have : T ≤ 2 * (T - 1) := by omega
    nlinarith
  have hcoeff {c n : ℕ} (hc : c ≤ jointLiftWindowBase) (hn : n ≤ 175) :
      c * K * Δ ^ n ≤ B := by
    dsimp only [B]
    gcongr
    omega
  by_cases hbig : 28 * a < A * T
  · have h := window_large_mean_gap ha hsix hbig
    have h' : T ^ 4 ≤ B * a ^ 1 := by
      simpa using h.trans (Nat.mul_le_mul_right a
        ((show 122449 ≤ jointLiftWindowBase by unfold jointLiftWindowBase; omega).trans hbase))
    exact window_power_lift (by omega) ha hB h' (m := 56768)
      (by norm_num) (by norm_num) (by norm_num)
  let H := 28 * a / (A * T) + 1
  let X := 3609600 * A ^ 4 * H ^ 6 / a ^ 3
  have hH : H * (A * T) ≤ 56 * a := by
    have := Nat.div_mul_le_self (28 * a) (A * T)
    dsimp only [H]
    rw [add_mul, one_mul]
    omega
  have hX : X * a ^ 3 ≤ 3609600 * A ^ 4 * H ^ 6 := Nat.div_mul_le_self _ _
  by_cases hscale : 124928 * A ^ 4 * H ^ 5 * X < a ^ 3
  · rcases hlocal hscale with h | h | h
    · have hm := remainder_window_arithmetic_conic_exponent
        (by omega : 0 < a) (by omega : 0 < A) h hH hX hT2
      have h' : T ^ 51 ≤ B * a ^ 15 := by
        calc T ^ 51 ≤ K * 3609600 ^ 5 * 56 ^ 30 * (8 * Δ) ^ 10 * a ^ 15 := hm
          _ = (3609600 ^ 5 * 56 ^ 30 * 8 ^ 10 * K * Δ ^ 10) * a ^ 15 := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ (hcoeff (by unfold jointLiftWindowBase; omega) (by norm_num))
      exact window_power_lift (by omega) ha hB h' (m := 4453)
        (by norm_num) (by norm_num) (by norm_num)
    · have hm := remainder_window_exceptional_conic_exponent
        (by omega : 0 < a) (by omega : 0 < A) h hH hX hT2
      have h' : T ^ 85 ≤ B * a ^ 25 := by
        calc T ^ 85 ≤ K * 3609600 ^ 8 * 56 ^ 49 * (8 * Δ) ^ 17 * a ^ 25 := hm
          _ = (3609600 ^ 8 * 56 ^ 49 * 8 ^ 17 * K * Δ ^ 17) * a ^ 25 := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ (hcoeff (by unfold jointLiftWindowBase; omega) (by norm_num))
      exact window_power_lift (by omega) ha hB h' (m := 2672)
        (by norm_num) (by norm_num) (by norm_num)
    · let S := 4352 * A ^ 3 * H ^ 3 / a ^ 2
      let Y := 1259991040 * A ^ 5 * H ^ 10 / a ^ 4
      rcases le_total (max H S) Y with hSY | hSY
      · rw [max_eq_right hSY] at h
        have hY : Y * T ^ 20 ≤ 1259991040 * 56 ^ 10 * (8 * Δ) ^ 5 * a ^ 6 :=
          rank_five_height_times_twenty (by omega) (by omega) hH (Nat.div_mul_le_self _ _) hT2
        have hm := remainder_window_joint_box_exponent
          (by omega : 0 < a) h hH hX hY hT2
        have h' : T ^ 887 ≤ B * a ^ 261 := by
          calc T ^ 887 ≤ K * 3609600 ^ 85 * 56 ^ 510 *
              (1259991040 * 56 ^ 10 * (8 * Δ) ^ 5) * (8 * Δ) ^ 170 * a ^ 261 := hm
            _ = (3609600 ^ 85 * 56 ^ 520 * 1259991040 * 8 ^ 175 * K * Δ ^ 175) * a ^ 261 := by ring
            _ ≤ _ := Nat.mul_le_mul_right _ (hcoeff (by unfold jointLiftWindowBase; omega) (by norm_num))
        exact window_power_lift (by omega) ha hB h' (m := 256)
          (by norm_num) (by norm_num) (by norm_num)
      · rw [max_eq_left hSY] at h
        have hS : S * T ^ 3 ≤ 4352 * 56 ^ 3 * a := curvature_height_times_cube
          (by omega) (by omega) hH (Nat.div_mul_le_self _ _)
        have hbox := max_curvature_height_times_cube (by omega : 0 < A)
          (show 1 ≤ 8 * Δ by omega) hH hS hT2
        have hm := remainder_window_joint_box_exponent
          (by omega : 0 < a) h hH hX (u := 3) (v := 1) (by simpa only [pow_one] using hbox) hT2
        have h' : T ^ 870 ≤ B * a ^ 256 := by
          calc T ^ 870 ≤ K * 3609600 ^ 85 * 56 ^ 510 *
              ((4352 * 56 ^ 3 + 56) * (8 * Δ)) * (8 * Δ) ^ 170 * a ^ 256 := hm
            _ = (3609600 ^ 85 * 56 ^ 510 * (4352 * 56 ^ 3 + 56) * 8 ^ 171 * K * Δ ^ 171) * a ^ 256 := by ring
            _ ≤ _ := Nat.mul_le_mul_right _ (hcoeff (by unfold jointLiftWindowBase; omega) (by norm_num))
        exact window_power_lift (by omega) ha hB h' (m := 261)
          (by norm_num) (by norm_num) (by norm_num)
  · have hm := remainder_window_small_exponent (by omega : 0 < a) (by omega : 0 < A)
      (by omega : a ^ 3 ≤ 124928 * A ^ 4 * H ^ 5 * X) hH hX hT2
    have h' : T ^ 17 ≤ B * a ^ 5 := by
      calc T ^ 17 ≤ 124928 * 3609600 * 56 ^ 11 * (8 * Δ) ^ 3 * a ^ 5 := hm
        _ = (124928 * 3609600 * 56 ^ 11 * 8 ^ 3 * Δ ^ 3) * a ^ 5 := by ring
        _ ≤ B * a ^ 5 := by
          apply Nat.mul_le_mul_right
          dsimp [B]
          have hc' : 124928 * 3609600 * 56 ^ 11 * 8 ^ 3 ≤ jointLiftWindowBase := by
            unfold jointLiftWindowBase; omega
          calc _ ≤ jointLiftWindowBase * Δ ^ 175 :=
              Nat.mul_le_mul hc' (Nat.pow_le_pow_right hΔ (by norm_num))
            _ = jointLiftWindowBase * 1 * Δ ^ 175 := by ring
            _ ≤ _ := by gcongr; omega
    exact window_power_lift (by omega) ha hB h' (m := 13358)
      (by norm_num) (by norm_num) (by norm_num)

end PierceLengthBound.FixedDividend
