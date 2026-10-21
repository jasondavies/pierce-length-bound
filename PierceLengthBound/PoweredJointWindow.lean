/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PoweredJointExponent
public import PierceLengthBound.PoweredJointLocalEstimate
public import PierceLengthBound.WindowRealReduction

/-! The joint-lift count branches in actual remainder-window coordinates.
All geometric counting assertions remain explicit hypotheses. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend

/-- A constant covering all window ranges for fixed coordinate powers. -/
def poweredJointWindowBase (m n L : ℕ) : ℕ :=
  1 + 122449 + 3609600 ^ 5 * 56 ^ 30 * 8 ^ 10 +
    3609600 ^ 8 * 56 ^ 49 * 8 ^ 17 +
    3609600 ^ (5 * L) * 56 ^ (30 * L) * (4352 * 56 ^ 3 + 56) ^ m * 8 ^ (m + 10 * L) +
    3609600 ^ (5 * L) * 56 ^ (30 * L + 10 * n) * 1259991040 ^ n * 8 ^ (5 * n + 10 * L) +
    124928 * 3609600 * 56 ^ 11 * 8 ^ 3

set_option exponentiation.threshold 1000 in
/-- Every window is bounded at any exponent dominating the two powered
ratios and the complementary-range exponent 5/17. -/
theorem window_real_of_powered_joint_count {a A T Δ K m n L : ℕ} {α : ℝ}
    (hm : 0 < m) (hL : 0 < L)
    (hα : (5 : ℝ) / 17 ≤ α)
    (hSexp : ((15 * L + m : ℕ) : ℝ) / (51 * L + 3 * m : ℕ) ≤ α)
    (hYexp : ((15 * L + 6 * n : ℕ) : ℝ) / (51 * L + 20 * n : ℕ) ≤ α)
    (hT : 36 ≤ T) (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3)
    (hdrop : T * (T - 1) ≤ 4 * A * Δ)
    (hlocal : let H := 28 * a / (A * T) + 1
      let X := 3609600 * A ^ 4 * H ^ 6 / a ^ 3
      let S := 4352 * A ^ 3 * H ^ 3 / a ^ 2
      let Y := 1259991040 * A ^ 5 * H ^ 10 / a ^ 4
      124928 * A ^ 4 * H ^ 5 * X < a ^ 3 →
        PoweredJointCountBranches K T H X (max (max H (S ^ m)) (Y ^ n)) L) :
    (T : ℝ) ≤ (poweredJointWindowBase m n L * (K + 1) * Δ ^ (17 + 10 * L + 5 * n + m) : ℕ) *
      (a : ℝ) ^ α := by
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
  let B := poweredJointWindowBase m n L * (K + 1) * Δ ^ (17 + 10 * L + 5 * n + m)
  have hc : 1 ≤ poweredJointWindowBase m n L := by unfold poweredJointWindowBase; omega
  have hB : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr (by dsimp [B]; positivity)
  have hbase : poweredJointWindowBase m n L ≤ B := by
    calc poweredJointWindowBase m n L = poweredJointWindowBase m n L * 1 * 1 := by ring
      _ ≤ B := by
        dsimp [B]
        gcongr
        · omega
        · exact Nat.one_le_pow (17 + 10 * L + 5 * n + m) Δ hΔ
  have hT2 : T ^ 2 ≤ (8 * Δ) * A := by
    have : T ≤ 2 * (T - 1) := by omega
    nlinarith
  have hcoeff {c e : ℕ} (hc : c ≤ poweredJointWindowBase m n L) (he : e ≤ 17 + 10 * L + 5 * n + m) :
      c * K * Δ ^ e ≤ B := by
    dsimp only [B]
    gcongr
    omega
  by_cases hbig : 28 * a < A * T
  · have h := window_large_mean_gap ha hsix hbig
    have h' : T ^ 4 ≤ B * a ^ 1 := by
      simpa using h.trans (Nat.mul_le_mul_right a
        ((show 122449 ≤ poweredJointWindowBase m n L by unfold poweredJointWindowBase; omega).trans hbase))
    apply window_real_bound_of_power ha hB (by decide : 0 < 4) h'
    norm_num only [Nat.cast_one, Nat.cast_ofNat]
    exact (by norm_num : (1 : ℝ) / 4 ≤ 5 / 17).trans hα
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
          _ ≤ _ := Nat.mul_le_mul_right _ (hcoeff (by unfold poweredJointWindowBase; omega) (by omega))
      apply window_real_bound_of_power ha hB (by decide : 0 < 51) h'
      exact (by norm_num : (15 : ℝ) / 51 ≤ 5 / 17).trans hα
    · have hm := remainder_window_exceptional_conic_exponent
        (by omega : 0 < a) (by omega : 0 < A) h hH hX hT2
      have h' : T ^ 85 ≤ B * a ^ 25 := by
        calc T ^ 85 ≤ K * 3609600 ^ 8 * 56 ^ 49 * (8 * Δ) ^ 17 * a ^ 25 := hm
          _ = (3609600 ^ 8 * 56 ^ 49 * 8 ^ 17 * K * Δ ^ 17) * a ^ 25 := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ (hcoeff (by unfold poweredJointWindowBase; omega) (by omega))
      apply window_real_bound_of_power ha hB (by decide : 0 < 85) h'
      exact (by norm_num : (25 : ℝ) / 85 ≤ 5 / 17).trans hα
    · let S := 4352 * A ^ 3 * H ^ 3 / a ^ 2
      let Y := 1259991040 * A ^ 5 * H ^ 10 / a ^ 4
      rcases le_total (max H (S ^ m)) (Y ^ n) with hSY | hSY
      · rw [max_eq_right hSY] at h
        have hY : Y ^ n * T ^ (20 * n) ≤
            (1259991040 * 56 ^ 10 * (8 * Δ) ^ 5) ^ n * a ^ (6 * n) :=
          powered_rank_five_height (by omega) (by omega) hH (Nat.div_mul_le_self _ _) hT2
        have hc := remainder_window_powered_box_exponent
          (by omega : 0 < a) h hH hX hY hT2
        have h' : T ^ (51 * L + 20 * n) ≤ B * a ^ (15 * L + 6 * n) := by
          calc _ ≤ K * 3609600 ^ (5 * L) * 56 ^ (30 * L) *
              (1259991040 * 56 ^ 10 * (8 * Δ) ^ 5) ^ n * (8 * Δ) ^ (10 * L) *
              a ^ (15 * L + 6 * n) := hc
            _ = (3609600 ^ (5 * L) * 56 ^ (30 * L + 10 * n) * 1259991040 ^ n *
              8 ^ (5 * n + 10 * L) * K * Δ ^ (5 * n + 10 * L)) * a ^ (15 * L + 6 * n) := by
                simp only [mul_pow, ← pow_mul, pow_add]
                ring
            _ ≤ _ := Nat.mul_le_mul_right _
              (hcoeff (by unfold poweredJointWindowBase; omega) (by omega))
        exact window_real_bound_of_power ha hB (by omega) h' hYexp
      · rw [max_eq_left hSY] at h
        have hS : S * T ^ 3 ≤ 4352 * 56 ^ 3 * a := curvature_height_times_cube
          (by omega) (by omega) hH (Nat.div_mul_le_self _ _)
        have hbox := max_powered_curvature_height hm (by omega : 0 < A)
          (show 1 ≤ 8 * Δ by omega) (show 1 ≤ H from Nat.le_add_left 1 _) hH hS hT2
        have hc := remainder_window_powered_box_exponent
          (by omega : 0 < a) h hH hX hbox hT2
        have h' : T ^ (51 * L + 3 * m) ≤ B * a ^ (15 * L + m) := by
          calc _ ≤ K * 3609600 ^ (5 * L) * 56 ^ (30 * L) *
              ((4352 * 56 ^ 3 + 56) * (8 * Δ)) ^ m * (8 * Δ) ^ (10 * L) *
              a ^ (15 * L + m) := hc
            _ = (3609600 ^ (5 * L) * 56 ^ (30 * L) * (4352 * 56 ^ 3 + 56) ^ m *
              8 ^ (m + 10 * L) * K * Δ ^ (m + 10 * L)) * a ^ (15 * L + m) := by
                simp only [mul_pow, pow_add]
                ring
            _ ≤ _ := Nat.mul_le_mul_right _
              (hcoeff (by unfold poweredJointWindowBase; omega) (by omega))
        exact window_real_bound_of_power ha hB (by omega) h' hSexp
  · have hm := remainder_window_small_exponent (by omega : 0 < a) (by omega : 0 < A)
      (by omega : a ^ 3 ≤ 124928 * A ^ 4 * H ^ 5 * X) hH hX hT2
    have h' : T ^ 17 ≤ B * a ^ 5 := by
      calc T ^ 17 ≤ 124928 * 3609600 * 56 ^ 11 * (8 * Δ) ^ 3 * a ^ 5 := hm
        _ = (124928 * 3609600 * 56 ^ 11 * 8 ^ 3 * Δ ^ 3) * a ^ 5 := by ring
        _ ≤ B * a ^ 5 := by
          apply Nat.mul_le_mul_right
          dsimp [B]
          have hc' : 124928 * 3609600 * 56 ^ 11 * 8 ^ 3 ≤ poweredJointWindowBase m n L := by
            unfold poweredJointWindowBase; omega
          calc _ ≤ poweredJointWindowBase m n L * Δ ^ (17 + 10 * L + 5 * n + m) :=
              Nat.mul_le_mul hc' (Nat.pow_le_pow_right hΔ (by omega))
            _ = poweredJointWindowBase m n L * 1 * Δ ^ (17 + 10 * L + 5 * n + m) := by ring
            _ ≤ _ := by gcongr; omega
    exact window_real_bound_of_power ha hB (by decide : 0 < 17) h' hα

end PierceLengthBound.FixedDividend
