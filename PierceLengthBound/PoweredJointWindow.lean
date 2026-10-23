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
  obtain ⟨hA, hΔ, ha, hT2⟩ := window_facts (by omega) hsix hdrop
  have hc₀ : 122449 + 124928 * 3609600 * 56 ^ 11 * 8 ^ 3 ≤ poweredJointWindowBase m n L := by
    unfold poweredJointWindowBase; omega
  replace hT2 : T ^ 2 ≤ (8 * Δ) * A := hT2.trans_eq (by ring)
  have hfin {N r c f : ℕ} (hN : 0 < N) (hc : c ≤ poweredJointWindowBase m n L)
      (hf : f ≤ 17 + 10 * L + 5 * n + m)
      (hT : T ^ N ≤ c * K * Δ ^ f * a ^ r) (hr : (r : ℝ) / N ≤ α) :=
    window_real_of_branch_power ha hΔ (by omega) hN hc K.le_succ hf hT hr
  by_cases hbig : 28 * a < A * T
  · exact window_real_large_mean_gap_of_base ha hΔ (by omega) hα hsix hbig
  let H := 28 * a / (A * T) + 1
  let X := 3609600 * A ^ 4 * H ^ 6 / a ^ 3
  have hH : H * (A * T) ≤ 56 * a := gap_height_mul_le (not_lt.mp hbig)
  have hX : X * a ^ 3 ≤ 3609600 * A ^ 4 * H ^ 6 := Nat.div_mul_le_self _ _
  by_cases hscale : 124928 * A ^ 4 * H ^ 5 * X < a ^ 3
  · rcases hlocal hscale with h | h | h
    · have hm := window_branch_exponent (L := 1) (q := 5) (u := 0) (v := 0) (B := 1) (F := 1)
        (by omega : 0 < a) (by simpa using h) hH hX (by simp) hT2
      have h' : T ^ 51 ≤ 3609600 ^ 5 * 56 ^ 30 * 8 ^ 10 * K * Δ ^ 10 * a ^ 15 := by
        calc T ^ 51 ≤ K * (3609600 * 56 ^ 6 * (8 * Δ) ^ 2) ^ 5 * 1 * a ^ (3 * 5 + 0) := hm
          _ = _ := by ring
      exact hfin (by decide) (by unfold poweredJointWindowBase; omega) (by omega) h'
        ((by norm_num : (15 : ℝ) / 51 ≤ 5 / 17).trans hα)
    · have hm := window_branch_exponent (L := 2) (q := 8) (u := 3) (v := 1) (B := H) (K := K)
        (F := 56 * (8 * Δ)) (by omega : 0 < a) (h.trans (le_of_eq (by ring)))
        hH hX (by simpa using gap_cube_box hH hT2) hT2
      have h' : T ^ 85 ≤ 3609600 ^ 8 * 56 ^ 49 * 8 ^ 17 * K * Δ ^ 17 * a ^ 25 := by
        calc T ^ 85 ≤ K * (3609600 * 56 ^ 6 * (8 * Δ) ^ 2) ^ 8 * (56 * (8 * Δ)) *
            a ^ (3 * 8 + 1) := hm
          _ = _ := by ring
      exact hfin (by decide) (by unfold poweredJointWindowBase; omega) (by omega) h'
        ((by norm_num : (25 : ℝ) / 85 ≤ 5 / 17).trans hα)
    · let S := 4352 * A ^ 3 * H ^ 3 / a ^ 2
      let Y := 1259991040 * A ^ 5 * H ^ 10 / a ^ 4
      rcases le_total (max H (S ^ m)) (Y ^ n) with hSY | hSY
      · rw [max_eq_right hSY] at h
        have hY : Y ^ n * T ^ (20 * n) ≤
            (1259991040 * 56 ^ 10 * (8 * Δ) ^ 5) ^ n * a ^ (6 * n) :=
          powered_rank_five_height (by omega) (by omega) hH (Nat.div_mul_le_self _ _) hT2
        have hc := remainder_window_powered_box_exponent
          (by omega : 0 < a) h hH hX hY hT2
        have h' : T ^ (51 * L + 20 * n) ≤ 3609600 ^ (5 * L) * 56 ^ (30 * L + 10 * n) *
            1259991040 ^ n * 8 ^ (5 * n + 10 * L) * K * Δ ^ (5 * n + 10 * L) *
            a ^ (15 * L + 6 * n) := by
          calc _ ≤ K * 3609600 ^ (5 * L) * 56 ^ (30 * L) *
              (1259991040 * 56 ^ 10 * (8 * Δ) ^ 5) ^ n * (8 * Δ) ^ (10 * L) *
              a ^ (15 * L + 6 * n) := hc
            _ = _ := by
                simp only [mul_pow, ← pow_mul, pow_add]
                ring
        exact hfin (by omega) (by unfold poweredJointWindowBase; omega) (by omega) h' hYexp
      · rw [max_eq_left hSY] at h
        have hS : S * T ^ 3 ≤ 4352 * 56 ^ 3 * a := curvature_height_times_cube
          (by omega) (by omega) hH (Nat.div_mul_le_self _ _)
        have hbox := max_powered_curvature_height hm (by omega : 0 < A)
          (show 1 ≤ 8 * Δ by omega) (show 1 ≤ H from Nat.le_add_left 1 _) hH hS hT2
        have hc := remainder_window_powered_box_exponent
          (by omega : 0 < a) h hH hX hbox hT2
        have h' : T ^ (51 * L + 3 * m) ≤ 3609600 ^ (5 * L) * 56 ^ (30 * L) *
            (4352 * 56 ^ 3 + 56) ^ m * 8 ^ (m + 10 * L) * K * Δ ^ (m + 10 * L) *
            a ^ (15 * L + m) := by
          calc _ ≤ K * 3609600 ^ (5 * L) * 56 ^ (30 * L) *
              ((4352 * 56 ^ 3 + 56) * (8 * Δ)) ^ m * (8 * Δ) ^ (10 * L) *
              a ^ (15 * L + m) := hc
            _ = _ := by
                simp only [mul_pow, pow_add]
                ring
        exact hfin (by omega) (by unfold poweredJointWindowBase; omega) (by omega) h' hSexp
  · have hm := remainder_window_small_exponent (by omega : 0 < a) (by omega : 0 < A)
      (by omega : a ^ 3 ≤ 124928 * A ^ 4 * H ^ 5 * X) hH hX hT2
    exact window_real_of_branch_power (c := 124928 * 3609600 * 56 ^ 11 * 8 ^ 3) (k := 1) (f := 3)
      ha hΔ (by omega) (by decide) (by omega) (by omega) (by omega) (hm.trans_eq (by ring)) hα

end PierceLengthBound.FixedDividend
