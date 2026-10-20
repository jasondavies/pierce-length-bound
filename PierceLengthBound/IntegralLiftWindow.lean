/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftExponent

/-! The three integral-coordinate count branches in actual remainder-window coordinates.
All geometric counting assertions remain explicit hypotheses. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend

/-- An absolute constant covering the five local ranges. -/
def integralLiftWindowBase : ℕ :=
  122449 + 3609600 ^ 5 * 56 ^ 30 * 8 ^ 10 +
    3609600 ^ 8 * 56 ^ 49 * 8 ^ 17 +
    3609600 ^ 50 * 56 ^ 300 * (896 * 56 ^ 3 + 56) * 8 ^ 101 +
    124928 * 3609600 * 56 ^ 11 * 8 ^ 3

/-- All three proposed integral-coordinate local terms, as an integer-power disjunction. -/
def IntegralLiftCountBranches (K T H X S : ℕ) : Prop :=
  T ≤ K * X ^ 5 ∨ T ^ 2 ≤ K * H * X ^ 8 ∨ T ^ 10 ≤ K * X ^ 50 * max H S

set_option exponentiation.threshold 1000 in
/-- Exact full-window reduction, conditional on the three-branch local count.
The larger common power avoids losing any of the target exponent to rounding. -/
theorem window_26163_of_integral_lift_count {a A T Δ K : ℕ}
    (hT : 36 ≤ T) (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3)
    (hdrop : T * (T - 1) ≤ 4 * A * Δ)
    (hlocal : let H := 28 * a / (A * T) + 1
      let X := 3609600 * A ^ 4 * H ^ 6 / a ^ 3
      let S := 896 * A ^ 3 * H ^ 3 / a ^ 2
      124928 * A ^ 4 * H ^ 5 * X < a ^ 3 → IntegralLiftCountBranches K T H X S) :
    T ^ 26163 ≤ (integralLiftWindowBase * (K + 1) * Δ ^ 101) ^ 6541 * a ^ 7701 := by
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
  let B := integralLiftWindowBase * (K + 1) * Δ ^ 101
  have hc : 1 ≤ integralLiftWindowBase := by unfold integralLiftWindowBase; omega
  have hB : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr (by dsimp [B]; positivity)
  have hbase : integralLiftWindowBase ≤ B := by
    calc integralLiftWindowBase = integralLiftWindowBase * 1 * 1 := by ring
      _ ≤ B := by
        dsimp [B]
        gcongr
        · omega
        · exact Nat.one_le_pow 101 Δ hΔ
  have hT2 : T ^ 2 ≤ (8 * Δ) * A := by
    have : T ≤ 2 * (T - 1) := by omega
    nlinarith
  have hcoeff {c n : ℕ} (hc : c ≤ integralLiftWindowBase) (hn : n ≤ 101) :
      c * K * Δ ^ n ≤ B := by
    dsimp only [B]
    gcongr
    omega
  by_cases hbig : 28 * a < A * T
  · have h := window_large_mean_gap ha hsix hbig
    have h' : T ^ 4 ≤ B * a ^ 1 := by
      simpa using h.trans (Nat.mul_le_mul_right a
        ((show 122449 ≤ integralLiftWindowBase by unfold integralLiftWindowBase; omega).trans hbase))
    exact window_power_lift (by omega) ha hB h' (m := 6541)
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
          _ ≤ _ := Nat.mul_le_mul_right _ (hcoeff (by unfold integralLiftWindowBase; omega) (by norm_num))
      exact window_power_lift (by omega) ha hB h' (m := 513)
        (by norm_num) (by norm_num) (by norm_num)
    · have hm := remainder_window_exceptional_conic_exponent
        (by omega : 0 < a) (by omega : 0 < A) h hH hX hT2
      have h' : T ^ 85 ≤ B * a ^ 25 := by
        calc T ^ 85 ≤ K * 3609600 ^ 8 * 56 ^ 49 * (8 * Δ) ^ 17 * a ^ 25 := hm
          _ = (3609600 ^ 8 * 56 ^ 49 * 8 ^ 17 * K * Δ ^ 17) * a ^ 25 := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ (hcoeff (by unfold integralLiftWindowBase; omega) (by norm_num))
      exact window_power_lift (by omega) ha hB h' (m := 308)
        (by norm_num) (by norm_num) (by norm_num)
    · let S := 896 * A ^ 3 * H ^ 3 / a ^ 2
      have hS : S * T ^ 3 ≤ 896 * 56 ^ 3 * a := lift_height_times_cube
        (by omega) (by omega) hH (Nat.div_mul_le_self _ _)
      have hbox := max_lift_height_times_cube (by omega : 0 < A)
        (show 1 ≤ 8 * Δ by omega) hH hS hT2
      have hm := remainder_window_integral_lift_exponent
        (by omega : 0 < a) (by omega : 0 < A) h hH hX hbox hT2
      have h' : T ^ 513 ≤ B * a ^ 151 := by
        calc T ^ 513 ≤ K * 3609600 ^ 50 * 56 ^ 300 *
            ((896 * 56 ^ 3 + 56) * (8 * Δ)) * (8 * Δ) ^ 100 * a ^ 151 := hm
          _ = (3609600 ^ 50 * 56 ^ 300 * (896 * 56 ^ 3 + 56) * 8 ^ 101 * K * Δ ^ 101) *
              a ^ 151 := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ (hcoeff (by unfold integralLiftWindowBase; omega) (by norm_num))
      exact window_power_lift (by omega) ha hB h' (m := 51)
        (by norm_num) (by norm_num) (by norm_num)
  · have hm := remainder_window_small_exponent (by omega : 0 < a) (by omega : 0 < A)
      (by omega : a ^ 3 ≤ 124928 * A ^ 4 * H ^ 5 * X) hH hX hT2
    have h' : T ^ 17 ≤ B * a ^ 5 := by
      calc T ^ 17 ≤ 124928 * 3609600 * 56 ^ 11 * (8 * Δ) ^ 3 * a ^ 5 := hm
        _ = (124928 * 3609600 * 56 ^ 11 * 8 ^ 3 * Δ ^ 3) * a ^ 5 := by ring
        _ ≤ B * a ^ 5 := by
          apply Nat.mul_le_mul_right
          dsimp [B]
          have hc' : 124928 * 3609600 * 56 ^ 11 * 8 ^ 3 ≤ integralLiftWindowBase := by
            unfold integralLiftWindowBase; omega
          calc _ ≤ integralLiftWindowBase * Δ ^ 101 :=
              Nat.mul_le_mul hc' (Nat.pow_le_pow_right hΔ (by norm_num))
            _ = integralLiftWindowBase * 1 * Δ ^ 101 := by ring
            _ ≤ _ := by gcongr; omega
    exact window_power_lift (by omega) ha hB h' (m := 1539)
      (by norm_num) (by norm_num) (by norm_num)

end PierceLengthBound.FixedDividend
