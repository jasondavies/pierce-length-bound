/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendWindow

/-!
# Reduction of the final window exponent to the local curve count

The local count is an explicit premise, required only when the scale excludes
lines. All integer rounding, complementary scales, and exponent comparisons in
this reduction are proved here. This is not yet a bound for the Pierce length.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend

/-- A fixed constant accommodating all three scale ranges. -/
def windowConstant305 : ℕ :=
  122449 ^ 77 + 3609600 ^ 29 * 56 ^ 177 * 8 ^ 61 +
    (124928 * 3609600 * 56 ^ 11 * 8 ^ 3) ^ 18

/-- A window with a large mean quotient gap has an elementary quarter-power bound. -/
lemma window_large_mean_gap {a A T : ℕ} (ha : 1 ≤ a)
    (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3) (hbig : 28 * a < A * T) :
    T ^ 4 ≤ 122449 * a := by
  have h1 : (28 * a) ^ 2 * T ^ 4 ≤ 96000000 * a ^ 3 := by
    calc (28 * a) ^ 2 * T ^ 4 ≤ (A * T) ^ 2 * T ^ 4 := by gcongr
      _ = T ^ 6 * A ^ 2 := by ring
      _ ≤ _ := hsix
  have h2 : (784 * T ^ 4) * a ^ 2 ≤ (784 * (122449 * a)) * a ^ 2 := by
    calc (784 * T ^ 4) * a ^ 2 = (28 * a) ^ 2 * T ^ 4 := by ring
      _ ≤ 96000000 * a ^ 3 := h1
      _ ≤ (784 * (122449 * a)) * a ^ 2 := by ring_nf; omega
  have := Nat.le_of_mul_le_mul_right h2 (by positivity)
  omega

set_option exponentiation.threshold 1000 in
/-- The full integer window reduction, with its single missing local-count premise explicit. -/
theorem window_305_of_local_count {a A T Δ K : ℕ}
    (hT : 36 ≤ T) (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3)
    (hdrop : T * (T - 1) ≤ 4 * A * Δ)
    (hlocal : let H := 28 * a / (A * T) + 1
      let M := 3609600 * A ^ 4 * H ^ 6 / a ^ 3
      124928 * A ^ 4 * H ^ 5 * M < a ^ 3 → T ^ 6 ≤ K * H ^ 3 * M ^ 29) :
    T ^ 305 ≤ windowConstant305 * (K + 1) * Δ ^ 61 * a ^ 90 := by
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
  have hT2 : T ^ 2 ≤ (8 * Δ) * A := by
    have hTT : T ^ 2 ≤ 2 * (T * (T - 1)) := by
      have : T ≤ 2 * (T - 1) := by omega
      nlinarith
    nlinarith
  by_cases hbig : 28 * a < A * T
  · have hquarter := window_large_mean_gap ha hsix hbig
    calc T ^ 305 ≤ T ^ 308 := Nat.pow_le_pow_right (by omega) (by norm_num)
      _ = (T ^ 4) ^ 77 := by ring
      _ ≤ (122449 * a) ^ 77 := by gcongr
      _ = 122449 ^ 77 * a ^ 77 := by ring
      _ ≤ windowConstant305 * (K + 1) * Δ ^ 61 * a ^ 90 := by
        have hc : 122449 ^ 77 ≤ windowConstant305 := by unfold windowConstant305; omega
        calc _ ≤ windowConstant305 * a ^ 90 := by gcongr; norm_num
             _ = windowConstant305 * 1 * 1 * a ^ 90 := by ring
             _ ≤ _ := by
               gcongr
               · omega
               · exact Nat.one_le_pow 61 Δ hΔ
  let H := 28 * a / (A * T) + 1
  let M := 3609600 * A ^ 4 * H ^ 6 / a ^ 3
  have hH : H * (A * T) ≤ 56 * a := by
    have := Nat.div_mul_le_self (28 * a) (A * T)
    dsimp only [H]
    rw [add_mul, one_mul]
    omega
  have hM : M * a ^ 3 ≤ 3609600 * A ^ 4 * H ^ 6 := Nat.div_mul_le_self _ _
  by_cases hscale : 124928 * A ^ 4 * H ^ 5 * M < a ^ 3
  · have hm := remainder_window_main_exponent (by omega : 0 < a) (by omega : 0 < A)
      (hlocal hscale) hH hM hT2
    have hc : 3609600 ^ 29 * 56 ^ 177 * 8 ^ 61 ≤ windowConstant305 := by
      unfold windowConstant305; omega
    calc T ^ 305 ≤ K * 3609600 ^ 29 * 56 ^ 177 * (8 * Δ) ^ 61 * a ^ 90 := hm
      _ = (3609600 ^ 29 * 56 ^ 177 * 8 ^ 61) * K * Δ ^ 61 * a ^ 90 := by ring
      _ ≤ _ := by gcongr; omega
  · have hm := remainder_window_small_exponent (by omega : 0 < a) (by omega : 0 < A)
      (by omega : a ^ 3 ≤ 124928 * A ^ 4 * H ^ 5 * M) hH hM hT2
    have hc : (124928 * 3609600 * 56 ^ 11 * 8 ^ 3) ^ 18 ≤ windowConstant305 := by
      unfold windowConstant305; omega
    calc T ^ 305 ≤ T ^ 306 := Nat.pow_le_pow_right (by omega) (by norm_num)
      _ = (T ^ 17) ^ 18 := by ring
      _ ≤ (124928 * 3609600 * 56 ^ 11 * (8 * Δ) ^ 3 * a ^ 5) ^ 18 := by gcongr
      _ = (124928 * 3609600 * 56 ^ 11 * 8 ^ 3) ^ 18 * Δ ^ 54 * a ^ 90 := by ring
      _ ≤ windowConstant305 * Δ ^ 61 * a ^ 90 := by gcongr; norm_num
      _ = windowConstant305 * 1 * Δ ^ 61 * a ^ 90 := by ring
      _ ≤ _ := by gcongr; omega

end PierceLengthBound.FixedDividend
