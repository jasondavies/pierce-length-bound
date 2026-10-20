/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ConicExponent
public import PierceLengthBound.FixedDividendMainReduction

/-! The three conic-count branches in actual remainder-window coordinates.
All geometric counting assertions remain explicit hypotheses. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend

/-- The arithmetic-conic term in remainder-window coordinates. -/
theorem remainder_window_arithmetic_conic_exponent {T H X A a C E D K : ℕ}
    (ha : 0 < a) (hA : 0 < A) (hcount : T ≤ K * X ^ 5)
    (hgap : H * (A * T) ≤ C * a) (hheight : X * a ^ 3 ≤ E * A ^ 4 * H ^ 6)
    (hdrop : T ^ 2 ≤ D * A) :
    T ^ 51 ≤ K * E ^ 5 * C ^ 30 * D ^ 10 * a ^ 15 := by
  have h1 : T * a ^ 15 ≤ K * E ^ 5 * A ^ 20 * H ^ 30 := by
    calc T * a ^ 15 ≤ (K * X ^ 5) * a ^ 15 := by gcongr
      _ = K * (X * a ^ 3) ^ 5 := by ring
      _ ≤ K * (E * A ^ 4 * H ^ 6) ^ 5 := by gcongr
      _ = _ := by ring
  have h2 : (T ^ 31 * A ^ 10) * (A ^ 20 * a ^ 15) ≤
      (K * E ^ 5 * C ^ 30 * a ^ 15) * (A ^ 20 * a ^ 15) := by
    calc _ = (T * a ^ 15) * (A * T) ^ 30 := by ring
      _ ≤ (K * E ^ 5 * A ^ 20 * H ^ 30) * (A * T) ^ 30 := by gcongr
      _ = K * E ^ 5 * A ^ 20 * (H * (A * T)) ^ 30 := by ring
      _ ≤ K * E ^ 5 * A ^ 20 * (C * a) ^ 30 := by gcongr
      _ = _ := by ring
  have h3 := Nat.le_of_mul_le_mul_right h2 (by positivity : 0 < A ^ 20 * a ^ 15)
  calc T ^ 51 = T ^ 31 * (T ^ 2) ^ 10 := by ring
    _ ≤ T ^ 31 * (D * A) ^ 10 := by gcongr
    _ = (T ^ 31 * A ^ 10) * D ^ 10 := by ring
    _ ≤ (K * E ^ 5 * C ^ 30 * a ^ 15) * D ^ 10 := by gcongr
    _ = _ := by ring

/-- The exceptional-parabola term in remainder-window coordinates. -/
theorem remainder_window_exceptional_conic_exponent {T H X A a C E D K : ℕ}
    (ha : 0 < a) (hA : 0 < A) (hcount : T ^ 2 ≤ K * H * X ^ 8)
    (hgap : H * (A * T) ≤ C * a) (hheight : X * a ^ 3 ≤ E * A ^ 4 * H ^ 6)
    (hdrop : T ^ 2 ≤ D * A) :
    T ^ 85 ≤ K * E ^ 8 * C ^ 49 * D ^ 17 * a ^ 25 := by
  have h1 : T ^ 2 * a ^ 24 ≤ K * E ^ 8 * A ^ 32 * H ^ 49 := by
    calc T ^ 2 * a ^ 24 ≤ (K * H * X ^ 8) * a ^ 24 := by gcongr
      _ = K * H * (X * a ^ 3) ^ 8 := by ring
      _ ≤ K * H * (E * A ^ 4 * H ^ 6) ^ 8 := by gcongr
      _ = _ := by ring
  have h2 : (T ^ 51 * A ^ 17) * (A ^ 32 * a ^ 24) ≤
      (K * E ^ 8 * C ^ 49 * a ^ 25) * (A ^ 32 * a ^ 24) := by
    calc _ = (T ^ 2 * a ^ 24) * (A * T) ^ 49 := by ring
      _ ≤ (K * E ^ 8 * A ^ 32 * H ^ 49) * (A * T) ^ 49 := by gcongr
      _ = K * E ^ 8 * A ^ 32 * (H * (A * T)) ^ 49 := by ring
      _ ≤ K * E ^ 8 * A ^ 32 * (C * a) ^ 49 := by gcongr
      _ = _ := by ring
  have h3 := Nat.le_of_mul_le_mul_right h2 (by positivity : 0 < A ^ 32 * a ^ 24)
  calc T ^ 85 = T ^ 51 * (T ^ 2) ^ 17 := by ring
    _ ≤ T ^ 51 * (D * A) ^ 17 := by gcongr
    _ = (T ^ 51 * A ^ 17) * D ^ 17 := by ring
    _ ≤ (K * E ^ 8 * C ^ 49 * a ^ 25) * D ^ 17 := by gcongr
    _ = _ := by ring

/-- Raise a window estimate to a common integer exponent without root rounding. -/
lemma window_power_lift {T a B n r m N R M : ℕ} (hT : 1 ≤ T) (ha : 1 ≤ a)
    (hB : 1 ≤ B) (h : T ^ n ≤ B * a ^ r)
    (hN : N ≤ n * m) (hR : r * m ≤ R) (hM : m ≤ M) :
    T ^ N ≤ B ^ M * a ^ R := by
  calc T ^ N ≤ T ^ (n * m) := Nat.pow_le_pow_right hT hN
    _ = (T ^ n) ^ m := (pow_mul T n m)
    _ ≤ (B * a ^ r) ^ m := by gcongr
    _ = B ^ m * a ^ (r * m) := by rw [mul_pow, pow_mul]
    _ ≤ _ := by gcongr

/-- An absolute constant covering the five local ranges. -/
def conicWindowBase : ℕ :=
  122449 + 3609600 ^ 5 * 56 ^ 30 * 8 ^ 10 +
    3609600 ^ 8 * 56 ^ 49 * 8 ^ 17 +
    3609600 ^ 44 * 56 ^ 267 * 8 ^ 91 +
    124928 * 3609600 * 56 ^ 11 * 8 ^ 3

/-- All three proposed local terms, as an integer-power disjunction. -/
def ConicCountBranches (K T H X : ℕ) : Prop :=
  T ≤ K * X ^ 5 ∨ T ^ 2 ≤ K * H * X ^ 8 ∨ T ^ 9 ≤ K * H ^ 3 * X ^ 44

set_option exponentiation.threshold 1000 in
/-- Exact full-window reduction, conditional on the three-branch local count.
The larger common power avoids losing any of the target exponent to rounding. -/
theorem window_4580_of_conic_count {a A T Δ K : ℕ}
    (hT : 36 ≤ T) (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3)
    (hdrop : T * (T - 1) ≤ 4 * A * Δ)
    (hlocal : let H := 28 * a / (A * T) + 1
      let X := 3609600 * A ^ 4 * H ^ 6 / a ^ 3
      124928 * A ^ 4 * H ^ 5 * X < a ^ 3 → ConicCountBranches K T H X) :
    T ^ 4580 ≤ (conicWindowBase * (K + 1) * Δ ^ 91) ^ 1145 * a ^ 1350 := by
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
  let B := conicWindowBase * (K + 1) * Δ ^ 91
  have hc : 1 ≤ conicWindowBase := by unfold conicWindowBase; omega
  have hB : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr (by dsimp [B]; positivity)
  have hbase : conicWindowBase ≤ B := by
    calc conicWindowBase = conicWindowBase * 1 * 1 := by ring
      _ ≤ B := by
        dsimp [B]
        gcongr
        · omega
        · exact Nat.one_le_pow 91 Δ hΔ
  have hT2 : T ^ 2 ≤ (8 * Δ) * A := by
    have : T ≤ 2 * (T - 1) := by omega
    nlinarith
  have hcoeff {c n : ℕ} (hc : c ≤ conicWindowBase) (hn : n ≤ 91) :
      c * K * Δ ^ n ≤ B := by
    dsimp only [B]
    gcongr
    omega
  by_cases hbig : 28 * a < A * T
  · have h := window_large_mean_gap ha hsix hbig
    have h' : T ^ 4 ≤ B * a ^ 1 := by
      simpa using h.trans (Nat.mul_le_mul_right a
        ((show 122449 ≤ conicWindowBase by unfold conicWindowBase; omega).trans hbase))
    exact window_power_lift (by omega) ha hB h' (m := 1145)
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
          _ ≤ _ := Nat.mul_le_mul_right _ (hcoeff (by unfold conicWindowBase; omega) (by norm_num))
      exact window_power_lift (by omega) ha hB h' (m := 90)
        (by norm_num) (by norm_num) (by norm_num)
    · have hm := remainder_window_exceptional_conic_exponent
        (by omega : 0 < a) (by omega : 0 < A) h hH hX hT2
      have h' : T ^ 85 ≤ B * a ^ 25 := by
        calc T ^ 85 ≤ K * 3609600 ^ 8 * 56 ^ 49 * (8 * Δ) ^ 17 * a ^ 25 := hm
          _ = (3609600 ^ 8 * 56 ^ 49 * 8 ^ 17 * K * Δ ^ 17) * a ^ 25 := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ (hcoeff (by unfold conicWindowBase; omega) (by norm_num))
      exact window_power_lift (by omega) ha hB h' (m := 54)
        (by norm_num) (by norm_num) (by norm_num)
    · have hm := remainder_window_higher_curve_exponent
        (by omega : 0 < a) (by omega : 0 < A) h hH hX hT2
      have h' : T ^ 458 ≤ B * a ^ 135 := by
        calc T ^ 458 ≤ K * 3609600 ^ 44 * 56 ^ 267 * (8 * Δ) ^ 91 * a ^ 135 := hm
          _ = (3609600 ^ 44 * 56 ^ 267 * 8 ^ 91 * K * Δ ^ 91) * a ^ 135 := by ring
          _ ≤ _ := Nat.mul_le_mul_right _ (hcoeff (by unfold conicWindowBase; omega) (by norm_num))
      exact window_power_lift (by omega) ha hB h' (m := 10)
        (by norm_num) (by norm_num) (by norm_num)
  · have hm := remainder_window_small_exponent (by omega : 0 < a) (by omega : 0 < A)
      (by omega : a ^ 3 ≤ 124928 * A ^ 4 * H ^ 5 * X) hH hX hT2
    have h' : T ^ 17 ≤ B * a ^ 5 := by
      calc T ^ 17 ≤ 124928 * 3609600 * 56 ^ 11 * (8 * Δ) ^ 3 * a ^ 5 := hm
        _ = (124928 * 3609600 * 56 ^ 11 * 8 ^ 3 * Δ ^ 3) * a ^ 5 := by ring
        _ ≤ B * a ^ 5 := by
          apply Nat.mul_le_mul_right
          dsimp [B]
          have hc' : 124928 * 3609600 * 56 ^ 11 * 8 ^ 3 ≤ conicWindowBase := by
            unfold conicWindowBase; omega
          calc _ ≤ conicWindowBase * Δ ^ 91 :=
              Nat.mul_le_mul hc' (Nat.pow_le_pow_right hΔ (by norm_num))
            _ = conicWindowBase * 1 * Δ ^ 91 := by ring
            _ ≤ _ := by gcongr; omega
    exact window_power_lift (by omega) ha hB h' (m := 270)
      (by norm_num) (by norm_num) (by norm_num)

end PierceLengthBound.FixedDividend
