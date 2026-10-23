/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionExponent

/-! Window reduction for polar projection. The counting estimate is an explicit input
here and is proved in `PolarProjectionMain`. The arithmetic below includes all three
bad-pattern box terms. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- Integer-power branches of the `X^(14/3) max(H,S,Y)^(1/17)` contribution. -/
def PolarBadCountBranches (K T H X S Y : ℕ) : Prop :=
  T ^ 51 ≤ K * X ^ 238 * H ^ 3 ∨ T ^ 51 ≤ K * X ^ 238 * S ^ 3 ∨
    T ^ 51 ≤ K * X ^ 238 * Y ^ 3

/-- Good patterns use degree `60n+56m`; bad patterns keep the old degree-17 graph. -/
def PolarProjectionCountBranches (K T H X S Y m n : ℕ) : Prop :=
  LatticeJointCountBranches K T H X S Y (polarProjectionGraphDegree m n) m n ∨
    PolarBadCountBranches K T H X S Y

/-- A fixed constant covering the three bad-pattern cases and large mean gaps. -/
def polarBadWindowBase : ℕ :=
  1 + 122449 + (3609600 * 56 ^ 6 * 8 ^ 2) ^ 238 *
    ((56 * 8) ^ 3 + (9472 * 56 ^ 3) ^ 3 + (1259991040 * 56 ^ 10 * 8 ^ 5) ^ 3)

set_option exponentiation.threshold 3000 in
/-- The enlarged bad-pattern contribution is still below exponent `5/17`. -/
theorem window_real_of_polar_bad_count {a A T Δ K : ℕ} {α : ℝ}
    (hα : (5 : ℝ) / 17 ≤ α) (hT : 36 ≤ T)
    (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3)
    (hdrop : T * (T - 1) ≤ 4 * A * Δ)
    (hbad : let H := 28 * a / (A * T) + 1
      let X := 3609600 * A ^ 4 * H ^ 6 / a ^ 3
      let S := 9472 * A ^ 3 * H ^ 3 / a ^ 2
      let Y := 1259991040 * A ^ 5 * H ^ 10 / a ^ 4
      PolarBadCountBranches K T H X S Y) :
    (T : ℝ) ≤ (polarBadWindowBase * (K + 1) * Δ ^ 491 : ℕ) * (a : ℝ) ^ α := by
  obtain ⟨hA, hΔ, ha, hT2⟩ := window_facts (by omega) hsix hdrop
  have hc₀ : 122449 ≤ polarBadWindowBase := by unfold polarBadWindowBase; omega
  have hfin {N r c f : ℕ} (hN : 0 < N) (hc : c ≤ polarBadWindowBase) (hf : f ≤ 491)
      (hcount : T ^ N ≤ c * K * Δ ^ f * a ^ r) (hr : (r : ℝ) / N ≤ α) :=
    window_real_of_branch_power ha hΔ (by omega) hN hc K.le_succ hf hcount hr
  by_cases hbig : 28 * a < A * T
  · exact window_real_large_mean_gap_of_base ha hΔ hc₀ hα hsix hbig
  let H := 28 * a / (A * T) + 1
  let X := 3609600 * A ^ 4 * H ^ 6 / a ^ 3
  let S := 9472 * A ^ 3 * H ^ 3 / a ^ 2
  let Y := 1259991040 * A ^ 5 * H ^ 10 / a ^ 4
  have hH : H * (A * T) ≤ 56 * a := gap_height_mul_le (not_lt.mp hbig)
  have hX : X * a ^ 3 ≤ 3609600 * A ^ 4 * H ^ 6 := Nat.div_mul_le_self _ _
  replace hT2 : T ^ 2 ≤ (8 * Δ) * A := hT2.trans_eq (by ring)
  have hE : 3609600 * 56 ^ 6 * (8 * Δ) ^ 2 = (3609600 * 56 ^ 6 * 8 ^ 2) * Δ ^ 2 := by ring
  rcases hbad with c | c | c
  · have hbox : H ^ 3 * T ^ 9 ≤ (56 * (8 * Δ)) ^ 3 * a ^ 3 := by
      have := Nat.pow_le_pow_left (gap_cube_box hH hT2) 3
      simpa only [mul_pow, ← pow_mul, show 3 * 3 = 9 from rfl] using this
    have hw := window_branch_exponent (L := 51) (q := 238) (u := 9) (v := 3)
      (by omega : 0 < a) c hH hX hbox hT2
    apply hfin (N := 2440) (r := 717)
      (c := (3609600 * 56 ^ 6 * 8 ^ 2) ^ 238 * (56 * 8) ^ 3) (f := 479)
      (by decide) (by unfold polarBadWindowBase; omega) (by decide)
    · calc _ ≤ _ := hw
           _ = _ := by rw [hE, mul_pow, mul_pow, ← pow_mul]; ring
    · exact (by norm_num : ((717 : ℕ) : ℝ) / (2440 : ℕ) ≤ 5 / 17).trans hα
  · have hS : S * T ^ 3 ≤ (9472 * 56 ^ 3) * a :=
      curvature_height_times_cube (by omega : 0 < a) (by omega : 0 < A) hH
        (Nat.div_mul_le_self _ _)
    have hbox : S ^ 3 * T ^ 9 ≤ (9472 * 56 ^ 3) ^ 3 * a ^ 3 := by
      have := Nat.pow_le_pow_left hS 3
      simpa only [mul_pow, ← pow_mul, show 3 * 3 = 9 from rfl] using this
    have hw := polarProjection_bad_curvature_window_power (by omega : 0 < a) c hH hX hbox hT2
    apply hfin (N := 2440) (r := 717)
      (c := (3609600 * 56 ^ 6 * 8 ^ 2) ^ 238 * (9472 * 56 ^ 3) ^ 3) (f := 476)
      (by decide) (by unfold polarBadWindowBase; omega) (by decide)
    · calc _ ≤ _ := hw
           _ = _ := by rw [hE, mul_pow, ← pow_mul]; ring
    · exact (by norm_num : ((717 : ℕ) : ℝ) / (2440 : ℕ) ≤ 5 / 17).trans hα
  · have hbox : Y ^ 3 * T ^ 60 ≤ (1259991040 * 56 ^ 10 * (8 * Δ) ^ 5) ^ 3 * a ^ 18 :=
      powered_rank_five_height (by omega : 0 < a) (by omega : 0 < A) hH
        (Nat.div_mul_le_self _ _) hT2
    have hw := polarProjection_bad_rank_five_window_power (by omega : 0 < a) c hH hX hbox hT2
    apply hfin (N := 2491) (r := 732)
      (c := (3609600 * 56 ^ 6 * 8 ^ 2) ^ 238 * (1259991040 * 56 ^ 10 * 8 ^ 5) ^ 3) (f := 491)
      (by decide) (by unfold polarBadWindowBase; omega) (by decide)
    · calc _ ≤ _ := hw
           _ = _ := by rw [hE, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul]; ring
    · exact (by norm_num : ((732 : ℕ) : ℝ) / (2491 : ℕ) ≤ 5 / 17).trans hα

/-- A coefficient covering both the good and bad pattern reductions. -/
def polarProjectionWindowBase (m n : ℕ) : ℕ :=
  latticeWindowBase (polarProjectionGraphDegree m n) m n + polarBadWindowBase

/-- A divisor-loss exponent covering both reductions. -/
def polarProjectionWindowDeltaExponent (m n : ℕ) : ℕ :=
  latticeWindowDeltaExponent (polarProjectionGraphDegree m n) n + 491

/-- Every polar counting branch implies the stated window exponent. -/
theorem window_real_of_polar_projection_count {a A T Δ K m n : ℕ} {α : ℝ}
    (hm : 0 < m) (hα : (5 : ℝ) / 17 ≤ α)
    (hHexp : latticeExponentH (polarProjectionGraphDegree m n) ≤ α)
    (hSexp : latticeExponentS (polarProjectionGraphDegree m n) m ≤ α)
    (hYexp : latticeExponentY (polarProjectionGraphDegree m n) n ≤ α)
    (hT : 36 ≤ T) (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3)
    (hdrop : T * (T - 1) ≤ 4 * A * Δ)
    (hlocal : let H := 28 * a / (A * T) + 1
      let X := 3609600 * A ^ 4 * H ^ 6 / a ^ 3
      let S := 9472 * A ^ 3 * H ^ 3 / a ^ 2
      let Y := 1259991040 * A ^ 5 * H ^ 10 / a ^ 4
      124928 * A ^ 4 * H ^ 5 * X < a ^ 3 →
        PolarProjectionCountBranches K T H X S Y m n) :
    (T : ℝ) ≤ (polarProjectionWindowBase m n * (K + 1) *
      Δ ^ polarProjectionWindowDeltaExponent m n : ℕ) * (a : ℝ) ^ α := by
  have hΔ : 1 ≤ Δ := by
    by_contra hc
    have hz : Δ = 0 := by omega
    simp [hz] at hdrop
    omega
  have hbound {c d : ℕ} (hc : c ≤ polarProjectionWindowBase m n)
      (hd : d ≤ polarProjectionWindowDeltaExponent m n)
      (h : (T : ℝ) ≤ (c * (K + 1) * Δ ^ d : ℕ) * (a : ℝ) ^ α) :
      (T : ℝ) ≤ (polarProjectionWindowBase m n * (K + 1) *
        Δ ^ polarProjectionWindowDeltaExponent m n : ℕ) * (a : ℝ) ^ α := by
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul_right _ hc) (Nat.pow_le_pow_right hΔ hd)
  let H := 28 * a / (A * T) + 1
  let X := 3609600 * A ^ 4 * H ^ 6 / a ^ 3
  let S := 9472 * A ^ 3 * H ^ 3 / a ^ 2
  let Y := 1259991040 * A ^ 5 * H ^ 10 / a ^ 4
  by_cases hb : PolarBadCountBranches K T H X S Y
  · exact hbound (Nat.le_add_left _ _) (Nat.le_add_left _ _)
      (window_real_of_polar_bad_count hα hT hsix hdrop hb)
  · apply hbound (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    apply window_real_of_lattice_count (h := polarProjectionGraphDegree m n)
      (m := m) (n := n) hm (by unfold polarProjectionGraphDegree; omega)
      hα hHexp hSexp hYexp hT hsix hdrop
    dsimp only
    intro hscale
    exact (hlocal hscale).resolve_right hb

end
end PierceLengthBound.FixedDividend
