/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.RealPowerBounds
public import PierceLengthBound.PoweredJointExponent
public import PierceLengthBound.FixedDividendWindow
public import ArithmeticHeights.Absolute

/-!
# Window exponents for the exterior lattice coordinates

The five-term local estimate splits into five integer-power branches. One generic window lemma
(`window_branch_exponent`) turns a branch `T^L ≤ K X^q B` with a box bound `B T^u ≪ a^v` into
`T^{L+10q+u} ≪ a^{3q+v}`. With `h = 10n + 7m` the five branches give the exponents
`5/17`, `5/17`, `45h/(153h-1)`, `(45h-3m)/(153h-11m)` and `(15h+6n)/(51h+20n)`.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Finset

/-- Five possible dominant terms in the lattice count. -/
def LatticeJointCountBranches (K T H X S Y h m n : ℕ) : Prop :=
  T ≤ K * X ^ 5 ∨ T ^ 2 ≤ K * H * X ^ 8 ∨ T ^ (3 * h) ≤ K * X ^ (15 * h - 1) * H ^ 3 ∨
    T ^ (3 * h) ≤ K * X ^ (15 * h - 2 * m) * S ^ (3 * m) ∨ T ^ h ≤ K * X ^ (5 * h) * Y ^ n

/-- The five-term estimate implies the five integer-power branches. -/
theorem lattice_branches_of_five_term_count {T H X S Y R hN m n : ℕ}
    (hm : 0 < m) (hmh : m ≤ hN)
    (hcount : let h : ℝ := (hN : ℝ)
      (T : ℝ) ≤ R * ((X : ℝ) ^ 5 + (X : ℝ) ^ 4 * (H : ℝ) ^ (1 / 2 : ℝ) +
        (X : ℝ) ^ (5 - (1 / h) / 3) * (H : ℝ) ^ (1 / h) +
        (X : ℝ) ^ (5 - (2 * m / h) / 3) * (S : ℝ) ^ (m / h) +
        (X : ℝ) ^ 5 * (Y : ℝ) ^ (n / h))) :
    LatticeJointCountBranches ((5 * (R + 1)) ^ (3 * hN))
      T H X S Y hN m n := by
  dsimp only at hcount
  have hN1 : 1 ≤ hN := by omega
  set h : ℝ := (hN : ℝ)
  have hh : (0 : ℝ) < h := by simp only [h]; exact_mod_cast (show 0 < hN by omega)
  let D := 5 * (R + 1)
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hDle (k : ℕ) (hk' : k ≤ 3 * hN) : D ^ k ≤ D ^ (3 * hN) :=
    Nat.pow_le_pow_right hD hk'
  have hXr : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  have t1 : 0 ≤ (X : ℝ) ^ 5 := by positivity
  have t2 : 0 ≤ (X : ℝ) ^ 4 * (H : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have t3 : 0 ≤ (X : ℝ) ^ (5 - (1 / h) / 3) * (H : ℝ) ^ (1 / h) := by positivity
  have t4 : 0 ≤ (X : ℝ) ^ (5 - (2 * m / h) / 3) * (S : ℝ) ^ (m / h) := by positivity
  have t5 : 0 ≤ (X : ℝ) ^ 5 * (Y : ℝ) ^ (n / h) := by positivity
  have hcase : (T : ℝ) ≤ D * (X : ℝ) ^ 5 ∨
      (T : ℝ) ≤ D * ((X : ℝ) ^ 4 * (H : ℝ) ^ (1 / 2 : ℝ)) ∨
      (T : ℝ) ≤ D * ((X : ℝ) ^ (5 - (1 / h) / 3) * (H : ℝ) ^ (1 / h)) ∨
      (T : ℝ) ≤ D * ((X : ℝ) ^ (5 - (2 * m / h) / 3) * (S : ℝ) ^ (m / h)) ∨
      (T : ℝ) ≤ D * ((X : ℝ) ^ 5 * (Y : ℝ) ^ (n / h)) := by
    have := le_of_le_sum_five t1 t2 t3 t4 t5 hcount
    simpa only [D, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using this
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  rcases hcase with c | c | c | c | c
  · left
    have hn : T ≤ D * X ^ 5 := by exact_mod_cast c
    exact hn.trans (Nat.mul_le_mul_right _ (by simpa using hDle 1 (by omega)))
  · right; left
    have hp := pow_le_pow_left₀ hT0 c 2
    have hs : ((H : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = H := by
      rw [rpow_pow_natCast (Nat.cast_nonneg _) 2 (e := 1) (by norm_num), pow_one]
    have hn : T ^ 2 ≤ D ^ 2 * H * X ^ 8 := by
      have he : (T : ℝ) ^ 2 ≤ (D : ℝ) ^ 2 * H * (X : ℝ) ^ 8 := by
        simpa only [mul_pow, hs, ← pow_mul, mul_assoc, mul_left_comm, mul_comm,
          Nat.reduceMul] using hp
      exact_mod_cast he
    exact hn.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (hDle 2 (by omega))))
  · right; right; left
    have hp := pow_le_pow_left₀ hT0 c (3 * hN)
    have hx : ((X : ℝ) ^ (5 - (1 / h) / 3)) ^ (3 * hN) = (X : ℝ) ^ (15 * hN - 1) :=
      rpow_pow_natCast hXr _ (by
        simp only [h]; push_cast [Nat.cast_sub (show 1 ≤ 15 * hN by omega)]
        field_simp; ring)
    have hHp : ((H : ℝ) ^ (1 / h)) ^ (3 * hN) = (H : ℝ) ^ 3 :=
      rpow_pow_natCast (Nat.cast_nonneg _) _ (by simp only [h]; push_cast; field_simp)
    have he : (T : ℝ) ^ (3 * hN) ≤ (D : ℝ) ^ (3 * hN) * (X : ℝ) ^ (15 * hN - 1) * (H : ℝ) ^ 3 := by
      rw [mul_pow, mul_pow, hx, hHp] at hp
      linarith
    exact_mod_cast he
  · right; right; right; left
    have hp := pow_le_pow_left₀ hT0 c (3 * hN)
    have hx : ((X : ℝ) ^ (5 - (2 * m / h) / 3)) ^ (3 * hN) = (X : ℝ) ^ (15 * hN - 2 * m) :=
      rpow_pow_natCast hXr _ (by
        simp only [h]; push_cast [Nat.cast_sub (show 2 * m ≤ 15 * hN by omega)]
        field_simp; ring)
    have hSp : ((S : ℝ) ^ ((m : ℝ) / h)) ^ (3 * hN) = (S : ℝ) ^ (3 * m) :=
      rpow_pow_natCast (Nat.cast_nonneg _) _ (by simp only [h]; push_cast; field_simp)
    have he : (T : ℝ) ^ (3 * hN) ≤
        (D : ℝ) ^ (3 * hN) * (X : ℝ) ^ (15 * hN - 2 * m) * (S : ℝ) ^ (3 * m) := by
      rw [mul_pow, mul_pow, hx, hSp] at hp
      linarith
    exact_mod_cast he
  · right; right; right; right
    have hp := pow_le_pow_left₀ hT0 c hN
    have hYp : ((Y : ℝ) ^ ((n : ℝ) / h)) ^ hN = (Y : ℝ) ^ n :=
      rpow_pow_natCast (Nat.cast_nonneg _) _ (by simp only [h]; field_simp)
    have he : (T : ℝ) ^ hN ≤ (D : ℝ) ^ hN * (X : ℝ) ^ (5 * hN) * (Y : ℝ) ^ n := by
      rw [mul_pow, mul_pow, hYp, ← pow_mul] at hp
      calc (T : ℝ) ^ hN ≤ _ := hp
        _ = _ := by ring
    have hn : T ^ hN ≤ D ^ hN * X ^ (5 * hN) * Y ^ n := by exact_mod_cast he
    exact hn.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (hDle hN (by omega))))

/-- The five-term split at the degree `h = 10n + 7m`. -/
theorem lattice_joint_branches_of_five_term_count {T H X S Y R m n : ℕ} (hm : 0 < m)
    (hcount : let h : ℝ := ((10 * n + 7 * m : ℕ) : ℝ)
      (T : ℝ) ≤ R * ((X : ℝ) ^ 5 + (X : ℝ) ^ 4 * (H : ℝ) ^ (1 / 2 : ℝ) +
        (X : ℝ) ^ (5 - (1 / h) / 3) * (H : ℝ) ^ (1 / h) +
        (X : ℝ) ^ (5 - (2 * m / h) / 3) * (S : ℝ) ^ (m / h) +
        (X : ℝ) ^ 5 * (Y : ℝ) ^ (n / h))) :
    LatticeJointCountBranches ((5 * (R + 1)) ^ (3 * (10 * n + 7 * m)))
      T H X S Y (10 * n + 7 * m) m n := by
  exact lattice_branches_of_five_term_count hm (by omega) hcount

/-- A constant covering all window ranges for fixed coordinate powers. After `1`, the summands
are the constants of the large-mean-gap window (`122449`), of the five branches of
`LatticeJointCountBranches` in order, and of the small-scale window. -/
def latticeWindowBase (h m n : ℕ) : ℕ :=
  1 + 122449 + 3609600 ^ 5 * 56 ^ 30 * 8 ^ 10 + 3609600 ^ 8 * 56 ^ 49 * 8 ^ 17 +
    (3609600 * 56 ^ 6 * 8 ^ 2) ^ (15 * h - 1) * (56 * 8) ^ 3 +
    (3609600 * 56 ^ 6 * 8 ^ 2) ^ (15 * h - 2 * m) * (9472 * 56 ^ 3) ^ (3 * m) +
    (3609600 * 56 ^ 6 * 8 ^ 2) ^ (5 * h) *
      (1259991040 * 56 ^ 10 * 8 ^ 5) ^ n +
    124928 * 3609600 * 56 ^ 11 * 8 ^ 3

/-- The power of `Δ` in the window bound: it covers the powers `10`, `17`, `30h + 1`,
`30h - 4m` and `10h + 5n` of the five branches for arbitrary graph degree `h`. -/
def latticeWindowDeltaExponent (h n : ℕ) : ℕ := 30 * h + 5 * n + 17

/-- The window constant `latticeWindowBase` at the degree `h = 10n + 7m`. -/
abbrev latticeJointWindowBase (m n : ℕ) : ℕ := latticeWindowBase (10 * n + 7 * m) m n

/-- The power `latticeWindowDeltaExponent` of the divisor bound at `h = 10n + 7m`. -/
abbrev latticeJointWindowDeltaExponent (m n : ℕ) : ℕ :=
  latticeWindowDeltaExponent (10 * n + 7 * m) n

/-- The window exponent of the gap branch `T^{3h} ≤ K X^{15h-1} H³`. -/
noncomputable def latticeExponentH (h : ℕ) : ℝ := ((45 * h : ℕ) : ℝ) / (153 * h - 1 : ℕ)

/-- The window exponent of the curvature branch `T^{3h} ≤ K X^{15h-2m} S^{3m}`. -/
noncomputable def latticeExponentS (h m : ℕ) : ℝ :=
  ((45 * h - 3 * m : ℕ) : ℝ) / (153 * h - 11 * m : ℕ)

/-- The window exponent of the rank-five branch `T^h ≤ K X^{5h} Yⁿ`. -/
noncomputable def latticeExponentY (h n : ℕ) : ℝ :=
  ((15 * h + 6 * n : ℕ) : ℝ) / (51 * h + 20 * n : ℕ)

set_option exponentiation.threshold 1000 in
/-- Every window is bounded at any exponent dominating the three lattice ratios and the
complementary exponent `5/17`. -/
theorem window_real_of_lattice_count {a A T Δ K h m n : ℕ} {α : ℝ}
    (hm : 0 < m) (hmh : m ≤ h)
    (hα : (5 : ℝ) / 17 ≤ α) (hHexp : latticeExponentH h ≤ α)
    (hSexp : latticeExponentS h m ≤ α)
    (hYexp : latticeExponentY h n ≤ α)
    (hT : 36 ≤ T) (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3)
    (hdrop : T * (T - 1) ≤ 4 * A * Δ)
    (hlocal : let H := 28 * a / (A * T) + 1
      let X := 3609600 * A ^ 4 * H ^ 6 / a ^ 3
      let S := 9472 * A ^ 3 * H ^ 3 / a ^ 2
      let Y := 1259991040 * A ^ 5 * H ^ 10 / a ^ 4
      124928 * A ^ 4 * H ^ 5 * X < a ^ 3 →
        LatticeJointCountBranches K T H X S Y h m n) :
    (T : ℝ) ≤ (latticeWindowBase h m n * (K + 1) *
      Δ ^ latticeWindowDeltaExponent h n : ℕ) * (a : ℝ) ^ α := by
  have hh1 : 1 ≤ h := by omega
  obtain ⟨hA, hΔ, ha, hT2⟩ := window_facts (by omega) hsix hdrop
  set e := latticeWindowDeltaExponent h n
  have he : e = 30 * h + 5 * n + 17 := rfl
  have hc₀ : 122449 + 124928 * 3609600 * 56 ^ 11 * 8 ^ 3 ≤ latticeWindowBase h m n := by
    unfold latticeWindowBase; omega
  replace hT2 : T ^ 2 ≤ (8 * Δ) * A := hT2.trans_eq (by ring)
  have hfin {N r c f : ℕ} (hN : 0 < N) (hc : c ≤ latticeWindowBase h m n) (hf : f ≤ e)
      (hT : T ^ N ≤ c * K * Δ ^ f * a ^ r) (hr : (r : ℝ) / N ≤ α) :=
    window_real_of_branch_power ha hΔ (by omega) hN hc K.le_succ hf hT hr
  by_cases hbig : 28 * a < A * T
  · exact window_real_large_mean_gap_of_base ha hΔ (by omega) hα hsix hbig
  let H := 28 * a / (A * T) + 1
  let X := 3609600 * A ^ 4 * H ^ 6 / a ^ 3
  have hH : H * (A * T) ≤ 56 * a := gap_height_mul_le (not_lt.mp hbig)
  have hX : X * a ^ 3 ≤ 3609600 * A ^ 4 * H ^ 6 := Nat.div_mul_le_self _ _
  have hE : 3609600 * 56 ^ 6 * (8 * Δ) ^ 2 = (3609600 * 56 ^ 6 * 8 ^ 2) * Δ ^ 2 := by ring
  by_cases hscale : 124928 * A ^ 4 * H ^ 5 * X < a ^ 3
  · rcases hlocal hscale with c | c | c | c | c
    · -- `T ≤ K X⁵`
      have hw := window_branch_exponent (L := 1) (q := 5) (u := 0) (v := 0) (B := 1) (F := 1)
        (by omega) (by simpa using c) hH hX (by simp) hT2
      apply hfin (N := 51) (r := 15) (c := 3609600 ^ 5 * 56 ^ 30 * 8 ^ 10) (f := 10)
        (by decide) (by unfold latticeWindowBase; omega) (by omega)
      · calc T ^ 51 ≤ K * (3609600 * 56 ^ 6 * (8 * Δ) ^ 2) ^ 5 * 1 * a ^ (3 * 5 + 0) := hw
          _ = _ := by ring
      · exact (by norm_num : ((15 : ℕ) : ℝ) / (51 : ℕ) ≤ 5 / 17).trans hα
    · -- `T² ≤ K H X⁸`
      have hw := window_branch_exponent (L := 2) (q := 8) (u := 3) (v := 1) (B := H) (K := K)
        (F := 56 * (8 * Δ)) (by omega) (c.trans (le_of_eq (by ring)))
        hH hX (by simpa using gap_cube_box hH hT2) hT2
      apply hfin (N := 85) (r := 25) (c := 3609600 ^ 8 * 56 ^ 49 * 8 ^ 17) (f := 17)
        (by decide) (by unfold latticeWindowBase; omega) (by omega)
      · calc T ^ 85 ≤ K * (3609600 * 56 ^ 6 * (8 * Δ) ^ 2) ^ 8 * (56 * (8 * Δ)) *
            a ^ (3 * 8 + 1) := hw
          _ = _ := by ring
      · exact (by norm_num : ((25 : ℕ) : ℝ) / (85 : ℕ) ≤ 5 / 17).trans hα
    · -- `T^{3h} ≤ K X^{15h-1} H³`
      have hbox : H ^ 3 * T ^ 9 ≤ (56 * (8 * Δ)) ^ 3 * a ^ 3 := by
        have := Nat.pow_le_pow_left (gap_cube_box hH hT2) 3
        calc H ^ 3 * T ^ 9 = (H * T ^ 3) ^ 3 := by ring
          _ ≤ _ := this
          _ = _ := by ring
      have hw := window_branch_exponent (L := 3 * h) (q := 15 * h - 1) (u := 9) (v := 3)
        (by omega) c hH hX hbox hT2
      apply hfin (N := 3 * h + 10 * (15 * h - 1) + 9) (r := 3 * (15 * h - 1) + 3)
        (c := (3609600 * 56 ^ 6 * 8 ^ 2) ^ (15 * h - 1) * (56 * 8) ^ 3)
        (f := 2 * (15 * h - 1) + 3) (by omega)
        (by unfold latticeWindowBase; omega)
        (by omega)
      · calc _ ≤ _ := hw
          _ = _ := by rw [hE, mul_pow, ← pow_mul]; ring
      · refine le_trans (le_of_eq ?_) hHexp
        unfold latticeExponentH
        congr 1 <;> push_cast [Nat.cast_sub (show 1 ≤ 15 * h by omega),
          Nat.cast_sub (show 1 ≤ 153 * h by omega)] <;> ring
    · -- `T^{3h} ≤ K X^{15h-2m} S^{3m}`
      let S := 9472 * A ^ 3 * H ^ 3 / a ^ 2
      have hS := curvature_height_times_cube (S := S) (by omega) (by omega) hH
        (Nat.div_mul_le_self _ _)
      have hbox : S ^ (3 * m) * T ^ (9 * m) ≤ (9472 * 56 ^ 3) ^ (3 * m) * a ^ (3 * m) := by
        have := Nat.pow_le_pow_left hS (3 * m)
        calc S ^ (3 * m) * T ^ (9 * m) = (S * T ^ 3) ^ (3 * m) := by
              rw [mul_pow, ← pow_mul]; ring_nf
          _ ≤ _ := this
          _ = _ := by rw [mul_pow]
      have hw := window_branch_exponent (L := 3 * h) (q := 15 * h - 2 * m) (u := 9 * m)
        (v := 3 * m) (by omega) c hH hX hbox hT2
      apply hfin (N := 3 * h + 10 * (15 * h - 2 * m) + 9 * m)
        (r := 3 * (15 * h - 2 * m) + 3 * m)
        (c := (3609600 * 56 ^ 6 * 8 ^ 2) ^ (15 * h - 2 * m) * (9472 * 56 ^ 3) ^ (3 * m))
        (f := 2 * (15 * h - 2 * m)) (by omega)
        (by unfold latticeWindowBase; omega)
        (by omega)
      · calc _ ≤ _ := hw
          _ = _ := by rw [hE, mul_pow, ← pow_mul]; ring
      · refine le_trans (le_of_eq ?_) hSexp
        unfold latticeExponentS
        congr 1 <;> push_cast [Nat.cast_sub (show 2 * m ≤ 15 * h by omega),
          Nat.cast_sub (show 3 * m ≤ 45 * h by omega),
          Nat.cast_sub (show 11 * m ≤ 153 * h by omega)] <;> ring
    · -- `T^h ≤ K X^{5h} Yⁿ`
      have hY : (1259991040 * A ^ 5 * H ^ 10 / a ^ 4) ^ n * T ^ (20 * n) ≤
          (1259991040 * 56 ^ 10 * (8 * Δ) ^ 5) ^ n * a ^ (6 * n) :=
        powered_rank_five_height (by omega) (by omega) hH (Nat.div_mul_le_self _ _) hT2
      have hw := window_branch_exponent (L := h) (q := 5 * h) (u := 20 * n) (v := 6 * n)
        (by omega) c hH hX hY hT2
      apply hfin (N := h + 10 * (5 * h) + 20 * n) (r := 3 * (5 * h) + 6 * n)
        (c := (3609600 * 56 ^ 6 * 8 ^ 2) ^ (5 * h) * (1259991040 * 56 ^ 10 * 8 ^ 5) ^ n)
        (f := 10 * h + 5 * n) (by omega) (by unfold latticeWindowBase; omega)
        (by omega)
      · calc _ ≤ _ := hw
          _ = _ := by rw [hE, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, pow_add]; ring
      · refine le_trans (le_of_eq ?_) hYexp
        unfold latticeExponentY
        congr 1 <;> push_cast <;> ring
  · have hw := remainder_window_small_exponent (by omega : 0 < a) (by omega : 0 < A)
      (by omega : a ^ 3 ≤ 124928 * A ^ 4 * H ^ 5 * X) hH hX hT2
    exact window_real_of_branch_power (c := 124928 * 3609600 * 56 ^ 11 * 8 ^ 3) (k := 1) (f := 3)
      ha hΔ (by omega) (by decide) (by omega) (by omega) (by omega) (hw.trans_eq (by ring)) hα

/-- `window_real_of_lattice_count` at the degree `h = 10n + 7m`. -/
theorem window_real_of_lattice_joint_count {a A T Δ K m n : ℕ} {α : ℝ}
    (hm : 0 < m)
    (hα : (5 : ℝ) / 17 ≤ α) (hHexp : latticeExponentH (10 * n + 7 * m) ≤ α)
    (hSexp : latticeExponentS (10 * n + 7 * m) m ≤ α)
    (hYexp : latticeExponentY (10 * n + 7 * m) n ≤ α)
    (hT : 36 ≤ T) (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3)
    (hdrop : T * (T - 1) ≤ 4 * A * Δ)
    (hlocal : let H := 28 * a / (A * T) + 1
      let X := 3609600 * A ^ 4 * H ^ 6 / a ^ 3
      let S := 9472 * A ^ 3 * H ^ 3 / a ^ 2
      let Y := 1259991040 * A ^ 5 * H ^ 10 / a ^ 4
      124928 * A ^ 4 * H ^ 5 * X < a ^ 3 →
        LatticeJointCountBranches K T H X S Y (10 * n + 7 * m) m n) :
    (T : ℝ) ≤ (latticeJointWindowBase m n * (K + 1) *
      Δ ^ latticeJointWindowDeltaExponent m n : ℕ) * (a : ℝ) ^ α := by
  exact window_real_of_lattice_count hm (by omega) hα hHexp hSexp hYexp hT hsix hdrop hlocal

end PierceLengthBound.FixedDividend
