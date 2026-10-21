/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.LatticeJointBound

/-!
# Optimizing the lattice exponents

With `r = n/m` and `h = 10n + 7m`, the curvature exponent is
`(45h - 3m)/(153h - 11m) = (450r + 312)/(1530r + 1060)`, decreasing in `r`, and the rank-five
exponent is `(15h + 6n)/(51h + 20n) = jointExponentY r`, increasing in `r`. They cross at
`r = √105/15`, with common value `γ = 471/1559 - 6√105/7795`, the smaller root of
`7795γ² - 4710γ + 711 = 0`. The gap exponent `45h/(153h - 1)` is below `γ` once `h > 17.2`.
Scaling `m, n` by a common factor keeps `r` fixed, and the proof scales by `6`, which gives
`h ≥ 102` with a margin that `nlinarith` checks easily (`latticeExponentH_lt`). Hence
`P(a, b) ≪ a^{γ + ε}` (`P_le_lattice_optimal`, paper `thm:lattice`).
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- The curvature exponent `latticeExponentS` as a function of the ratio `r = n/m`. -/
def latticeExponentSRatio (r : ℝ) : ℝ := (450 * r + 312) / (1530 * r + 1060)
/-- The optimal ratio `r = √105/15`, where `15r² = 7`. -/
def latticeOptimalRatio : ℝ := Real.sqrt 105 / 15
/-- The optimal exponent `γ* = 471/1559 - 6√105/7795 ≈ 0.2942294`. -/
def latticeOptimalExponent : ℝ := 471 / 1559 - 6 * Real.sqrt 105 / 7795

lemma sqrt105_facts : Real.sqrt 105 ^ 2 = 105 ∧ 0 ≤ Real.sqrt 105 ∧ Real.sqrt 105 < 41 / 4 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 105 by norm_num)
  have hp := Real.sqrt_nonneg (105 : ℝ)
  exact ⟨hs, hp, by nlinarith⟩

lemma latticeOptimalRatio_pos : 0 < latticeOptimalRatio := by
  unfold latticeOptimalRatio
  have : 0 < Real.sqrt 105 := Real.sqrt_pos.mpr (by norm_num)
  positivity

lemma latticeOptimal_crossing :
    latticeExponentSRatio latticeOptimalRatio = latticeOptimalExponent ∧
      jointExponentY latticeOptimalRatio = latticeOptimalExponent := by
  obtain ⟨hs, hp, -⟩ := sqrt105_facts
  constructor
  · unfold latticeExponentSRatio latticeOptimalRatio latticeOptimalExponent
    apply (div_eq_iff (by positivity)).mpr
    linear_combination (612 / 7795 : ℝ) * hs
  · unfold jointExponentY latticeOptimalRatio latticeOptimalExponent
    apply (div_eq_iff (by positivity)).mpr
    linear_combination (212 / 7795 : ℝ) * hs

/-- `γ*` lies above `5/17` and above `4590/15605 = latticeExponentH 102`, and below `153/520`. -/
lemma latticeOptimal_bounds :
    (5 : ℝ) / 17 < latticeOptimalExponent ∧ (4590 : ℝ) / 15605 < latticeOptimalExponent ∧
      latticeOptimalExponent < 153 / 520 := by
  obtain ⟨hs, hp, hlt⟩ := sqrt105_facts
  unfold latticeOptimalExponent
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

lemma latticeExponentSRatio_antitone {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    latticeExponentSRatio s ≤ latticeExponentSRatio r := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  unfold latticeExponentSRatio
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

/-- The positive crossing minimizes the larger of the two exponents. The proofs do not use
this; it records that `γ*` is the best exponent of the method. -/
theorem latticeOptimal_minimum {r : ℝ} (hr : 0 < r) :
    latticeOptimalExponent ≤ max (latticeExponentSRatio r) (jointExponentY r) := by
  rcases le_total r latticeOptimalRatio with h | h
  · rw [← latticeOptimal_crossing.1]
    exact (latticeExponentSRatio_antitone hr h).trans (le_max_left _ _)
  · rw [← latticeOptimal_crossing.2]
    exact (jointExponentY_monotone latticeOptimalRatio_pos h).trans (le_max_right _ _)

/-- Positive rational ratios attain every prescribed loss above the optimum. -/
theorem latticeOptimal_rational_approximation {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℚ, 0 < r ∧
      max (latticeExponentSRatio r) (jointExponentY r) < latticeOptimalExponent + ε := by
  obtain ⟨r, hr, hrε⟩ := exists_rat_btwn
    (show latticeOptimalRatio < latticeOptimalRatio + ε by linarith)
  have hr0 : (0 : ℝ) < r := latticeOptimalRatio_pos.trans hr
  refine ⟨r, by exact_mod_cast hr0, max_lt ?_ ?_⟩
  · have h := latticeExponentSRatio_antitone latticeOptimalRatio_pos hr.le
    rw [latticeOptimal_crossing.1] at h
    linarith
  · have hsub := jointExponentY_sub latticeOptimalRatio_pos hr0
    rw [latticeOptimal_crossing.2] at hsub
    have hd : 42 < (530 * (r : ℝ) + 357) * (530 * latticeOptimalRatio + 357) := by
      nlinarith [latticeOptimalRatio_pos, mul_pos hr0 latticeOptimalRatio_pos]
    have hb : 42 * ((r : ℝ) - latticeOptimalRatio) /
        ((530 * (r : ℝ) + 357) * (530 * latticeOptimalRatio + 357)) < ε := by
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith
    linarith

/-- The window exponents in terms of the ratio `n/m`. -/
lemma lattice_exponents_ratio {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    latticeExponentS (10 * n + 7 * m) m = latticeExponentSRatio ((n : ℝ) / m) ∧
      latticeExponentY (10 * n + 7 * m) n = jointExponentY ((n : ℝ) / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · unfold latticeExponentS latticeExponentSRatio
    push_cast [Nat.cast_sub (show 3 * m ≤ 45 * (10 * n + 7 * m) by omega),
      Nat.cast_sub (show 11 * m ≤ 153 * (10 * n + 7 * m) by omega)]
    rw [div_eq_div_iff (by nlinarith) (by positivity)]
    field_simp
    ring
  · unfold latticeExponentY jointExponentY
    push_cast
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
    ring

/-- The gap exponent is below the optimum once `h ≥ 102`. -/
lemma latticeExponentH_lt {h : ℕ} (hh : 102 ≤ h) :
    latticeExponentH h < latticeOptimalExponent := by
  have hb := latticeOptimal_bounds.2.1
  unfold latticeExponentH
  have hhR : (102 : ℝ) ≤ h := by exact_mod_cast hh
  push_cast [Nat.cast_sub (show 1 ≤ 153 * h by omega)]
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- **The optimized lattice bound** (paper, `thm:lattice`). -/
theorem P_le_lattice_optimal :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ (latticeOptimalExponent + ε) := by
  intro ε hε
  obtain ⟨r, hr, hbound⟩ := latticeOptimal_rational_approximation (by positivity : 0 < ε / 2)
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  -- scaling by `6` keeps `n / m = r` and gives `h = 10n + 7m ≥ 102`
  let m := 6 * r.den
  let n := 6 * r.num.toNat
  have hm : 0 < m := by have := r.pos; omega
  have hn : 0 < n := by omega
  have hratio : (n : ℝ) / m = (r : ℝ) := by
    simp only [n, m]
    push_cast
    rw [mul_div_mul_left _ _ (by norm_num), Rat.cast_def]
    congr 1
    exact_mod_cast Int.toNat_of_nonneg hnum.le
  obtain ⟨hS, hY⟩ := lattice_exponents_ratio hm hn
  have hH := latticeExponentH_lt (h := 10 * n + 7 * m) (by have := r.pos; omega)
  have hbase := latticeOptimal_bounds.1
  have he : latticeJointExponent m n < latticeOptimalExponent + ε / 2 := by
    unfold latticeJointExponent
    rw [hS, hY, hratio]
    refine max_lt (max_lt (by linarith) (by linarith)) hbound
  obtain ⟨C, hC, hP⟩ := P_le_lattice_joint m n hm hn (ε / 2) (by positivity)
  refine ⟨C, hC, fun a b hb hba => ?_⟩
  apply (hP a b hb hba).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ a by omega))
  linarith

end
end PierceLengthBound.FixedDividend
