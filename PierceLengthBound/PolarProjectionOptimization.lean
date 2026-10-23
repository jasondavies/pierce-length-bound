/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionExponent
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Instances.Rat

/-!
# Optimizing the polar-projection exponents

The two powered-coordinate exponents cross at
`r = (√82849 - 47)/360`. Their minimum maximum is
`α = (41301 - 3√82849)/137480`. Positive integer coordinate powers achieve every prescribed
loss above `α`; doubling a positive rational numerator and denominator also makes the gap
exponent smaller than `α`.

This file isolates the exponent optimization. `PolarProjectionMain` supplies the counting
and geometric inputs and proves the resulting length bounds for Pierce orbits.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

def polarProjectionExponentSRatio (r : ℝ) : ℝ := (2700 * r + 2517) / (9180 * r + 8557)
def polarProjectionExponentYRatio (r : ℝ) : ℝ := (906 * r + 840) / (3080 * r + 2856)
def polarProjectionOptimalRatio : ℝ := (Real.sqrt 82849 - 47) / 360
def polarProjectionOptimalExponent : ℝ := (41301 - 3 * Real.sqrt 82849) / 137480

lemma sqrt82849_facts :
    Real.sqrt 82849 ^ 2 = 82849 ∧ 287 < Real.sqrt 82849 ∧ Real.sqrt 82849 < 288 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 82849 by norm_num)
  have hp := Real.sqrt_nonneg (82849 : ℝ)
  exact ⟨hs, by nlinarith, by nlinarith⟩

lemma polarProjectionOptimalRatio_pos : 0 < polarProjectionOptimalRatio := by
  have := sqrt82849_facts.2.1
  unfold polarProjectionOptimalRatio
  linarith

lemma polarProjectionOptimalRatio_equation :
    180 * polarProjectionOptimalRatio ^ 2 + 47 * polarProjectionOptimalRatio - 112 = 0 := by
  have hs := sqrt82849_facts.1
  unfold polarProjectionOptimalRatio
  nlinarith

lemma polarProjectionOptimal_crossing :
    polarProjectionExponentSRatio polarProjectionOptimalRatio = polarProjectionOptimalExponent ∧
      polarProjectionExponentYRatio polarProjectionOptimalRatio =
        polarProjectionOptimalExponent := by
  have hr := polarProjectionOptimalRatio_pos
  have hs := sqrt82849_facts.1
  constructor
  · unfold polarProjectionExponentSRatio
    apply (div_eq_iff (by positivity)).mpr
    unfold polarProjectionOptimalRatio polarProjectionOptimalExponent
    linear_combination (153 / 274960 : ℝ) * hs
  · unfold polarProjectionExponentYRatio
    apply (div_eq_iff (by positivity)).mpr
    unfold polarProjectionOptimalRatio polarProjectionOptimalExponent
    linear_combination (11 / 58920 : ℝ) * hs

lemma polarProjectionOptimalExponent_equation :
    68740 * polarProjectionOptimalExponent ^ 2 -
      41301 * polarProjectionOptimalExponent + 6201 = 0 := by
  have hs := sqrt82849_facts.1
  unfold polarProjectionOptimalExponent
  nlinarith

/-- The optimized exponent is above the method's threshold, below the explicit rational
choice, and above the gap exponent at degree 232. -/
lemma polarProjectionOptimal_bounds :
    (5 : ℝ) / 17 < polarProjectionOptimalExponent ∧
      (10440 : ℝ) / 35495 < polarProjectionOptimalExponent ∧
      polarProjectionOptimalExponent < 4317 / 14677 := by
  obtain ⟨hs, hlo, hhi⟩ := sqrt82849_facts
  unfold polarProjectionOptimalExponent
  exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

lemma polarProjectionExponentSRatio_antitone {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    polarProjectionExponentSRatio s ≤ polarProjectionExponentSRatio r := by
  have hs : 0 < s := hr.trans_le hrs
  unfold polarProjectionExponentSRatio
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

lemma polarProjectionExponentYRatio_monotone {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    polarProjectionExponentYRatio r ≤ polarProjectionExponentYRatio s := by
  have hs : 0 < s := hr.trans_le hrs
  unfold polarProjectionExponentYRatio
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

/-- The positive crossing minimizes the larger of the two powered-coordinate exponents. -/
theorem polarProjectionOptimal_minimum {r : ℝ} (hr : 0 < r) :
    polarProjectionOptimalExponent ≤
      max (polarProjectionExponentSRatio r) (polarProjectionExponentYRatio r) := by
  rcases le_total r polarProjectionOptimalRatio with h | h
  · rw [← polarProjectionOptimal_crossing.1]
    exact (polarProjectionExponentSRatio_antitone hr h).trans (le_max_left _ _)
  · rw [← polarProjectionOptimal_crossing.2]
    exact (polarProjectionExponentYRatio_monotone polarProjectionOptimalRatio_pos h).trans
      (le_max_right _ _)

lemma polarProjectionExponentYRatio_sub {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    polarProjectionExponentYRatio s - polarProjectionExponentYRatio r =
      336 * (s - r) / ((3080 * s + 2856) * (3080 * r + 2856)) := by
  unfold polarProjectionExponentYRatio
  field_simp
  ring

/-- A positive rational ratio achieves every prescribed positive loss above the optimum. -/
theorem polarProjectionOptimal_rational_approximation {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℚ, 0 < r ∧
      max (polarProjectionExponentSRatio r) (polarProjectionExponentYRatio r) <
        polarProjectionOptimalExponent + ε := by
  obtain ⟨r, hr, hrε⟩ := exists_rat_btwn
    (show polarProjectionOptimalRatio < polarProjectionOptimalRatio + ε by linarith)
  have hr0 : (0 : ℝ) < r := polarProjectionOptimalRatio_pos.trans hr
  refine ⟨r, by exact_mod_cast hr0, max_lt ?_ ?_⟩
  · have h := polarProjectionExponentSRatio_antitone polarProjectionOptimalRatio_pos hr.le
    rw [polarProjectionOptimal_crossing.1] at h
    linarith
  · have hsub := polarProjectionExponentYRatio_sub polarProjectionOptimalRatio_pos hr0
    rw [polarProjectionOptimal_crossing.2] at hsub
    have hd : 336 < (3080 * (r : ℝ) + 2856) * (3080 * polarProjectionOptimalRatio + 2856) := by
      nlinarith [polarProjectionOptimalRatio_pos, mul_pos hr0 polarProjectionOptimalRatio_pos]
    have hb : 336 * ((r : ℝ) - polarProjectionOptimalRatio) /
        ((3080 * (r : ℝ) + 2856) * (3080 * polarProjectionOptimalRatio + 2856)) < ε := by
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith
    linarith

/-- The window exponents reduce to the ratio formulas at degree
`60n + 56m`. -/
lemma polarProjection_exponents_ratio {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    latticeExponentS (polarProjectionGraphDegree m n) m =
        polarProjectionExponentSRatio ((n : ℝ) / m) ∧
      latticeExponentY (polarProjectionGraphDegree m n) n =
        polarProjectionExponentYRatio ((n : ℝ) / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · unfold latticeExponentS polarProjectionExponentSRatio polarProjectionGraphDegree
    push_cast [Nat.cast_sub (show 3 * m ≤ 45 * (60 * n + 56 * m) by omega),
      Nat.cast_sub (show 11 * m ≤ 153 * (60 * n + 56 * m) by omega)]
    rw [div_eq_div_iff (by nlinarith) (by positivity)]
    field_simp
    ring
  · unfold latticeExponentY polarProjectionExponentYRatio polarProjectionGraphDegree
    push_cast
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
    ring

/-- Scaling both coordinate powers makes the gap exponent harmless. -/
lemma polarProjection_gap_exponent_lt {h : ℕ} (hh : 232 ≤ h) :
    latticeExponentH h < polarProjectionOptimalExponent := by
  have hb := polarProjectionOptimal_bounds.2.1
  have hbase := polarProjectionOptimal_bounds.1
  have hhR : (232 : ℝ) ≤ h := by exact_mod_cast hh
  unfold latticeExponentH
  push_cast [Nat.cast_sub (show 1 ≤ 153 * h by omega)]
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- Fixed positive integer coordinate powers achieve every prescribed loss above the
optimized exponent. -/
theorem polarProjectionOptimal_integer_powers {ε : ℝ} (hε : 0 < ε) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
      polarProjectionExponent m n < polarProjectionOptimalExponent + ε := by
  obtain ⟨r, hr, hbound⟩ := polarProjectionOptimal_rational_approximation hε
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  let m := 2 * r.den
  let n := 2 * r.num.toNat
  have hm : 0 < m := by have := r.pos; omega
  have hn : 0 < n := by omega
  refine ⟨m, n, hm, hn, ?_⟩
  have hratio : (n : ℝ) / m = (r : ℝ) := by
    simp only [n, m]
    push_cast
    rw [mul_div_mul_left _ _ (by norm_num), Rat.cast_def]
    congr 1
    exact_mod_cast Int.toNat_of_nonneg hnum.le
  obtain ⟨hS, hY⟩ := polarProjection_exponents_ratio hm hn
  have hH := polarProjection_gap_exponent_lt (h := polarProjectionGraphDegree m n)
    (by unfold polarProjectionGraphDegree; have := r.pos; omega)
  have hbase := polarProjectionOptimal_bounds.1
  unfold polarProjectionExponent
  rw [hS, hY, hratio]
  exact max_lt (max_lt (by linarith) (by linarith)) hbound

end
end PierceLengthBound.FixedDividend
