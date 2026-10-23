/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.LatticeJointWindow
public import PierceLengthBound.LatticeJointLocalEstimate
public import PierceLengthBound.FixedDividendGlobalReduction

/-!
# Length bounds from the exterior lattice coordinates

For fixed positive powers `m, n` with `h = 10n + 7m`, the lattice coordinates give
`P(a, b) ≪ a^{E + ε}` where `E` is the largest of `5/17`, `45h/(153h-1)`,
`(45h-3m)/(153h-11m)` and `(15h+6n)/(51h+20n)` (`P_le_lattice_joint`). The choice `m = 3`,
`n = 2` gives `153/520` (`P_le_153_520`).

These theorems use the short-vector count `short_count` through the fractional lattice weights.
They are separate from `P_le_joint_optimal`, whose dependency audit excludes those counts.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- The largest window exponent of the lattice coordinates. -/
def latticeJointExponent (m n : ℕ) : ℝ :=
  max (max ((5 : ℝ) / 17) (latticeExponentH (10 * n + 7 * m)))
    (max (latticeExponentS (10 * n + 7 * m) m) (latticeExponentY (10 * n + 7 * m) n))

/-- Every fixed pair of positive powers gives its lattice exponent (paper,
`cor:latticeexponent`). -/
theorem P_le_lattice_joint (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ (latticeJointExponent m n + ε) := by
  obtain ⟨R, hR, hcount⟩ := latticeJointFiveTermEstimate_exists m n hm hn
  let h := 10 * n + 7 * m
  let K := fun a => (5 * (R a + 1)) ^ (3 * h)
  let C₀ := latticeJointWindowBase m n
  let q := latticeJointWindowDeltaExponent m n
  let S := fun a => C₀ * (K a + 1) * tauMax (32 * a ^ 7) ^ q
  have hK : SlowGrowth K := ((slowGrowth_const 5).mul (slowGrowth_add_one hR)).pow (3 * h)
  have hS : SlowGrowth S := ((slowGrowth_const C₀).mul (slowGrowth_add_one hK)).mul
    ((tauMax_slow 32 7).pow q)
  have hα : (5 : ℝ) / 17 ≤ latticeJointExponent m n := (le_max_left _ _).trans (le_max_left _ _)
  apply P_le_of_real_visits hS (by linarith : 0 ≤ latticeJointExponent m n)
  intro a b k _hb hba
  refine or_iff_not_imp_left.mpr fun hT => ?_
  obtain ⟨s, W, hsT⟩ := visits_run (k := k) hba.le (by omega)
  apply window_real_of_lattice_joint_count (K := K a) hm hα
    ((le_max_right _ _).trans (le_max_left _ _))
    ((le_max_left _ _).trans (le_max_right _ _))
    ((le_max_right _ _).trans (le_max_right _ _)) (by omega)
    (six_step_bound W (by omega)) (drop_bound W (tauMax_divBound a) (by omega))
  dsimp only
  intro hscale
  apply lattice_joint_branches_of_five_term_count (R := R a) hm
  simpa only [LatticeJointFiveTermEstimate, selectedGapHeight, selectedMinorHeight,
    selectedAllMinorHeight, selectedRankFiveHeight] using
    hcount a b s _ (2 ^ k) hba W.mem hsT (by omega) hscale

/-- The explicit rational choice `m = 3`, `n = 2`. -/
theorem P_le_153_520 :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((153 : ℝ) / 520 + ε) := by
  have he : latticeJointExponent 3 2 = 153 / 520 := by
    simp only [latticeJointExponent, latticeExponentH, latticeExponentS, latticeExponentY]
    norm_num
  simpa only [he] using P_le_lattice_joint 3 2 (by decide) (by decide)

end
end PierceLengthBound.FixedDividend
