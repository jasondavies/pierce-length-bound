/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionLocalEstimate
public import PierceLengthBound.PolarProjectionOptimization
public import PierceLengthBound.FixedDividendGlobalReduction

/-! Global consequences of the local polar estimate. The six-term estimate
`PolarProjectionSixTermEstimate` is a hypothesis here; `PolarProjectionMain`
proves it from the degree-twelve branch sieve, the common-base bound and the
exceptional-pattern counts. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- The complete dyadic-window reduction from the six-term local estimate. -/
theorem P_le_polar_projection_of_six_term_count (m n : ℕ) (hm : 0 < m)
    {R : ℕ → ℕ} (hR : SlowGrowth R) (hcount : PolarProjectionSixTermEstimate m n R) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ (polarProjectionExponent m n + ε) := by
  let h := polarProjectionGraphDegree m n
  let K := fun a => polarProjectionCountSlack (R a) m n
  let C₀ := polarProjectionWindowBase m n
  let q := polarProjectionWindowDeltaExponent m n
  let S := fun a => C₀ * (K a + 1) * tauMax (2 * a) ^ q
  have hK : SlowGrowth K := ((slowGrowth_const 10).mul (slowGrowth_add_one hR)).pow (3 * h + 51)
  have hS : SlowGrowth S := ((slowGrowth_const C₀).mul (slowGrowth_add_one hK)).mul
    (tauMax_two_mul_slow.pow q)
  have hα : (5 : ℝ) / 17 ≤ polarProjectionExponent m n := (le_max_left _ _).trans (le_max_left _ _)
  apply P_le_of_real_visits hS (by linarith : 0 ≤ polarProjectionExponent m n)
  intro a b k _hb hba
  refine or_iff_not_imp_left.mpr fun hT => ?_
  obtain ⟨s, W, hsT⟩ := visits_run (k := k) hba.le (by omega)
  apply window_real_of_polar_projection_count (K := K a) hm hα
    ((le_max_right _ _).trans (le_max_left _ _))
    ((le_max_left _ _).trans (le_max_right _ _))
    ((le_max_right _ _).trans (le_max_right _ _)) (by omega)
    (six_step_bound W (by omega)) (drop_bound W (tauMax_divBound a) (by omega))
  dsimp only
  intro hscale
  apply polar_projection_branches_of_six_term_count (R := R a) hm
  simpa only [PolarProjectionSixTermEstimate, selectedGapHeight, selectedMinorHeight,
    selectedAllMinorHeight, selectedRankFiveHeight] using
    hcount a b s _ (2 ^ k) hba W.mem hsT (by omega) hscale

/-- The rational polar exponent `4317/14677` (powers `m = 3`, `n = 2`), from the
six-term estimate for these powers. -/
theorem P_le_4317_14677_of_six_term_count {R : ℕ → ℕ} (hR : SlowGrowth R)
    (hcount : PolarProjectionSixTermEstimate 3 2 R) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((4317 : ℝ) / 14677 + ε) := by
  simpa only [polarProjection_rational_example.2.2.2.2] using
    P_le_polar_projection_of_six_term_count 3 2 (by decide) hR hcount

/-- The optimized polar exponent, from the six-term estimates for all positive
powers `m`, `n`. -/
theorem P_le_polar_optimal_of_six_term_estimates
    (hcounts : ∀ m n : ℕ, 0 < m → 0 < n →
      ∃ R : ℕ → ℕ, SlowGrowth R ∧ PolarProjectionSixTermEstimate m n R) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ (polarProjectionOptimalExponent + ε) := by
  intro ε hε
  obtain ⟨m, n, hm, hn, he⟩ := polarProjectionOptimal_integer_powers
    (by positivity : 0 < ε / 2)
  obtain ⟨R, hR, hc⟩ := hcounts m n hm hn
  exact P_le_of_exponent_le (by linarith)
    (P_le_polar_projection_of_six_term_count m n hm hR hc (ε / 2) (by positivity))

end
end PierceLengthBound.FixedDividend
