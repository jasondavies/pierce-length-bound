/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionLocalEstimate
public import PierceLengthBound.PolarProjectionOptimization

/-! Global consequences of the local polar estimate. This module keeps the six-term estimate
as an explicit input. `PolarProjectionMain` supplies its proof from the degree-24 branch sieve,
the actual common-base bound and the exceptional-pattern counts. -/

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
  let S := fun a => C₀ * (K a + 1) * tauMax (32 * a ^ 7) ^ q
  have hK : SlowGrowth K := ((slowGrowth_const 10).mul (slowGrowth_add_one hR)).pow (3 * h + 51)
  have hS : SlowGrowth S := ((slowGrowth_const C₀).mul (slowGrowth_add_one hK)).mul
    ((tauMax_slow 32 7).pow q)
  have hα : (5 : ℝ) / 17 ≤ polarProjectionExponent m n := (le_max_left _ _).trans (le_max_left _ _)
  apply P_le_of_real_visits hS (by linarith : 0 ≤ polarProjectionExponent m n)
  intro a b k _hb hba
  by_cases hT : (visits a b k).card ≤ 35
  · exact Or.inl hT
  right
  set T := (visits a b k).card
  have hne : (visits a b k).Nonempty := by rw [← Finset.card_pos]; omega
  have W := visits_window hba.le hne
  set s := (visits a b k).min' hne
  have hmem : ∀ j < T, 2 ^ k ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * 2 ^ k := W.mem
  have hsT : s + T ≤ P a b := by
    have h := (hmem (T - 1) (by omega)).1
    have := lt_P_of_orb_pos (a := a) (b := b) (i := s + (T - 1))
      (lt_of_lt_of_le (Nat.two_pow_pos k) h)
    omega
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
    hcount a b s T (2 ^ k) hba hmem hsT (by omega) hscale

/-- The explicit rational polar exponent, conditional on its local counting estimate. -/
theorem P_le_4317_14677_of_six_term_count {R : ℕ → ℕ} (hR : SlowGrowth R)
    (hcount : PolarProjectionSixTermEstimate 3 2 R) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((4317 : ℝ) / 14677 + ε) := by
  simpa only [polarProjection_rational_example.2.2.2.2] using
    P_le_polar_projection_of_six_term_count 3 2 (by decide) hR hcount

/-- Optimization over fixed powers, with each required local estimate explicit. -/
theorem P_le_polar_optimal_of_six_term_estimates
    (hcounts : ∀ m n : ℕ, 0 < m → 0 < n →
      ∃ R : ℕ → ℕ, SlowGrowth R ∧ PolarProjectionSixTermEstimate m n R) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ (polarProjectionOptimalExponent + ε) := by
  intro ε hε
  obtain ⟨m, n, hm, hn, he⟩ := polarProjectionOptimal_integer_powers
    (by positivity : 0 < ε / 2)
  obtain ⟨R, hR, hc⟩ := hcounts m n hm hn
  obtain ⟨C, hC, hP⟩ := P_le_polar_projection_of_six_term_count m n hm hR hc
    (ε / 2) (by positivity)
  refine ⟨C, hC, fun a b hb hba => ?_⟩
  apply (hP a b hb hba).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ a by omega))
  linarith

end
end PierceLengthBound.FixedDividend
