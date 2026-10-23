/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftExponent
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Instances.Rat

/-! Exact optimization of the two powered-coordinate exponents.
These results optimize the proposed local count; they do not prove that count. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-! ### Optimizing the larger of two exponents -/

/-- A ratio `(a r + b)/(c r + d)` is continuous where its denominator is nonzero. -/
lemma continuousAt_ratio {a b c d r : ℝ} (h : c * r + d ≠ 0) :
    ContinuousAt (fun r => (a * r + b) / (c * r + d)) r :=
  ((continuousAt_id.const_mul a).add continuousAt_const).div
    ((continuousAt_id.const_mul c).add continuousAt_const) h

/-- **Rational approximation of a crossing.** If `f` is antitone to the right of `r₀ > 0`, `g`
is continuous at `r₀` and `f r₀ = g r₀ = α`, then positive rationals `r` bring
`max (f r) (g r)` arbitrarily close to `α`. -/
theorem exists_rat_max_lt_of_crossing {f g : ℝ → ℝ} {r₀ α ε : ℝ} (hr₀ : 0 < r₀)
    (hf : ∀ s, r₀ ≤ s → f s ≤ f r₀) (hg : ContinuousAt g r₀) (hfα : f r₀ = α)
    (hgα : g r₀ = α) (hε : 0 < ε) : ∃ r : ℚ, 0 < r ∧ max (f r) (g r) < α + ε := by
  obtain ⟨δ, hδ, hgδ⟩ := Metric.continuousAt_iff.mp hg ε hε
  obtain ⟨r, hr, hrδ⟩ := exists_rat_btwn (show r₀ < r₀ + δ by linarith)
  refine ⟨r, by exact_mod_cast hr₀.trans hr, max_lt (by linarith [hf r hr.le]) ?_⟩
  have := hgδ (show dist (r : ℝ) r₀ < δ by rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith)
  rw [Real.dist_eq, hgα] at this
  linarith [le_abs_self (g r - α)]

/-- A positive rational `r` is `n / m` for the positive integers `m = c · den r` and
`n = c · num r`, for every `c > 0`. -/
lemma rat_eq_div_scaled {r : ℚ} (hr : 0 < r) {c : ℕ} (hc : 0 < c) :
    0 < c * r.den ∧ 0 < c * r.num.toNat ∧
      ((c * r.num.toNat : ℕ) : ℝ) / ((c * r.den : ℕ) : ℝ) = r := by
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  refine ⟨Nat.mul_pos hc r.pos, Nat.mul_pos hc (by omega), ?_⟩
  push_cast
  rw [mul_div_mul_left _ _ (by exact_mod_cast hc.ne'), Rat.cast_def]
  congr 1
  exact_mod_cast Int.toNat_of_nonneg hnum.le

/-! ### The powered joint exponents -/

def jointExponentS (r : ℝ) : ℝ := (150 * r + 106) / (510 * r + 360)
def jointExponentY (r : ℝ) : ℝ := (156 * r + 105) / (530 * r + 357)
def jointOptimalRatio : ℝ := (5 + Real.sqrt 655) / 30
def jointOptimalExponent : ℝ := (1310 - Real.sqrt 655) / 4365

lemma jointOptimalRatio_pos : 0 < jointOptimalRatio := by
  unfold jointOptimalRatio
  positivity

lemma jointOptimal_crossing :
    jointExponentS jointOptimalRatio = jointOptimalExponent ∧
      jointExponentY jointOptimalRatio = jointOptimalExponent := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 655 by norm_num)
  have hp := Real.sqrt_nonneg (655 : ℝ)
  constructor
  · unfold jointExponentS jointOptimalRatio jointOptimalExponent
    apply (div_eq_iff (by positivity)).mpr
    nlinarith
  · unfold jointExponentY jointOptimalRatio jointOptimalExponent
    apply (div_eq_iff (by positivity)).mpr
    nlinarith

lemma jointExponentS_antitone {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    jointExponentS s ≤ jointExponentS r := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  unfold jointExponentS
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

lemma jointExponentY_monotone {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    jointExponentY r ≤ jointExponentY s := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  unfold jointExponentY
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

/-- The positive crossing minimizes the maximum of the two exponents. -/
theorem jointOptimal_minimum {r : ℝ} (hr : 0 < r) :
    jointOptimalExponent ≤ max (jointExponentS r) (jointExponentY r) := by
  rcases le_total r jointOptimalRatio with h | h
  · rw [← jointOptimal_crossing.1]
    exact (jointExponentS_antitone hr h).trans (le_max_left _ _)
  · rw [← jointOptimal_crossing.2]
    exact (jointExponentY_monotone jointOptimalRatio_pos h).trans (le_max_right _ _)

/-- Positive rational ratios attain every prescribed loss above the optimum. -/
theorem jointOptimal_rational_approximation {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℚ, 0 < r ∧
      max (jointExponentS r) (jointExponentY r) < jointOptimalExponent + ε :=
  exists_rat_max_lt_of_crossing jointOptimalRatio_pos
    (fun _ h => jointExponentS_antitone jointOptimalRatio_pos h)
    (continuousAt_ratio (ne_of_gt (by linarith [jointOptimalRatio_pos]))) jointOptimal_crossing.1
    jointOptimal_crossing.2 hε

/-- The claimed powered degree inequality gives 10n+7m on every component d>=4. -/
lemma joint_powered_degree_minimum {d m n δ : ℕ} (hd : 4 ≤ d)
    (hdegree : (5 * n + 3 * m) * d + 2 * m ≤ 2 * δ) : 10 * n + 7 * m ≤ δ := by
  have h := Nat.mul_le_mul_left (5 * n + 3 * m) hd
  nlinarith

lemma joint_powered_exponents {m n : ℝ} (hm : 0 < m) (hn : 0 < n) :
    (15 * (10 * n + 7 * m) + m) / (51 * (10 * n + 7 * m) + 3 * m) =
        jointExponentS (n / m) ∧
      (15 * (10 * n + 7 * m) + 6 * n) / (51 * (10 * n + 7 * m) + 20 * n) =
        jointExponentY (n / m) := by
  constructor <;> dsimp [jointExponentS, jointExponentY] <;> field_simp <;> ring

/-- The powers can be fixed positive integers depending only on the desired loss. -/
theorem jointOptimal_integer_powers {ε : ℝ} (hε : 0 < ε) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
      max ((15 * (10 * (n : ℝ) + 7 * m) + m) / (51 * (10 * n + 7 * m) + 3 * m))
        ((15 * (10 * (n : ℝ) + 7 * m) + 6 * n) / (51 * (10 * n + 7 * m) + 20 * n)) <
          jointOptimalExponent + ε := by
  obtain ⟨r, hr, hbound⟩ := jointOptimal_rational_approximation hε
  obtain ⟨hm, hn, he⟩ := rat_eq_div_scaled hr one_pos
  refine ⟨1 * r.den, 1 * r.num.toNat, hm, hn, ?_⟩
  have hmR : (0 : ℝ) < (1 * r.den : ℕ) := by exact_mod_cast hm
  have hnR : (0 : ℝ) < (1 * r.num.toNat : ℕ) := by exact_mod_cast hn
  rw [(joint_powered_exponents hmR hnR).1, (joint_powered_exponents hmR hnR).2, he]
  exact hbound

end
end PierceLengthBound.FixedDividend
