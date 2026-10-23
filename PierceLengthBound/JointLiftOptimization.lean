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

def jointExponentS (r : ℝ) : ℝ := (150 * r + 106) / (510 * r + 360)
def jointExponentY (r : ℝ) : ℝ := (156 * r + 105) / (530 * r + 357)
def jointOptimalRatio : ℝ := (5 + Real.sqrt 655) / 30
def jointOptimalExponent : ℝ := (1310 - Real.sqrt 655) / 4365

lemma jointOptimalRatio_pos : 0 < jointOptimalRatio := by
  unfold jointOptimalRatio
  positivity

lemma jointOptimalRatio_equation :
    30 * jointOptimalRatio ^ 2 - 10 * jointOptimalRatio - 21 = 0 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 655 by norm_num)
  unfold jointOptimalRatio
  nlinarith

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

lemma jointExponentY_sub {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    jointExponentY s - jointExponentY r =
      42 * (s - r) / ((530 * s + 357) * (530 * r + 357)) := by
  unfold jointExponentY
  field_simp
  ring

/-- Positive rational ratios attain every prescribed loss above the optimum. -/
theorem jointOptimal_rational_approximation {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℚ, 0 < r ∧
      max (jointExponentS r) (jointExponentY r) < jointOptimalExponent + ε := by
  obtain ⟨r, hr, hrε⟩ :=
    exists_rat_btwn (show jointOptimalRatio < jointOptimalRatio + ε by linarith)
  have hr0 : (0 : ℝ) < r := jointOptimalRatio_pos.trans hr
  refine ⟨r, by exact_mod_cast hr0, max_lt ?_ ?_⟩
  · have h := jointExponentS_antitone jointOptimalRatio_pos hr.le
    rw [jointOptimal_crossing.1] at h
    linarith
  · have hsub := jointExponentY_sub jointOptimalRatio_pos hr0
    rw [jointOptimal_crossing.2] at hsub
    have hd : 42 < (530 * (r : ℝ) + 357) * (530 * jointOptimalRatio + 357) := by
      nlinarith [jointOptimalRatio_pos, mul_pos hr0 jointOptimalRatio_pos]
    have hb : 42 * ((r : ℝ) - jointOptimalRatio) /
        ((530 * (r : ℝ) + 357) * (530 * jointOptimalRatio + 357)) < ε := by
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith
    linarith

lemma joint_powered_rational_example :
    10 * (51 : ℕ) + 7 * 50 = 860 ∧
      jointExponentS ((51 : ℝ) / 50) = 1295 / 4401 ∧
      jointExponentY ((51 : ℝ) / 50) = 2201 / 7480 ∧
      max (jointExponentS ((51 : ℝ) / 50)) (jointExponentY ((51 : ℝ) / 50)) = 2201 / 7480 := by
  norm_num [jointExponentS, jointExponentY]

lemma jointOptimal_comparison :
    (5 : ℝ) / 17 < jointOptimalExponent ∧ jointOptimalExponent < 2201 / 7480 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 655 by norm_num)
  have hp := Real.sqrt_nonneg (655 : ℝ)
  unfold jointOptimalExponent
  constructor <;> nlinarith


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
  have hn : 0 < r.num := Rat.num_pos.mpr hr
  have hnNat : 0 < r.num.toNat := by omega
  refine ⟨r.den, r.num.toNat, r.pos, hnNat, ?_⟩
  have he : (r.num.toNat : ℝ) / (r.den : ℝ) = (r : ℝ) := by
    rw [Rat.cast_def]
    congr 1
    exact_mod_cast Int.toNat_of_nonneg hn.le
  have hmR : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hnR : (0 : ℝ) < r.num.toNat := by exact_mod_cast hnNat
  rw [(joint_powered_exponents hmR hnR).1, (joint_powered_exponents hmR hnR).2, he]
  exact hbound

end
end PierceLengthBound.FixedDividend
