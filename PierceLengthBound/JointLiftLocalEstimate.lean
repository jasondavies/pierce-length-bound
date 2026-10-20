/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftGlobalReduction

/-! Convert the candidate's displayed three-term real estimate into the integer
local hypothesis, retaining every slack factor explicitly. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend

set_option maxHeartbeats 1000000 in
-- The three-term real inequality requires normalization of the nested maximum.
/-- The displayed joint-coordinate estimate implies the three integer-power branches. -/
theorem joint_lift_branches_of_three_term_count {T H X S Y R : ℕ}
    (hcount : (T : ℝ) ≤ R * ((X : ℝ) ^ 5 + (X : ℝ) ^ 4 * (H : ℝ) ^ (1 / 2 : ℝ) +
      (X : ℝ) ^ (5 : ℕ) * (max (max H S) Y : ℝ) ^ (1 / 17 : ℝ))) :
    JointLiftCountBranches ((3 * (R + 1)) ^ 17) T H X S Y := by
  let D := 3 * (R + 1)
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hD1 : D ≤ D ^ 17 := by
    simpa using Nat.pow_le_pow_right hD (by norm_num : 1 ≤ 17)
  have hD2 : D ^ 2 ≤ D ^ 17 := Nat.pow_le_pow_right hD (by norm_num)
  have hcase : (T : ℝ) ≤ D * (X : ℝ) ^ 5 ∨
      (T : ℝ) ≤ D * ((X : ℝ) ^ 4 * (H : ℝ) ^ (1 / 2 : ℝ)) ∨
      (T : ℝ) ≤ D * ((X : ℝ) ^ (5 : ℕ) * (max (max H S) Y : ℝ) ^ (1 / 17 : ℝ)) := by
    by_contra h
    push Not at h
    have h1 : 0 ≤ (X : ℝ) ^ 5 := by positivity
    have h2 : 0 ≤ (X : ℝ) ^ 4 * (H : ℝ) ^ (1 / 2 : ℝ) := by positivity
    have h3 : 0 ≤ (X : ℝ) ^ (5 : ℕ) * (max (max H S) Y : ℝ) ^ (1 / 17 : ℝ) := by positivity
    dsimp [D] at h
    push_cast at h
    nlinarith only [hcount, h.1, h.2.1, h.2.2, h1, h2, h3]
  change JointLiftCountBranches (D ^ 17) T H X S Y
  rcases hcase with h | h | h
  · left
    have hn : T ≤ D * X ^ 5 := by exact_mod_cast h
    exact hn.trans (Nat.mul_le_mul_right _ hD1)
  · right; left
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg T) h 2
    have hs : ((H : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = H := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    have hn : T ^ 2 ≤ D ^ 2 * H * X ^ 8 := by
      have he : (T : ℝ) ^ 2 ≤ (D : ℝ) ^ 2 * H * (X : ℝ) ^ 8 := by
        simpa only [mul_pow, hs, ← pow_mul, mul_assoc, mul_left_comm, mul_comm,
          Nat.reduceMul] using hp
      exact_mod_cast he
    exact hn.trans (by gcongr)
  · right; right
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg T) h 17
    have hs : ((max (max H S) Y : ℝ) ^ (1 / 17 : ℝ)) ^ 17 = max (max H S) Y := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num [max_assoc]
    have he : (T : ℝ) ^ 17 ≤ (D : ℝ) ^ 17 * (X : ℝ) ^ 85 * max (max H S) Y := by
      simpa only [mul_pow, hs, ← pow_mul, Nat.reduceMul, mul_assoc] using hp
    exact_mod_cast he

/-- The candidate's three-term local estimate on actual remainder windows. -/
def JointLiftThreeTermEstimate (R : ℕ → ℕ) : Prop :=
  ∀ a b s T A : ℕ, b < a →
    (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
    s + T ≤ P a b → 36 ≤ T →
    124928 * A ^ 4 * selectedGapHeight a A T ^ 5 * selectedMinorHeight a A T < a ^ 3 →
    let H : ℝ := selectedGapHeight a A T
    let X : ℝ := selectedMinorHeight a A T
    let S : ℝ := selectedCurvatureHeight a A T
    let Y : ℝ := selectedRankFiveHeight a A T
    (T : ℝ) ≤ R a * (X ^ 5 + X ^ 4 * H ^ (1 / 2 : ℝ) + X ^ 5 * (max (max H S) Y) ^ (1 / 17 : ℝ))

/-- Direct conditional conclusion from the estimate displayed in the new candidate. -/
theorem P_le_128_435_of_three_term_estimate {R : ℕ → ℕ} (hR : SlowGrowth R)
    (hlocal : JointLiftThreeTermEstimate R) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((128 : ℝ) / 435 + ε) := by
  have hc : SlowGrowth (fun _ : ℕ => 3) := by
    intro η hη
    refine ⟨3, by norm_num, fun a ha => ?_⟩
    have hp := Real.one_le_rpow (by exact_mod_cast ha : (1 : ℝ) ≤ a) hη.le
    norm_num
    linarith
  apply P_le_128_435_of_joint_lift_count ((hc.mul (slowGrowth_add_one hR)).pow 17)
  intro a b s T A hba hmem hsT hT hscale
  apply joint_lift_branches_of_three_term_count
  simpa only [Nat.cast_max] using hlocal a b s T A hba hmem hsT hT hscale

end PierceLengthBound.FixedDividend
