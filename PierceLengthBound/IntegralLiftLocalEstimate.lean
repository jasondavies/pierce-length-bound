/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftGlobalReduction

/-! Convert the candidate's displayed three-term real estimate into the integer
local hypothesis, retaining every slack factor explicitly. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend

/-- The displayed integral-coordinate estimate implies the three integer-power branches. -/
theorem integral_lift_branches_of_three_term_count {T H X S R : ℕ}
    (hcount : (T : ℝ) ≤ R * ((X : ℝ) ^ 5 + (X : ℝ) ^ 4 * (H : ℝ) ^ (1 / 2 : ℝ) +
      (X : ℝ) ^ (5 : ℕ) * (max H S : ℝ) ^ (1 / 10 : ℝ))) :
    IntegralLiftCountBranches ((3 * (R + 1)) ^ 10) T H X S := by
  let D := 3 * (R + 1)
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hD1 : D ≤ D ^ 10 := by
    simpa using Nat.pow_le_pow_right hD (by norm_num : 1 ≤ 10)
  have hD2 : D ^ 2 ≤ D ^ 10 := Nat.pow_le_pow_right hD (by norm_num)
  have hcase : (T : ℝ) ≤ D * (X : ℝ) ^ 5 ∨
      (T : ℝ) ≤ D * ((X : ℝ) ^ 4 * (H : ℝ) ^ (1 / 2 : ℝ)) ∨
      (T : ℝ) ≤ D * ((X : ℝ) ^ (5 : ℕ) * (max H S : ℝ) ^ (1 / 10 : ℝ)) := by
    by_contra h
    push Not at h
    have h1 : 0 ≤ (X : ℝ) ^ 5 := by positivity
    have h2 : 0 ≤ (X : ℝ) ^ 4 * (H : ℝ) ^ (1 / 2 : ℝ) := by positivity
    have h3 : 0 ≤ (X : ℝ) ^ (5 : ℕ) * (max H S : ℝ) ^ (1 / 10 : ℝ) := by positivity
    dsimp [D] at h
    push_cast at h
    nlinarith
  change IntegralLiftCountBranches (D ^ 10) T H X S
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
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg T) h 10
    have hs : ((max H S : ℝ) ^ (1 / 10 : ℝ)) ^ 10 = max H S := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    have he : (T : ℝ) ^ 10 ≤ (D : ℝ) ^ 10 * (X : ℝ) ^ 50 * max H S := by
      simpa only [mul_pow, hs, ← pow_mul, Nat.reduceMul, mul_assoc] using hp
    exact_mod_cast he

/-- The candidate's three-term local estimate on actual remainder windows. -/
def IntegralLiftThreeTermEstimate (R : ℕ → ℕ) : Prop :=
  ∀ a b s T A : ℕ, b < a →
    (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
    s + T ≤ P a b → 36 ≤ T →
    124928 * A ^ 4 * selectedGapHeight a A T ^ 5 * selectedMinorHeight a A T < a ^ 3 →
    let H : ℝ := selectedGapHeight a A T
    let X : ℝ := selectedMinorHeight a A T
    let S : ℝ := selectedLiftHeight a A T
    (T : ℝ) ≤ R a * (X ^ 5 + X ^ 4 * H ^ (1 / 2 : ℝ) + X ^ 5 * (max H S) ^ (1 / 10 : ℝ))

/-- Direct conditional conclusion from the estimate displayed in the new candidate. -/
theorem P_le_151_513_of_three_term_estimate {R : ℕ → ℕ} (hR : SlowGrowth R)
    (hlocal : IntegralLiftThreeTermEstimate R) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((151 : ℝ) / 513 + ε) := by
  have hc : SlowGrowth (fun _ : ℕ => 3) := slowGrowth_const _
  apply P_le_151_513_of_integral_lift_count ((hc.mul (slowGrowth_add_one hR)).pow 10)
  intro a b s T A hba hmem hsT hT hscale
  apply integral_lift_branches_of_three_term_count
  simpa only [Nat.cast_max] using hlocal a b s T A hba hmem hsT hT hscale

end PierceLengthBound.FixedDividend
