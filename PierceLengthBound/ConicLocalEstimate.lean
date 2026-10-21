/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ConicGlobalReduction

/-! Convert the candidate's displayed three-term real estimate into the integer
local hypothesis, retaining every slack factor explicitly. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend

/-- The displayed conic estimate implies the three integer-power branches. -/
theorem conic_branches_of_three_term_count {T H X R : ℕ}
    (hcount : (T : ℝ) ≤ R * ((X : ℝ) ^ 5 + (X : ℝ) ^ 4 * (H : ℝ) ^ (1 / 2 : ℝ) +
      (X : ℝ) ^ (44 / 9 : ℝ) * (H : ℝ) ^ (1 / 3 : ℝ))) :
    ConicCountBranches ((3 * (R + 1)) ^ 9) T H X := by
  let D := 3 * (R + 1)
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hD1 : D ≤ D ^ 9 := by
    simpa using Nat.pow_le_pow_right hD (by norm_num : 1 ≤ 9)
  have hD2 : D ^ 2 ≤ D ^ 9 := Nat.pow_le_pow_right hD (by norm_num)
  have hcase : (T : ℝ) ≤ D * (X : ℝ) ^ 5 ∨
      (T : ℝ) ≤ D * ((X : ℝ) ^ 4 * (H : ℝ) ^ (1 / 2 : ℝ)) ∨
      (T : ℝ) ≤ D * ((X : ℝ) ^ (44 / 9 : ℝ) * (H : ℝ) ^ (1 / 3 : ℝ)) := by
    by_contra h
    push Not at h
    have h1 : 0 ≤ (X : ℝ) ^ 5 := by positivity
    have h2 : 0 ≤ (X : ℝ) ^ 4 * (H : ℝ) ^ (1 / 2 : ℝ) := by positivity
    have h3 : 0 ≤ (X : ℝ) ^ (44 / 9 : ℝ) * (H : ℝ) ^ (1 / 3 : ℝ) := by positivity
    dsimp [D] at h
    push_cast at h
    nlinarith
  change ConicCountBranches (D ^ 9) T H X
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
        simpa only [mul_pow, hs, ← pow_mul, mul_assoc, mul_left_comm, mul_comm, Nat.reduceMul] using hp
      exact_mod_cast he
    exact hn.trans (by gcongr)
  · right; right
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg T) h 9
    have hx : ((X : ℝ) ^ (44 / 9 : ℝ)) ^ 9 = (X : ℝ) ^ 44 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    have hh : ((H : ℝ) ^ (1 / 3 : ℝ)) ^ 9 = (H : ℝ) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    have he : (T : ℝ) ^ 9 ≤ (D : ℝ) ^ 9 * (H : ℝ) ^ 3 * (X : ℝ) ^ 44 := by
      simpa only [mul_pow, hx, hh, mul_assoc, mul_left_comm, mul_comm] using hp
    exact_mod_cast he

/-- The candidate's three-term local estimate on actual remainder windows. -/
def ConicThreeTermEstimate (R : ℕ → ℕ) : Prop :=
  ∀ a b s T A : ℕ, b < a →
    (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
    s + T ≤ P a b → 36 ≤ T →
    124928 * A ^ 4 * selectedGapHeight a A T ^ 5 * selectedMinorHeight a A T < a ^ 3 →
    let H : ℝ := selectedGapHeight a A T
    let X : ℝ := selectedMinorHeight a A T
    (T : ℝ) ≤ R a * (X ^ 5 + X ^ 4 * H ^ (1 / 2 : ℝ) + X ^ (44 / 9 : ℝ) * H ^ (1 / 3 : ℝ))

/-- Direct conditional conclusion from the estimate displayed in the new candidate. -/
theorem P_le_135_458_of_three_term_estimate {R : ℕ → ℕ} (hR : SlowGrowth R)
    (hlocal : ConicThreeTermEstimate R) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((135 : ℝ) / 458 + ε) := by
  have hc : SlowGrowth (fun _ : ℕ => 3) := slowGrowth_const _
  apply P_le_135_458_of_conic_count ((hc.mul (slowGrowth_add_one hR)).pow 9)
  intro a b s T A hba hmem hsT hT hscale
  exact conic_branches_of_three_term_count (hlocal a b s T A hba hmem hsT hT hscale)

end PierceLengthBound.FixedDividend
