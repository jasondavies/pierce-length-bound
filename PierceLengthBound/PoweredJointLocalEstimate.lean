/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PoweredJointPatternCount

/-! Assemble the proved powered pattern counts into the three local terms
and extract integer-power count branches without changing their exponents. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Finset

/-- Three possible dominant terms in the powered count. -/
def PoweredJointCountBranches (K T H X B L : ℕ) : Prop :=
  T ≤ K * X ^ 5 ∨ T ^ 2 ≤ K * H * X ^ 8 ∨ T ^ L ≤ K * X ^ (5 * L) * B

set_option maxHeartbeats 1000000 in
-- The three-term real inequality requires normalization of the nested maximum.
/-- The displayed joint-coordinate estimate implies the three integer-power branches. -/
theorem powered_joint_branches_of_three_term_count {T H X B R L : ℕ} (hL : 2 ≤ L)
    (hcount : (T : ℝ) ≤ R * ((X : ℝ) ^ 5 + (X : ℝ) ^ 4 * (H : ℝ) ^ (1 / 2 : ℝ) +
      (X : ℝ) ^ (5 : ℕ) * (B : ℝ) ^ (1 / (L : ℝ)))) :
    PoweredJointCountBranches ((3 * (R + 1)) ^ L) T H X B L := by
  let D := 3 * (R + 1)
  have hD : 1 ≤ D := by dsimp [D]; omega
  have hD1 : D ≤ D ^ L := by
    simpa using Nat.pow_le_pow_right hD (by omega : 1 ≤ L)
  have hD2 : D ^ 2 ≤ D ^ L := Nat.pow_le_pow_right hD hL
  have hcase : (T : ℝ) ≤ D * (X : ℝ) ^ 5 ∨
      (T : ℝ) ≤ D * ((X : ℝ) ^ 4 * (H : ℝ) ^ (1 / 2 : ℝ)) ∨
      (T : ℝ) ≤ D * ((X : ℝ) ^ (5 : ℕ) * (B : ℝ) ^ (1 / (L : ℝ))) := by
    by_contra h
    push Not at h
    have h1 : 0 ≤ (X : ℝ) ^ 5 := by positivity
    have h2 : 0 ≤ (X : ℝ) ^ 4 * (H : ℝ) ^ (1 / 2 : ℝ) := by positivity
    have h3 : 0 ≤ (X : ℝ) ^ (5 : ℕ) * (B : ℝ) ^ (1 / (L : ℝ)) := by positivity
    dsimp [D] at h
    push_cast at h
    nlinarith only [hcount, h.1, h.2.1, h.2.2, h1, h2, h3]
  change PoweredJointCountBranches (D ^ L) T H X B L
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
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg T) h L
    have hs : ((B : ℝ) ^ (1 / (L : ℝ))) ^ L = B := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
      rw [one_div_mul_cancel hL0, Real.rpow_one]
    have he : (T : ℝ) ^ L ≤ (D : ℝ) ^ L * (X : ℝ) ^ (5 * L) * B := by
      simpa only [mul_pow, hs, ← pow_mul, Nat.reduceMul, mul_assoc] using hp
    exact_mod_cast he

/-- The displayed powered estimate on actual remainder windows. -/
def PoweredJointThreeTermEstimate (m n : ℕ) (R : ℕ → ℕ) : Prop :=
  ∀ a b s T A : ℕ, b < a →
    (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
    s + T ≤ P a b → 36 ≤ T →
    124928 * A ^ 4 * selectedGapHeight a A T ^ 5 * selectedMinorHeight a A T < a ^ 3 →
    let H : ℝ := selectedGapHeight a A T
    let X : ℝ := selectedMinorHeight a A T
    let S : ℝ := selectedCurvatureHeight a A T
    let Y : ℝ := selectedRankFiveHeight a A T
    (T : ℝ) ≤ R a * (X ^ 5 + X ^ 4 * H ^ (1 / 2 : ℝ) +
      X ^ 5 * (max (max H (S ^ m)) (Y ^ n)) ^ (1 / ((10 * n + 7 * m : ℕ) : ℝ)))

/-- Assemble the ordinary full-pattern count, exceptional-pattern count, and
quartic multiplicity into the displayed local estimate. -/
theorem powered_joint_three_term_of_pattern_estimate {m n : ℕ} {R : ℕ → ℕ}
    (hcurve : PoweredJointPatternEstimate m n R) :
    PoweredJointThreeTermEstimate m n (integralLiftPatternSlack R) := by
  intro a b s T A hba hmem hsT hT hscale
  classical
  let G := selectedStarts a b s T A
  let pm := fun i => plk (Mi a b i)
  let H := selectedGapHeight a A T
  let X := selectedMinorHeight a A T
  let B := max (max H (selectedCurvatureHeight a A T ^ m)) (selectedRankFiveHeight a A T ^ n)
  have facts := fun i hi => selectedStart_spec hmem hsT (i := i) hi
  have hmult : G.card ≤ 4 * (G.image fun i => (pm i, kap a b i)).card :=
    selectedStarts_card_le_pair_image hba hmem hsT
  have hp := pattern_sum_two_classes G pm (kap a b) (fun p => ∃ d, ExceptionalMinorRelation p d)
    (show (0 : ℝ) ≤ R a * (1 + (B : ℝ) ^ (1 / ((10 * n + 7 * m : ℕ) : ℝ))) by positivity)
    (show (0 : ℝ) ≤ R a * (H : ℝ) ^ (1 / 2 : ℝ) by positivity)
    (show ((G.image pm).card : ℝ) ≤ ordinaryPatternSlack a * (X : ℝ) ^ 5 by
      exact_mod_cast selected_ordinary_pattern_count hba hmem hsT hT)
    (show (((G.image pm).filter fun p => ∃ d, ExceptionalMinorRelation p d).card : ℝ) ≤
        exceptionalPatternSlack a * (X : ℝ) ^ 4 by
      exact_mod_cast selected_exceptional_pattern_count_slack hba hmem hsT hT)
    (by simpa only [G, pm, H, B, Nat.cast_max, Nat.cast_pow] using hcurve a b s T A hba hmem hsT hT hscale)
  have hTcard := selectedStarts_card hba hmem hsT hT
  change T ≤ 2 * G.card at hTcard
  have hTc : (T : ℝ) ≤ 8 * ((G.image fun i => (pm i, kap a b i)).card : ℝ) := by
    exact_mod_cast (show T ≤ 8 * (G.image fun i => (pm i, kap a b i)).card by omega)
  dsimp only
  have hO : (ordinaryPatternSlack a : ℝ) ≤ ordinaryPatternSlack a + exceptionalPatternSlack a :=
    le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hE : (exceptionalPatternSlack a : ℝ) ≤ ordinaryPatternSlack a + exceptionalPatternSlack a :=
    le_add_of_nonneg_left (Nat.cast_nonneg _)
  calc (T : ℝ) ≤ 8 * ((ordinaryPatternSlack a : ℝ) * (X : ℝ) ^ 5 *
        ((R a : ℝ) * (1 + (B : ℝ) ^ (1 / ((10 * n + 7 * m : ℕ) : ℝ)))) +
        (exceptionalPatternSlack a : ℝ) * (X : ℝ) ^ 4 * ((R a : ℝ) * (H : ℝ) ^ (1 / 2 : ℝ))) :=
      hTc.trans (mul_le_mul_of_nonneg_left hp (by norm_num))
    _ ≤ 8 * (((ordinaryPatternSlack a : ℝ) + exceptionalPatternSlack a) * (X : ℝ) ^ 5 *
        ((R a : ℝ) * (1 + (B : ℝ) ^ (1 / ((10 * n + 7 * m : ℕ) : ℝ)))) +
        ((ordinaryPatternSlack a : ℝ) + exceptionalPatternSlack a) * (X : ℝ) ^ 4 *
          ((R a : ℝ) * (H : ℝ) ^ (1 / 2 : ℝ))) := by gcongr
    _ = _ := by simp only [integralLiftPatternSlack, Nat.cast_mul, Nat.cast_add,
        Nat.cast_ofNat, Nat.cast_max, Nat.cast_pow, B, H, X]; ring

/-- Every fixed pair of positive powers has the full local three-term bound. -/
theorem poweredJointThreeTermEstimate_exists (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ PoweredJointThreeTermEstimate m n R := by
  obtain ⟨R, hR, hcount⟩ := poweredJointPatternEstimate_exists m n hm hn
  exact ⟨integralLiftPatternSlack R, integralLiftPatternSlack_slow hR,
    powered_joint_three_term_of_pattern_estimate hcount⟩

end PierceLengthBound.FixedDividend
