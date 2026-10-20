/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftPatternCount
public import PierceLengthBound.JointLiftLocalEstimate

/-! Ordinary pattern counting for the integral-coordinate lift. No weighted
lattice incidence estimate occurs in the count or in its proof. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Finset

/-- Geometric estimates remaining per full pattern: square-root counting for
exceptional patterns, and a constant plus seventeenth-root graph count otherwise. -/
def JointLiftPatternEstimate (R : ℕ → ℕ) : Prop :=
  ∀ a b s T A : ℕ, b < a →
    (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
    s + T ≤ P a b → 36 ≤ T →
    124928 * A ^ 4 * selectedGapHeight a A T ^ 5 * selectedMinorHeight a A T < a ^ 3 →
    ∀ p ∈ (selectedStarts a b s T A).image (fun i => plk (Mi a b i)),
      ((((selectedStarts a b s T A).filter fun i => plk (Mi a b i) = p).image
        (kap a b)).card : ℝ) ≤
      if ∃ d, ExceptionalMinorRelation p d then
        (R a : ℝ) * (selectedGapHeight a A T : ℝ) ^ (1 / 2 : ℝ)
      else (R a : ℝ) * (1 + (max (max (selectedGapHeight a A T) (selectedCurvatureHeight a A T)) (selectedRankFiveHeight a A T) : ℝ) ^
        (1 / 17 : ℝ))

/-- Assemble the ordinary full-pattern count, exceptional-pattern count, and
quartic multiplicity into the displayed local estimate. -/
theorem jointLift_three_term_of_pattern_estimate {R : ℕ → ℕ}
    (hcurve : JointLiftPatternEstimate R) :
    JointLiftThreeTermEstimate (integralLiftPatternSlack R) := by
  intro a b s T A hba hmem hsT hT hscale
  classical
  let G := selectedStarts a b s T A
  let pm := fun i => plk (Mi a b i)
  let H := selectedGapHeight a A T
  let X := selectedMinorHeight a A T
  let B := max (max H (selectedCurvatureHeight a A T)) (selectedRankFiveHeight a A T)
  have facts := fun i hi => selectedStart_spec hmem hsT (i := i) hi
  have hmult : G.card ≤ 4 * (G.image fun i => (pm i, kap a b i)).card := by
    apply pattern_gap_multiplicity (θ := theta a b) (Q := fun i => (qq a b i : ℤ))
      (a := (a : ℤ)) (fun i _ => theta_eq i)
    · intro i hi i' hi' h
      have hP := (facts i hi).1
      have hP' := (facts i' hi').1
      simp only [Nat.cast_inj] at h
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact (qq_strictMono (a := a) (b := b) hlt (by omega)).ne h
      · exact (qq_strictMono (a := a) (b := b) hlt (by omega)).ne h.symm
    · intro i hi
      simpa [theta] using Lz_pos hba (i := i) (by have := (facts i hi).1; omega)
    · intro i hi
      simpa [theta, kap] using mult_at (a := a) (b := b) (i := i)
        (by have := (facts i hi).1; omega)
  have hp := pattern_sum_two_classes G pm (kap a b) (fun p => ∃ d, ExceptionalMinorRelation p d)
    (show (0 : ℝ) ≤ R a * (1 + (B : ℝ) ^ (1 / 17 : ℝ)) by positivity)
    (show (0 : ℝ) ≤ R a * (H : ℝ) ^ (1 / 2 : ℝ) by positivity)
    (show ((G.image pm).card : ℝ) ≤ ordinaryPatternSlack a * (X : ℝ) ^ 5 by
      exact_mod_cast selected_ordinary_pattern_count hba hmem hsT hT)
    (show (((G.image pm).filter fun p => ∃ d, ExceptionalMinorRelation p d).card : ℝ) ≤
        exceptionalPatternSlack a * (X : ℝ) ^ 4 by
      exact_mod_cast selected_exceptional_pattern_count_slack hba hmem hsT hT)
    (by simpa only [G, pm, H, B, Nat.cast_max] using hcurve a b s T A hba hmem hsT hT hscale)
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
        ((R a : ℝ) * (1 + (B : ℝ) ^ (1 / 17 : ℝ))) +
        (exceptionalPatternSlack a : ℝ) * (X : ℝ) ^ 4 * ((R a : ℝ) * (H : ℝ) ^ (1 / 2 : ℝ))) :=
      hTc.trans (mul_le_mul_of_nonneg_left hp (by norm_num))
    _ ≤ 8 * (((ordinaryPatternSlack a : ℝ) + exceptionalPatternSlack a) * (X : ℝ) ^ 5 *
        ((R a : ℝ) * (1 + (B : ℝ) ^ (1 / 17 : ℝ))) +
        ((ordinaryPatternSlack a : ℝ) + exceptionalPatternSlack a) * (X : ℝ) ^ 4 *
          ((R a : ℝ) * (H : ℝ) ^ (1 / 2 : ℝ))) := by gcongr
    _ = _ := by simp only [integralLiftPatternSlack, Nat.cast_mul, Nat.cast_add,
        Nat.cast_ofNat, Nat.cast_max, B, H, X]; ring

/-- The final exponent now depends only on the two unweighted per-pattern
arithmetic estimates, with all combinatorial and analytic assembly proved. -/
theorem P_le_128_435_of_pattern_estimate {R : ℕ → ℕ} (hR : SlowGrowth R)
    (hcurve : JointLiftPatternEstimate R) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((128 : ℝ) / 435 + ε) :=
  P_le_128_435_of_three_term_estimate (integralLiftPatternSlack_slow hR)
    (jointLift_three_term_of_pattern_estimate hcurve)

end PierceLengthBound.FixedDividend
