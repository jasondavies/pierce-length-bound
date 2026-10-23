/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionPointCount
public import PierceLengthBound.PolarProjectionLocalEstimate
public import PierceLengthBound.LatticeJointLocalEstimate

/-! Sum the actual polar pattern estimates, including every exceptional and
bad pattern, into the six-term local inequality. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

open scoped Classical in
/-- Cardinality of the bad full patterns in an actual selected orbit window. -/
def PolarBadPatternCount (good : ℕ → (Fin 10 → ℤ) → Prop) (Rbad : ℕ → ℕ) : Prop :=
  ∀ {a b s T A : ℕ}, b < a →
    (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
    s + T ≤ P a b → 36 ≤ T →
    ((((selectedStarts a b s T A).image (fun i => plk (Mi a b i))).filter
      (fun p => ¬ good a p)).card : ℝ) ≤
      Rbad a * (selectedMinorHeight a A T : ℝ) ^ (14 / 3 : ℝ)

/-- A single coefficient for the five ordinary terms and the bad-pattern term. -/
def polarPatternSlack (R Rbad : ℕ → ℕ) (a : ℕ) : ℕ :=
  8 * R a * (2 * ordinaryPatternSlack a + exceptionalPatternSlack a +
    8 * latticeWeightSlack a + Rbad a)

lemma polarPatternSlack_slow {R Rbad : ℕ → ℕ} (hR : SlowGrowth R)
    (hbad : SlowGrowth Rbad) : SlowGrowth (polarPatternSlack R Rbad) := by
  exact ((slowGrowth_const 8).mul hR).mul
    (slowGrowth_add (slowGrowth_add
      (slowGrowth_add ((slowGrowth_const 2).mul ordinaryPatternSlack_slow)
        exceptionalPatternSlack_slow) ((slowGrowth_const 8).mul latticeWeightSlack_slow)) hbad)

/-- The six-term inequality follows by summing actual point counts with the
proved fractional lattice weights and the cardinality of the bad patterns. -/
theorem polar_six_term_of_pattern_estimate {m n : ℕ} (hm : 0 < m)
    {good : ℕ → (Fin 10 → ℤ) → Prop} {R Rbad : ℕ → ℕ}
    (hcurve : JointPatternEstimate (polarPatternBox good m n) 1 R)
    (hbad : PolarBadPatternCount good Rbad) :
    PolarProjectionSixTermEstimate m n (polarPatternSlack R Rbad) := by
  intro a b s T A hba hmem hsT hT hscale
  classical
  set hN : ℕ := polarProjectionGraphDegree m n
  set H := selectedGapHeight a A T
  set X := selectedMinorHeight a A T
  set S := selectedAllMinorHeight a A T
  set Y := selectedRankFiveHeight a A T
  have hh1 : (1 : ℝ) ≤ hN := by
    simp only [hN, polarProjectionGraphDegree]; push_cast
    nlinarith [show (1 : ℝ) ≤ m by exact_mod_cast hm,
      show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  have hm2 : (2 * m : ℝ) ≤ hN := by
    simp only [hN, polarProjectionGraphDegree]
    push_cast
    nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n,
      show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
  -- a bad pattern contributes the unconditional box, at most `B^{1/17}`
  let B : ℕ := max H (max S Y)
  let extra := fun p => if good a p then (0 : ℝ) else (B : ℝ) ^ (1 / 17 : ℝ)
  have hbox (p) (hp : p ∈ (selectedStarts a b s T A).image (fun i => plk (Mi a b i))) :
      polarPatternBox good m n p a A T ^ (1 : ℝ) ≤ 1 + 3 * (H : ℝ) ^ (1 / (hN : ℝ)) *
          ((shortR p : ℝ)⁻¹) ^ (1 / (hN : ℝ)) +
        8 * (S : ℝ) ^ ((m : ℝ) / hN) * ((shortR p : ℝ)⁻¹) ^ (2 * (m : ℝ) / hN) +
        (Y : ℝ) ^ ((n : ℝ) / hN) + extra p := by
    rw [Real.rpow_one, polarPatternBox]
    by_cases hgood : good a p
    · simp only [extra, hgood, ↓reduceIte, add_zero]
      exact selected_lattice_box_rpow_le hh1 hm2 hba hmem hsT hp
    · simp only [extra, hgood, ↓reduceIte]
      have hB : jointLiftBox p a A T ≤ (B : ℝ) := by
        have hS : selectedCurvatureHeight a A T ≤ S := by
          dsimp [S, selectedCurvatureHeight, selectedAllMinorHeight]
          apply Nat.div_le_div_right
          gcongr; norm_num
        dsimp only [jointLiftBox, B, H, Y]
        push_cast
        exact max_le (max_le (le_max_left _ _)
          ((by exact_mod_cast hS : (selectedCurvatureHeight a A T : ℝ) ≤ S).trans
            ((le_max_left _ _).trans (le_max_right _ _))))
          ((le_max_right _ _).trans (le_max_right _ _))
      have hpower := Real.rpow_le_rpow (by positivity : 0 ≤ jointLiftBox p a A T)
        hB (by norm_num : (0 : ℝ) ≤ 1 / 17)
      have : 0 ≤ 1 + 3 * (H : ℝ) ^ (1 / (hN : ℝ)) * ((shortR p : ℝ)⁻¹) ^ (1 / (hN : ℝ)) +
          8 * (S : ℝ) ^ ((m : ℝ) / hN) * ((shortR p : ℝ)⁻¹) ^ (2 * (m : ℝ) / hN) +
          (Y : ℝ) ^ ((n : ℝ) / hN) := by positivity
      linarith
  have hextra : ∑ p ∈ (selectedStarts a b s T A).image (fun i => plk (Mi a b i)), extra p ≤
      Rbad a * ((X : ℝ) ^ (14 / 3 : ℝ) * (B : ℝ) ^ (1 / 17 : ℝ)) := by
    simp only [extra, sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hbad hba hmem hsT hT) (by positivity)
  have h := lattice_terms_of_pattern_sum hh1 hm2 hba hmem hsT hT (Nat.cast_nonneg _)
    (by positivity) (selected_count_le_pattern_sum hcurve hba hmem hsT hT hscale
      (polarPatternBox_nonneg good m n)) hbox hextra
  refine h.trans (le_of_eq ?_)
  dsimp [polarPatternSlack, polarGoodTerms, polarBadTerm, hN, H, X, S, Y, B]
  push_cast
  ring

/-- The arithmetic counting assembly needs only a degree theorem on retained
prime components and a count of the patterns where it is unavailable. -/
theorem polar_six_term_of_retained_degree (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (good : ℕ → (Fin 10 → ℤ) → Prop) (hdegree : PolarRetainedDegree m n good)
    {Rbad : ℕ → ℕ} (hRbad : SlowGrowth Rbad) (hbad : PolarBadPatternCount good Rbad) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ PolarProjectionSixTermEstimate m n R := by
  obtain ⟨R, hR, hcount⟩ := polar_pattern_count_of_retained_degree m n hm hn good hdegree
  exact ⟨polarPatternSlack R Rbad, polarPatternSlack_slow hR hRbad,
    polar_six_term_of_pattern_estimate hm hcount hbad⟩

end
end PierceLengthBound.FixedDividend
