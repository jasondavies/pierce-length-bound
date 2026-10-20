/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PoweredJointNonexceptionalCount
public import PierceLengthBound.OrbitPatternCurveCount
public import PierceLengthBound.JointLiftPatternCount

/-! The powered joint-lift pattern estimate, with all component and external
counting hypotheses discharged for every fixed pair of positive powers. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

/-- Geometric estimates remaining per full pattern: square-root counting for
exceptional patterns, and a constant plus powered-graph graph count otherwise. -/
def PoweredJointPatternEstimate (m n : ℕ) (R : ℕ → ℕ) : Prop :=
  ∀ a b s T A : ℕ, b < a →
    (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
    s + T ≤ P a b → 36 ≤ T →
    124928 * A ^ 4 * selectedGapHeight a A T ^ 5 * selectedMinorHeight a A T < a ^ 3 →
    ∀ p ∈ (selectedStarts a b s T A).image (fun i => plk (Mi a b i)),
      ((((selectedStarts a b s T A).filter fun i => plk (Mi a b i) = p).image
        (kap a b)).card : ℝ) ≤
      if ∃ d, ExceptionalMinorRelation p d then
        (R a : ℝ) * (selectedGapHeight a A T : ℝ) ^ (1 / 2 : ℝ)
      else (R a : ℝ) * (1 + (max (max (selectedGapHeight a A T) (selectedCurvatureHeight a A T ^ m)) (selectedRankFiveHeight a A T ^ n) : ℝ) ^
        (1 / ((10 * n + 7 * m : ℕ) : ℝ)))

/-- The powered joint-lift pattern estimate holds with a proved subpolynomial coefficient.
It has no external counting, graph-degree, or retained-component assumptions. -/
theorem poweredJointPatternEstimate_exists (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ PoweredJointPatternEstimate m n R := by
  classical
  obtain ⟨Re, hRe, he⟩ := selected_pattern_curve_gap_count_slow
  obtain ⟨Rn, hRn, hcountn⟩ := selected_nonexceptional_powered_joint_gap_count_slow m n hm hn
  have hR : SlowGrowth (fun a => Re a + Rn a) := by
    intro η hη
    obtain ⟨Ce, hCe, hbe⟩ := hRe η hη
    obtain ⟨Cn, hCn, hbn⟩ := hRn η hη
    refine ⟨Ce + Cn, by positivity, fun a ha => ?_⟩
    have := hbe a ha
    have := hbn a ha
    push_cast
    nlinarith
  refine ⟨fun a => Re a + Rn a, hR, ?_⟩
  intro a b s T A hba hmem hsT hT hscale p hp
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
  have hi7 : i + 7 < P a b := by
    have := (selectedStart_spec hmem hsT hi).1
    omega
  let G := (selectedStarts a b s T A).filter (fun l => plk (Mi a b l) = plk (Mi a b i))
  have hG : G ⊆ selectedStarts a b s T A := filter_subset _ _
  have hθ (l) (hl : l ∈ G) : theta a b i = theta a b l := by
    rw [theta_eq, theta_eq, (mem_filter.mp hl).2]
  change ((G.image (kap a b)).card : ℝ) ≤ _
  split_ifs with hex
  · calc ((G.image (kap a b)).card : ℝ) ≤
          (Re a : ℝ) * (selectedGapHeight a A T : ℝ) ^ (1 / (2 : ℝ)) :=
        he hba hmem hsT hT hi7 hscale G hG hθ
      _ ≤ _ := by
        push_cast
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Nat.cast_nonneg _))
          (by positivity)
  · have hne : NonexceptionalPattern (patternRho a b i) (patternU a b i)
        (patternV a b i) := by
      by_contra hnot
      exact hex (orbit_exceptional_minor_relation hba (by omega : i + 6 < P a b) hnot)
    calc ((G.image (kap a b)).card : ℝ) ≤ (Rn a : ℝ) *
          (1 + (max (max (selectedGapHeight a A T) (selectedCurvatureHeight a A T ^ m))
            (selectedRankFiveHeight a A T ^ n) : ℝ) ^ (1 / ((10 * n + 7 * m : ℕ) : ℝ))) :=
        hcountn hba hmem hsT hT hi7 hne G hG hθ
      _ ≤ _ := by
        push_cast
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (Nat.cast_nonneg _))
          (by positivity)

end
end PierceLengthBound.FixedDividend
