/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftNonexceptionalCount
public import PierceLengthBound.OrbitPatternCurveCount
public import PierceLengthBound.JointLiftPatternCount

/-! Unconditional joint-lift length bound. Both branches of the actual pattern
estimate follow from the formalized curve-counting theorem and component geometry. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

/-- The joint-lift pattern estimate holds with a proved subpolynomial coefficient.
It has no external counting, graph-degree, or retained-component assumptions. -/
theorem jointLiftPatternEstimate_exists :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ JointLiftPatternEstimate R := by
  classical
  obtain ⟨Re, hRe, he⟩ := selected_pattern_curve_gap_count_slow
  obtain ⟨Rn, hRn, hn⟩ := selected_nonexceptional_joint_gap_count_slow
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
          (1 + (max (max (selectedGapHeight a A T) (selectedCurvatureHeight a A T))
            (selectedRankFiveHeight a A T) : ℝ) ^ (1 / (17 : ℝ))) :=
        hn hba hmem hsT hT hi7 hne G hG hθ
      _ ≤ _ := by
        push_cast
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (Nat.cast_nonneg _))
          (by positivity)

/-- The unconditional length bound from the unpowered joint lift. -/
theorem P_le_128_435 :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((128 : ℝ) / 435 + ε) := by
  obtain ⟨R, hR, hcount⟩ := jointLiftPatternEstimate_exists
  exact P_le_128_435_of_pattern_estimate hR hcount

end
end PierceLengthBound.FixedDividend
