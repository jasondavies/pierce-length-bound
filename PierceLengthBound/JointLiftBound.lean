/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftNonexceptionalCount
public import PierceLengthBound.JointLiftPatternCount

/-! Unconditional joint-lift length bound. Both branches of the actual pattern
estimate follow from the formalized curve-counting theorem and component geometry. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- The joint-lift pattern estimate holds with a proved subpolynomial coefficient.
It has no external counting, graph-degree, or retained-component assumptions. -/
theorem jointLiftPatternEstimate_exists :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ JointLiftPatternEstimate R := by
  obtain ⟨Rn, hRn, hcountn⟩ := selected_nonexceptional_joint_gap_count_slow
  exact jointPatternEstimate_of_nonexceptional hRn hcountn

/-- The unconditional length bound from the unpowered joint lift. -/
theorem P_le_128_435 :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((128 : ℝ) / 435 + ε) := by
  obtain ⟨R, hR, hcount⟩ := jointLiftPatternEstimate_exists
  exact P_le_128_435_of_pattern_estimate hR hcount

end
end PierceLengthBound.FixedDividend
