/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftComponentCount
public import PierceLengthBound.JointPatternCount

/-! The nonexceptional joint-lift count: `JointPatternCount` applied to the component count of
`JointLiftComponentCount` in the box `jointLiftBox`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- The nonexceptional branch of the joint-lift pattern count, with all
geometric and arithmetic inputs discharged on the actual orbit. -/
theorem selected_nonexceptional_joint_gap_count_slow :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ JointNonexceptionalCount jointLiftBox (1 / 17) R := by
  obtain ⟨R, hR, hcount⟩ := selected_joint_component_gap_count_slow
  exact jointNonexceptionalCount_of_components hR
    fun hba hmem hsT hT hne I hI hf hg hd G hG hpat hz =>
      hcount hba hmem hsT hT hne I hI hf hg hd G hG (theta_eq_of_plk_eq hpat) hz

end
end PierceLengthBound.FixedDividend
