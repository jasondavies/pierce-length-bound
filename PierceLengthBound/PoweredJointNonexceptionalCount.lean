/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PoweredJointComponentCount
public import PierceLengthBound.JointPatternCount

/-! The nonexceptional powered count: `JointPatternCount` applied to the component count
of `PoweredJointComponentCount` in the box `poweredJointBox`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- The nonexceptional branch of the powered pattern count, with all
geometric and arithmetic inputs discharged on the actual orbit. -/
theorem selected_nonexceptional_powered_joint_gap_count_slow (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧
      JointNonexceptionalCount (poweredJointBox m n) (1 / ((10 * n + 7 * m : ℕ) : ℝ)) R := by
  obtain ⟨R, hR, hcount⟩ := selected_powered_joint_component_gap_count_slow m n hm hn
  exact jointNonexceptionalCount_of_components hR
    fun hba hmem hsT hT hne I hI hf hg hd G hG hpat hz =>
      hcount hba hmem hsT hT hne I hI hf hg hd G hG (theta_eq_of_plk_eq hpat) hz

end
end PierceLengthBound.FixedDividend
