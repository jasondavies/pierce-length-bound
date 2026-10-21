/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PoweredJointComponentCount
public import PierceLengthBound.JointPatternCount

/-! The actual rational component cover supplies the full nonexceptional
pattern estimate. No graph-degree or retained-identity hypothesis remains. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

/-- The box of the powered joint graph; it does not depend on the pattern. -/
abbrev poweredJointBox (m n : ℕ) : (Fin 10 → ℤ) → ℕ → ℕ → ℕ → ℝ := fun _ a A T =>
  (max (max (selectedGapHeight a A T) (selectedCurvatureHeight a A T ^ m))
    (selectedRankFiveHeight a A T ^ n) : ℝ)

/-- The nonexceptional branch of the joint-lift pattern count, with all
geometric and arithmetic inputs discharged on the actual orbit. -/
theorem selected_nonexceptional_powered_joint_gap_count_slow (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧
      JointNonexceptionalCount (poweredJointBox m n) (10 * n + 7 * m) R := by
  obtain ⟨R, hR, hcount⟩ := selected_powered_joint_component_gap_count_slow m n hm hn
  exact jointNonexceptionalCount_of_components (B := poweredJointBox m n)
    (fun _ _ _ _ => by positivity) hR
    fun hba hmem hsT hT hne I hI hf hg hd G hG hpat hz =>
      hcount hba hmem hsT hT hne I hI hf hg hd G hG
        (fun l hl => by rw [theta_eq, theta_eq, hpat l hl]) hz

end
end PierceLengthBound.FixedDividend
