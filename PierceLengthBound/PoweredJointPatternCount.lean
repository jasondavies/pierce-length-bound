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
  JointPatternEstimate (poweredJointBox m n) (10 * n + 7 * m) R

/-- The powered joint-lift pattern estimate holds with a proved subpolynomial coefficient.
It has no external counting, graph-degree, or retained-component assumptions. -/
theorem poweredJointPatternEstimate_exists (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ PoweredJointPatternEstimate m n R := by
  obtain ⟨Rn, hRn, hcountn⟩ := selected_nonexceptional_powered_joint_gap_count_slow m n hm hn
  exact jointPatternEstimate_of_nonexceptional (B := poweredJointBox m n)
    (fun _ _ _ _ => by positivity) hRn hcountn

end
end PierceLengthBound.FixedDividend
