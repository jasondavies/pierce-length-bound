/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PoweredJointBound
public import PierceLengthBound.JointLiftBound

/-! Public submission statements for the joint-invariant length bounds. -/

@[expose] public section
namespace PierceLengthBound

/-- The optimized unconditional joint-invariant bound. -/
theorem P_le_joint_optimal :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ (((1310 : ℝ) - Real.sqrt 655) / 4365 + ε) :=
  FixedDividend.P_le_joint_optimal

/-- The rational joint-invariant bound, with powers `m = 50` of the curvature coordinates and
`n = 51` of the rank-five invariant. -/
theorem P_le_2201_7480 :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((2201 : ℝ) / 7480 + ε) :=
  FixedDividend.P_le_2201_7480

/-- The unpowered joint-invariant bound. -/
theorem P_le_128_435 :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((128 : ℝ) / 435 + ε) :=
  FixedDividend.P_le_128_435

end PierceLengthBound
