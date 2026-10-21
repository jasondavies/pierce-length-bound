/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.LatticeJointOptimization

/-! Public submission statements for the exterior-lattice length bounds. -/

@[expose] public section
namespace PierceLengthBound

/-- The optimized unconditional bound from exterior lattice coordinates. -/
theorem P_le_lattice_optimal :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((471 : ℝ) / 1559 - 6 * Real.sqrt 105 / 7795 + ε) :=
  FixedDividend.P_le_lattice_optimal

/-- The rational exterior-lattice bound, with powers `m = 3` of the curvature coordinates and
`n = 2` of the rank-five invariant. -/
theorem P_le_153_520 :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((153 : ℝ) / 520 + ε) :=
  FixedDividend.P_le_153_520

end PierceLengthBound
