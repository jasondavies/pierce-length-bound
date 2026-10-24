/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.LatticeJointOptimization

/-! Top-level statements of the exterior-lattice length bounds: the optimized exponent
`γ* = 471/1559 - 6√105/7795` (Theorem 1.3, `thm:lattice`) and the rational instance
`153/520` (Corollary 9.11, `cor:latticeexponent`). -/

@[expose] public section
namespace PierceLengthBound

/-- The optimized bound `P(a, b) ≪ a^{γ* + ε}` from exterior lattice coordinates. -/
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
