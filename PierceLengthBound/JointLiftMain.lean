/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PoweredJointBound

/-! # Joint-invariant length bounds

Public statements of the joint-invariant bounds (Theorem 1.2 and Corollary 8.14 of the paper).
All three are instances of the powered bound `FixedDividend.P_le_powered_joint` in
`PoweredJointBound`: the optimal exponent by choosing the powers `m, n`, and the rational
exponents `2201/7480` and `128/435` by the choices `(m, n) = (50, 51)` and `(1, 1)`. -/

@[expose] public section
namespace PierceLengthBound

/-- Theorem 1.2 (joint-invariant bound): `P(a,b) ≪_ε a^(α_* + ε)` with
`α_* = (1310 - √655) / 4365`. -/
theorem P_le_joint_optimal :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ (((1310 : ℝ) - Real.sqrt 655) / 4365 + ε) :=
  FixedDividend.P_le_joint_optimal

/-- The rational joint-invariant bound `2201/7480` (Corollary 8.14), with powers `m = 50` of the
curvature coordinates and `n = 51` of the rank-five invariant. -/
theorem P_le_2201_7480 :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((2201 : ℝ) / 7480 + ε) :=
  FixedDividend.P_le_2201_7480

/-- The unpowered joint-invariant bound `128/435`, the case `m = n = 1` of Corollary 8.14. -/
theorem P_le_128_435 :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((128 : ℝ) / 435 + ε) :=
  FixedDividend.P_le_128_435

end PierceLengthBound
