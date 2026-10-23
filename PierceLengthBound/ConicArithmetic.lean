/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Tactic

/-! Completion of the square for an affine binary quadratic, and the parabolic parameter
`t = 2αx + βy + d` with `t² = (2βd - 4αe)y + d² - 4αf` on a conic of discriminant zero
(the parameter of Lemma A.1, `lem:jointconicparameter`). -/

@[expose] public section
namespace PierceLengthBound.FixedDividend

/-- General affine binary quadratic. -/
def conicValue {K : Type*} [CommRing K] (α β γ d e f x y : K) : K :=
  α * x ^ 2 + β * x * y + γ * y ^ 2 + d * x + e * y + f

/-- Completion of the square, retaining the discriminant term. -/
theorem conic_square_identity {K : Type*} [CommRing K] (α β γ d e f x y : K) :
    (2 * α * x + β * y + d) ^ 2 -
      ((β ^ 2 - 4 * α * γ) * y ^ 2 + (2 * β * d - 4 * α * e) * y + d ^ 2 - 4 * α * f) =
      4 * α * conicValue α β γ d e f x y := by
  unfold conicValue
  ring

/-- At every point of a discriminant-zero conic, the parameter `t = 2αx + βy + d` satisfies
`t² = (2βd - 4αe)y + d² - 4αf`. -/
theorem parabola_parameter_identity {K : Type*} [CommRing K] (α β γ d e f x y : K)
    (hΔ : β ^ 2 - 4 * α * γ = 0) (hc : conicValue α β γ d e f x y = 0) :
    (2 * α * x + β * y + d) ^ 2 = (2 * β * d - 4 * α * e) * y + d ^ 2 - 4 * α * f := by
  have h := conic_square_identity α β γ d e f x y
  rw [hΔ, hc] at h
  linear_combination h

end PierceLengthBound.FixedDividend
