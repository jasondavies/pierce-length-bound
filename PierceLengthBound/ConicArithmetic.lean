/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Tactic

/-! Algebraic identities and injective parameters for affine conics.
The geometric reduction to such a conic remains a separate obligation. -/

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

/-- Every point of a discriminant-zero conic has the proposed parabolic parameter. -/
theorem parabola_parameter_identity {K : Type*} [CommRing K] (α β γ d e f x y : K)
    (hΔ : β ^ 2 - 4 * α * γ = 0) (hc : conicValue α β γ d e f x y = 0) :
    (2 * α * x + β * y + d) ^ 2 = (2 * β * d - 4 * α * e) * y + d ^ 2 - 4 * α * f := by
  have h := conic_square_identity α β γ d e f x y
  rw [hΔ, hc] at h
  linear_combination h

/-- The parameter determines both coordinates whenever its required denominators are nonzero. -/
theorem parabola_reconstruction {K : Type*} [Field K] [CharZero K]
    {α β γ d e f x y : K} (hα : α ≠ 0) (hJ : 2 * β * d - 4 * α * e ≠ 0)
    (hΔ : β ^ 2 - 4 * α * γ = 0) (hc : conicValue α β γ d e f x y = 0) :
    let t := 2 * α * x + β * y + d
    y = (t ^ 2 - (d ^ 2 - 4 * α * f)) / (2 * β * d - 4 * α * e) ∧
    x = (t - β * y - d) / (2 * α) := by
  dsimp only
  constructor
  · apply (eq_div_iff hJ).mpr
    linear_combination -(parabola_parameter_identity α β γ d e f x y hΔ hc)
  · apply (eq_div_iff (mul_ne_zero (by norm_num) hα)).mpr
    ring

/-- The same completion of squares gives the norm equation for nonparabolic conics. -/
theorem conic_norm_identity {K : Type*} [CommRing K] (α β γ d e f x y : K) :
    ((β ^ 2 - 4 * α * γ) * y + (β * d - 2 * α * e)) ^ 2 -
      (β ^ 2 - 4 * α * γ) * (2 * α * x + β * y + d) ^ 2 -
      ((β * d - 2 * α * e) ^ 2 + (β ^ 2 - 4 * α * γ) * (4 * α * f - d ^ 2)) =
      -4 * α * (β ^ 2 - 4 * α * γ) * conicValue α β γ d e f x y := by
  unfold conicValue
  ring

/-- The norm-coordinate change is injective. -/
theorem conic_norm_coordinates_injective {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    {α β γ d e : K} (hα : α ≠ 0) (hΔ : β ^ 2 - 4 * α * γ ≠ 0) :
    Function.Injective (fun z : K × K =>
      ((β ^ 2 - 4 * α * γ) * z.2 + (β * d - 2 * α * e),
        2 * α * z.1 + β * z.2 + d)) := by
  intro z w he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  dsimp only at h1 h2
  have hy : z.2 = w.2 := mul_left_cancel₀ hΔ (add_right_cancel h1)
  apply Prod.ext ?_ hy
  rw [hy] at h2
  exact mul_left_cancel₀ (mul_ne_zero (by norm_num) hα)
    (add_right_cancel (add_right_cancel h2))

end PierceLengthBound.FixedDividend
