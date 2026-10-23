/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendConicPlaneModel

/-! Explicit denominator clearing for the two parabolic plane charts. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- Integral coefficients after multiplication by the square of the common
coefficient denominator and the square of the eliminated plane coefficient. -/
def integralPlaneConicCoefficients (a b c l0 l1 l2 D n0 n1 n2 e : ℤ) : Fin 6 → ℤ := ![
  b * D * n2 ^ 2 + c * D * n1 ^ 2 + (b * n2 - c * n1) ^ 2,
  2 * c * D * n0 * n1 + 2 * (a * n2 - c * n0) * (b * n2 - c * n1),
  a * D * n2 ^ 2 + c * D * n0 ^ 2 + (a * n2 - c * n0) ^ 2,
  2 * c * D * n1 * e - 2 * c * e * (b * n2 - c * n1) + l1 * n2 ^ 2 - l2 * n1 * n2,
  2 * c * D * n0 * e - 2 * c * e * (a * n2 - c * n0) + l0 * n2 ^ 2 - l2 * n0 * n2,
  c * D * e ^ 2 + (c * e) ^ 2 - l2 * e * n2]

/-- Clearing denominators multiplies the plane conic coefficients by `D² n₂²`. -/
lemma integralPlaneConicCoefficients_eq (a b c l0 l1 l2 D n0 n1 n2 e : ℤ)
    (hD : D ≠ 0) (hn : n2 ≠ 0) (j : Fin 6) :
    (integralPlaneConicCoefficients a b c l0 l1 l2 D n0 n1 n2 e j : ℚ) =
      (D : ℚ) ^ 2 * (n2 : ℚ) ^ 2 *
        planeConicCoefficients ((a : ℚ) / D) ((b : ℚ) / D) ((c : ℚ) / D)
          ((l0 : ℚ) / D ^ 2) ((l1 : ℚ) / D ^ 2) ((l2 : ℚ) / D ^ 2)
          (-(n0 : ℚ) / n2) (-(n1 : ℚ) / n2) (-(e : ℚ) / n2) j := by
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hn' : (n2 : ℚ) ≠ 0 := by exact_mod_cast hn
  fin_cases j <;>
    simp [integralPlaneConicCoefficients, planeConicCoefficients] <;>
    field_simp <;> ring

lemma conicValue_scale {K : Type*} [CommRing K] (s : K) (c : Fin 6 → K) (x y : K) :
    conicValue (s * c 0) (s * c 1) (s * c 2) (s * c 3) (s * c 4) (s * c 5) x y =
      s * conicValue (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) x y := by
  simp only [conicValue]
  ring

/-- Nondegeneracy and the parabolic equation survive the explicit clearing. -/
theorem integralPlaneConicCoefficients_parabolic
    (a b c l0 l1 l2 D n0 n1 n2 e : ℤ) (hD : D ≠ 0) (hn : n2 ≠ 0)
    (v : Fin 6 → ℚ)
    (hv : ∀ j, v j = planeConicCoefficients ((a : ℚ) / D) ((b : ℚ) / D)
      ((c : ℚ) / D) ((l0 : ℚ) / D ^ 2) ((l1 : ℚ) / D ^ 2) ((l2 : ℚ) / D ^ 2)
      (-(n0 : ℚ) / n2) (-(n1 : ℚ) / n2) (-(e : ℚ) / n2) j)
    (hα : v 0 ≠ 0) (hΔ : (v 1) ^ 2 - 4 * v 0 * v 2 = 0)
    (hJ : 2 * v 1 * v 3 - 4 * v 0 * v 4 ≠ 0) :
    let w := integralPlaneConicCoefficients a b c l0 l1 l2 D n0 n1 n2 e
    w 0 ≠ 0 ∧ (w 1) ^ 2 - 4 * w 0 * w 2 = 0 ∧
      2 * w 1 * w 3 - 4 * w 0 * w 4 ≠ 0 ∧
      ∀ x y : ℤ, conicValue (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) x y = 0 →
        conicValue (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) x y = 0 := by
  let w := integralPlaneConicCoefficients a b c l0 l1 l2 D n0 n1 n2 e
  let s : ℚ := (D : ℚ) ^ 2 * (n2 : ℚ) ^ 2
  have hs : s ≠ 0 := mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hD))
    (pow_ne_zero _ (by exact_mod_cast hn))
  have he (j : Fin 6) : (w j : ℚ) = s * v j := by
    rw [hv]
    exact integralPlaneConicCoefficients_eq a b c l0 l1 l2 D n0 n1 n2 e hD hn j
  have ha' : (w 0 : ℚ) ≠ 0 := by rw [he]; exact mul_ne_zero hs hα
  have hd' : (w 1 : ℚ) ^ 2 - 4 * w 0 * w 2 = 0 := by
    simp only [he]
    linear_combination s ^ 2 * hΔ
  have hj' : 2 * (w 1 : ℚ) * w 3 - 4 * w 0 * w 4 ≠ 0 := by
    simp only [he]
    rw [show 2 * (s * v 1) * (s * v 3) - 4 * (s * v 0) * (s * v 4) =
      s ^ 2 * (2 * v 1 * v 3 - 4 * v 0 * v 4) by ring]
    exact mul_ne_zero (pow_ne_zero _ hs) hJ
  refine ⟨by exact_mod_cast ha', by exact_mod_cast hd', by exact_mod_cast hj', ?_⟩
  intro x y hp
  have hh : conicValue (w 0 : ℚ) (w 1) (w 2) (w 3) (w 4) (w 5) x y = 0 := by
    simp only [he, conicValue_scale, hp, mul_zero]
  change conicValue (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) x y = 0
  unfold conicValue at hh ⊢
  exact_mod_cast hh

end
end PierceLengthBound.FixedDividend
