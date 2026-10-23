/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendSecondConicChart
public import PierceLengthBound.ConicArithmetic

/-!
# Explicit restriction of the actual ternary quadratic to a plane

The six binary coefficients are given by exact formulas. The conic equation lies
in every ideal containing the plane and the ternary quadratic. A rational point
and absence of additional affine linear relations force the parabolic parameter
denominator to be nonzero.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- The binary equation in the first two original coordinate variables. -/
def secondPlaneConicPolynomial {K : Type*} [CommRing K] (v : Fin 6 → K) :
    MvPolynomial (Fin 3) K :=
  conicValue (C (v 0)) (C (v 1)) (C (v 2)) (C (v 3)) (C (v 4)) (C (v 5)) (X 2) (X 0)

/-- Restriction is an actual ideal-theoretic consequence, including all lower
terms of the plane and quadratic. -/
theorem secondPlaneConicPolynomial_mem {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin 3) K)) (a b c l0 l1 l2 n0 n2 n1 e : K)
    (hn1 : n1 ≠ 0)
    (hf : ternaryQuadratic a c b l0 l2 l1 ∈ I)
    (hp : C n0 * X 0 + C n2 * X 2 + C n1 * X 1 + C e ∈ I) :
    secondPlaneConicPolynomial (planeConicCoefficients a b c l0 l1 l2
      (-n0 / n1) (-n2 / n1) (-e / n1)) ∈ I := by
  let k := -n0 / n1
  let m := -n2 / n1
  let t := -e / n1
  let z' : MvPolynomial (Fin 3) K := C k * X 0 + C m * X 2 + C t
  have hT : X 1 - z' ∈ I := by
    have ht := I.mul_mem_left (C n1⁻¹) hp
    have herr := affine_plane_error (S := MvPolynomial (Fin 3) K)
      n0 n2 n1 e hn1 (X 2) (X 0) (X 1)
    change C n1⁻¹ * (C n0 * X 0 + C n2 * X 2 + C n1 * X 1 + C e) = X 1 - z' at herr
    have herr' : C n1⁻¹ * (C n0 * X 0 + C n2 * X 2 + C n1 * X 1 + C e) =
        X 1 - z' := herr
    rw [herr'] at ht
    exact ht
  have hid : ternaryQuadratic a c b l0 l2 l1 -
      secondPlaneConicPolynomial (planeConicCoefficients a b c l0 l1 l2 k m t) =
      (X 1 - z') * (C c * (X 1 + z') + C c *
        (2 * (C a * X 0 + C b * X 2) + C c * (X 1 + z')) + C l2) := by
    simp only [ternaryQuadratic, secondPlaneConicPolynomial, planeConicCoefficients,
      conicValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons, map_add, map_mul,
      map_pow, map_ofNat, z']
    ring
  have hh := I.mul_mem_right (C c * (X 1 + z') + C c *
    (2 * (C a * X 0 + C b * X 2) + C c * (X 1 + z')) + C l2) hT
  rw [← hid] at hh
  simpa only [sub_sub_cancel] using I.sub_mem hf hh

/-- A rational point rules out the degenerate discriminant-zero model when
additional affine linear equations have already been excluded. -/
theorem second_parabola_denominator_ne_zero_of_no_line {K : Type*} [Field K] [CharZero K]
    (I : Ideal (MvPolynomial (Fin 3) K)) [I.IsPrime]
    (α β γ d e f : K) (hα : α ≠ 0) (hΔ : β ^ 2 - 4 * α * γ = 0)
    (hc : secondPlaneConicPolynomial ![α, β, γ, d, e, f] ∈ I)
    (x y : K) (hpoint : conicValue α β γ d e f x y = 0)
    (hline : ∀ a b c : K, b ≠ 0 →
      C a * X 0 + C b * X 2 + C c ∉ I) :
    2 * β * d - 4 * α * e ≠ 0 := by
  intro hJ
  let t := 2 * α * x + β * y + d
  have hE : t ^ 2 = d ^ 2 - 4 * α * f := by
    simpa only [hJ, zero_mul, zero_add] using
      parabola_parameter_identity α β γ d e f x y hΔ hpoint
  let T : MvPolynomial (Fin 3) K := 2 * C α * X 2 + C β * X 0 + C d
  have hid : (T - C t) * (T + C t) =
      4 * C α * secondPlaneConicPolynomial ![α, β, γ, d, e, f] := by
    have hΔ' := congrArg (C : K →+* MvPolynomial (Fin 3) K) hΔ
    have hJ' := congrArg (C : K →+* MvPolynomial (Fin 3) K) hJ
    have hE' := congrArg (C : K →+* MvPolynomial (Fin 3) K) hE
    simp only [map_sub, map_mul, map_pow, map_ofNat, map_zero] at hΔ' hJ' hE'
    simp only [T, secondPlaneConicPolynomial, conicValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons]
    linear_combination X 0 ^ 2 * hΔ' + X 0 * hJ' - hE'
  have hm : (T - C t) * (T + C t) ∈ I := by rw [hid]; exact I.mul_mem_left _ hc
  have h2 : 2 * α ≠ 0 := mul_ne_zero (by norm_num) hα
  rcases (inferInstance : I.IsPrime).mem_or_mem hm with h | h
  · apply hline β (2 * α) (d - t) h2
    convert h using 1
    simp only [T, map_sub, map_mul, map_ofNat]
    ring
  · apply hline β (2 * α) (d + t) h2
    convert h using 1
    simp only [T, map_add, map_mul, map_ofNat]
    ring

end
end PierceLengthBound.FixedDividend
