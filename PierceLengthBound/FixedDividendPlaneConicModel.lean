/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendRationalConicDiscriminant
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

/-- Binary coefficients in order α, β, γ, d, e, f, with x the second original
node, y the first, and the third node equal to k*y+m*x+t. -/
def planeConicCoefficients {K : Type*} [CommRing K]
    (a b c l0 l1 l2 k m t : K) : Fin 6 → K := ![
  b + c * m ^ 2 + (b + c * m) ^ 2,
  2 * c * k * m + 2 * (a + c * k) * (b + c * m),
  a + c * k ^ 2 + (a + c * k) ^ 2,
  2 * c * m * t + 2 * c * t * (b + c * m) + l1 + l2 * m,
  2 * c * k * t + 2 * c * t * (a + c * k) + l0 + l2 * k,
  c * t ^ 2 + (c * t) ^ 2 + l2 * t]

/-- The binary equation in the first two original coordinate variables. -/
def planeConicPolynomial {K : Type*} [CommRing K] (v : Fin 6 → K) :
    MvPolynomial (Fin 3) K :=
  conicValue (C (v 0)) (C (v 1)) (C (v 2)) (C (v 3)) (C (v 4)) (C (v 5)) (X 1) (X 0)

lemma affine_plane_error {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    (n0 n1 n2 e : K) (hn2 : n2 ≠ 0) (x y z : S) :
    algebraMap K S n2⁻¹ *
      (algebraMap K S n0 * y + algebraMap K S n1 * x + algebraMap K S n2 * z +
        algebraMap K S e) =
    z - (algebraMap K S (-n0 / n2) * y + algebraMap K S (-n1 / n2) * x +
      algebraMap K S (-e / n2)) := by
  have hh : algebraMap K S n2⁻¹ * algebraMap K S n2 = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hn2, map_one]
  simp only [div_eq_mul_inv, map_mul, map_neg]
  linear_combination z * hh

/-- Restriction is an actual ideal-theoretic consequence, including all lower
terms of the plane and quadratic. -/
theorem planeConicPolynomial_mem {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin 3) K)) (a b c l0 l1 l2 n0 n1 n2 e : K)
    (hn2 : n2 ≠ 0)
    (hf : ternaryQuadratic a b c l0 l1 l2 ∈ I)
    (hp : C n0 * X 0 + C n1 * X 1 + C n2 * X 2 + C e ∈ I) :
    planeConicPolynomial (planeConicCoefficients a b c l0 l1 l2
      (-n0 / n2) (-n1 / n2) (-e / n2)) ∈ I := by
  let k := -n0 / n2
  let m := -n1 / n2
  let t := -e / n2
  let z' : MvPolynomial (Fin 3) K := C k * X 0 + C m * X 1 + C t
  have hT : X 2 - z' ∈ I := by
    have ht := I.mul_mem_left (C n2⁻¹) hp
    have herr := affine_plane_error (S := MvPolynomial (Fin 3) K)
      n0 n1 n2 e hn2 (X 1) (X 0) (X 2)
    change C n2⁻¹ * (C n0 * X 0 + C n1 * X 1 + C n2 * X 2 + C e) = X 2 - z' at herr
    rw [herr] at ht
    exact ht
  have hid : ternaryQuadratic a b c l0 l1 l2 -
      planeConicPolynomial (planeConicCoefficients a b c l0 l1 l2 k m t) =
      (X 2 - z') * (C c * (X 2 + z') + C c *
        (2 * (C a * X 0 + C b * X 1) + C c * (X 2 + z')) + C l2) := by
    simp only [ternaryQuadratic, planeConicPolynomial, planeConicCoefficients,
      conicValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons, map_add, map_mul,
      map_pow, map_ofNat, z']
    ring
  have hh := I.mul_mem_right (C c * (X 2 + z') + C c *
    (2 * (C a * X 0 + C b * X 1) + C c * (X 2 + z')) + C l2) hT
  rw [← hid] at hh
  simpa only [sub_sub_cancel] using I.sub_mem hf hh

/-- A rational point rules out the degenerate discriminant-zero model when
additional affine linear equations have already been excluded. -/
theorem parabola_denominator_ne_zero_of_no_line {K : Type*} [Field K] [CharZero K]
    (I : Ideal (MvPolynomial (Fin 3) K)) [I.IsPrime]
    (α β γ d e f : K) (hα : α ≠ 0) (hΔ : β ^ 2 - 4 * α * γ = 0)
    (hc : planeConicPolynomial ![α, β, γ, d, e, f] ∈ I)
    (x y : K) (hpoint : conicValue α β γ d e f x y = 0)
    (hline : ∀ a b c : K, b ≠ 0 →
      C a * X 0 + C b * X 1 + C c ∉ I) :
    2 * β * d - 4 * α * e ≠ 0 := by
  intro hJ
  let t := 2 * α * x + β * y + d
  have hE : t ^ 2 = d ^ 2 - 4 * α * f := by
    simpa only [hJ, zero_mul, zero_add] using
      parabola_parameter_identity α β γ d e f x y hΔ hpoint
  let T : MvPolynomial (Fin 3) K := 2 * C α * X 1 + C β * X 0 + C d
  have hid : (T - C t) * (T + C t) =
      4 * C α * planeConicPolynomial ![α, β, γ, d, e, f] := by
    have hΔ' := congrArg (C : K →+* MvPolynomial (Fin 3) K) hΔ
    have hJ' := congrArg (C : K →+* MvPolynomial (Fin 3) K) hJ
    have hE' := congrArg (C : K →+* MvPolynomial (Fin 3) K) hE
    simp only [map_sub, map_mul, map_pow, map_ofNat, map_zero] at hΔ' hJ' hE'
    simp only [T, planeConicPolynomial, conicValue, Matrix.cons_val_zero,
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
