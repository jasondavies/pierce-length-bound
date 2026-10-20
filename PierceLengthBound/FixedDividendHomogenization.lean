/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendCurveEquations
public import PierceLengthBound.FixedDividendParity
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# Homogenized fixed-dividend equations

Reversing the radial polynomial at the prescribed degree gives the homogeneous
polynomial, with the new polynomial variable representing the infinity coordinate.
The fixed-dividend equation has the exact square/fourth-power form, and the
restrictions at infinity are the certified leading forms.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

/-- Homogenization with a prescribed degree, encoded as a polynomial in the new
coordinate with multivariate coefficients. -/
def curveHomogenize {K : Type*} [CommRing K] (n : ℕ) (f : MvPolynomial (Fin 3) K) :
    Polynomial (MvPolynomial (Fin 3) K) := (radialMap f).reflect n

lemma reflect_pow_of_natDegree_le {R : Type*} [CommRing R] (f : R[X]) {d : ℕ}
    (hf : f.natDegree ≤ d) (n : ℕ) : (f ^ n).reflect (d * n) = f.reflect d ^ n := by
  induction n with
  | zero => simp [reflect_one]
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ, reflect_mul _ _ (natDegree_pow_le.trans
      (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left n hf)) hf, ih, pow_succ]

lemma reflect_raise_degree {R : Type*} [CommRing R] (f : R[X]) {d : ℕ}
    (hf : f.natDegree ≤ d) (n : ℕ) : f.reflect (d + n) = f.reflect d * X ^ n := by
  simpa only [mul_one, reflect_one] using
    reflect_mul f 1 hf (show (1 : R[X]).natDegree ≤ n by simp)

/-- The degree-twelve equation homogenizes with exactly two powers of infinity. -/
theorem curveEquation_homogenize {K : Type*} [CommRing K] [Nontrivial K]
    (ρ u v ρ' u' v' A a : K) :
    curveHomogenize 12 (curveEquation ρ u v ρ' u' v' A a) =
      C (MvPolynomial.C A) * X ^ 2 *
        curveHomogenize 10 (curveResultant ρ u v ρ' u' v') -
      C (MvPolynomial.C a) * curveHomogenize 3 (curveNorm ρ u v ρ' u' v') ^ 4 := by
  simp only [curveHomogenize, curveEquation, map_sub, map_mul, map_pow, radialMap_C,
    reflect_sub, reflect_C_mul]
  rw [show 12 = 10 + 2 by decide,
    reflect_raise_degree _ (radialMap_resultant_degree ρ u v ρ' u' v')]
  rw [show 10 + 2 = 3 * 4 by decide,
    reflect_pow_of_natDegree_le _ (radialMap_norm_degree ρ u v ρ' u' v')]
  ring

lemma curveHomogenize_at_infinity {K : Type*} [CommRing K]
    (n : ℕ) (f : MvPolynomial (Fin 3) K) :
    (curveHomogenize n f).eval 0 = (radialMap f).coeff n := by
  rw [curveHomogenize, ← coeff_zero_eq_eval_zero, coeff_reflect, revAt_zero]

lemma curveQuadratic_at_infinity {K : Type*} [CommRing K] (ρ u v ρ' u' v' : K) :
    (curveHomogenize 2 (curveQuadratic ρ u v ρ' u' v')).eval 0 =
      leadingQuadratic (-ρ - u) (u - v) (v - 1) := by
  rw [curveHomogenize_at_infinity, radialMap_quadratic_coeff]

lemma curveNorm_at_infinity {K : Type*} [CommRing K] (ρ u v ρ' u' v' : K) :
    (curveHomogenize 3 (curveNorm ρ u v ρ' u' v')).eval 0 =
      leadingCubic (-ρ - u) (u - v) (v - 1) := by
  rw [curveHomogenize_at_infinity, radialMap_norm_coeff]

/-- Normalize coefficient extraction before substituting a large polynomial. -/
lemma mvPolynomial_coeff_commRing {K : Type*} [CommRing K]
    (p : Polynomial (MvPolynomial (Fin 3) K)) (n : ℕ) :
    p.coeff n = @Polynomial.coeff (MvPolynomial (Fin 3) K)
      (CommRing.toCommSemiring.toSemiring) p n := rfl

/-- Exact resultant form on the infinity hyperplane, before any specialization. -/
lemma curveResultant_at_infinity {K : Type*} [CommRing K] [Nontrivial K]
    (ρ u v ρ' u' v' : K) :
    (curveHomogenize 10 (curveResultant ρ u v ρ' u' v')).eval 0 =
      MvPolynomial.C (ρ * (-ρ - u) * (u - v) * (v - 1)) *
        nodeVandermonde (completeNodes (MvPolynomial.C ρ) (MvPolynomial.C u)
          (MvPolynomial.C v) MvPolynomial.X) := by
  apply (curveHomogenize_at_infinity 10 _).trans
  apply (congrArg (fun p : Polynomial (MvPolynomial (Fin 3) K) => p.coeff 10)
    (radialMap_resultant ρ u v ρ' u' v')).trans
  apply (mvPolynomial_coeff_commRing _ 10).trans
  refine (affineResultant_coeff_ten _ _ _ _ _ _ _ _).trans ?_
  simp [coeffs]

/-- Evaluating the quadratic leading form gives precisely the second node moment. -/
lemma eval_leadingQuadratic_moment {K : Type*} [CommRing K] (ρ u v : K) (z : Fin 3 → K) :
    MvPolynomial.eval z (leadingQuadratic (-ρ - u) (u - v) (v - 1)) =
      ∑ j : Fin 5, coeffs ρ u v j * completeDirection ρ u v z j ^ 2 := by
  simp [leadingQuadratic, ternaryQuadratic, coeffs, completeDirection, fourthNode,
    Fin.sum_univ_succ]
  ring

/-- Evaluating the cubic leading form gives precisely the third node moment. -/
lemma eval_leadingCubic_moment {K : Type*} [CommRing K] (ρ u v : K) (z : Fin 3 → K) :
    MvPolynomial.eval z (leadingCubic (-ρ - u) (u - v) (v - 1)) =
      ∑ j : Fin 5, coeffs ρ u v j * completeDirection ρ u v z j ^ 3 := by
  simp [leadingCubic, coeffs, completeDirection, fourthNode, Fin.sum_univ_succ]
  ring

/-- A nonzero projective direction is not the single zero node cluster. -/
lemma completeDirection_not_constant {K : Type*} [CommRing K] (ρ u v : K) (z : Fin 3 → K)
    (hz : ∃ j, z j ≠ 0) : ∃ i j, completeDirection ρ u v z i ≠
      completeDirection ρ u v z j := by
  obtain ⟨j, hj⟩ := hz
  fin_cases j
  · exact ⟨1, 0, by simpa [completeDirection] using hj⟩
  · exact ⟨2, 0, by simpa [completeDirection] using hj⟩
  · exact ⟨3, 0, by simpa [completeDirection] using hj⟩

/-- The two homogeneous equations at an actual nonzero infinity direction force
nonvanishing of the resultant there. No smoothness assumption is used. -/
theorem nonexceptional_resultant_at_infinity_ne_zero {ρ u v : ℝ}
    (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0) (hne : NonexceptionalPattern ρ u v)
    (ρ' u' v' A a : ℂ) (ha : a ≠ 0) (z : Fin 3 → ℂ) (hz : ∃ j, z j ≠ 0)
    (hq : MvPolynomial.eval z
      ((curveHomogenize 2 (curveQuadratic (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v')).eval 0) = 0)
    (he : MvPolynomial.eval z
      ((curveHomogenize 12 (curveEquation (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v' A a)).eval 0) = 0) :
    MvPolynomial.eval z
      ((curveHomogenize 10 (curveResultant (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v')).eval 0) ≠ 0 := by
  rw [curveQuadratic_at_infinity, eval_leadingQuadratic_moment] at hq
  rw [curveEquation_homogenize] at he
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_mul, zero_sub, map_neg, map_mul, MvPolynomial.eval_C, map_pow,
    neg_eq_zero, mul_eq_zero, ha, false_or, pow_eq_zero_iff (by decide : 4 ≠ 0)] at he
  rw [curveNorm_at_infinity, eval_leadingCubic_moment] at he
  have hm : ∀ m < 4, ∑ j : Fin 5, coeffs (ρ : ℂ) (u : ℂ) (v : ℂ) j *
      completeDirection (ρ : ℂ) (u : ℂ) (v : ℂ) z j ^ m = 0 := by
    intro m hm
    interval_cases m
    · exact completeDirection_moment_zero _ _ _ _
    · exact completeDirection_moment_one _ _ _ _
    · exact hq
    · exact he
  have hV := nonexceptional_leading_vandermonde_ne_zero hρ hu hv hne
    (completeDirection (ρ : ℂ) (u : ℂ) (v : ℂ) z)
    (completeDirection_not_constant _ _ _ z hz) (by simp [completeDirection]) hm
  have hc : (ρ : ℂ) * (-(ρ : ℂ) - u) * ((u : ℂ) - v) * ((v : ℂ) - 1) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
    all_goals norm_cast
    all_goals linarith
  rw [curveResultant_at_infinity]
  simpa [nodeVandermonde, completeNodes, completeDirection, fourthNode] using
    mul_ne_zero hc hV

end
end PierceLengthBound.FixedDividend
