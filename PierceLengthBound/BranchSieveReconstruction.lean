/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveElimination
public import PierceLengthBound.BranchSieveQuadratic
import Mathlib.Tactic

/-! The linear-subresultant reconstruction of the third infinity location, and the
nonvanishing invariant needed to adjoin the two branch signs. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

/-- Denominator of the third-location reconstruction. -/
def branchLocationDenominator {R : Type*} [CommRing R] (c1 c2 c3 : R) : R[X] :=
  C (c3 - 1) * (C (c2 * (c2 + c3 + 1)) * X ^ 2 + C (2 * c1 * c2) * X +
    C (c1 * (c1 + c3 + 1)))

/-- Negated numerator of the third-location reconstruction. -/
def branchLocationNumerator {R : Type*} [CommRing R] (c1 c2 c3 : R) : R[X] :=
  C (c2 * (c2 + 1) * (c2 + c3 + 1)) * X ^ 3 +
    C (c1 * c2 * (3 * c2 + c3 + 2)) * X ^ 2 +
    C (c1 * c2 * (3 * c1 + c3 + 2)) * X + C (c1 * (c1 + 1) * (c1 + c3 + 1))

/-- The reduced linear subresultant is a polynomial combination of the two moment equations. -/
theorem branchInfinity_linear_subresultant {R : Type*} [CommRing R] (c1 c2 c3 t y : R) :
    (c3 * (c3 + 1)) ^ 2 * (branchInfinityCubic c1 c2 c3 t).eval y -
      ((c3 * (c3 + 1)) * (c3 * (1 - c3 ^ 2)) * y +
        (c3 * (c3 + 1)) * (-3 * c3 ^ 2 * (c1 + c2 * t)) -
        (2 * c3 * (c1 + c2 * t)) * (c3 * (1 - c3 ^ 2))) *
          (branchInfinityQuadratic c1 c2 c3 t).eval y =
      c3 ^ 2 * (c3 + 1) *
        ((branchLocationDenominator c1 c2 c3).eval t * y +
          (branchLocationNumerator c1 c2 c3).eval t) := by
  simp only [branchInfinityCubic, branchInfinityQuadratic, branchLocationDenominator,
    branchLocationNumerator, eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  ring

/-- The evaluation map from parameter polynomials in `t` to the generic sextic field. -/
def branchLocationEvaluation : BranchLocationParameters[X] →+* BranchLocationExtension :=
  (AdjoinRoot.mk _).comp (Polynomial.mapRingHom
    (algebraMap BranchLocationParameters BranchLocationField))

/-- A polynomial of degree below six cannot vanish at the generic location if one
coefficient specialization shows it nonzero. -/
lemma branchLocationEvaluation_ne_zero {p : BranchLocationParameters[X]}
    (hdegree : p.natDegree < 6)
    (hs : p.map (MvPolynomial.eval ![-7, 8, -4]) ≠ 0) : branchLocationEvaluation p ≠ 0 := by
  have hp : p ≠ 0 := by intro h; exact hs (by rw [h, Polynomial.map_zero])
  have hm : p.map (algebraMap BranchLocationParameters BranchLocationField) ≠ 0 := by
    intro h
    apply hp
    apply Polynomial.map_injective
      (algebraMap BranchLocationParameters BranchLocationField)
      (IsFractionRing.injective BranchLocationParameters BranchLocationField)
    simpa only [Polynomial.map_zero] using h
  intro he
  have hdiv := AdjoinRoot.mk_eq_zero.mp he
  have hle := natDegree_le_of_dvd hdiv hm
  rw [branchGenericLocationSextic_fraction_natDegree] at hle
  change 6 ≤ (p.map (algebraMap BranchLocationParameters BranchLocationField)).natDegree at hle
  have hmap : (p.map (algebraMap BranchLocationParameters BranchLocationField)).natDegree ≤
      p.natDegree := natDegree_map_le
  omega

/-- The polynomial denominator over the three independent parameters. -/
def branchGenericDenominator : BranchLocationParameters[X] :=
  branchLocationDenominator (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)

/-- The polynomial numerator over the three independent parameters. -/
def branchGenericNumerator : BranchLocationParameters[X] :=
  branchLocationNumerator (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)

private lemma branchLocationEvaluation_X_ne_zero : branchLocationEvaluation X ≠ 0 := by
  apply branchLocationEvaluation_ne_zero
  · simp
  · simp

private lemma branchLocationEvaluation_X_sub_one_ne_zero :
    branchLocationEvaluation (X - 1) ≠ 0 := by
  apply branchLocationEvaluation_ne_zero
  · compute_degree
    norm_num
  · simpa using (Polynomial.X_sub_C_ne_zero (1 : ℚ))

lemma branchGenericDenominator_ne_zero :
    branchLocationEvaluation branchGenericDenominator ≠ 0 := by
  apply branchLocationEvaluation_ne_zero
  · unfold branchGenericDenominator branchLocationDenominator
    compute_degree
    norm_num
  · intro h
    have := congrArg (fun p : ℚ[X] => p.coeff 0) h
    norm_num [branchGenericDenominator, branchLocationDenominator, map_ofNat] at this

lemma branchGenericNumerator_ne_zero :
    branchLocationEvaluation branchGenericNumerator ≠ 0 := by
  apply branchLocationEvaluation_ne_zero
  · unfold branchGenericNumerator branchLocationNumerator
    compute_degree
    norm_num
  · intro h
    have := congrArg (fun p : ℚ[X] => p.coeff 0) h
    norm_num [branchGenericNumerator, branchLocationNumerator, map_ofNat] at this

private lemma branchGenericNumerator_add_denominator_ne_zero :
    branchLocationEvaluation (branchGenericNumerator + branchGenericDenominator) ≠ 0 := by
  apply branchLocationEvaluation_ne_zero
  · unfold branchGenericNumerator branchGenericDenominator
    unfold branchLocationNumerator branchLocationDenominator
    compute_degree
    norm_num
  · intro h
    have := congrArg (fun p : ℚ[X] => p.coeff 0) h
    norm_num [branchGenericNumerator, branchGenericDenominator, branchLocationNumerator,
      branchLocationDenominator, map_ofNat] at this

private lemma branchGenericNumerator_add_X_denominator_ne_zero :
    branchLocationEvaluation (branchGenericNumerator + X * branchGenericDenominator) ≠ 0 := by
  apply branchLocationEvaluation_ne_zero
  · unfold branchGenericNumerator branchGenericDenominator
    unfold branchLocationNumerator branchLocationDenominator
    compute_degree
    norm_num
  · intro h
    have := congrArg (fun p : ℚ[X] => p.coeff 0) h
    norm_num [branchGenericNumerator, branchGenericDenominator, branchLocationNumerator,
      branchLocationDenominator, map_ofNat] at this

/-- The reconstructed third location in the generic sextic field. -/
def branchGenericThirdLocation : BranchLocationExtension :=
  -branchLocationEvaluation branchGenericNumerator /
    branchLocationEvaluation branchGenericDenominator

/-- The Vandermonde factor governing the quadratic branch sign. -/
def branchGenericDelta : BranchLocationExtension :=
  let t := branchLocationEvaluation X
  let y := branchGenericThirdLocation
  t * y * (t - 1) * (y - 1) * (y - t)

/-- None of the five factors in the branch-sign invariant vanishes generically. -/
theorem branchGenericDelta_ne_zero : branchGenericDelta ≠ 0 := by
  have ht := branchLocationEvaluation_X_ne_zero
  have ht1 : branchLocationEvaluation X - 1 ≠ 0 := by
    simpa only [map_sub, map_one] using branchLocationEvaluation_X_sub_one_ne_zero
  have hy : branchGenericThirdLocation ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr branchGenericNumerator_ne_zero) branchGenericDenominator_ne_zero
  have hy1 : branchGenericThirdLocation ≠ 1 := by
    intro he
    have h := (div_eq_iff branchGenericDenominator_ne_zero).mp he
    apply branchGenericNumerator_add_denominator_ne_zero
    rw [map_add]
    linear_combination -h
  have hyt : branchGenericThirdLocation ≠ branchLocationEvaluation X := by
    intro he
    have h := (div_eq_iff branchGenericDenominator_ne_zero).mp he
    apply branchGenericNumerator_add_X_denominator_ne_zero
    rw [map_add, map_mul]
    linear_combination -h
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ht hy) ht1)
    (sub_ne_zero.mpr hy1)) (sub_ne_zero.mpr hyt)

/-- A normalized coefficient viewed in the generic location field. -/
def branchGenericCoefficient (i : Fin 3) : BranchLocationExtension :=
  branchLocationEvaluation (C (MvPolynomial.X i))

open scoped RatFunc
attribute [local instance] Polynomial.algebra

/-- For every nonzero rational dividend, the reconstructed generic location and branch
sign give a field of degree twelve over `ℚ(c₁,c₂,c₃)(A)`.
This does not yet identify `t + β` as a primitive element or count specializations. -/
theorem branchGenericSignExtension_field_degree (a : ℚ) (ha : a ≠ 0) :
    IsField (AdjoinRoot (branchSignPolynomial
      (algebraMap ℚ BranchLocationExtension a) branchGenericDelta)) ∧
    Module.finrank (RatFunc BranchLocationField) (AdjoinRoot (branchSignPolynomial
      (algebraMap ℚ BranchLocationExtension a) branchGenericDelta)) = 12 := by
  have haa : algebraMap ℚ BranchLocationExtension a ≠ 0 :=
    by simpa only [map_zero] using (algebraMap ℚ BranchLocationExtension).injective.ne ha
  let : FiniteDimensional BranchLocationField BranchLocationExtension :=
    Module.finite_of_finrank_pos (by rw [branchLocationExtension_finrank]; norm_num)
  exact ⟨branchSignExtension_isField haa branchGenericDelta_ne_zero,
    branchSignTower_finrank branchLocationExtension_finrank _ _⟩

end
end PierceLengthBound.FixedDividend
