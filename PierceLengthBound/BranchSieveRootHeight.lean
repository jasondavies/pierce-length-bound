/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Tactic

/-! Height bounds for integral roots in the one-parameter arithmetic sieve.
These estimates bound the initially unbounded root coordinate before the
degree-raising shear is applied. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial Finset NNReal
open scoped Polynomial.Bivariate

/-- An integral polynomial with coefficients bounded by `H` has all its
integer roots in the interval `[-H-1,H+1]`. -/
theorem branch_integer_root_abs_le {p : ℤ[X]} (hp : p ≠ 0) {H : ℕ}
    (hcoeff : ∀ j, |p.coeff j| ≤ (H : ℤ)) {y : ℤ} (hy : p.eval y = 0) :
    |y| ≤ (H : ℤ) + 1 := by
  let q : ℝ[X] := p.map (Int.castRingHom ℝ)
  have hq : q ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hp
  have hroot : q.IsRoot (y : ℝ) := by
    change (p.map (Int.castRingHom ℝ)).eval ((Int.castRingHom ℝ) y) = 0
    rw [eval_map_apply, hy, map_zero]
  have hcoeffq : ∀ j, ‖q.coeff j‖₊ ≤ (H : ℝ≥0) := by
    intro j
    apply NNReal.coe_le_coe.mp
    simp only [q, coeff_map, coe_nnnorm, NNReal.coe_natCast,
      Real.norm_eq_abs]
    change |(p.coeff j : ℝ)| ≤ (H : ℝ)
    exact_mod_cast hcoeff j
  have hlc : (1 : ℝ≥0) ≤ ‖q.leadingCoeff‖₊ := by
    have hz : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
    have habs : (1 : ℤ) ≤ |p.leadingCoeff| := Int.one_le_abs hz
    rw [show q.leadingCoeff = (p.leadingCoeff : ℝ) from leadingCoeff_map_of_injective
      Int.cast_injective p]
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_one, coe_nnnorm, Real.norm_eq_abs]
    exact_mod_cast habs
  have hb : q.cauchyBound ≤ (H : ℝ≥0) + 1 := by
    rw [cauchyBound]
    apply add_le_add (b := (H : ℝ≥0)) ?_ le_rfl
    exact (div_le_self (by positivity) hlc).trans (Finset.sup_le fun j _ => hcoeffq j)
  have hr := (hroot.norm_lt_cauchyBound hq).le.trans hb
  have hr' := NNReal.coe_le_coe.mpr hr
  simp only [coe_nnnorm, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one,
    Real.norm_eq_abs] at hr'
  exact_mod_cast hr'

/-- Evaluation in an integer interval preserves an explicit coefficient-height bound. -/
theorem branch_integer_polynomial_eval_abs_le (p : ℤ[X]) {d H B : ℕ}
    (hd : p.natDegree ≤ d) (hH : ∀ j, |p.coeff j| ≤ (H : ℤ))
    (hB : 1 ≤ B) {t : ℤ} (ht : |t| ≤ (B : ℤ)) :
    |p.eval t| ≤ ((d + 1) * H * B ^ d : ℕ) := by
  rw [eval_eq_sum_range' (by omega : p.natDegree < d + 1)]
  calc
    |∑ j ∈ range (d + 1), p.coeff j * t ^ j|
        ≤ ∑ j ∈ range (d + 1), |p.coeff j * t ^ j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range (d + 1), (H : ℤ) * (B : ℤ) ^ d := by
      apply sum_le_sum
      intro j hj
      rw [abs_mul, abs_pow]
      apply mul_le_mul (hH j) ?_ (by positivity) (by positivity)
      exact (pow_le_pow_left₀ (abs_nonneg t) ht j).trans
        (pow_le_pow_right₀ (by exact_mod_cast hB)
          (by simpa using Nat.le_of_lt_succ (mem_range.mp hj)))
    _ = _ := by simp; ring

/-- Outside the leading-coefficient zero set, an integral root of the specialized
bivariate polynomial has controlled height. All constants are displayed. -/
theorem branch_specialization_root_abs_le (p : ℤ[X][Y]) {d H B : ℕ}
    (hd : ∀ i, (p.coeff i).natDegree ≤ d)
    (hH : ∀ i j, |(p.coeff i).coeff j| ≤ (H : ℤ))
    (hB : 1 ≤ B) {t y : ℤ} (ht : |t| ≤ (B : ℤ))
    (hlead : p.leadingCoeff.eval t ≠ 0) (hy : p.evalEval t y = 0) :
    |y| ≤ ((d + 1) * H * B ^ d : ℕ) + 1 := by
  let q : ℤ[X] := p.map (evalRingHom t)
  have hq : q ≠ 0 := by
    intro hz
    have hh := congrArg (fun f : ℤ[X] => f.coeff p.natDegree) hz
    apply hlead
    simpa only [q, coeff_map, coeff_natDegree, coeff_zero, coe_evalRingHom] using hh
  apply branch_integer_root_abs_le hq
  · intro j
    simpa only [q, coeff_map, coe_evalRingHom] using
      branch_integer_polynomial_eval_abs_le (p.coeff j) (hd j) (hH j) hB ht
  · simpa only [q, eval_map, eval₂_evalRingHom] using hy

end
end PierceLengthBound.FixedDividend
