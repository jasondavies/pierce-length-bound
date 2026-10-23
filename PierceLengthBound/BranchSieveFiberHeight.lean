/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveRootHeight
public import PierceLengthBound.BranchSieveShear
import Mathlib.Tactic

/-! Coefficient and integer-root height control for a fiber of an actual
two-variable integer polynomial. These bounds use the original coefficient
height, before the power shear raises the total degree. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Finset

def branchFiberPolynomial (t : ℤ) : MvPolynomial (Fin 2) ℤ →+* Polynomial ℤ :=
  eval₂Hom Polynomial.C ![Polynomial.C t, Polynomial.X]

lemma branchFiberPolynomial_monomial (t : ℤ) (s : Fin 2 →₀ ℕ) (c : ℤ) :
    branchFiberPolynomial t (monomial s c) = Polynomial.monomial (s 1) (c * t ^ s 0) := by
  simp only [branchFiberPolynomial, coe_eval₂Hom, eval₂_monomial]
  rw [Finsupp.prod_fintype _ _ (by simp)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, ← Polynomial.C_pow,
    Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul_monomial]

lemma branchFiberPolynomial_eval (p : MvPolynomial (Fin 2) ℤ) (t y : ℤ) :
    (branchFiberPolynomial t p).eval y = eval ![t, y] p := by
  have hh : (Polynomial.evalRingHom y).comp (branchFiberPolynomial t) = eval ![t, y] := by
    ext i
    · simp [branchFiberPolynomial]
    · fin_cases i <;> simp [branchFiberPolynomial]
  exact DFunLike.congr_fun hh p

/-- Every fiber coefficient is bounded by the number of original monomials
times their maximum possible specialized size. -/
theorem branchFiberPolynomial_coeff_abs_le (p : MvPolynomial (Fin 2) ℤ)
    {H B : ℕ} (hH : ∀ s, |p.coeff s| ≤ (H : ℤ)) (hB : 1 ≤ B)
    {t : ℤ} (ht : |t| ≤ (B : ℤ)) (j : ℕ) :
    |(branchFiberPolynomial t p).coeff j| ≤
      (p.support.card * H * B ^ p.degreeOf 0 : ℕ) := by
  classical
  conv_lhs => rw [p.as_sum, map_sum, Polynomial.finsetSum_coeff]
  calc
    |∑ s ∈ p.support, (branchFiberPolynomial t (monomial s (p.coeff s))).coeff j|
        ≤ ∑ s ∈ p.support, |(branchFiberPolynomial t (monomial s (p.coeff s))).coeff j| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ p.support, (H : ℤ) * (B : ℤ) ^ p.degreeOf 0 := by
      apply sum_le_sum
      intro s hs
      rw [branchFiberPolynomial_monomial, Polynomial.coeff_monomial]
      split_ifs
      · rw [abs_mul, abs_pow]
        apply mul_le_mul (hH s) ?_ (by positivity) (by positivity)
        exact (pow_le_pow_left₀ (abs_nonneg t) ht _).trans
          (pow_le_pow_right₀ (by exact_mod_cast hB) (le_degreeOf_of_mem_support 0 hs))
      · simp only [abs_zero]; positivity
    _ = _ := by simp; ring

/-- Integral roots of nonzero fibers have height controlled by the original
coefficient height and parameter interval. -/
theorem branchFiberPolynomial_root_abs_le (p : MvPolynomial (Fin 2) ℤ)
    {H B : ℕ} (hH : ∀ s, |p.coeff s| ≤ (H : ℤ)) (hB : 1 ≤ B)
    {t y : ℤ} (ht : |t| ≤ (B : ℤ))
    (htnz : branchFiberPolynomial t p ≠ 0) (hy : eval ![t, y] p = 0) :
    |y| ≤ (p.support.card * H * B ^ p.degreeOf 0 : ℕ) + 1 :=
  branch_integer_root_abs_le htnz (branchFiberPolynomial_coeff_abs_le p hH hB ht)
    (by simpa only [branchFiberPolynomial_eval] using hy)

/-- The sheared root lies in one explicit box whenever the shear exponent
dominates the parameter degree. -/
theorem branchFiberPolynomial_sheared_root_abs_le (p : MvPolynomial (Fin 2) ℤ)
    {H B e : ℕ} (hH : ∀ s, |p.coeff s| ≤ (H : ℤ)) (hB : 1 ≤ B)
    (he : p.degreeOf 0 ≤ e) {t y : ℤ} (ht : |t| ≤ (B : ℤ))
    (htnz : branchFiberPolynomial t p ≠ 0) (hy : eval ![t, y] p = 0) :
    |y - t ^ e| ≤ ((p.support.card * H + 2) * B ^ e : ℕ) := by
  have hybound := branchFiberPolynomial_root_abs_le p hH hB ht htnz hy
  have hp : (B : ℤ) ^ p.degreeOf 0 ≤ (B : ℤ) ^ e :=
    pow_le_pow_right₀ (by exact_mod_cast hB) he
  have hpone : (1 : ℤ) ≤ (B : ℤ) ^ e := one_le_pow₀ (by exact_mod_cast hB)
  calc
    |y - t ^ e| ≤ |y| + |t ^ e| := abs_sub _ _
    _ ≤ ((p.support.card * H * B ^ p.degreeOf 0 : ℕ) : ℤ) + 1 + (B : ℤ) ^ e := by
      gcongr
      simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg t) ht e
    _ ≤ ((p.support.card * H + 2) * B ^ e : ℕ) := by
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (p.support.card : ℤ) * H)]

end
end PierceLengthBound.FixedDividend
