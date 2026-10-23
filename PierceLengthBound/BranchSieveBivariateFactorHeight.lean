/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveFactorHeight
public import PierceLengthBound.BranchSieveShear
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import CCDN.Height.PolynomialBoxHeight
import Mathlib.Tactic

/-! Height control for integer factors of bivariate polynomials, reduced to
the univariate Mahler-measure bound by an injective Kronecker substitution. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Finset

theorem branchKroneckerHom_coeff_abs_le (p : MvPolynomial (Fin 2) ℤ)
    {H : ℕ} (hH : ∀ s, |p.coeff s| ≤ (H : ℤ)) (e j : ℕ) :
    |(branchKroneckerHom e p).coeff j| ≤ (p.support.card * H : ℕ) := by
  classical
  conv_lhs => rw [p.as_sum, map_sum, Polynomial.finsetSum_coeff]
  calc
    |∑ s ∈ p.support, (branchKroneckerHom e (monomial s (p.coeff s))).coeff j|
      ≤ ∑ s ∈ p.support, |(branchKroneckerHom e (monomial s (p.coeff s))).coeff j| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ p.support, (H : ℤ) := by
      apply sum_le_sum
      intro s _
      rw [branchKroneckerHom_monomial, Polynomial.coeff_monomial]
      split_ifs
      · exact hH s
      · simp only [abs_zero]; positivity
    _ = _ := by simp

theorem branchKroneckerHom_ne_zero {p : MvPolynomial (Fin 2) ℤ}
    (hp : p ≠ 0) {e : ℕ} (he : p.degreeOf 0 < e) : branchKroneckerHom e p ≠ 0 := by
  classical
  obtain ⟨s, hs⟩ := MvPolynomial.support_nonempty.mpr hp
  intro hz
  have hc := branchKroneckerHom_coeff he hs
  rw [hz, Polynomial.coeff_zero] at hc
  exact (MvPolynomial.mem_support_iff.mp hs) hc.symm

theorem branchKroneckerHom_natDegree_upper (p : MvPolynomial (Fin 2) ℤ)
    {e : ℕ} (he : 1 ≤ e) :
    (branchKroneckerHom e p).natDegree ≤ e * p.totalDegree := by
  rw [← branchAxisHom_shear]
  exact (branchAxisHom_natDegree_le _).trans (branchPowerShear_totalDegree_upper p he 1)

/-- For fixed total degree, the height of any integer bivariate factor is
bounded by a constant times the original coefficient height. -/
theorem branch_bivariate_factor_coeff_height (p : MvPolynomial (Fin 2) ℤ)
    (hp : p ≠ 0) {d H : ℕ} (hd : p.totalDegree ≤ d)
    (hH : ∀ s, |p.coeff s| ≤ (H : ℤ))
    (q : MvPolynomial (Fin 2) ℤ) (hdiv : q ∣ p) (s : Fin 2 →₀ ℕ) :
    |q.coeff s| ≤
      (2 ^ ((d + 1) * d) * ((d + 1) * d + 1) * ((d + 1) ^ 2 * H) : ℕ) := by
  classical
  by_cases hs : s ∈ q.support
  · obtain ⟨r, hr⟩ := hdiv
    have hq : q ≠ 0 := by intro hz; apply hp; simp [hr, hz]
    have hrne : r ≠ 0 := by intro hz; apply hp; simp [hr, hz]
    have hpd : p.degreeOf 0 < d + 1 :=
      Nat.lt_succ_of_le ((degreeOf_le_totalDegree p 0).trans hd)
    have hqd : q.degreeOf 0 < d + 1 := by
      have hadd : p.degreeOf 0 = q.degreeOf 0 + r.degreeOf 0 := by
        rw [hr, degreeOf_mul_eq hq hrne]
      omega
    have hcard : p.support.card ≤ (d + 1) ^ 2 := by
      apply (CCDN.polynomial_support_card_le p).trans
      simpa using Nat.pow_le_pow_left (Nat.add_le_add_right hd 1) 2
    have hheight : ∀ j, |(branchKroneckerHom (d + 1) p).coeff j| ≤
        ((d + 1) ^ 2 * H : ℕ) := by
      intro j
      apply (branchKroneckerHom_coeff_abs_le p hH (d + 1) j).trans
      exact_mod_cast Nat.mul_le_mul_right H hcard
    have hbound := branch_integer_factor_coeff_height
      (branchKroneckerHom (d + 1) p) (branchKroneckerHom_ne_zero hp hpd)
      ((branchKroneckerHom_natDegree_upper p (by omega : 1 ≤ d + 1)).trans
        (Nat.mul_le_mul_left (d + 1) hd)) hheight
      (branchKroneckerHom (d + 1) q) (map_dvd (branchKroneckerHom (d + 1)) ⟨r, hr⟩)
      (s 0 + (d + 1) * s 1)
    simpa only [branchKroneckerHom_coeff hqd hs] using hbound
  · rw [MvPolynomial.notMem_support_iff.mp hs, abs_zero]
    positivity

end
end PierceLengthBound.FixedDividend
