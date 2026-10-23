/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveFactorHeight
public import PierceLengthBound.BranchSieveShear
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic

/-! Height control for integer factors of bivariate polynomials, reduced to
the univariate Mahler-measure bound by an injective Kronecker substitution. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Finset

/-- The two-variable Kronecker substitution with radix `e ≥ 1` has degree at
most `e` times the total degree. -/
theorem branchMultiKronecker_two_natDegree_le (p : MvPolynomial (Fin 2) ℤ)
    {e : ℕ} (he : 1 ≤ e) :
    (branchMultiKronecker e 2 p).natDegree ≤ e * p.totalDegree := by
  rw [← branchAxisHom_shear]
  exact (branchAxisHom_natDegree_le _).trans (branchPowerShear_totalDegree_upper p he 1)

/-- Every coefficient of an integer factor of a bivariate `p` of total degree
at most `d` and height at most `H` is bounded by
`2^((d+1)d) ((d+1)d+1) (d+1)² H`. -/
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
    have hpd (i) : p.degreeOf i < d + 1 :=
      Nat.lt_succ_of_le ((degreeOf_le_totalDegree p i).trans hd)
    have hqd : q.degreeOf 0 < d + 1 := by
      have hadd : p.degreeOf 0 = q.degreeOf 0 + r.degreeOf 0 := by
        rw [hr, degreeOf_mul_eq hq hrne]
      have := hpd 0
      omega
    have hheight : ∀ j, |(branchMultiKronecker (d + 1) 2 p).coeff j| ≤
        ((d + 1) ^ 2 * H : ℕ) := by
      intro j
      obtain hz | ⟨t, _, ht⟩ := branchMultiKronecker_coefficient_cases p hpd j
      · rw [hz, abs_zero]; positivity
      · rw [ht]
        exact (hH t).trans (by exact_mod_cast Nat.le_mul_of_pos_left H (by positivity))
    have hbound := branch_integer_factor_coeff_height
      (branchMultiKronecker (d + 1) 2 p) (branchMultiKronecker_ne_zero hp hpd)
      ((branchMultiKronecker_two_natDegree_le p (by omega : 1 ≤ d + 1)).trans
        (Nat.mul_le_mul_left (d + 1) hd)) hheight
      (branchMultiKronecker (d + 1) 2 q) (map_dvd (branchMultiKronecker (d + 1) 2) ⟨r, hr⟩)
      (s 0 + (d + 1) * s 1)
    simpa only [branchMultiKronecker_two_coeff hqd hs] using hbound
  · rw [MvPolynomial.notMem_support_iff.mp hs, abs_zero]
    positivity

end
end PierceLengthBound.FixedDividend
