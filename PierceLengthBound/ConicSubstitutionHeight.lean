/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib

/-! Uniform integer coefficient bounds for fixed polynomial constructions under
bounded quadratic substitution. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial Finset

lemma integer_polynomial_mul_height {F G : Polynomial ℤ} {d e H K : ℕ}
    (hF : F.natDegree ≤ d) (hG : G.natDegree ≤ e)
    (hFH : ∀ n, |F.coeff n| ≤ H) (hGK : ∀ n, |G.coeff n| ≤ K) :
    ∀ n, |(F * G).coeff n| ≤ ((d + e + 1) * H * K : ℕ) := by
  intro n
  by_cases hn : n ≤ d + e
  · rw [coeff_mul]
    calc
      |∑ x ∈ antidiagonal n, F.coeff x.1 * G.coeff x.2| ≤
          ∑ x ∈ antidiagonal n, |F.coeff x.1 * G.coeff x.2| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ antidiagonal n, (H : ℤ) * K := by
        apply sum_le_sum
        intro x hx
        rw [abs_mul]
        exact mul_le_mul (hFH _) (hGK _) (abs_nonneg _) (Nat.cast_nonneg _)
      _ = (n + 1 : ℕ) * (H : ℤ) * K := by simp [mul_assoc]
      _ ≤ ((d + e + 1) * H * K : ℕ) := by
        push_cast
        gcongr
        exact_mod_cast hn
  · rw [coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt (by omega)), abs_zero]
    positivity

/-- A fixed multivariate integer polynomial evaluated on bounded quadratic
integer polynomials has a uniform polynomial coefficient-height bound.
The constants depend only on the fixed expression. -/
theorem fixed_polynomial_substitution_height {σ : Type*}
    (f : MvPolynomial σ ℤ) :
    ∃ d C e : ℕ, 1 ≤ C ∧ ∀ (H : ℕ), 1 ≤ H → ∀ z : σ → Polynomial ℤ,
      (∀ j, (z j).natDegree ≤ 2) → (∀ j n, |(z j).coeff n| ≤ H) →
      (MvPolynomial.eval₂ Polynomial.C z f).natDegree ≤ d ∧
        ∀ n, |(MvPolynomial.eval₂ Polynomial.C z f).coeff n| ≤ (C * H ^ e : ℕ) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, a.natAbs + 1, 0, by omega, ?_⟩
    intro H hH z hzd hzc
    simp only [MvPolynomial.eval₂_C, natDegree_C]
    refine ⟨le_rfl, ?_⟩
    intro n
    by_cases hn : n = 0
    · subst n
      simp only [coeff_C_zero, pow_zero, mul_one]
      rw [Int.abs_eq_natAbs]
      exact_mod_cast Nat.le_succ a.natAbs
    · rw [coeff_C, ite_eq_right hn, abs_zero]
      positivity
  | add f g ihf ihg =>
    obtain ⟨d, C, e, hC, hf⟩ := ihf
    obtain ⟨d', C', e', hC', hg⟩ := ihg
    refine ⟨max d d', C + C', e + e', by omega, ?_⟩
    intro H hH z hzd hzc
    obtain ⟨hfd, hfc⟩ := hf H hH z hzd hzc
    obtain ⟨hgd, hgc⟩ := hg H hH z hzd hzc
    rw [MvPolynomial.eval₂_add]
    refine ⟨natDegree_add_le_of_le hfd hgd, ?_⟩
    intro n
    have he : H ^ e ≤ H ^ (e + e') := Nat.pow_le_pow_right hH (by omega)
    have he' : H ^ e' ≤ H ^ (e + e') := Nat.pow_le_pow_right hH (by omega)
    rw [coeff_add]
    calc |(MvPolynomial.eval₂ Polynomial.C z f).coeff n +
        (MvPolynomial.eval₂ Polynomial.C z g).coeff n| ≤
        |(MvPolynomial.eval₂ Polynomial.C z f).coeff n| +
          |(MvPolynomial.eval₂ Polynomial.C z g).coeff n| := abs_add_le _ _
      _ ≤ (C * H ^ e : ℕ) + (C' * H ^ e' : ℕ) := add_le_add (hfc n) (hgc n)
      _ ≤ ((C + C') * H ^ (e + e') : ℕ) := by
        exact_mod_cast (show C * H ^ e + C' * H ^ e' ≤ (C + C') * H ^ (e + e') by
          nlinarith [Nat.mul_le_mul_left C he, Nat.mul_le_mul_left C' he'])
  | mul_X f j ih =>
    obtain ⟨d, C, e, hC, hf⟩ := ih
    refine ⟨d + 2, (d + 3) * C, e + 1, by nlinarith, ?_⟩
    intro H hH z hzd hzc
    obtain ⟨hfd, hfc⟩ := hf H hH z hzd hzc
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    refine ⟨natDegree_mul_le.trans (Nat.add_le_add hfd (hzd j)), ?_⟩
    intro n
    have h := integer_polynomial_mul_height hfd (hzd j) hfc (hzc j) n
    convert h using 1
    push_cast
    ring

end
end PierceLengthBound.FixedDividend
