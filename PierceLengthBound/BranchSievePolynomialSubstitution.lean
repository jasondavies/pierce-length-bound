/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Uniform degree and height control under substitution into a fixed integer
polynomial. The constants depend on that fixed polynomial and on the input
degree bound, and the height bound is polynomial in the input height. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

/-- A sum of terms each bounded by `M` in absolute value is bounded by
the number of terms times `M`. -/
theorem branch_abs_sum_le_card_mul {ι : Type*} (s : Finset ι) (f : ι → ℤ) {M : ℤ}
    (h : ∀ i ∈ s, |f i| ≤ M) : |∑ i ∈ s, f i| ≤ s.card * M :=
  (abs_sum_le_sum_abs _ _).trans ((sum_le_sum h).trans_eq (by simp))

/-- The coefficient height of a product is at most `(m+n+1) A B`. -/
theorem branch_polynomial_mul_coeff_height (p q : Polynomial ℤ) {m n A B : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n)
    (hA : ∀ j, |p.coeff j| ≤ (A : ℤ)) (hB : ∀ j, |q.coeff j| ≤ (B : ℤ)) (j : ℕ) :
    |(p * q).coeff j| ≤ ((m + n + 1) * A * B : ℕ) := by
  by_cases hj : j ≤ m + n
  · rw [Polynomial.coeff_mul]
    refine (branch_abs_sum_le_card_mul _ _ (M := (A : ℤ) * B) fun ij _ => ?_).trans ?_
    · rw [abs_mul]
      exact mul_le_mul (hA _) (hB _) (by positivity) (by positivity)
    · rw [Finset.Nat.card_antidiagonal, mul_assoc (m + n + 1) A B]
      exact_mod_cast Nat.mul_le_mul_right (A * B) (by omega : j + 1 ≤ m + n + 1)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      ((Polynomial.natDegree_mul_le.trans (Nat.add_le_add hp hq)).trans_lt (by omega)), abs_zero]
    positivity

/-- Substituting polynomials of degree at most `D` and height at most `H` into a
fixed integer polynomial gives degree at most `M` and height at most
`C (H+1)^E`, with `M`, `E`, `C` independent of `H`. -/
theorem branch_fixed_polynomial_substitution_bound {σ : Type*}
    (P : MvPolynomial σ ℤ) (D : ℕ) :
    ∃ M E C : ℕ, 0 < C ∧ ∀ (H : ℕ) (v : σ → Polynomial ℤ),
      (∀ i, (v i).natDegree ≤ D) → (∀ i j, |(v i).coeff j| ≤ (H : ℤ)) →
      (MvPolynomial.eval₂ Polynomial.C v P).natDegree ≤ M ∧
      ∀ j, |(MvPolynomial.eval₂ Polynomial.C v P).coeff j| ≤ (C * (H + 1) ^ E : ℕ) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, 0, a.natAbs + 1, by omega, ?_⟩
    intro H v _hv _hH
    simp only [MvPolynomial.eval₂_C, Polynomial.natDegree_C, le_refl, true_and]
    intro j
    rw [Polynomial.coeff_C]
    split_ifs
    · simpa only [pow_zero, mul_one, Nat.cast_add, Int.natCast_natAbs, Nat.cast_one] using
        (show |a| ≤ |a| + 1 by omega)
    · simp only [abs_zero]; positivity
  | add P Q ihP ihQ =>
    obtain ⟨M₁, E₁, C₁, hC₁, hP⟩ := ihP
    obtain ⟨M₂, E₂, C₂, hC₂, hQ⟩ := ihQ
    refine ⟨max M₁ M₂, E₁ + E₂, C₁ + C₂, by omega, ?_⟩
    intro H v hv hH
    obtain ⟨hPd, hPh⟩ := hP H v hv hH
    obtain ⟨hQd, hQh⟩ := hQ H v hv hH
    rw [MvPolynomial.eval₂_add]
    refine ⟨(Polynomial.natDegree_add_le _ _).trans (max_le_max hPd hQd), ?_⟩
    intro j
    rw [Polynomial.coeff_add]
    apply (abs_add_le _ _).trans ((add_le_add (hPh j) (hQh j)).trans ?_)
    have hE₁ : (H + 1) ^ E₁ ≤ (H + 1) ^ (E₁ + E₂) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hE₂ : (H + 1) ^ E₂ ≤ (H + 1) ^ (E₁ + E₂) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hh : C₁ * (H + 1) ^ E₁ + C₂ * (H + 1) ^ E₂ ≤
        (C₁ + C₂) * (H + 1) ^ (E₁ + E₂) := by
      simpa only [add_mul] using
        Nat.add_le_add (Nat.mul_le_mul_left C₁ hE₁) (Nat.mul_le_mul_left C₂ hE₂)
    exact_mod_cast hh
  | mul_X P i ih =>
    obtain ⟨M, E, C, hC, hP⟩ := ih
    refine ⟨M + D, E + 1, (M + D + 1) * C, by positivity, ?_⟩
    intro H v hv hH
    obtain ⟨hPd, hPh⟩ := hP H v hv hH
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    refine ⟨Polynomial.natDegree_mul_le.trans (Nat.add_le_add hPd (hv i)), ?_⟩
    intro j
    apply (branch_polynomial_mul_coeff_height _ _ hPd (hv i) hPh (hH i) j).trans
    have hh : (M + D + 1) * (C * (H + 1) ^ E) * H ≤
        ((M + D + 1) * C) * (H + 1) ^ (E + 1) := by
      rw [pow_succ]
      calc
        _ ≤ (M + D + 1) * (C * (H + 1) ^ E) * (H + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        _ = _ := by ring
    exact_mod_cast hh

end
end PierceLengthBound.FixedDividend
