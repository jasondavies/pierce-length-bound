/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.NumberTheory.MahlerMeasure
public import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-! A coefficient-height bound for integer polynomial factors. The bound
depends only on the original degree and coefficient height. It is needed
when the universal factor-resolvent polynomial is split into irreducible
components before applying the integral-root count. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial Finset

theorem branch_integer_polynomial_mahlerMeasure_le (p : ℤ[X]) {d H : ℕ}
    (hd : p.natDegree ≤ d) (hH : ∀ j, |p.coeff j| ≤ (H : ℤ)) :
    (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ ((d + 1) * H : ℕ) := by
  let q := p.map (Int.castRingHom ℂ)
  have hdegree : q.natDegree ≤ d := (natDegree_map_le.trans hd)
  apply (mahlerMeasure_le_sum_norm_coeff q).trans
  rw [Polynomial.sum_over_range' q (by simp : ∀ n : ℕ, ‖(0 : ℂ)‖ = 0)
    (d + 1) (by omega : q.natDegree < d + 1)]
  calc
    ∑ j ∈ range (d + 1), ‖q.coeff j‖ ≤ ∑ _j ∈ range (d + 1), (H : ℝ) := by
      apply sum_le_sum
      intro j _
      have hh : ‖q.coeff j‖ = (|p.coeff j| : ℤ) := by
        simp [q, Complex.norm_intCast]
      rw [hh]
      exact_mod_cast hH j
    _ = _ := by simp

/-- An integer factor has coefficient height at most `2^d (d+1) H`. -/
theorem branch_integer_factor_coeff_height (p : ℤ[X]) (hp : p ≠ 0) {d H : ℕ}
    (hd : p.natDegree ≤ d) (hH : ∀ j, |p.coeff j| ≤ (H : ℤ))
    (q : ℤ[X]) (hdiv : q ∣ p) (j : ℕ) :
    |q.coeff j| ≤ (2 ^ d * (d + 1) * H : ℕ) := by
  obtain ⟨r, hr⟩ := hdiv
  have hrne : r ≠ 0 := by intro hz; apply hp; simp [hr, hz]
  have hqd : q.natDegree ≤ d :=
    (natDegree_le_of_dvd ⟨r, hr⟩ hp).trans hd
  have hm := norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure j
    (q.map (Int.castRingHom ℂ)) (r.map (Int.castRingHom ℂ))
    (one_le_mahlerMeasure_of_ne_zero hrne)
  rw [← Polynomial.map_mul, ← hr] at hm
  have hchoose : (q.map (Int.castRingHom ℂ)).natDegree.choose j ≤ 2 ^ d :=
    (Nat.choose_le_two_pow _ _).trans
      (Nat.pow_le_pow_right (by norm_num) (natDegree_map_le.trans hqd))
  have hbound := mul_le_mul (show
      (((q.map (Int.castRingHom ℂ)).natDegree.choose j : ℕ) : ℝ) ≤ (2 ^ d : ℕ) by
        exact_mod_cast hchoose)
    (branch_integer_polynomial_mahlerMeasure_le p hd hH)
    (mahlerMeasure_nonneg _) (by positivity)
  have hfinal := hm.trans hbound
  have hnorm : ‖(q.map (Int.castRingHom ℂ)).coeff j‖ = (|q.coeff j| : ℤ) := by
    simp [Complex.norm_intCast]
  rw [hnorm] at hfinal
  rw [mul_assoc (2 ^ d) (d + 1) H]
  exact_mod_cast hfinal

end
end PierceLengthBound.FixedDividend
