/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSievePolynomialSubstitution
public import CCDN.Noether.BivariateTotalDegree
import Mathlib.Tactic

/-! Uniform bounds for a fixed polynomial whose coefficients are polynomial
expressions in a bounded-degree integer polynomial family. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial Finset

theorem branch_fixed_resolvent_substitution_bound {σ : Type*}
    (Q : Polynomial (MvPolynomial σ ℤ)) (D : ℕ) :
    ∃ M E C : ℕ, 0 < C ∧ ∀ (H : ℕ) (v : σ → Polynomial ℤ),
      (∀ i, (v i).natDegree ≤ D) → (∀ i j, |(v i).coeff j| ≤ (H : ℤ)) →
      CCDN.bivariateTotalDegree
        (Q.map (MvPolynomial.eval₂Hom Polynomial.C v)) ≤ M ∧
      ∀ i j, |((Q.map (MvPolynomial.eval₂Hom Polynomial.C v)).coeff i).coeff j| ≤
        (C * (H + 1) ^ E : ℕ) := by
  classical
  have hex (i : Fin (Q.natDegree + 1)) :=
    branch_fixed_polynomial_substitution_bound (Q.coeff i) D
  choose m e c hc hb using hex
  let M := univ.sup m
  let E := univ.sup e
  let C := univ.sup c + 1
  refine ⟨Q.natDegree + M, E, C, by dsimp [C]; omega, ?_⟩
  intro H v hv hH
  have hcoeff (i j : ℕ) :
      |((Q.map (MvPolynomial.eval₂Hom Polynomial.C v)).coeff i).coeff j| ≤
        (C * (H + 1) ^ E : ℕ) := by
    rw [coeff_map]
    by_cases hi : i ≤ Q.natDegree
    · let k : Fin (Q.natDegree + 1) := ⟨i, by omega⟩
      have h := (hb k H v hv hH).2 j
      have he : e k ≤ E := le_sup (mem_univ k)
      have hC : c k ≤ C := (le_sup (mem_univ k)).trans (Nat.le_succ _)
      apply h.trans
      exact_mod_cast Nat.mul_le_mul hC (Nat.pow_le_pow_right (by omega) he)
    · simp only [coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < i),
        map_zero, coeff_zero, abs_zero]
      positivity
  refine ⟨?_, hcoeff⟩
  rw [CCDN.bivariateTotalDegree_le_iff]
  intro i j hij
  have hi : i ≤ Q.natDegree := by
    by_contra h
    simp only [coeff_map, coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < i),
      map_zero, coeff_zero] at hij
    exact hij rfl
  let k : Fin (Q.natDegree + 1) := ⟨i, by omega⟩
  have hj : j ≤ m k :=
    (le_natDegree_of_ne_zero (by
      simpa only [coeff_map, MvPolynomial.coe_eval₂Hom, k] using hij)).trans
      (hb k H v hv hH).1
  exact Nat.add_le_add hi (hj.trans (le_sup (mem_univ k)))

end
end PierceLengthBound.FixedDividend
