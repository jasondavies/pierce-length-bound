/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.Polynomial.IntegralNormalization
public import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic

/-! Fixed-degree integral normalization. Unlike normalization by the actual
degree, this polynomial construction commutes with every specialization. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial Finset

def branchMonicization {R : Type*} [CommSemiring R] (n : ℕ) (p : R[X]) : R[X] :=
  X ^ n + ∑ j ∈ range n, monomial j (p.coeff j * p.coeff n ^ (n - 1 - j))

theorem branchMonicization_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (n : ℕ) (p : R[X]) :
    (branchMonicization n p).map φ = branchMonicization n (p.map φ) := by
  simp [branchMonicization, Polynomial.map_sum, Polynomial.map_monomial]

theorem branchMonicization_coeff {R : Type*} [CommSemiring R]
    (n : ℕ) (p : R[X]) (j : ℕ) :
    (branchMonicization n p).coeff j =
      (if n = j then 1 else 0) +
        if j < n then p.coeff j * p.coeff n ^ (n - 1 - j) else 0 := by
  classical
  simp [branchMonicization, coeff_X_pow, coeff_monomial, eq_comm]

theorem branchMonicization_monic {R : Type*} [CommSemiring R]
    (n : ℕ) (p : R[X]) : (branchMonicization n p).Monic := by
  nontriviality R
  apply monic_of_natDegree_le_of_coeff_eq_one n
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro j hj
    rw [branchMonicization_coeff]
    simp only [ite_eq_right (by omega : n ≠ j), ite_eq_right (by omega : ¬j < n), add_zero]
  · simp [branchMonicization_coeff]

theorem branchMonicization_natDegree {R : Type*} [CommSemiring R] [Nontrivial R]
    (n : ℕ) (p : R[X]) : (branchMonicization n p).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro j hj
    rw [branchMonicization_coeff]
    simp only [ite_eq_right (by omega : n ≠ j), ite_eq_right (by omega : ¬j < n), add_zero]
  · simp [branchMonicization_coeff]

theorem branchMonicization_eq_integralNormalization
    {R : Type*} [CommSemiring R] (n : ℕ) (p : R[X]) (hp : p ≠ 0)
    (hn : p.natDegree = n) : branchMonicization n p = p.integralNormalization := by
  ext j
  rw [branchMonicization_coeff]
  by_cases hj : j = n
  · subst j
    simpa [hn] using
      (p.integralNormalization_coeff_natDegree hp).symm
  · rw [integralNormalization_coeff_ne_natDegree (by omega)]
    rw [ite_eq_right (Ne.symm hj), zero_add]
    by_cases hlt : j < n
    · simp only [ite_eq_left hlt, leadingCoeff, hn]
    · rw [ite_eq_right hlt, coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

theorem branch_integralNormalization_irreducible_iff {K : Type*} [Field K]
    (p : K[X]) (hp : p ≠ 0) (hn : 1 ≤ p.natDegree) :
    Irreducible p.integralNormalization ↔ Irreducible p := by
  let a := p.leadingCoeff
  have ha : a ≠ 0 := leadingCoeff_ne_zero.mpr hp
  let : Invertible a := invertibleOfNonzero ha
  have he : (algEquivCMulXAddC a 0) p.integralNormalization =
      C (a ^ (p.natDegree - 1)) * p := by
    simp only [algEquivCMulXAddC_apply, C_0, add_zero, ← comp_eq_aeval]
    ext j
    rw [comp_C_mul_X_coeff, coeff_C_mul]
    simpa only [a, mul_comm] using integralNormalization_coeff_mul_leadingCoeff_pow j hn
  rw [← MulEquiv.irreducible_iff (f := algEquivCMulXAddC a 0), he]
  rw [mul_comm]
  exact (associated_mul_unit_left p _
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero _ ha)))).irreducible_iff

theorem branchMonicization_irreducible_iff {K : Type*} [Field K]
    (n : ℕ) (p : K[X]) (hn : p.natDegree = n) (hpos : 1 ≤ n)
    (hlead : p.coeff n ≠ 0) :
    Irreducible (branchMonicization n p) ↔ Irreducible p := by
  have hp : p ≠ 0 := by intro hz; simp [hz] at hlead
  rw [branchMonicization_eq_integralNormalization n p hp hn]
  exact branch_integralNormalization_irreducible_iff p hp (by omega)

theorem branchMonicization_eval₂_scaled {R S : Type*}
    [CommSemiring R] [CommSemiring S] (n : ℕ) (p : R[X])
    (hn : p.natDegree = n) (hpos : 1 ≤ n) (φ : R →+* S) (x : S) :
    (branchMonicization n p).eval₂ φ (φ (p.coeff n) * x) =
      φ (p.coeff n) ^ (n - 1) * p.eval₂ φ x := by
  have hp : p ≠ 0 := by intro hz; simp only [hz, natDegree_zero] at hn; omega
  rw [branchMonicization_eq_integralNormalization n p hp hn]
  have h := integralNormalization_eval₂_leadingCoeff_mul (by omega : 1 ≤ p.natDegree) φ x
  simpa only [leadingCoeff, hn] using h

theorem branchMonicization_specialized_irreducible_iff
    {R K : Type*} [CommSemiring R] [Field K]
    (n : ℕ) (p : R[X]) (hd : p.natDegree ≤ n) (hpos : 1 ≤ n)
    (φ : R →+* K) (hlead : φ (p.coeff n) ≠ 0) :
    Irreducible ((branchMonicization n p).map φ) ↔ Irreducible (p.map φ) := by
  rw [branchMonicization_map]
  have hlead' : (p.map φ).coeff n ≠ 0 := by simpa only [coeff_map] using hlead
  have hn : (p.map φ).natDegree = n := le_antisymm (natDegree_map_le.trans hd)
    (le_natDegree_of_ne_zero hlead')
  exact branchMonicization_irreducible_iff n (p.map φ) hn hpos hlead'

theorem branchMonicization_eq_of_leading_zero {R : Type*} [CommSemiring R]
    (n : ℕ) (p : R[X]) (hn : 1 ≤ n) (hz : p.coeff n = 0) :
    branchMonicization n p = X ^ (n - 1) * (X + C (p.coeff (n - 1))) := by
  classical
  unfold branchMonicization
  rw [Finset.sum_eq_single (n - 1)]
  · rw [Nat.sub_self, pow_zero, mul_one, ← C_mul_X_pow_eq_monomial]
    have hpow : (X : R[X]) ^ n = X ^ (n - 1) * X := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ]
    rw [hpow]
    ring
  · intro j hj hjne
    have hjlt : j < n := Finset.mem_range.mp hj
    rw [hz, zero_pow (by omega : n - 1 - j ≠ 0), mul_zero, map_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

theorem branchMonicization_leading_ne_zero_of_irreducible {K : Type*} [Field K]
    (n : ℕ) (p : K[X]) (hn : 2 ≤ n) (hir : Irreducible (branchMonicization n p)) :
    p.coeff n ≠ 0 := by
  intro hz
  have he := branchMonicization_eq_of_leading_zero n p (by omega) hz
  obtain hu | hu := hir.isUnit_or_isUnit he
  · exact not_isUnit_of_natDegree_pos _ (by simpa using (show 0 < n - 1 by omega)) hu
  · exact not_isUnit_of_natDegree_pos _ (by simp) hu

end
end PierceLengthBound.FixedDividend
