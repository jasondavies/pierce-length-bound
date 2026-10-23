/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib

/-! Degree and leading-coefficient control under polynomial coordinate substitution. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial MvPolynomial

lemma coeff_prod_sum_degree_bounds {K ι : Type*} [CommRing K]
    (s : Finset ι) (p : ι → Polynomial K) (d : ι → ℕ)
    (hp : ∀ i ∈ s, (p i).natDegree ≤ d i) :
    (∏ i ∈ s, p i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (p i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
      coeff_mul_add_eq_of_natDegree_le (hp i (Finset.mem_insert_self ..))]
    · rw [ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))]
    · exact (natDegree_prod_le s p).trans (Finset.sum_le_sum fun j hj =>
        hp j (Finset.mem_insert_of_mem hj))

lemma polynomial_substitution_monomial_degree {K : Type*} [CommRing K]
    (z : Fin 3 → Polynomial K) {m : ℕ} (hz : ∀ j, (z j).natDegree ≤ m)
    (d : Fin 3 →₀ ℕ) (c : K) :
    (MvPolynomial.aeval z (MvPolynomial.monomial d c)).natDegree ≤
      m * d.sum (fun _ e => e) := by
  rw [MvPolynomial.aeval_monomial]
  apply (natDegree_C_mul_le _ _).trans
  change (∏ i ∈ d.support, z i ^ d i).natDegree ≤ _
  calc (∏ i ∈ d.support, z i ^ d i).natDegree ≤
      ∑ i ∈ d.support, (z i ^ d i).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ i ∈ d.support, m * d i := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [Nat.mul_comm] using natDegree_pow_le_of_le (d i) (hz i)
    _ = _ := by simp only [Finsupp.sum, Finset.mul_sum]

/-- Substitution multiplies the total degree bound by the maximum coordinate degree. -/
theorem polynomial_substitution_degree {K : Type*} [CommRing K]
    (z : Fin 3 → Polynomial K) {m : ℕ} (hz : ∀ j, (z j).natDegree ≤ m)
    (f : MvPolynomial (Fin 3) K) :
    (MvPolynomial.aeval z f).natDegree ≤ m * f.totalDegree := by
  conv_lhs => rw [f.as_sum, map_sum]
  apply natDegree_sum_le_of_forall_le
  intro d hd
  exact (polynomial_substitution_monomial_degree z hz d _).trans
    (Nat.mul_le_mul_left m (MvPolynomial.le_totalDegree hd))

lemma polynomial_substitution_monomial_top {K : Type*} [CommRing K]
    (z : Fin 3 → Polynomial K) {m : ℕ} (hz : ∀ j, (z j).natDegree ≤ m)
    (d : Fin 3 →₀ ℕ) (c : K) :
    (MvPolynomial.aeval z (MvPolynomial.monomial d c)).coeff
        (m * d.sum (fun _ e => e)) =
      MvPolynomial.eval (fun j => (z j).coeff m) (MvPolynomial.monomial d c) := by
  classical
  rw [MvPolynomial.aeval_monomial, MvPolynomial.eval_monomial]
  change (Polynomial.C c * ∏ i ∈ d.support, z i ^ d i).coeff _ = _
  rw [Polynomial.coeff_C_mul]
  have hs : m * d.sum (fun _ e => e) = ∑ i ∈ d.support, d i * m := by
    simp only [Finsupp.sum, Finset.mul_sum, Nat.mul_comm]
  rw [hs, coeff_prod_sum_degree_bounds]
  · simp only [coeff_pow_of_natDegree_le (hz _)]
    rfl
  · intro i hi
    exact natDegree_pow_le_of_le _ (hz i)

/-- The highest possible parameter coefficient is the top homogeneous form
at the highest coordinate coefficients. -/
theorem polynomial_substitution_top_coefficient {K : Type*} [CommRing K]
    (z : Fin 3 → Polynomial K) {m d : ℕ} (hm : 0 < m)
    (hz : ∀ j, (z j).natDegree ≤ m)
    (f : MvPolynomial (Fin 3) K) (hf : f.totalDegree ≤ d) :
    (MvPolynomial.aeval z f).coeff (m * d) =
      MvPolynomial.eval (fun j => (z j).coeff m) (MvPolynomial.homogeneousComponent d f) := by
  classical
  conv_lhs => rw [f.as_sum, map_sum, Polynomial.finsetSum_coeff]
  rw [MvPolynomial.homogeneousComponent_apply, map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hed : e.degree = d
  · rw [ite_eq_left hed]
    have hd : e.sum (fun _ n => n) = d := hed
    rw [← hd]
    exact polynomial_substitution_monomial_top z hz e _
  · rw [ite_eq_right hed]
    have hle := (MvPolynomial.le_totalDegree he).trans hf
    have hlt : e.sum (fun _ n => n) < d := by
      change e.sum (fun _ n => n) ≠ d at hed
      omega
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      ((polynomial_substitution_monomial_degree z hz e _).trans_lt
        (Nat.mul_lt_mul_of_pos_left hlt hm))

/-- More distinct parameter values than the degree bound force a symbolic
identity. This permits a bounded exceptional set instead of an assumed identity. -/
theorem polynomial_substitution_zero_of_many_points {K ι : Type*}
    [Field K] [Fintype ι] (z : Fin 3 → Polynomial K) {m : ℕ}
    (hz : ∀ j, (z j).natDegree ≤ m) (f : MvPolynomial (Fin 3) K)
    (t : ι → K) (ht : Function.Injective t)
    (hp : ∀ i, MvPolynomial.eval (fun j => (z j).eval (t i)) f = 0)
    (hcard : m * f.totalDegree < Fintype.card ι) : MvPolynomial.aeval z f = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ ht
  · intro i
    have he : (Polynomial.evalRingHom (t i)).comp (MvPolynomial.aeval z).toRingHom =
        MvPolynomial.eval (fun j => (z j).eval (t i)) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp
      · intro j
        simp
    exact (congrArg (fun h : MvPolynomial (Fin 3) K →+* K => h f) he).trans (hp i)
  · exact (polynomial_substitution_degree z hz f).trans_lt hcard

end
end PierceLengthBound.FixedDividend
