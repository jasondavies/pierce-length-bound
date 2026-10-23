/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

/-! Bounded multivariate Kronecker substitution and its coefficientwise inverse.
The inverse is linear, rather than multiplicative, and commutes with coefficient
specialization. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Finset

def branchMultiWeight (a : ℕ) {n : ℕ} (s : Fin n → ℕ) : ℕ :=
  ∑ i, a ^ i.val * s i

lemma branchMultiWeight_succ (a : ℕ) {n : ℕ} (s : Fin (n + 1) → ℕ) :
    branchMultiWeight a s = s 0 + a * branchMultiWeight a (fun i => s i.succ) := by
  simp only [branchMultiWeight, Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_mul,
    Fin.val_succ, pow_succ, mul_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  ring

theorem branchMultiWeight_injective {a n : ℕ} {s t : Fin n → ℕ}
    (hs : ∀ i, s i < a) (ht : ∀ i, t i < a)
    (h : branchMultiWeight a s = branchMultiWeight a t) : s = t := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    rw [branchMultiWeight_succ, branchMultiWeight_succ] at h
    have h0 := congrArg (fun j => j % a) h
    simp only [Nat.add_mod, Nat.mul_mod_right, add_zero,
      Nat.mod_eq_of_lt (hs 0), Nat.mod_eq_of_lt (ht 0)] at h0
    have htail : branchMultiWeight a (fun i => s i.succ) =
        branchMultiWeight a (fun i => t i.succ) := by
      rw [h0] at h
      exact Nat.eq_of_mul_eq_mul_left (by have := hs 0; omega) (Nat.add_left_cancel h)
    have hi := ih (fun i => hs i.succ) (fun i => ht i.succ) htail
    funext i
    exact Fin.cases h0 (fun j => congrFun hi j) i

variable {R : Type*} [CommSemiring R]

def branchMultiKronecker (a n : ℕ) : MvPolynomial (Fin n) R →+* Polynomial R :=
  eval₂Hom Polynomial.C (fun i => Polynomial.X ^ (a ^ i.val))

lemma branchMultiKronecker_monomial (a n : ℕ) (s : Fin n →₀ ℕ) (c : R) :
    branchMultiKronecker a n (monomial s c) =
      Polynomial.monomial (branchMultiWeight a s) c := by
  simp only [branchMultiKronecker, coe_eval₂Hom, eval₂_monomial]
  rw [Finsupp.prod_fintype]
  · simp only [← pow_mul, Finset.prod_pow_eq_pow_sum, branchMultiWeight,
      Polynomial.C_mul_X_pow_eq_monomial]
  · intro i; simp

theorem branchMultiKronecker_coeff {a n : ℕ} {p : MvPolynomial (Fin n) R}
    (ha : ∀ i, p.degreeOf i < a) {s : Fin n →₀ ℕ} (hs : s ∈ p.support) :
    (branchMultiKronecker a n p).coeff (branchMultiWeight a s) = p.coeff s := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, branchMultiKronecker_monomial, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single s]
  · simp
  · intro t ht hts
    apply Polynomial.coeff_monomial_of_ne
    intro heq
    apply hts
    apply DFunLike.coe_injective
    exact branchMultiWeight_injective
      (fun i => (le_degreeOf_of_mem_support i ht).trans_lt (ha i))
      (fun i => (le_degreeOf_of_mem_support i hs).trans_lt (ha i)) heq.symm
  · exact fun h => (h hs).elim

def branchMultiExponent {a n : ℕ} (s : Fin n → Fin a) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (s i).val)

@[simp] lemma branchMultiExponent_apply {a n : ℕ} (s : Fin n → Fin a) (i : Fin n) :
    branchMultiExponent s i = (s i).val := by
  simp [branchMultiExponent]

def branchMultiDecode (a n : ℕ) : Polynomial R →ₗ[R] MvPolynomial (Fin n) R where
  toFun p := ∑ s : Fin n → Fin a, monomial (branchMultiExponent s)
    (p.coeff (branchMultiWeight a (branchMultiExponent s)))
  map_add' p q := by simp [Finset.sum_add_distrib]
  map_smul' c p := by
    simp only [Polynomial.coeff_smul, Finset.smul_sum, map_smul, RingHom.id_apply]

theorem branchMultiDecode_monomial {a n : ℕ} (s : Fin n →₀ ℕ)
    (hs : ∀ i, s i < a) (c : R) :
    branchMultiDecode a n (Polynomial.monomial (branchMultiWeight a s) c) =
      monomial s c := by
  classical
  let t : Fin n → Fin a := fun i => ⟨s i, hs i⟩
  have ht : branchMultiExponent t = s := by ext i; rfl
  change (∑ u : Fin n → Fin a, monomial (branchMultiExponent u)
    ((Polynomial.monomial (branchMultiWeight a s) c).coeff
      (branchMultiWeight a (branchMultiExponent u)))) = _
  rw [Finset.sum_eq_single t]
  · simp [ht]
  · intro u _ hut
    rw [Polynomial.coeff_monomial_of_ne]
    · simp
    · intro heq
      have hu := branchMultiWeight_injective (s := (s : Fin n → ℕ))
        (t := branchMultiExponent u) hs
        (fun i => (u i).isLt) heq.symm
      apply hut
      funext i
      apply Fin.ext
      exact (congrFun hu i).symm
  · simp

/-- Decoding recovers every polynomial whose separate degrees fit the radix. -/
theorem branchMultiDecode_encode {a n : ℕ} (p : MvPolynomial (Fin n) R)
    (ha : ∀ i, p.degreeOf i < a) :
    branchMultiDecode a n (branchMultiKronecker a n p) = p := by
  classical
  conv_lhs => rw [p.as_sum, map_sum, map_sum]
  conv_rhs => rw [p.as_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [branchMultiKronecker_monomial]
  exact branchMultiDecode_monomial s
    (fun i => (le_degreeOf_of_mem_support i hs).trans_lt (ha i)) _

/-- The decoder is independent of the coefficient ring. -/
theorem branchMultiDecode_map {S : Type*} [CommSemiring S] (f : R →+* S)
    (a n : ℕ) (p : Polynomial R) :
    MvPolynomial.map f (branchMultiDecode a n p) =
      branchMultiDecode a n (p.map f) := by
  classical
  simp [branchMultiDecode]

theorem branchMultiKronecker_ne_zero {a n : ℕ} {p : MvPolynomial (Fin n) R}
    (hp : p ≠ 0) (ha : ∀ i, p.degreeOf i < a) : branchMultiKronecker a n p ≠ 0 := by
  intro h
  have := branchMultiDecode_encode p ha
  rw [h, map_zero] at this
  exact hp this.symm

theorem branchMultiKronecker_injOn {a n : ℕ} {p q : MvPolynomial (Fin n) R}
    (hp : ∀ i, p.degreeOf i < a) (hq : ∀ i, q.degreeOf i < a)
    (h : branchMultiKronecker a n p = branchMultiKronecker a n q) : p = q := by
  simpa only [branchMultiDecode_encode p hp, branchMultiDecode_encode q hq] using
    congrArg (branchMultiDecode a n) h

theorem branchMultiKronecker_natDegree_le {a n : ℕ} (ha : 1 ≤ a)
    (p : MvPolynomial (Fin n) R) :
    (branchMultiKronecker a n p).natDegree ≤ a ^ n * p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  rw [branchMultiKronecker_monomial]
  apply (Polynomial.natDegree_monomial_le _).trans
  calc
    branchMultiWeight a s ≤ ∑ i : Fin n, a ^ n * s i := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right ha i.isLt.le)
    _ = a ^ n * s.sum (fun _ e => e) := by
      rw [Finsupp.sum_fintype]
      · simp only [mul_sum]
      · simp
    _ ≤ a ^ n * p.totalDegree := Nat.mul_le_mul_left _ (le_totalDegree hs)

end
end PierceLengthBound.FixedDividend
