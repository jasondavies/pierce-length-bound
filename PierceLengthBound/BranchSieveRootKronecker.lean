/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveMultivariateKronecker
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

/-! Kronecker substitution with the monic root variable assigned the highest
radix digit. This guarantees that the encoded family is still monic. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Finset

theorem branchMultiWeight_lt {a n : ℕ} (s : Fin n → ℕ) (hs : ∀ i, s i < a) :
    branchMultiWeight a s < a ^ n := by
  induction n with
  | zero => simp [branchMultiWeight]
  | succ n ih =>
    rw [branchMultiWeight_succ, pow_succ]
    have htail := ih (fun i => s i.succ) (fun i => hs i.succ)
    have h0 := hs 0
    nlinarith

theorem branchMultiKronecker_natDegree_lt {R : Type*} [CommSemiring R]
    {a n : ℕ} (ha : 0 < a) (p : MvPolynomial (Fin n) R)
    (hp : ∀ i, p.degreeOf i < a) :
    (branchMultiKronecker a n p).natDegree < a ^ n := by
  classical
  have hpow : 0 < a ^ n := pow_pos ha _
  suffices h : (branchMultiKronecker a n p).natDegree ≤ a ^ n - 1 by omega
  conv_lhs => rw [p.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  rw [branchMultiKronecker_monomial]
  apply (Polynomial.natDegree_monomial_le _).trans
  have h := branchMultiWeight_lt (s : Fin n → ℕ)
    (fun i => (le_degreeOf_of_mem_support i hs).trans_lt (hp i))
  omega

def branchRootKronecker {R : Type*} [CommSemiring R] (a n : ℕ) :
    Polynomial (MvPolynomial (Fin n) R) →+* Polynomial R :=
  Polynomial.eval₂RingHom (branchMultiKronecker a n) (Polynomial.X ^ (a ^ n))

theorem branchRootKronecker_monic {R : Type*} [CommSemiring R] [Nontrivial R]
    {a n : ℕ} (ha : 0 < a) (p : Polynomial (MvPolynomial (Fin n) R)) (hp : p.Monic)
    (hdeg : ∀ j i, (p.coeff j).degreeOf i < a) :
    (branchRootKronecker a n p).Monic := by
  classical
  by_cases hp0 : p.natDegree = 0
  · have he : p = 1 := hp.natDegree_eq_zero.mp hp0
    simp [he]
  have he : branchRootKronecker a n p =
      Polynomial.X ^ (a ^ n * p.natDegree) +
        ∑ j ∈ range p.natDegree,
          branchMultiKronecker a n (p.coeff j) * Polynomial.X ^ (a ^ n * j) := by
    simp only [branchRootKronecker, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range,
      sum_range_succ, hp.coeff_natDegree, map_one, one_mul, ← pow_mul]
    rw [add_comm]
  rw [he]
  apply Polynomial.monic_X_pow_add
  have hpow : 0 < a ^ n := pow_pos ha _
  have htotal : 0 < a ^ n * p.natDegree := Nat.mul_pos hpow (Nat.pos_of_ne_zero hp0)
  apply lt_of_le_of_lt Polynomial.degree_le_natDegree
  norm_cast
  suffices h : (∑ j ∈ range p.natDegree,
      branchMultiKronecker a n (p.coeff j) * Polynomial.X ^ (a ^ n * j)).natDegree ≤
        a ^ n * p.natDegree - 1 by omega
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  apply Polynomial.natDegree_mul_le.trans
  rw [Polynomial.natDegree_X_pow]
  have hcoeff := branchMultiKronecker_natDegree_lt ha (p.coeff j) (hdeg j)
  have hj' := mem_range.mp hj
  have hmul : a ^ n * (j + 1) ≤ a ^ n * p.natDegree := Nat.mul_le_mul_left _ hj'
  apply Nat.le_sub_one_of_lt
  calc
    _ < a ^ n + a ^ n * j := Nat.add_lt_add_right hcoeff _
    _ = a ^ n * (j + 1) := by ring
    _ ≤ _ := hmul

def branchRootLastEquiv (R : Type*) [CommSemiring R] (n : ℕ) :
    Polynomial (MvPolynomial (Fin n) R) ≃ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  (MvPolynomial.finSuccEquiv R n).symm.trans
    (MvPolynomial.renameEquiv R (finRotate (n + 1)).symm)

lemma branch_rotate_symm_zero (n : ℕ) : (finRotate (n + 1)).symm 0 = Fin.last n :=
  (finRotate (n + 1)).symm_apply_eq.mpr finRotate_last.symm

lemma branch_rotate_symm_succ {n : ℕ} (i : Fin n) :
    (finRotate (n + 1)).symm i.succ = i.castSucc :=
  (finRotate (n + 1)).symm_apply_eq.mpr (finRotate_of_lt i.isLt).symm

theorem branchRootLastEquiv_X {R : Type*} [CommSemiring R] (n : ℕ) :
    branchRootLastEquiv R n Polynomial.X = MvPolynomial.X (Fin.last n) := by
  have he : (MvPolynomial.finSuccEquiv R n).symm Polynomial.X = MvPolynomial.X 0 :=
    (MvPolynomial.finSuccEquiv R n).symm_apply_eq.mpr finSuccEquiv_X_zero.symm
  change rename (finRotate (n + 1)).symm ((MvPolynomial.finSuccEquiv R n).symm Polynomial.X) = _
  rw [he, rename_X, branch_rotate_symm_zero]

theorem branchRootLastEquiv_C {R : Type*} [CommSemiring R] (n : ℕ)
    (p : MvPolynomial (Fin n) R) :
    branchRootLastEquiv R n (Polynomial.C p) = MvPolynomial.rename Fin.castSucc p := by
  have h : (branchRootLastEquiv R n).toRingHom.comp Polynomial.C =
      (MvPolynomial.rename (R := R) (Fin.castSucc : Fin n → Fin (n + 1))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      have he : (MvPolynomial.finSuccEquiv R n).symm (Polynomial.C (MvPolynomial.C c)) =
          MvPolynomial.C c :=
        (MvPolynomial.finSuccEquiv R n).symm_apply_eq.mpr (by simp [finSuccEquiv_apply])
      simp [RingHom.comp_apply, branchRootLastEquiv, he, renameEquiv_apply]
    · intro i
      have he : (MvPolynomial.finSuccEquiv R n).symm (Polynomial.C (MvPolynomial.X i)) =
          MvPolynomial.X i.succ :=
        (MvPolynomial.finSuccEquiv R n).symm_apply_eq.mpr finSuccEquiv_X_succ.symm
      change rename (finRotate (n + 1)).symm
        ((MvPolynomial.finSuccEquiv R n).symm (Polynomial.C (MvPolynomial.X i))) =
          rename Fin.castSucc (MvPolynomial.X i)
      rw [he, rename_X, rename_X, branch_rotate_symm_succ]
  exact DFunLike.congr_fun h p

theorem branchRootKronecker_eq_multi {R : Type*} [CommSemiring R] (a n : ℕ)
    (p : Polynomial (MvPolynomial (Fin n) R)) :
    branchRootKronecker a n p = branchMultiKronecker a (n + 1) (branchRootLastEquiv R n p) := by
  have hc : (branchMultiKronecker a (n + 1)).comp
      (MvPolynomial.rename (R := R) (Fin.castSucc : Fin n → Fin (n + 1))).toRingHom =
      (branchMultiKronecker a n : MvPolynomial (Fin n) R →+* _) := by
    apply MvPolynomial.ringHom_ext <;> intro i <;>
      simp [RingHom.comp_apply, branchMultiKronecker]
  have h : (branchRootKronecker a n : Polynomial (MvPolynomial (Fin n) R) →+* _) =
      (branchMultiKronecker a (n + 1)).comp (branchRootLastEquiv R n).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro q
      change branchRootKronecker a n (Polynomial.C q) =
        branchMultiKronecker a (n + 1) (branchRootLastEquiv R n (Polynomial.C q))
      rw [branchRootLastEquiv_C]
      simp only [branchRootKronecker, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      exact (DFunLike.congr_fun hc q).symm
    · simp [RingHom.comp_apply, branchRootLastEquiv_X, branchRootKronecker,
        branchMultiKronecker]
  exact DFunLike.congr_fun h p

def branchRootExponentPrefix {n : ℕ} (s : Fin (n + 1) →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => s i.castSucc)

@[simp] lemma branchRootExponentPrefix_apply {n : ℕ} (s : Fin (n + 1) →₀ ℕ) (i : Fin n) :
    branchRootExponentPrefix s i = s i.castSucc := rfl

theorem branchRootLastEquiv_coeff {R : Type*} [CommSemiring R] {n : ℕ}
    (p : Polynomial (MvPolynomial (Fin n) R)) (s : Fin (n + 1) →₀ ℕ) :
    (branchRootLastEquiv R n p).coeff s =
      (p.coeff (s (Fin.last n))).coeff (branchRootExponentPrefix s) := by
  have he : (Finsupp.cons (s (Fin.last n)) (branchRootExponentPrefix s)).mapDomain
      (finRotate (n + 1)).symm = s := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [← branch_rotate_symm_zero,
        Finsupp.mapDomain_apply_of_injective (finRotate (n + 1)).symm.injective]
      rfl
    · rw [← branch_rotate_symm_succ j,
        Finsupp.mapDomain_apply_of_injective (finRotate (n + 1)).symm.injective]
      rw [branch_rotate_symm_succ, Finsupp.cons_succ]
      rfl
  change (rename (finRotate (n + 1)).symm ((MvPolynomial.finSuccEquiv R n).symm p)).coeff s = _
  conv_lhs => rw [← he, coeff_rename_mapDomain _ (finRotate (n + 1)).symm.injective]
  have hf := finSuccEquiv_coeff_coeff (branchRootExponentPrefix s)
    ((MvPolynomial.finSuccEquiv R n).symm p) (s (Fin.last n))
  simpa only [AlgEquiv.apply_symm_apply] using hf.symm

theorem branchRootLastEquiv_degreeOf_le {R : Type*} [CommSemiring R] {n d : ℕ}
    (p : Polynomial (MvPolynomial (Fin n) R)) (hp : p.natDegree ≤ d)
    (hD : ∀ j, (p.coeff j).totalDegree ≤ d) (i : Fin (n + 1)) :
    (branchRootLastEquiv R n p).degreeOf i ≤ d := by
  apply degreeOf_le_iff.mpr
  intro s hs
  have hc := mem_support_iff.mp hs
  rw [branchRootLastEquiv_coeff] at hc
  have hpnz : p.coeff (s (Fin.last n)) ≠ 0 := by
    intro he
    exact hc (by rw [he]; rfl)
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact (Polynomial.le_natDegree_of_ne_zero hpnz).trans hp
  · exact (le_degreeOf_of_mem_support j (mem_support_iff.mpr hc)).trans
      ((degreeOf_le_totalDegree (p.coeff (s (Fin.last n))) j).trans (hD _))

theorem branchRootLastEquiv_totalDegree_le {R : Type*} [CommSemiring R] {n d : ℕ}
    (p : Polynomial (MvPolynomial (Fin n) R)) (hD : ∀ j, (p.coeff j).totalDegree ≤ d) :
    (branchRootLastEquiv R n p).totalDegree ≤ p.natDegree + d := by
  classical
  apply Finset.sup_le
  intro s hs
  have hc := mem_support_iff.mp hs
  rw [branchRootLastEquiv_coeff] at hc
  have hpnz : p.coeff (s (Fin.last n)) ≠ 0 := by
    intro he
    exact hc (by rw [he]; rfl)
  have hroot := Polynomial.le_natDegree_of_ne_zero hpnz
  have hprefix := (le_totalDegree (mem_support_iff.mpr hc)).trans (hD (s (Fin.last n)))
  change s.sum (fun _ e => e) ≤ _
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_castSucc]
  rw [Finsupp.sum_fintype _ _ (by simp)] at hprefix
  change (∑ j : Fin n, s j.castSucc) ≤ d at hprefix
  omega

theorem branchRootLastEquiv_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) R)) :
    MvPolynomial.map φ (branchRootLastEquiv R n p) =
      branchRootLastEquiv S n (p.map (MvPolynomial.map φ)) := by
  ext s
  simp only [MvPolynomial.coeff_map, branchRootLastEquiv_coeff, Polynomial.coeff_map]

end
end PierceLengthBound.FixedDividend
