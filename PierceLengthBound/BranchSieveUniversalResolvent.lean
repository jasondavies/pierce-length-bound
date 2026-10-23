/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-! Universal integral resolvents. A polynomial expression in `d` roots is
annihilated by a monic degree-`d!` polynomial whose coefficients are integer
polynomials in the elementary symmetric functions of those roots.
For fixed `d` and a fixed expression this is one fixed polynomial, so its
coefficient height and degree are independent of the specialization. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Finset

/-- The product of `X - σ(P)` over all permutations `σ` of the `d` roots. -/
def branchOrbitResolvent {d : ℕ} (P : MvPolynomial (Fin d) ℤ) :
    Polynomial (MvPolynomial (Fin d) ℤ) :=
  ∏ e : Equiv.Perm (Fin d), (Polynomial.X - Polynomial.C (rename e P))

lemma branchOrbitResolvent_monic {d : ℕ} (P : MvPolynomial (Fin d) ℤ) :
    (branchOrbitResolvent P).Monic := by
  exact Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)

lemma branchOrbitResolvent_natDegree {d : ℕ} (P : MvPolynomial (Fin d) ℤ) :
    (branchOrbitResolvent P).natDegree = d.factorial := by
  rw [branchOrbitResolvent, Polynomial.natDegree_prod_of_monic]
  · simp [Fintype.card_perm]
  · intro e _; exact Polynomial.monic_X_sub_C _

lemma branchOrbitResolvent_rename {d : ℕ} (P : MvPolynomial (Fin d) ℤ)
    (τ : Equiv.Perm (Fin d)) :
    (branchOrbitResolvent P).map (rename τ).toRingHom = branchOrbitResolvent P := by
  simp only [branchOrbitResolvent, Polynomial.map_prod, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    rename_rename]
  apply Fintype.prod_equiv (Equiv.mulLeft τ)
  intro e
  rfl

lemma branchOrbitResolvent_coeff_symmetric {d : ℕ} (P : MvPolynomial (Fin d) ℤ) (j : ℕ) :
    ((branchOrbitResolvent P).coeff j).IsSymmetric := by
  intro τ
  have h := congrArg (fun q : Polynomial (MvPolynomial (Fin d) ℤ) => q.coeff j)
    (branchOrbitResolvent_rename P τ)
  simpa only [Polynomial.coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using h

/-- The orbit resolvent of `P` is the image of a monic integer polynomial of
degree `d!` in the elementary symmetric polynomials. -/
theorem branch_exists_universal_resolvent {d : ℕ} (P : MvPolynomial (Fin d) ℤ) :
    ∃ Q : Polynomial (MvPolynomial (Fin d) ℤ), Q.Monic ∧ Q.natDegree = d.factorial ∧
      Q.map (aeval (fun i : Fin d => esymm (Fin d) ℤ (i.val + 1))).toRingHom =
        branchOrbitResolvent P := by
  classical
  let h : MvPolynomial (Fin d) ℤ →+* MvPolynomial (Fin d) ℤ :=
    (aeval (fun i : Fin d => esymm (Fin d) ℤ (i.val + 1))).toRingHom
  have hc : ∀ j, (branchOrbitResolvent P).coeff j ∈ Set.range h := by
    intro j
    obtain ⟨q, hq⟩ := (esymmAlgHom_surjective ℤ (σ := Fin d) (n := d) (by simp))
      ⟨(branchOrbitResolvent P).coeff j, branchOrbitResolvent_coeff_symmetric P j⟩
    refine ⟨q, ?_⟩
    simpa only [h, esymmAlgHom_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      using congrArg Subtype.val hq
  obtain ⟨Q, hQ, hdeg, hmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.lifts_iff_coeff_lifts (branchOrbitResolvent P)).mpr hc)
    (branchOrbitResolvent_monic P)
  exact ⟨Q, hmonic, hdeg.trans (branchOrbitResolvent_natDegree P), hQ⟩

/-- A chosen monic integer polynomial in the elementary symmetric functions
whose image is the orbit resolvent of `P`. -/
def branchUniversalResolvent {d : ℕ} (P : MvPolynomial (Fin d) ℤ) :
    Polynomial (MvPolynomial (Fin d) ℤ) :=
  (branch_exists_universal_resolvent P).choose

theorem branchUniversalResolvent_monic {d : ℕ} (P : MvPolynomial (Fin d) ℤ) :
    (branchUniversalResolvent P).Monic :=
  (branch_exists_universal_resolvent P).choose_spec.1

theorem branchUniversalResolvent_map {d : ℕ} (P : MvPolynomial (Fin d) ℤ) :
    (branchUniversalResolvent P).map
      (aeval (fun i : Fin d => esymm (Fin d) ℤ (i.val + 1))).toRingHom =
        branchOrbitResolvent P :=
  (branch_exists_universal_resolvent P).choose_spec.2.2

theorem branchOrbitResolvent_eval_self {d : ℕ} (P : MvPolynomial (Fin d) ℤ)
    {A : Type*} [CommRing A] (f : MvPolynomial (Fin d) ℤ →+* A) :
    (branchOrbitResolvent P).eval₂ f (f P) = 0 := by
  classical
  rw [branchOrbitResolvent, Polynomial.eval₂_finsetProd]
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : Equiv.Perm (Fin d)))
  simp

/-- The universal resolvent equation holds for every family of `d` elements of a
commutative ring, not necessarily distinct. -/
theorem branch_universal_resolvent_equation {d : ℕ} (P : MvPolynomial (Fin d) ℤ)
    {Q : Polynomial (MvPolynomial (Fin d) ℤ)}
    (hQ : Q.map (aeval (fun i : Fin d => esymm (Fin d) ℤ (i.val + 1))).toRingHom =
      branchOrbitResolvent P)
    {A : Type*} [CommRing A] (roots : Fin d → A) :
    Q.eval₂ (aeval (fun i : Fin d =>
      (Finset.univ.val.map roots).esymm (i.val + 1))).toRingHom (aeval roots P) = 0 := by
  let f : MvPolynomial (Fin d) ℤ →+* A := (aeval roots).toRingHom
  have hc : f.comp (aeval (R := ℤ)
      (fun i : Fin d => esymm (Fin d) ℤ (i.val + 1))).toRingHom =
      (aeval (R := ℤ)
        (fun i : Fin d => (Finset.univ.val.map roots).esymm (i.val + 1))).toRingHom := by
    ext i
    · simp [f]
    · simp [f, MvPolynomial.aeval_esymm_eq_multiset_esymm]
  have hv := branchOrbitResolvent_eval_self P f
  rw [← hQ, Polynomial.eval₂_map, hc] at hv
  exact hv

end
end PierceLengthBound.FixedDividend
