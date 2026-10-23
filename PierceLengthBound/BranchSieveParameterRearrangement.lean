/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveParameterSpecialization
public import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Tactic

/-! Put the first Hilbert parameter in the scalar polynomial ring while
retaining all other parameters as variables. This is an actual algebra
equivalence, so it preserves irreducibility before Kronecker substitution. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Finset

def branchFirstParameterEquiv (R : Type*) [CommSemiring R] (r : ℕ) :
    MvPolynomial (Fin (r + 1)) R ≃ₐ[R] MvPolynomial (Fin r) (Polynomial R) :=
  (renameEquiv R (_root_.finSuccEquiv r)).trans (optionEquivRight R (Fin r))

theorem branchFirstParameterEquiv_eq (R : Type*) [CommSemiring R] (r : ℕ) :
    (branchFirstParameterEquiv R r).toRingHom =
      eval₂Hom (C.comp Polynomial.C) (Fin.cases (C Polynomial.X) X) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [branchFirstParameterEquiv]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i <;>
      simp [branchFirstParameterEquiv]

theorem branchFirstParameterEquiv_monomial {R : Type*} [CommSemiring R] {r : ℕ}
    (s : Fin (r + 1) →₀ ℕ) (c : R) :
    branchFirstParameterEquiv R r (monomial s c) =
      monomial s.tail (Polynomial.monomial (s 0) c) := by
  change (branchFirstParameterEquiv R r).toRingHom (monomial s c) = _
  rw [branchFirstParameterEquiv_eq]
  simp only [coe_eval₂Hom, eval₂_monomial, RingHom.comp_apply]
  rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [← map_pow, ← mul_assoc, ← map_mul, Polynomial.C_mul_X_pow_eq_monomial]
  rw [monomial_eq]
  rw [Finsupp.prod_fintype _ _ (by simp)]
  rfl

theorem branchFirstParameterEquiv_coeff {R : Type*} [CommSemiring R] {r : ℕ}
    (f : MvPolynomial (Fin (r + 1)) R) (s : Fin r →₀ ℕ) (j : ℕ) :
    ((branchFirstParameterEquiv R r f).coeff s).coeff j = f.coeff (s.cons j) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]
  | monomial t c =>
    rw [branchFirstParameterEquiv_monomial]
    by_cases htail : t.tail = s
    · rw [htail, coeff_monomial]
      simp only [ite_true, Polynomial.coeff_monomial, coeff_monomial]
      have he : t = s.cons j ↔ t 0 = j := by
        constructor
        · intro h
          have := congrArg (fun u : Fin (r + 1) →₀ ℕ => u 0) h
          simpa using this
        · intro h
          rw [← h, ← htail, Finsupp.cons_tail]
      simp only [he]
    · have hne : s.cons j ≠ t := by
        intro he
        have := congrArg Finsupp.tail he
        simp only [Finsupp.tail_cons] at this
        exact htail this.symm
      simp only [coeff_monomial, Ne.symm hne, htail, ite_false, Polynomial.coeff_zero]

theorem branchFirstParameterEquiv_support_degree {R : Type*} [CommSemiring R] {r d : ℕ}
    (f : MvPolynomial (Fin (r + 1)) R) (hd : f.totalDegree ≤ d)
    (s : Fin r →₀ ℕ) (j : ℕ)
    (hs : ((branchFirstParameterEquiv R r f).coeff s).coeff j ≠ 0) :
    j + s.sum (fun _ e => e) ≤ d := by
  rw [branchFirstParameterEquiv_coeff] at hs
  have h := (le_totalDegree (mem_support_iff.mpr hs)).trans hd
  simpa only [Finsupp.sum_cons] using h

theorem branchFirstParameterEquiv_coefficient_degree {R : Type*} [CommSemiring R]
    {r d : ℕ} (f : MvPolynomial (Fin (r + 1)) R) (hd : f.totalDegree ≤ d)
    (s : Fin r →₀ ℕ) : ((branchFirstParameterEquiv R r f).coeff s).natDegree ≤ d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  by_contra hn
  have h := branchFirstParameterEquiv_support_degree f hd s j hn
  omega

theorem branchFirstParameterEquiv_totalDegree {R : Type*} [CommSemiring R]
    {r d : ℕ} (f : MvPolynomial (Fin (r + 1)) R) (hd : f.totalDegree ≤ d) :
    (branchFirstParameterEquiv R r f).totalDegree ≤ d := by
  classical
  apply Finset.sup_le
  intro s hs
  have hsne := mem_support_iff.mp hs
  obtain ⟨j, hj⟩ : ∃ j, ((branchFirstParameterEquiv R r f).coeff s).coeff j ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hsne
    apply Polynomial.ext
    intro j
    simpa using hn j
  have h := branchFirstParameterEquiv_support_degree f hd s j hj
  omega

def branchFamilyParameterRearrangement (R : Type*) [CommSemiring R] (r : ℕ) :
    Polynomial (MvPolynomial (Fin (r + 1)) R) ≃+*
      Polynomial (MvPolynomial (Fin r) (Polynomial R)) :=
  Polynomial.mapEquiv (branchFirstParameterEquiv R r).toRingEquiv

theorem branchFamilyParameterRearrangement_bounds {r d H : ℕ}
    (p : Polynomial (MvPolynomial (Fin (r + 1)) ℤ)) (hp : p.Monic)
    (hdeg : p.natDegree ≤ d) (hD : ∀ j, (p.coeff j).totalDegree ≤ d)
    (hH : ∀ j s, |(p.coeff j).coeff s| ≤ (H : ℤ)) :
    let q := branchFamilyParameterRearrangement ℤ r p
    q.Monic ∧ q.natDegree ≤ d ∧ (∀ j, (q.coeff j).totalDegree ≤ d) ∧
      (∀ j s, ((q.coeff j).coeff s).natDegree ≤ d) ∧
      ∀ j s k, |((q.coeff j).coeff s).coeff k| ≤ (H : ℤ) := by
  dsimp only
  have hq : (branchFamilyParameterRearrangement ℤ r p).Monic := hp.map _
  refine ⟨hq, Polynomial.natDegree_map_le.trans hdeg, ?_, ?_, ?_⟩
  · intro j
    change ((p.map (branchFirstParameterEquiv ℤ r).toRingHom).coeff j).totalDegree ≤ d
    rw [Polynomial.coeff_map]
    exact branchFirstParameterEquiv_totalDegree (p.coeff j) (hD j)
  · intro j s
    change (((p.map (branchFirstParameterEquiv ℤ r).toRingHom).coeff j).coeff s).natDegree ≤ d
    rw [Polynomial.coeff_map]
    exact branchFirstParameterEquiv_coefficient_degree (p.coeff j) (hD j) s
  · intro j s k
    change |(((p.map (branchFirstParameterEquiv ℤ r).toRingHom).coeff j).coeff s).coeff k| ≤ _
    rw [Polynomial.coeff_map]
    exact (branchFirstParameterEquiv_coeff (p.coeff j) s k) ▸ hH j (s.cons k)

theorem branchFirstParameterEquiv_specialize {r : ℕ} (t : ℤ)
    (f : MvPolynomial (Fin (r + 1)) ℤ) :
    MvPolynomial.map (Polynomial.evalRingHom t) (branchFirstParameterEquiv ℤ r f) =
      branchHeadSpecialization t f := by
  have he : (MvPolynomial.map (Polynomial.evalRingHom t)).comp
      (branchFirstParameterEquiv ℤ r).toRingHom = branchHeadSpecialization t := by
    rw [branchFirstParameterEquiv_eq]
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [branchHeadSpecialization]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [branchHeadSpecialization]
  exact DFunLike.congr_fun he f

theorem branchFamilyParameterRearrangement_specialize {r : ℕ} (t : ℤ)
    (p : Polynomial (MvPolynomial (Fin (r + 1)) ℤ)) :
    (branchFamilyParameterRearrangement ℤ r p).map
      (MvPolynomial.map (Polynomial.evalRingHom t)) = branchFamilyHead t p := by
  apply Polynomial.ext
  intro j
  simp only [Polynomial.coeff_map, branchFamilyParameterRearrangement,
    Polynomial.mapEquiv_apply, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
    branchFamilyHead]
  exact branchFirstParameterEquiv_specialize t (p.coeff j)

theorem branchFirstParameterEquiv_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) {r : ℕ} (f : MvPolynomial (Fin (r + 1)) R) :
    MvPolynomial.map (Polynomial.mapRingHom φ) (branchFirstParameterEquiv R r f) =
      branchFirstParameterEquiv S r (MvPolynomial.map φ f) := by
  have he : (MvPolynomial.map (Polynomial.mapRingHom φ)).comp
      (branchFirstParameterEquiv R r).toRingHom =
        (branchFirstParameterEquiv S r).toRingHom.comp (MvPolynomial.map φ) := by
    rw [branchFirstParameterEquiv_eq, branchFirstParameterEquiv_eq]
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
  exact DFunLike.congr_fun he f

theorem branchFamilyParameterRearrangement_rational {r : ℕ}
    (p : Polynomial (MvPolynomial (Fin (r + 1)) ℤ)) :
    (branchFamilyParameterRearrangement ℤ r p).map
        (MvPolynomial.map (Polynomial.mapRingHom (Int.castRingHom ℚ))) =
      branchFamilyParameterRearrangement ℚ r (branchFamilyRational p) := by
  apply Polynomial.ext
  intro j
  simp only [branchFamilyParameterRearrangement, Polynomial.mapEquiv_apply,
    branchFamilyRational, Polynomial.coeff_map, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_toRingEquiv]
  exact branchFirstParameterEquiv_map (Int.castRingHom ℚ) (p.coeff j)

theorem branchFamilyParameterRearrangement_irreducible {r : ℕ}
    (p : Polynomial (MvPolynomial (Fin (r + 1)) ℤ))
    (hp : Irreducible (branchFamilyRational p)) :
    Irreducible ((branchFamilyParameterRearrangement ℤ r p).map
      (MvPolynomial.map (Polynomial.mapRingHom (Int.castRingHom ℚ)))) := by
  rw [branchFamilyParameterRearrangement_rational]
  exact (MulEquiv.irreducible_iff
    (f := (branchFamilyParameterRearrangement ℚ r).toMulEquiv)).mpr hp

theorem branchFamilyParameterRearrangement_eval_rational {r : ℕ} (t : ℤ)
    (p : Polynomial (MvPolynomial (Fin (r + 1)) ℤ)) :
    (branchFamilyParameterRearrangement ℤ r p).map
        (MvPolynomial.map ((Int.castRingHom ℚ).comp (Polynomial.evalRingHom t))) =
      branchFamilyRational (branchFamilyHead t p) := by
  have he : MvPolynomial.map (σ := Fin r)
      ((Int.castRingHom ℚ).comp (Polynomial.evalRingHom t)) =
      (MvPolynomial.map (Int.castRingHom ℚ)).comp
        (MvPolynomial.map (Polynomial.evalRingHom t)) := by
    apply RingHom.ext
    intro f
    exact (MvPolynomial.map_map _ _ _).symm
  rw [he, ← Polynomial.map_map, branchFamilyParameterRearrangement_specialize]
  rfl

end
end PierceLengthBound.FixedDividend
