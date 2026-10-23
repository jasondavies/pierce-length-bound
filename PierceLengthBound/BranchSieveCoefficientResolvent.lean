/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveUniversalResolvent
public import PierceLengthBound.BranchSieveFactorSpecialization
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Data.Multiset.Fintype
import Mathlib.Tactic

/-! The coefficients of every monic factor of a split monic polynomial are
fixed polynomial expressions in an enumeration of its roots. Together with the
universal resolvents of `BranchSieveUniversalResolvent`, this gives coefficient
equations whose form depends only on the degree and a subset of root
positions. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Finset

/-- The `j`th coefficient of `∏_{i ∈ s} (X - X_i)`, as an integer polynomial in
the roots. -/
def branchFactorCoefficientExpression {d : ℕ} (s : Finset (Fin d)) (j : ℕ) :
    MvPolynomial (Fin d) ℤ :=
  (∏ i ∈ s, (Polynomial.X - Polynomial.C (X i)) :
    Polynomial (MvPolynomial (Fin d) ℤ)).coeff j

theorem branchFactorCoefficientExpression_eval {d : ℕ} (s : Finset (Fin d)) (j : ℕ)
    {A : Type*} [CommRing A] (roots : Fin d → A) :
    aeval roots (branchFactorCoefficientExpression s j) =
      (∏ i ∈ s, (Polynomial.X - Polynomial.C (roots i))).coeff j := by
  have hh := Polynomial.coeff_map (aeval roots).toRingHom
    (p := ∏ i ∈ s, (Polynomial.X - Polynomial.C (X i : MvPolynomial (Fin d) ℤ))) j
  simpa only [branchFactorCoefficientExpression, Polynomial.map_prod, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    aeval_X] using hh.symm

/-- A split degree-`d` polynomial admits an enumeration of its roots, with
multiplicities retained. -/
theorem branch_exists_root_enumeration {L : Type*} [Field L] (p : Polynomial L)
    (hsplit : p.Splits) :
    ∃ roots : Fin p.natDegree → L, Finset.univ.val.map roots = p.roots := by
  classical
  let e : Fin p.natDegree ≃ p.roots := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Multiset.card_coe, hsplit.natDegree_eq_card_roots])
  refine ⟨fun i => (e i : L), ?_⟩
  have he : Finset.univ.val.map e = (Finset.univ : Finset p.roots).val :=
    Multiset.map_univ_val_equiv e
  rw [show (fun i => (e i : L)) = (fun x : p.roots => (x : L)) ∘ e by rfl,
    ← Multiset.map_map, he, Multiset.map_univ_coe]

/-- All coefficients of a monic divisor use one common subset of root positions. -/
theorem branch_monic_factor_coefficient_expression {L : Type*} [Field L]
    (p : Polynomial L) (hp : p.Monic) (hsplit : p.Splits)
    (roots : Fin p.natDegree → L) (hroots : Finset.univ.val.map roots = p.roots)
    {q : Polynomial L} (hq : q.Monic) (hdiv : q ∣ p) :
    ∃ s : Finset (Fin p.natDegree), s.card = q.natDegree ∧
      ∀ j : ℕ, aeval roots (branchFactorCoefficientExpression s j) = q.coeff j := by
  classical
  have hqr : q.roots ≤ Finset.univ.val.map roots := by
    rw [hroots]
    exact Polynomial.roots.le_of_dvd hp.ne_zero hdiv
  obtain ⟨u, hu, humap⟩ := branch_submultiset_lifts roots hqr
  have hnodup : u.Nodup := Multiset.nodup_of_le hu (Finset.univ.nodup)
  let s : Finset (Fin p.natDegree) := ⟨u, hnodup⟩
  have hqsplit := hsplit.of_dvd hp.ne_zero hdiv
  have hprod : (∏ i ∈ s, (Polynomial.X - Polynomial.C (roots i))) = q := by
    rw [hqsplit.eq_prod_roots_of_monic hq, ← humap, Multiset.map_map]
    rfl
  refine ⟨s, ?_, ?_⟩
  · have hc := congrArg Multiset.card humap
    change u.card = q.natDegree
    simpa only [Multiset.card_map, ← hqsplit.natDegree_eq_card_roots] using hc
  · intro j
    rw [branchFactorCoefficientExpression_eval, hprod]

/-- The coefficients of `p` with the signs of the elementary symmetric functions
of its roots, read from degree `d - 1` downward. -/
def branchSignedCoefficients {R : Type*} [CommRing R] (p : Polynomial R) (d : ℕ) :
    Fin d → R := fun i => (-1) ^ (i.val + 1) * p.coeff (d - (i.val + 1))

/-- Vieta's formulas in the indexing of `branchSignedCoefficients`. -/
theorem branch_root_esymm_eq_signedCoefficient {L : Type*} [Field L]
    (p : Polynomial L) (hp : p.Monic) (hsplit : p.Splits)
    (roots : Fin p.natDegree → L) (hroots : Finset.univ.val.map roots = p.roots)
    (i : Fin p.natDegree) :
    (Finset.univ.val.map roots).esymm (i.val + 1) =
      branchSignedCoefficients p p.natDegree i := by
  rw [hroots]
  have hi : i.val + 1 ≤ p.natDegree := i.isLt
  have hv := Polynomial.coeff_eq_esymm_roots_of_splits hsplit
    (k := p.natDegree - (i.val + 1)) (Nat.sub_le _ _)
  rw [hp.leadingCoeff, one_mul, Nat.sub_sub_self hi] at hv
  dsimp only [branchSignedCoefficients]
  rw [hv, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- Every coefficient of every monic factor satisfies one of the fixed
universal equations, specialized solely at the original polynomial's coefficients. -/
theorem branch_monic_factor_universal_equation {L : Type*} [Field L]
    (p : Polynomial L) (hp : p.Monic) (hsplit : p.Splits)
    {q : Polynomial L} (hq : q.Monic) (hdiv : q ∣ p) :
    ∃ s : Finset (Fin p.natDegree), s.card = q.natDegree ∧
      ∀ j : ℕ,
        (branchUniversalResolvent (branchFactorCoefficientExpression s j)).eval₂
          (aeval (branchSignedCoefficients p p.natDegree)).toRingHom (q.coeff j) = 0 := by
  obtain ⟨roots, hroots⟩ := branch_exists_root_enumeration p hsplit
  obtain ⟨s, hs, hcoeff⟩ :=
    branch_monic_factor_coefficient_expression p hp hsplit roots hroots hq hdiv
  refine ⟨s, hs, ?_⟩
  intro j
  have hv := branch_universal_resolvent_equation (branchFactorCoefficientExpression s j)
    (branchUniversalResolvent_map _) roots
  have he : (fun i : Fin p.natDegree => (Finset.univ.val.map roots).esymm (i.val + 1)) =
      branchSignedCoefficients p p.natDegree := by
    funext i
    exact branch_root_esymm_eq_signedCoefficient p hp hsplit roots hroots i
  rwa [he, hcoeff] at hv

end
end PierceLengthBound.FixedDividend
