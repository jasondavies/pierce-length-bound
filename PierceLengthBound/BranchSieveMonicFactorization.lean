/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveNestedFactorHeight
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

/-! Integral monic irreducible factorization, including multiplicities and
uniform bounds for every factor of a bounded bivariate polynomial. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial UniqueFactorizationMonoid

theorem branch_exists_integral_monic_factorization
    {R F : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (p : R[X]) (hp : p.Monic) :
    ∃ S : Multiset R[X], S.prod = p ∧ S.card ≤ p.natDegree ∧
      ∀ q ∈ S, q.Monic ∧ Irreducible (q.map (algebraMap R F)) ∧ q ∣ p := by
  classical
  let P := p.map (algebraMap R F)
  let G := normalizedFactors P
  have hG (q : {q : F[X] // q ∈ G}) :
      Irreducible q.val ∧ q.val.Monic ∧ q.val ∣ P :=
    (Polynomial.mem_normalizedFactors_iff (hp.map _).ne_zero).mp q.property
  have hlift (q : {q : F[X] // q ∈ G}) :
      ∃ q₀ : R[X], q₀.map (algebraMap R F) = q.val := by
    obtain ⟨q₀, hq₀⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd F hp (hG q).2.2
    rw [(hG q).2.1.leadingCoeff, Polynomial.C_1, mul_one] at hq₀
    exact ⟨q₀, hq₀⟩
  choose lift hlift using hlift
  let S := G.attach.map lift
  have hS (q : R[X]) (hq : q ∈ S) :
      q.Monic ∧ Irreducible (q.map (algebraMap R F)) ∧ q ∣ p := by
    obtain ⟨qF, _hqF, rfl⟩ := Multiset.mem_map.mp hq
    have hmonic : (lift qF).Monic := Polynomial.monic_of_injective
      (IsFractionRing.injective R F) (by rw [hlift]; exact (hG qF).2.1)
    exact ⟨hmonic, by rw [hlift]; exact (hG qF).1,
      hp.dvd_of_fraction_map_dvd_fraction_map hmonic (by rw [hlift]; exact (hG qF).2.2)⟩
  have hprod : S.prod = p := by
    apply Polynomial.map_injective _ (IsFractionRing.injective R F)
    change (Polynomial.mapRingHom (algebraMap R F)) S.prod = P
    rw [map_multiset_prod]
    change ((G.attach.map lift).map (Polynomial.map (algebraMap R F))).prod = P
    rw [Multiset.map_map]
    have he : Polynomial.map (algebraMap R F) ∘ lift = Subtype.val := funext hlift
    rw [he, Multiset.attach_map_val]
    have h := Polynomial.leadingCoeff_mul_prod_normalizedFactors P
    have hPm : P.Monic := hp.map _
    simpa only [hPm.leadingCoeff, Polynomial.C_1, one_mul] using h
  refine ⟨S, hprod, ?_, hS⟩
  rw [← hprod, natDegree_multiset_prod_of_monic S (fun q hq => (hS q hq).1)]
  have hpositive (q : R[X]) (hq : q ∈ S) : 1 ≤ q.natDegree := by
    apply Nat.succ_le_iff.mpr
    apply (hS q hq).1.natDegree_pos.mpr
    intro he
    have hir := (hS q hq).2.1
    simp only [he, Polynomial.map_one, not_irreducible_one] at hir
  clear hprod hS
  clear_value S
  revert hpositive
  induction S using Multiset.induction_on with
  | empty => simp
  | @cons q T ih =>
    intro hpositive
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
    have hq := hpositive q (Multiset.mem_cons_self _ _)
    have hT := ih (fun r hr => hpositive r (Multiset.mem_cons_of_mem hr))
    omega

theorem branch_bivariate_monic_factorization {F : Type*} [Field F]
    [Algebra ℤ[X] F] [IsFractionRing ℤ[X] F]
    (p : ℤ[X][X]) (hp : p.Monic) {d H : ℕ}
    (hd : CCDN.bivariateTotalDegree p ≤ d)
    (hH : ∀ i j, |(p.coeff i).coeff j| ≤ (H : ℤ)) :
    ∃ S : Multiset ℤ[X][X], S.prod = p ∧ S.card ≤ p.natDegree ∧
      ∀ q ∈ S, q.Monic ∧ Irreducible (q.map (algebraMap ℤ[X] F)) ∧
        q ∣ p ∧ CCDN.bivariateTotalDegree q ≤ d ∧
        ∀ i j, |(q.coeff i).coeff j| ≤
          (2 ^ ((d + 1) * d) * ((d + 1) * d + 1) * ((d + 1) ^ 2 * H) : ℕ) := by
  obtain ⟨S, hprod, hcard, hS⟩ := branch_exists_integral_monic_factorization (F := F) p hp
  refine ⟨S, hprod, hcard, ?_⟩
  intro q hq
  obtain ⟨hqm, hqir, hdiv⟩ := hS q hq
  exact ⟨hqm, hqir, hdiv, (branch_nested_totalDegree_le_of_dvd hp.ne_zero hdiv).trans hd,
    branch_nested_factor_coeff_height p hp.ne_zero hd hH q hdiv⟩

end
end PierceLengthBound.FixedDividend
