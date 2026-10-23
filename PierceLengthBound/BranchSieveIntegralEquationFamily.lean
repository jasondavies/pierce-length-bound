/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveIntegerSpecialization
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Data.Multiset.Powerset
import Mathlib.Tactic

/-! A single finite family of integral coefficient equations covers all
proper factors at all integer specializations. Its cardinality depends only
on the original polynomial degree. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial Finset

/-- A split degree-`d` polynomial has at most `2^d` monic divisors. -/
theorem branch_monic_factor_card_le {L : Type*} [Field L] (p : L[X]) (hp : p ≠ 0)
    (hsplit : p.Splits) :
    letI := Polynomial.fintypeSubtypeMonicDvd p hp
    Fintype.card {q : L[X] // q.Monic ∧ q ∣ p} ≤ 2 ^ p.natDegree := by
  classical
  let := Polynomial.fintypeSubtypeMonicDvd p hp
  let S := p.roots.powerset.toFinset
  let f : {q : L[X] // q.Monic ∧ q ∣ p} → S := fun q =>
    ⟨q.val.roots, Multiset.mem_toFinset.mpr
      (Multiset.mem_powerset.mpr (Polynomial.roots.le_of_dvd hp q.property.2))⟩
  have hinj : Function.Injective f := by
    intro q r h
    have hr : q.val.roots = r.val.roots := congrArg Subtype.val h
    apply Subtype.ext
    rw [(hsplit.of_dvd hp q.property.2).eq_prod_roots_of_monic q.property.1,
      (hsplit.of_dvd hp r.property.2).eq_prod_roots_of_monic r.property.1, hr]
  apply (Fintype.card_le_of_injective f hinj).trans
  rw [Fintype.card_coe]
  apply (Multiset.toFinset_card_le _).trans
  rw [Multiset.card_powerset]
  exact Nat.pow_le_pow_right (by norm_num) (Polynomial.card_roots' p)

variable {R F L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field L] [Algebra R L] [Algebra F L] [IsScalarTower R F L]

/-- One finite family of monic integral coefficient equations, each recorded with the
factor and coefficient it comes from, contains every factor-coefficient minimal
polynomial of degree at least two. -/
theorem branch_exists_integral_equation_family (p : R[X]) (hp : p.Monic)
    (hsplit : (p.map (algebraMap R L)).Splits) :
    ∃ E : Finset R[X], E.card ≤ 2 ^ p.natDegree * (p.natDegree + 1) ∧
      (∀ f ∈ E, f.Monic ∧ Irreducible (f.map (algebraMap R F)) ∧ 2 ≤ f.natDegree ∧
        ∃ q : Polynomial (integralClosure R L), q.Monic ∧
          q ∣ p.map (algebraMap R (integralClosure R L)) ∧
          ∃ j ≤ p.natDegree, f = minpoly R (q.coeff j)) ∧
      ∀ q : Polynomial (integralClosure R L), q.Monic →
        q ∣ p.map (algebraMap R (integralClosure R L)) →
        ∀ j : ℕ, 2 ≤ (minpoly R (q.coeff j)).natDegree → minpoly R (q.coeff j) ∈ E := by
  classical
  let S := integralClosure R L
  let P := p.map (algebraMap R L)
  let := Polynomial.fintypeSubtypeMonicDvd P (hp.map _).ne_zero
  let G := {q : S[X] // q.Monic ∧ q ∣ p.map (algebraMap R S)}
  let Gext := {q : L[X] // q.Monic ∧ q ∣ P}
  let toL : G → Gext := fun q => ⟨q.val.map (algebraMap S L), q.property.1.map _, by
    simpa only [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] using
      Polynomial.map_dvd (algebraMap S L) q.property.2⟩
  have hinj : Function.Injective toL := by
    intro q r h
    apply Subtype.ext
    exact Polynomial.map_injective (algebraMap S L)
      (FaithfulSMul.algebraMap_injective S L) (congrArg Subtype.val h)
  let := Fintype.ofInjective toL hinj
  have hGcard : Fintype.card G ≤ 2 ^ p.natDegree := by
    apply (Fintype.card_le_of_injective toL hinj).trans
    simpa only [P, hp.natDegree_map] using branch_monic_factor_card_le P (hp.map _).ne_zero hsplit
  let make : G × Fin (p.natDegree + 1) → R[X] := fun x => minpoly R (x.1.val.coeff x.2.val)
  let E := (Finset.univ.image make).filter (fun f => 2 ≤ f.natDegree)
  refine ⟨E, ?_, ?_, ?_⟩
  · apply (Finset.card_filter_le _ _).trans
    apply Finset.card_image_le.trans
    simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using
      Nat.mul_le_mul_right (p.natDegree + 1) hGcard
  · intro f hf
    obtain ⟨himage, hfdeg⟩ := Finset.mem_filter.mp hf
    obtain ⟨⟨q, j⟩, _hq, rfl⟩ := Finset.mem_image.mp himage
    have hint := Polynomial.isIntegral_coeff_of_dvd p q.val hp q.property.1 q.property.2 j.val
    have hmin := minpoly.isIntegrallyClosed_eq_field_fractions F L hint
    have hqLdiv : q.val.map (algebraMap S L) ∣
        (p.map (algebraMap R F)).map (algebraMap F L) := by
      simpa only [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] using
        Polynomial.map_dvd (algebraMap S L) q.property.2
    have hintF := Polynomial.isIntegral_coeff_of_dvd (p.map (algebraMap R F))
      (q.val.map (algebraMap S L)) (hp.map _) (q.property.1.map _) hqLdiv j.val
    refine ⟨minpoly.monic hint, ?_, hfdeg, q.val, q.property.1, q.property.2,
      j.val, by omega, rfl⟩
    change Irreducible ((minpoly R (q.val.coeff j.val)).map (algebraMap R F))
    rw [← hmin]
    simpa only [Polynomial.coeff_map] using minpoly.irreducible hintF
  · intro q hq hdiv j hdeg
    have hc : q.coeff j ≠ 0 := by
      intro hz
      have hzdeg : (minpoly R (0 : integralClosure R L)).natDegree ≤ 1 := by
        simpa only [Polynomial.natDegree_X] using Polynomial.natDegree_le_natDegree
          (minpoly.min R (0 : integralClosure R L) Polynomial.monic_X (by simp))
      rw [hz] at hdeg
      omega
    have hj : j ≤ p.natDegree := by
      apply (Polynomial.le_natDegree_of_ne_zero hc).trans
      simpa only [hp.natDegree_map] using Polynomial.natDegree_le_of_dvd hdiv (hp.map _).ne_zero
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
      ⟨⟨⟨q, hq, hdiv⟩, ⟨j, by omega⟩⟩, Finset.mem_univ _, rfl⟩, hdeg⟩

end
end PierceLengthBound.FixedDividend
