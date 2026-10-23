/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveUniformResolvents
public import PierceLengthBound.BranchSieveIntegerSpecialization
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Data.Multiset.Powerset
import Mathlib.Tactic

/-! A single finite family of monic irreducible integral coefficient equations
covers every proper monic factor at every integer specialization. Its
cardinality is at most `2^n (n + 1)`, and its degree and height bounds depend
only on the degree `n` and the coefficient degree bound `D`, with height
polynomial in the coefficient height `H`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

section IntegralEquations
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

end IntegralEquations

open Polynomial

/-- For a monic `p ∈ ℤ[X][X]` of degree `n`, irreducible over the fraction field,
with coefficients of degree at most `D` and height at most `H`, there is a family
of at most `2^n (n + 1)` monic irreducible equations of total degree at most `M`
and height at most `C (H + 1)^E` such that every proper monic factor of every
integer specialization yields an integer root of one specialized equation. The
constants depend only on `n` and `D`. -/
theorem branch_uniform_integer_equation_family (n D : ℕ) :
    ∃ M E C : ℕ, 0 < C ∧ ∀ (F L : Type*) [Field F]
      [Algebra ℤ[X] F] [IsFractionRing ℤ[X] F] [Field L]
      [Algebra ℤ[X] L] [Algebra F L] [IsScalarTower ℤ[X] F L]
      [FaithfulSMul ℤ[X] L],
      ∀ (p : ℤ[X][X]), p.Monic → p.natDegree = n →
      Irreducible (p.map (algebraMap ℤ[X] F)) →
      (p.map (algebraMap ℤ[X] L)).Splits →
      ∀ H : ℕ, (∀ j, (p.coeff j).natDegree ≤ D) →
      (∀ i j, |(p.coeff i).coeff j| ≤ (H : ℤ)) →
      ∃ G : Finset ℤ[X][X], G.card ≤ 2 ^ n * (n + 1) ∧
      (∀ f ∈ G, f.Monic ∧ Irreducible (f.map (algebraMap ℤ[X] F)) ∧
        2 ≤ f.natDegree ∧ CCDN.bivariateTotalDegree f ≤ M ∧
        ∀ i j, |(f.coeff i).coeff j| ≤ (C * (H + 1) ^ E : ℕ)) ∧
      ∀ (t : ℤ) (q : ℤ[X]), q.Monic → q ∣ p.map (evalRingHom t) →
        0 < q.natDegree → q.natDegree < n →
        ∃ f ∈ G, ∃ y : ℤ, (f.map (evalRingHom t)).eval y = 0 := by
  obtain ⟨M, E, C, hC, hb⟩ := branch_uniform_integral_minpoly_bounds n D
  refine ⟨M, E, C, hC, ?_⟩
  intro F L _ _ _ _ _ _ _ _ p hp hn hir hsplit H hD hH
  obtain ⟨G, hcard, hG, hcover⟩ :=
    branch_exists_integral_equation_family (F := F) p hp hsplit
  refine ⟨G, by simpa only [hn] using hcard, ?_, ?_⟩
  · intro f hf
    obtain ⟨hfm, hfir, hfdeg, q, hq, hdiv, j, hj, rfl⟩ := hG f hf
    obtain ⟨hdegree, hheight⟩ := hb L p hp hn hsplit H hD hH q hq hdiv j (hn ▸ hj)
    exact ⟨hfm, hfir, hfdeg, hdegree, hheight⟩
  · intro t q hq hdiv hqpos hqlt
    obtain ⟨q₀, hq₀, hq₀div, j, _hfm, _hfir, hfdeg, hroot⟩ :=
      branch_integer_specialization_witness p hp hir hsplit t q hq hdiv hqpos
        (by simpa only [hn] using hqlt)
    refine ⟨_, hcover q₀ hq₀ hq₀div j hfdeg, q.coeff j, ?_⟩
    simpa only [Polynomial.eval_map, Polynomial.eval₂_evalRingHom] using hroot

end
end PierceLengthBound.FixedDividend
