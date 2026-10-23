/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveFactorWitness
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.FieldTheory.Minpoly.Finite
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Data.Multiset.Powerset
public import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.Tactic

/-! A bounded finite family of irreducible coefficient equations covers
every nonconstant proper factor over a splitting extension. This is the
algebraic finite-family step of the effective Hilbert sieve. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial Finset

variable {L : Type*} [Field L]

/-- A split degree-`d` polynomial has at most `2^d` monic divisors. -/
theorem branch_monic_factor_card_le (p : L[X]) (hp : p ≠ 0) (hsplit : p.Splits) :
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

variable {F : Type*} [Field F] [Algebra F L] [Module.Finite F L]

/-- The splitting-extension degree is uniformly bounded in terms of the
original degree. This bounds the root-variable degrees of coefficient equations. -/
theorem branch_splittingField_finrank_le_factorial (p : F[X]) (hp : p.Separable) :
    Module.finrank F p.SplittingField ≤ p.natDegree.factorial := by
  classical
  let : Fact ((p.map (algebraMap F p.SplittingField)).Splits) :=
    ⟨IsSplittingField.splits p.SplittingField p⟩
  have hcard := Fintype.card_le_of_injective (Polynomial.Gal.galActionHom p p.SplittingField)
    (Polynomial.Gal.galActionHom_injective p p.SplittingField)
  rw [Fintype.card_perm, Polynomial.card_rootSet_eq_natDegree hp
    (IsSplittingField.splits p.SplittingField p)] at hcard
  simpa only [← Nat.card_eq_fintype_card, Polynomial.Gal.card_of_separable hp] using hcard

/-- One finite set of irreducible coefficient equations detects all proper
monic factors. Its size is bounded by `2^deg p`, and its equation degrees
lie between two and the splitting-extension degree. -/
theorem branch_exists_factor_equation_family {p : F[X]}
    (hp : Irreducible p) (hpmonic : p.Monic)
    (hsplit : (p.map (algebraMap F L)).Splits) :
    ∃ E : Finset F[X], E.card ≤ 2 ^ p.natDegree ∧
      (∀ f ∈ E, Irreducible f ∧ 2 ≤ f.natDegree ∧ f.natDegree ≤ Module.finrank F L) ∧
      ∀ q : L[X], q.Monic → q ∣ p.map (algebraMap F L) →
        0 < q.natDegree → q.natDegree < p.natDegree →
        ∃ f ∈ E, ∃ j : ℕ, aeval (q.coeff j) f = 0 := by
  classical
  let P := p.map (algebraMap F L)
  have hP : P ≠ 0 := Polynomial.map_ne_zero hp.ne_zero
  let := Polynomial.fintypeSubtypeMonicDvd P hP
  let G := {q : L[X] // q.Monic ∧ q ∣ P}
  let S : Finset G := Finset.univ.filter
    (fun q => 0 < q.val.natDegree ∧ q.val.natDegree < p.natDegree)
  have hw : ∀ q : S, ∃ j : ℕ, Irreducible (minpoly F (q.val.val.coeff j)) ∧
      2 ≤ (minpoly F (q.val.val.coeff j)).natDegree ∧
      aeval (q.val.val.coeff j) (minpoly F (q.val.val.coeff j)) = 0 := by
    intro q
    obtain ⟨hpos, hlt⟩ := (mem_filter.mp q.property).2
    exact branch_proper_factor_minpoly_witness hp hpmonic q.val.property.1
      q.val.property.2 hpos hlt
  choose j hj using hw
  let f : S → F[X] := fun q => minpoly F (q.val.val.coeff (j q))
  let E := Finset.univ.image f
  refine ⟨E, ?_, ?_, ?_⟩
  · apply (Finset.card_image_le.trans (by simp : Finset.univ.card ≤ Fintype.card S)).trans
    apply (show Fintype.card S ≤ Fintype.card G from by
      simpa only [Fintype.card_coe] using Finset.card_le_univ S).trans
    simpa only [P, Polynomial.natDegree_map] using branch_monic_factor_card_le P hP hsplit
  · intro g hg
    obtain ⟨q, _hq, rfl⟩ := mem_image.mp hg
    exact ⟨(hj q).1, (hj q).2.1, minpoly.natDegree_le (q.val.val.coeff (j q))⟩
  · intro q hq hdiv hpos hlt
    let qG : G := ⟨q, hq, hdiv⟩
    have hqS : qG ∈ S := mem_filter.mpr ⟨mem_univ _, hpos, hlt⟩
    let qS : S := ⟨qG, hqS⟩
    exact ⟨f qS, mem_image.mpr ⟨qS, mem_univ _, rfl⟩, j qS, (hj qS).2.2⟩

end
end PierceLengthBound.FixedDividend
