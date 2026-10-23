/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.MvPolynomial.Groebner
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
public import PierceLengthBound.FixedDividendFilteredIntersection

/-!
# Standard monomials in a filtered coordinate ring

Division by all nonzero ideal elements produces a unique representative supported
on standard monomials. Degree lexicographic order preserves the total-degree
filtration, giving an exact combinatorial model for its dimensions.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- Exponents not divisible by any leading exponent of a nonzero ideal element. -/
def standardExponents {K σ : Type*} [Field K] (I : Ideal (MvPolynomial σ K))
    (m : MonomialOrder σ) : Set (σ →₀ ℕ) :=
  {a | ∀ f ∈ I, f ≠ 0 → ¬ m.degree f ≤ a}

lemma standardExponents_lower {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ) :
    IsLowerSet (standardExponents I m) := by
  intro a b hab hb f hf hn hfa
  exact hb f hf hn (hfa.trans hab)

/-- A standard polynomial belonging to the ideal is zero. -/
lemma standard_polynomial_eq_zero {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ)
    {f : MvPolynomial σ K} (hf : f ∈ restrictSupport K (standardExponents I m))
    (hI : f ∈ I) : f = 0 := by
  by_contra hn
  exact (hf (m.degree_mem_support hn)) f hI hn le_rfl

/-- Degree-compatible division gives a standard representative in the same
filtered piece of the quotient. -/
theorem exists_standard_representative {K σ : Type*} [Field K]
    [LinearOrder σ] [WellFoundedGT σ] (I : Ideal (MvPolynomial σ K))
    (f : MvPolynomial σ K) :
    ∃ r : MvPolynomial σ K,
      r ∈ restrictSupport K (standardExponents I MonomialOrder.degLex) ∧
      r.totalDegree ≤ f.totalDegree ∧ f - r ∈ I := by
  classical
  let B : Set (MvPolynomial σ K) := {b | b ∈ I ∧ b ≠ 0}
  obtain ⟨g, r, hsum, hdeg, hstd⟩ :=
    MonomialOrder.div_set (m := MonomialOrder.degLex)
      (B := B) (fun b hb => MonomialOrder.isUnit_leadingCoeff.mpr hb.2) f
  refine ⟨r, ?_, ?_, ?_⟩
  · intro a ha b hb hn
    exact hstd a ha b ⟨hb, hn⟩
  · have hg : Finsupp.linearCombination (MvPolynomial σ K)
        (fun b : B => b.val) g ∈ restrictTotalDegree σ K f.totalDegree := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      apply Submodule.sum_mem
      intro b _
      rw [smul_eq_mul, mul_comm, mem_restrictTotalDegree]
      exact degLex_totalDegree_monotone (hdeg b)
    have hr : r = f - Finsupp.linearCombination (MvPolynomial σ K)
        (fun b : B => b.val) g := by rw [hsum]; ring
    rw [← mem_restrictTotalDegree, hr]
    exact Submodule.sub_mem _ (by rw [mem_restrictTotalDegree]) hg
  · have hg : Finsupp.linearCombination (MvPolynomial σ K)
        (fun b : B => b.val) g ∈ I := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      apply I.sum_mem
      intro b _
      exact I.mul_mem_left _ b.property.1
    simpa only [hsum, add_sub_cancel_right] using hg

/-- Standard exponents of total degree at most `N`. -/
def boundedStandardExponents {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (m : MonomialOrder σ) (N : ℕ) : Set (σ →₀ ℕ) :=
  {a | a ∈ standardExponents I m ∧ a.sum (fun _ e => e) ≤ N}

/-- Standard representatives describe precisely each filtered coordinate space. -/
theorem map_bounded_standard_eq {K σ : Type*} [Field K]
    [LinearOrder σ] [WellFoundedGT σ] (I : Ideal (MvPolynomial σ K)) (N : ℕ) :
    (restrictSupport K (boundedStandardExponents I MonomialOrder.degLex N)).map
        (Ideal.Quotient.mkₐ K I).toLinearMap = filteredCoordinateSpace I N := by
  apply le_antisymm
  · apply Submodule.map_mono
    exact restrictSupport_mono K (fun _ ha => ha.2)
  · rintro y ⟨f, hf, rfl⟩
    obtain ⟨r, hr, hdegree, hI⟩ := exists_standard_representative I f
    refine Submodule.mem_map.mpr ⟨r, ?_, ?_⟩
    · intro a ha
      exact ⟨hr ha, (le_totalDegree ha).trans
        (hdegree.trans ((mem_restrictTotalDegree σ N f).mp hf))⟩
    · have hq := Ideal.Quotient.eq_zero_iff_mem.mpr hI
      rw [map_sub, sub_eq_zero] at hq
      exact hq.symm

/-- The filtered Hilbert function counts the standard monomials of bounded degree. -/
theorem filteredCoordinateSpace_finrank_eq_standard_card {K σ : Type*} [Field K]
    [LinearOrder σ] [WellFoundedGT σ] (I : Ideal (MvPolynomial σ K)) (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace I N) =
      Nat.card (boundedStandardExponents I MonomialOrder.degLex N) := by
  let V := restrictSupport K (boundedStandardExponents I MonomialOrder.degLex N)
  let φ := (Ideal.Quotient.mkₐ K I).toLinearMap.comp V.subtype
  have hinj : Function.Injective φ := by
    intro f g h
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply standard_polynomial_eq_zero I MonomialOrder.degLex
    · apply Submodule.sub_mem
      · exact restrictSupport_mono K (fun _ ha => ha.1) f.property
      · exact restrictSupport_mono K (fun _ ha => ha.1) g.property
    · apply Ideal.Quotient.eq_zero_iff_mem.mp
      change (Ideal.Quotient.mkₐ K I) (f.val - g.val) = 0
      rw [map_sub, sub_eq_zero]
      exact h
  have hrange : φ.range = filteredCoordinateSpace I N := by
    rw [show φ = (Ideal.Quotient.mkₐ K I).toLinearMap.comp V.subtype from rfl,
      LinearMap.range_comp, Submodule.range_subtype]
    exact map_bounded_standard_eq I N
  rw [← hrange, LinearMap.finrank_range_of_inj hinj]
  exact Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)

end
end PierceLengthBound.FixedDividend
