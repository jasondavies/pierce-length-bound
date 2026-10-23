/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib

/-!
# Separating prime components

Finite incomparable prime components admit polynomial separators. The accompanying
linear algebra combines independent families detected on distinct components.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- Distinct minimal primes are incomparable. -/
lemma minimalPrimes_not_le {R : Type*} [CommRing R] (I : Ideal R)
    {p q : Ideal R} (hp : p ∈ I.minimalPrimes) (hq : q ∈ I.minimalPrimes)
    (hne : p ≠ q) : ¬ p ≤ q := by
  intro h
  exact hne (le_antisymm h (hq.2 hp.1 h))

/-- An element separating one minimal prime from every other member of a finite
family of minimal primes. -/
theorem exists_component_separator {R : Type*} [CommRing R] (I : Ideal R)
    (S : Finset (Ideal R)) (hS : ∀ p ∈ S, p ∈ I.minimalPrimes)
    {p : Ideal R} (hp : p ∈ S) :
    ∃ r : R, r ∉ p ∧ ∀ q ∈ S, q ≠ p → r ∈ q := by
  classical
  let : p.IsPrime := (hS p hp).isPrime
  have hex (q : {q : Ideal R // q ∈ S.erase p}) : ∃ x : R, x ∈ q.val ∧ x ∉ p := by
    have hne := (Finset.mem_erase.mp q.property).1
    have hq := (Finset.mem_erase.mp q.property).2
    have hnot := minimalPrimes_not_le I (hS q.val hq) (hS p hp) hne
    by_contra h
    apply hnot
    intro x hx
    by_contra hxp
    exact h ⟨x, hx, hxp⟩
  choose r hrmem hrnot using hex
  refine ⟨∏ q : {q : Ideal R // q ∈ S.erase p}, r q, ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨q, _, hq⟩
    exact hrnot q hq
  · intro q hq hne
    exact q.prod_mem (i := ⟨q, Finset.mem_erase.mpr ⟨hne, hq⟩⟩) (by simp)
      (hrmem ⟨q, Finset.mem_erase.mpr ⟨hne, hq⟩⟩)

/-- Independent families remain jointly independent when linear maps separate
one family from all the others. -/
theorem linearIndependent_of_separating_maps {K V ι κ : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Finite ι] [Finite κ]
    (W : ι → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (φ : ∀ i, V →ₗ[K] W i) (v : ι → κ → V)
    (hoff : ∀ i j, i ≠ j → ∀ k, φ i (v j k) = 0)
    (hon : ∀ i, LinearIndependent K (fun k => φ i (v i k))) :
    LinearIndependent K (fun p : ι × κ => v p.1 p.2) := by
  classical
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  rw [Fintype.linearIndependent_iff]
  intro a ha p
  obtain ⟨i, k⟩ := p
  have hm := congrArg (φ i) ha
  simp only [map_sum, map_smul, map_zero, Fintype.sum_prod_type] at hm
  have hrow : ∑ j, ∑ k, a (j, k) • φ i (v j k) = ∑ k, a (i, k) • φ i (v i k) := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      simp [hoff i j hji.symm]
    · simp
  rw [hrow] at hm
  exact Fintype.linearIndependent_iff.mp (hon i) (fun k => a (i, k)) hm k


/-- Powers of a transcendental element are linearly independent. -/
lemma transcendental_powers_independent {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    {y : A} (hy : Transcendental K y) : LinearIndependent K (fun n : ℕ => y ^ n) := by
  have h := (Polynomial.basisMonomials K).linearIndependent.map'
    (Polynomial.aeval y).toLinearMap
    (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp hy))
  simpa [Function.comp_def, Polynomial.coe_basisMonomials,
    Polynomial.monomial_one_right_eq_X_pow] using h

end
end PierceLengthBound.FixedDividend
