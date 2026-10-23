/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendCurveEquations
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# Finite prime decomposition of the fixed-dividend intersection

A prime first equation and genuine nondivisibility force every minimal prime of
the two-equation ideal to have height exactly two. No Hilbert-function degree or
Bézout estimate is assumed or claimed here.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- A nontrivial two-equation intersection with prime first equation is purely
of codimension two: all its minimal primes have height two. -/
theorem minimalPrime_pair_height_two {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] {f g : R} (hf : Prime f) (hfg : ¬ f ∣ g)
    {p : Ideal R} (hp : p ∈ (Ideal.span ({f, g} : Set R)).minimalPrimes) :
    p.height = 2 := by
  classical
  let : p.IsPrime := hp.isPrime
  let : (Ideal.span ({f} : Set R)).IsPrime := (Ideal.span_singleton_prime hf.ne_zero).mpr hf
  have hpf : Ideal.span ({f} : Set R) ≤ p :=
    (Ideal.span_mono (by simp : ({f} : Set R) ⊆ {f, g})).trans hp.le
  have hpg : g ∈ p := hp.le (Ideal.subset_span (by simp))
  have hlt : Ideal.span ({f} : Set R) < p := by
    apply lt_of_le_of_ne hpf
    intro he
    exact hfg (Ideal.mem_span_singleton.mp (he ▸ hpg))
  have h1 := Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr hf.ne_zero) hf.not_isUnit
  have hlo := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [h1] at hlo
  have hhi : p.height ≤ 2 := by
    have h := Ideal.height_le_card_of_mem_minimalPrimes_span_finset
      (s := ({f, g} : Finset R)) (by simpa using hp)
    exact h.trans (by exact_mod_cast (Finset.card_le_two : ({f, g} : Finset R).card ≤ 2))
  norm_num at hlo
  exact le_antisymm hhi hlo

/-- The zero locus of an ideal, with coordinates in its coefficient field. -/
def coordinateZeroLocus {K σ : Type*} [CommRing K] (I : Ideal (MvPolynomial σ K)) : Set (σ → K) :=
  {x | ∀ p ∈ I, MvPolynomial.eval x p = 0}

/-- Every common zero lies on a minimal-prime component, and conversely. -/
theorem common_zero_iff_minimalPrime {K σ : Type*} [Field K]
    (f g : MvPolynomial σ K) (x : σ → K) :
    (MvPolynomial.eval x f = 0 ∧ MvPolynomial.eval x g = 0) ↔
      ∃ p ∈ (Ideal.span ({f, g} : Set (MvPolynomial σ K))).minimalPrimes,
        x ∈ coordinateZeroLocus p := by
  constructor
  · rintro ⟨hf, hg⟩
    let φ := MvPolynomial.eval₂Hom (RingHom.id K) x
    let : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
    have hle : Ideal.span ({f, g} : Set (MvPolynomial σ K)) ≤ RingHom.ker φ := by
      rw [Ideal.span_le]
      intro p hp
      rcases hp with rfl | hp
      · exact hf
      · have : p = g := by simpa using hp
        subst p
        exact hg
    obtain ⟨p, hp, hpx⟩ := Ideal.exists_minimalPrimes_le hle
    exact ⟨p, hp, fun q hq => hpx hq⟩
  · rintro ⟨p, hp, hx⟩
    exact ⟨hx f (hp.le (Ideal.subset_span (by simp))),
      hx g (hp.le (Ideal.subset_span (by simp)))⟩

/-- A finite decomposition into prime zero loci, each of codimension two. -/
theorem finite_prime_decomposition_height_two {K σ : Type*} [Field K] [Finite σ]
    {f g : MvPolynomial σ K} (hf : Prime f) (hfg : ¬ f ∣ g) :
    ∃ S : Finset (Ideal (MvPolynomial σ K)),
      (∀ p ∈ S, p.IsPrime ∧ p.height = 2) ∧
      (∀ x, (MvPolynomial.eval x f = 0 ∧ MvPolynomial.eval x g = 0) ↔
        ∃ p ∈ S, x ∈ coordinateZeroLocus p) := by
  classical
  let hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing
    (MvPolynomial σ K) (Ideal.span ({f, g} : Set (MvPolynomial σ K)))
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro p hp
    have hp' := hfin.mem_toFinset.mp hp
    exact ⟨hp'.isPrime, minimalPrime_pair_height_two hf hfg hp'⟩
  · intro x
    simpa only [hfin.mem_toFinset] using common_zero_iff_minimalPrime f g x

lemma curveQuadratic_degree_le_two {K : Type*} [CommRing K] [Nontrivial K]
    (ρ u v ρ' u' v' : K) : (curveQuadratic ρ u v ρ' u' v').totalDegree ≤ 2 :=
  lineQuadratic_totalDegree_le_two ρ u v ρ' u' v' MvPolynomial.X (by simp)

lemma curveNorm_degree_le_three {K : Type*} [CommRing K] [Nontrivial K]
    (ρ u v ρ' u' v' : K) : (curveNorm ρ u v ρ' u' v').totalDegree ≤ 3 :=
  lineNorm_totalDegree_le_three ρ u v ρ' u' v' MvPolynomial.X (by simp)

lemma curveResultant_degree_le_ten {K : Type*} [Field K]
    (ρ u v ρ' u' v' : K) : (curveResultant ρ u v ρ' u' v').totalDegree ≤ 10 := by
  unfold curveResultant
  apply fixed_dividend_resultant_totalDegree_le_ten
  intro j
  fin_cases j
  all_goals simp only [completeNodes, Fin.reduceFinMk, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  all_goals try exact le_of_eq (MvPolynomial.totalDegree_X _)
  change (fourthNode (MvPolynomial.C ρ) (MvPolynomial.C u) (MvPolynomial.C v)
    (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) :
      MvPolynomial (Fin 3) K).totalDegree ≤ 1
  have he : (fourthNode (MvPolynomial.C ρ) (MvPolynomial.C u) (MvPolynomial.C v)
      (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) : MvPolynomial (Fin 3) K) =
      MvPolynomial.C (ρ + u) * MvPolynomial.X 0 +
      MvPolynomial.C (-u + v) * MvPolynomial.X 1 +
      MvPolynomial.C (1 - v) * MvPolynomial.X 2 := by
    simp [fourthNode]
    ring
  rw [he]
  exact linear_form_degree_le _ _ _

end
end PierceLengthBound.FixedDividend
