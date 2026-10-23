/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveMultivariateKronecker
public import PierceLengthBound.BranchSieveFactorSpecialization
public import PierceLengthBound.BranchSieveNestedFactorHeight
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import Mathlib.Data.Multiset.Powerset
import Mathlib.Tactic

/-! Regrouping specialized irreducible factors and extracting the nonzero
coefficient obstructions in the multivariable Kronecker argument. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial Finset UniqueFactorizationMonoid

theorem branchMultiKronecker_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (a n : ℕ) (p : MvPolynomial (Fin n) R) :
    (branchMultiKronecker a n p).map φ =
      branchMultiKronecker a n (MvPolynomial.map φ p) := by
  have he : (Polynomial.mapRingHom φ).comp (branchMultiKronecker a n) =
      (branchMultiKronecker a n).comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [branchMultiKronecker]
    · intro i
      simp [branchMultiKronecker]
  exact DFunLike.congr_fun he p

/-- Bounded-digit encoding never merges coefficients. Every encoded
coefficient is either zero or exactly one original coefficient. -/
theorem branchMultiKronecker_coefficient_cases {R : Type*} [CommSemiring R]
    {a n : ℕ} (p : MvPolynomial (Fin n) R) (ha : ∀ i, p.degreeOf i < a) (k : ℕ) :
    (branchMultiKronecker a n p).coeff k = 0 ∨
      ∃ s ∈ p.support, (branchMultiKronecker a n p).coeff k = p.coeff s := by
  classical
  by_cases hs : ∃ s ∈ p.support, branchMultiWeight a s = k
  · obtain ⟨s, hs, he⟩ := hs
    right
    exact ⟨s, hs, he ▸ branchMultiKronecker_coeff ha hs⟩
  · left
    conv_lhs => rw [p.as_sum, map_sum, Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro s hs'
    rw [branchMultiKronecker_monomial, Polynomial.coeff_monomial_of_ne]
    exact fun he => hs ⟨s, hs', he.symm⟩

theorem branchMultiKronecker_nested_height {a n H : ℕ}
    (p : MvPolynomial (Fin n) ℤ[X]) (ha : ∀ i, p.degreeOf i < a)
    (hH : ∀ s j, |(p.coeff s).coeff j| ≤ (H : ℤ)) (k j : ℕ) :
    |((branchMultiKronecker a n p).coeff k).coeff j| ≤ (H : ℤ) := by
  obtain hz | ⟨s, _, hs⟩ := branchMultiKronecker_coefficient_cases p ha k
  · simp [hz]
  · rw [hs]
    exact hH s j

theorem branchMultiKronecker_coefficient_degree {R : Type*} [CommSemiring R]
    {a n D : ℕ} (p : MvPolynomial (Fin n) R[X]) (ha : ∀ i, p.degreeOf i < a)
    (hD : ∀ s, (p.coeff s).natDegree ≤ D) (k : ℕ) :
    ((branchMultiKronecker a n p).coeff k).natDegree ≤ D := by
  obtain hz | ⟨s, _, hs⟩ := branchMultiKronecker_coefficient_cases p ha k
  · simp [hz]
  · rw [hs]
    exact hD s

theorem branch_multivariate_coefficient_degree_mul_le
    {σ R : Type*} [CommRing R] (f g : MvPolynomial σ R[X]) {D E : ℕ}
    (hf : ∀ s, (f.coeff s).natDegree ≤ D)
    (hg : ∀ s, (g.coeff s).natDegree ≤ E) (s : σ →₀ ℕ) :
    ((f * g).coeff s).natDegree ≤ D + E := by
  classical
  rw [MvPolynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro u hu
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hf u.1) (hg u.2))

theorem branchMultiDecode_coefficient_degree_le
    {R : Type*} [CommRing R] (a n : ℕ) (p : R[X][X]) {D : ℕ}
    (hp : ∀ j, (p.coeff j).natDegree ≤ D) (s : Fin n →₀ ℕ) :
    ((branchMultiDecode a n p).coeff s).natDegree ≤ D := by
  classical
  change ((∑ u : Fin n → Fin a, MvPolynomial.monomial (branchMultiExponent u)
    (p.coeff (branchMultiWeight a (branchMultiExponent u)))).coeff s).natDegree ≤ D
  rw [MvPolynomial.coeff_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro u hu
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · exact hp _
  · simp

theorem branch_kronecker_residual_coefficient_degree_le
    {R : Type*} [CommRing R] (a n : ℕ) (f : MvPolynomial (Fin n) R[X])
    (q q' : R[X][X]) {D : ℕ}
    (hf : ∀ s, (f.coeff s).natDegree ≤ D)
    (hq : ∀ j, (q.coeff j).natDegree ≤ D)
    (hq' : ∀ j, (q'.coeff j).natDegree ≤ D) (s : Fin n →₀ ℕ) :
    ((f - branchMultiDecode a n q * branchMultiDecode a n q').coeff s).natDegree ≤ 2 * D := by
  rw [MvPolynomial.coeff_sub]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact (hf s).trans (by omega)
  · simpa only [two_mul] using
      (branch_multivariate_coefficient_degree_mul_le
        (branchMultiDecode a n q) (branchMultiDecode a n q')
        (branchMultiDecode_coefficient_degree_le a n q hq)
        (branchMultiDecode_coefficient_degree_le a n q' hq') s)

/-- If every factor remains irreducible after specialization, a monic
specialized divisor is exactly a product of a submultiset of the original
factors. Multiplicities are retained. -/
theorem branch_irreducible_factor_specialization_lifts
    {R K : Type*} [CommRing R] [Field K] (φ : R →+* K)
    (Q : Multiset R[X]) (hmonic : ∀ q ∈ Q, q.Monic)
    (hirr : ∀ q ∈ Q, Irreducible (q.map φ))
    (g : K[X]) (hg : g.Monic) (hdiv : g ∣ Q.prod.map φ) :
    ∃ U : Multiset R[X], U ≤ Q ∧ U.prod.map φ = g := by
  classical
  let Q' := Q.map (Polynomial.map φ)
  have hQ' : ∀ q ∈ Q', q.Monic ∧ Irreducible q := by
    intro q hq
    change q ∈ Q.map (Polynomial.map φ) at hq
    obtain ⟨q₀, hq₀, rfl⟩ := Multiset.mem_map.mp hq
    exact ⟨(hmonic q₀ hq₀).map φ, hirr q₀ hq₀⟩
  have hQ0 : Q'.prod ≠ 0 := Multiset.prod_ne_zero fun h => (hQ' 0 h).1.ne_zero rfl
  have hnorm : normalizedFactors Q'.prod = Q' := by
    rw [normalizedFactors_prod_eq Q' (fun q hq => (hQ' q hq).2)]
    simpa only [Multiset.map_id'] using
      Multiset.map_congr rfl fun q hq => (hQ' q hq).1.normalize_eq_self
  have hle : normalizedFactors g ≤ Q' := by
    rw [← hnorm]
    apply (dvd_iff_normalizedFactors_le_normalizedFactors hg.ne_zero hQ0).mp
    simpa only [Q', Polynomial.map_multiset_prod] using hdiv
  obtain ⟨U, hU, hmap⟩ := branch_submultiset_lifts (Polynomial.map φ) hle
  refine ⟨U, hU, ?_⟩
  rw [Polynomial.map_multiset_prod, hmap, prod_normalizedFactors_eq hg.ne_zero,
    hg.normalize_eq_self]

/-- A candidate factorization of an irreducible family cannot become a
proper factorization unless a nonzero coefficient of its residual vanishes. -/
theorem branch_factor_specialization_nonzero_residual
    {σ K : Type*} [Field K]
    (f g h : MvPolynomial σ K[X]) (hf : Irreducible f) (t : K)
    (hfactor : MvPolynomial.map (evalRingHom t) f =
      MvPolynomial.map (evalRingHom t) g * MvPolynomial.map (evalRingHom t) h)
    (hg : ¬ IsUnit (MvPolynomial.map (evalRingHom t) g))
    (hh : ¬ IsUnit (MvPolynomial.map (evalRingHom t) h)) :
    ∃ s : σ →₀ ℕ, (f - g * h).coeff s ≠ 0 ∧ ((f - g * h).coeff s).eval t = 0 := by
  have hres : f - g * h ≠ 0 := by
    intro he
    have heq : f = g * h := sub_eq_zero.mp he
    obtain hu | hu := hf.isUnit_or_isUnit heq
    · exact hg (hu.map (MvPolynomial.map (evalRingHom t)))
    · exact hh (hu.map (MvPolynomial.map (evalRingHom t)))
  obtain ⟨s, hs⟩ : ∃ s, (f - g * h).coeff s ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hres
    apply MvPolynomial.ext _ _
    intro s
    simpa using hn s
  refine ⟨s, hs, ?_⟩
  have hz : MvPolynomial.map (evalRingHom t) (f - g * h) = 0 := by
    rw [map_sub, map_mul, hfactor, sub_self]
  have hc := congrArg (fun p : MvPolynomial σ K => p.coeff s) hz
  simpa only [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply, Polynomial.coe_evalRingHom] using hc

/-- A fixed finite family of candidate factorizations has a fixed finite
set of nonzero coefficient obstructions. Their number is bounded by the
number of candidates, and their degrees by the residual coefficient degrees. -/
theorem branch_factor_family_coefficient_obstructions
    {σ ι K : Type*} [Field K] [Fintype ι]
    (f : MvPolynomial σ K[X]) (hf : Irreducible f)
    (g h : ι → MvPolynomial σ K[X]) (D : ℕ)
    (hD : ∀ i s, ((f - g i * h i).coeff s).natDegree ≤ D) :
    ∃ E : Finset K[X], E.card ≤ Fintype.card ι ∧
      (∀ e ∈ E, e ≠ 0 ∧ e.natDegree ≤ D) ∧
      ∀ t : K, (∃ i, MvPolynomial.map (evalRingHom t) f =
          MvPolynomial.map (evalRingHom t) (g i) * MvPolynomial.map (evalRingHom t) (h i) ∧
        ¬ IsUnit (MvPolynomial.map (evalRingHom t) (g i)) ∧
        ¬ IsUnit (MvPolynomial.map (evalRingHom t) (h i))) →
        ∃ e ∈ E, e.eval t = 0 := by
  classical
  let J := {i : ι // f - g i * h i ≠ 0}
  have hcoeff (i : J) : ∃ s, (f - g i.val * h i.val).coeff s ≠ 0 := by
    by_contra hn
    push Not at hn
    apply i.property
    apply MvPolynomial.ext _ _
    intro s
    simpa using hn s
  choose s hs using hcoeff
  let e : J → K[X] := fun i => (f - g i.val * h i.val).coeff (s i)
  let E := Finset.univ.image e
  refine ⟨E, ?_, ?_, ?_⟩
  · exact card_image_le.trans ((by simp : Finset.univ.card = Fintype.card J).le.trans
      (Fintype.card_subtype_le _))
  · intro q hq
    obtain ⟨i, _, rfl⟩ := mem_image.mp hq
    exact ⟨hs i, hD i.val (s i)⟩
  · intro t ht
    obtain ⟨i, hfactor, hg, hh⟩ := ht
    obtain ⟨s₀, hs₀, _⟩ := branch_factor_specialization_nonzero_residual f (g i) (h i)
      hf t hfactor hg hh
    have hne : f - g i * h i ≠ 0 := by
      intro hz
      exact hs₀ (by rw [hz]; simp)
    let j : J := ⟨i, hne⟩
    refine ⟨e j, mem_image.mpr ⟨j, mem_univ _, rfl⟩, ?_⟩
    have hz : MvPolynomial.map (evalRingHom t) (f - g i * h i) = 0 := by
      rw [map_sub, map_mul, hfactor, sub_self]
    have hc := congrArg (fun p : MvPolynomial σ K => p.coeff (s j)) hz
    change ((f - g i * h i).coeff (s j)).eval t = 0
    simpa only [MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply, Polynomial.coe_evalRingHom] using hc

/-- The proper subsets in the Kronecker proof yield at most exponentially
many nonzero coefficient cuts. Outside those cuts, irreducibility of every
specialized Kronecker factor excludes every proper factorization whose
separate degrees fit the radix and whose encoded factors are monic. -/
theorem branch_kronecker_coefficient_obstructions
    {K : Type*} [Field K] (a n : ℕ) (f : MvPolynomial (Fin n) K[X])
    (hf : Irreducible f) (Q : Multiset K[X][X])
    (hQ : ∀ q ∈ Q, q.Monic) (hprod : branchMultiKronecker a n f = Q.prod)
    (D : ℕ) (hfD : ∀ s, (f.coeff s).natDegree ≤ D)
    (hQD : CCDN.bivariateTotalDegree Q.prod ≤ D) :
    ∃ E : Finset K[X], E.card ≤ 2 ^ Q.card ∧
      (∀ e ∈ E, e ≠ 0 ∧ e.natDegree ≤ 2 * D) ∧
      ∀ t : K, (∀ q ∈ Q, Irreducible (q.map (evalRingHom t))) →
        (∃ g h : MvPolynomial (Fin n) K,
          MvPolynomial.map (evalRingHom t) f = g * h ∧ ¬ IsUnit g ∧ ¬ IsUnit h ∧
          (∀ i, g.degreeOf i < a) ∧ (∀ i, h.degreeOf i < a) ∧
          (branchMultiKronecker a n g).Monic) →
        ∃ e ∈ E, e.eval t = 0 := by
  classical
  let J := Q.powerset.toFinset
  let g : J → MvPolynomial (Fin n) K[X] := fun U => branchMultiDecode a n U.val.prod
  let h : J → MvPolynomial (Fin n) K[X] := fun U =>
    branchMultiDecode a n (Q - U.val).prod
  have hQ0 : Q.prod ≠ 0 := by
    simpa only [Multiset.map_id] using (monic_multiset_prod_of_monic Q id hQ).ne_zero
  have hU (U : J) : U.val ≤ Q := Multiset.mem_powerset.mp (Multiset.mem_toFinset.mp U.property)
  have hUD (U : J) (j : ℕ) : (U.val.prod.coeff j).natDegree ≤ D :=
    (CCDN.bivariate_coefficient_natDegree_le_totalDegree U.val.prod j).trans
      ((branch_nested_totalDegree_le_of_dvd hQ0 (Multiset.prod_dvd_prod_of_le (hU U))).trans hQD)
  have hVD (U : J) (j : ℕ) : ((Q - U.val).prod.coeff j).natDegree ≤ D :=
    (CCDN.bivariate_coefficient_natDegree_le_totalDegree (Q - U.val).prod j).trans
      ((branch_nested_totalDegree_le_of_dvd hQ0
        (Multiset.prod_dvd_prod_of_le (Multiset.sub_le_self Q U.val))).trans hQD)
  obtain ⟨E, hEcard, hE, hcover⟩ := branch_factor_family_coefficient_obstructions
    f hf g h (2 * D) (fun U s =>
      branch_kronecker_residual_coefficient_degree_le a n f U.val.prod (Q - U.val).prod
        hfD (hUD U) (hVD U) s)
  refine ⟨E, hEcard.trans ?_, hE, ?_⟩
  · rw [Fintype.card_coe]
    exact (Multiset.toFinset_card_le _).trans_eq (Multiset.card_powerset Q)
  · intro t hirr hwitness
    obtain ⟨g₀, h₀, hfactor, hg₀, hh₀, hgdeg, hhdeg, hgmonic⟩ := hwitness
    have hfactorKr : Q.prod.map (evalRingHom t) =
        branchMultiKronecker a n g₀ * branchMultiKronecker a n h₀ := by
      rw [← hprod, branchMultiKronecker_map, hfactor, map_mul]
    obtain ⟨U, hUQ, hmapU⟩ := branch_irreducible_factor_specialization_lifts
      (evalRingHom t) Q hQ hirr (branchMultiKronecker a n g₀) hgmonic
      ⟨branchMultiKronecker a n h₀, hfactorKr⟩
    have hmapV : (Q - U).prod.map (evalRingHom t) = branchMultiKronecker a n h₀ := by
      apply mul_left_cancel₀ hgmonic.ne_zero
      rw [← hmapU, ← Polynomial.map_mul, ← Multiset.prod_add,
        add_tsub_cancel_of_le hUQ]
      simpa only [hmapU] using hfactorKr
    let j : J := ⟨U, Multiset.mem_toFinset.mpr (Multiset.mem_powerset.mpr hUQ)⟩
    have hgj : MvPolynomial.map (evalRingHom t) (g j) = g₀ := by
      rw [show g j = branchMultiDecode a n U.prod from rfl,
        branchMultiDecode_map, hmapU, branchMultiDecode_encode g₀ hgdeg]
    have hhj : MvPolynomial.map (evalRingHom t) (h j) = h₀ := by
      rw [show h j = branchMultiDecode a n (Q - U).prod from rfl,
        branchMultiDecode_map, hmapV, branchMultiDecode_encode h₀ hhdeg]
    apply hcover t
    exact ⟨j, by rw [hgj, hhj]; exact hfactor,
      by rwa [hgj], by rwa [hhj]⟩

end
end PierceLengthBound.FixedDividend
