/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionNormalizationLength
public import PierceLengthBound.NormalizedFiberOrders
public import Mathlib.RingTheory.DedekindDomain.PID

/-! Residue-weighted branch orders of a section are bounded by its colength.
In a principal ideal domain the colength of an ideal is the sum of the
colengths of its prime factors; the normalization of a one-dimensional local
domain is semilocal Dedekind, hence principal, and has the same section
colengths as the original ring. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open UniqueFactorizationMonoid
open scoped Pointwise

/-- A finite Dedekind algebra over a local ring is semilocal and hence a
principal ideal ring. -/
theorem finite_local_normalization_isPrincipal {R S : Type*}
    [CommRing R] [IsLocalRing R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] [Module.Finite R S] : IsPrincipalIdealRing S := by
  apply IsPrincipalIdealRing.of_finite_maximals
  apply (Algebra.QuasiFinite.finite_primesOver (S := S) (IsLocalRing.maximalIdeal R)).subset
  intro q hq
  let : q.IsMaximal := hq
  have hu : q.under R = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal q)
  exact ⟨hq.isPrime, ⟨hu.symm⟩⟩

lemma section_quotient_finite_of_le {K S : Type*} [Field K]
    [CommRing S] [Algebra K S] {I J : Ideal S} (h : I ≤ J)
    [Module.Finite K (S ⧸ I)] : Module.Finite K (S ⧸ J) :=
  Module.Finite.of_surjective (Ideal.Quotient.factorₐ K h).toLinearMap
    (Ideal.Quotient.factor_surjective h)

/-- Colength is additive on products of nonzero principal ideals. -/
theorem principal_ideal_product_section_finrank {K S : Type*} [Field K]
    [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] [Algebra K S]
    (I J : Ideal S) (hJ : J ≠ ⊥)
    [Module.Finite K (S ⧸ I)] [Module.Finite K (S ⧸ J)] :
    Module.finrank K (S ⧸ I * J) =
      Module.finrank K (S ⧸ I) + Module.finrank K (S ⧸ J) := by
  let a := Submodule.IsPrincipal.generator I
  let b := Submodule.IsPrincipal.generator J
  have ha : Ideal.span {a} = I := Ideal.span_singleton_generator I
  have hb : Ideal.span {b} = J := Ideal.span_singleton_generator J
  have hb0 : b ≠ 0 := by
    intro hz
    exact hJ (by rw [← hb, hz, Ideal.span_singleton_zero])
  let : Module.Finite K (S ⧸ Ideal.span {a}) := by rwa [ha]
  let : Module.Finite K (S ⧸ Ideal.span {b}) := by rwa [hb]
  have he := principal_product_quotient_finrank (K := K) a b hb0
  rw [← Ideal.span_singleton_mul_span_singleton a b, ha, hb] at he
  exact he

/-- Factoring a nonzero ideal expresses its colength as the sum of the
colengths of its prime factors, with repetitions. -/
theorem ideal_product_section_finrank {K S : Type*} [Field K]
    [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] [Algebra K S]
    (s : Multiset (Ideal S)) (hs : s.prod ≠ ⊥)
    [hfin : Module.Finite K (S ⧸ s.prod)] :
    Module.finrank K (S ⧸ s.prod) =
      (s.map (fun I => Module.finrank K (S ⧸ I))).sum := by
  classical
  revert hs hfin
  induction s using Multiset.induction_on with
  | empty =>
    intro _ _
    rw [Multiset.prod_zero, Multiset.map_zero, Multiset.sum_zero, Ideal.one_eq_top]
    exact Module.finrank_zero_of_subsingleton
  | @cons I s ih =>
    intro hs hfin
    have hprod : I * s.prod ≠ ⊥ := by simpa only [Multiset.prod_cons] using hs
    have hsp : s.prod ≠ ⊥ := by
      intro hz
      exact hprod (by rw [hz, Ideal.mul_bot])
    let : Module.Finite K (S ⧸ I * s.prod) := by
      rw [Multiset.prod_cons] at hfin
      exact hfin
    let : Module.Finite K (S ⧸ I) :=
      section_quotient_finite_of_le (show I * s.prod ≤ I from Ideal.mul_le_left)
    let : Module.Finite K (S ⧸ s.prod) :=
      section_quotient_finite_of_le (show I * s.prod ≤ s.prod from Ideal.mul_le_right)
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
    exact (principal_ideal_product_section_finrank (K := K) I s.prod hsp).trans
        (congrArg (Module.finrank K (S ⧸ I) + ·) (ih hsp))

/-- The colength of a nonzero ideal is the sum of the colengths of its
normalized prime factors, with multiplicity. -/
theorem ideal_section_finrank_eq_factor_sum {K S : Type*} [Field K]
    [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] [Algebra K S]
    (I : Ideal S) (hI : I ≠ ⊥) [Module.Finite K (S ⧸ I)] :
    Module.finrank K (S ⧸ I) =
      ((normalizedFactors I).map (fun q => Module.finrank K (S ⧸ q))).sum := by
  have he : (normalizedFactors I).prod = I :=
    associated_iff_eq.mp (prod_normalizedFactors hI)
  let : Module.Finite K (S ⧸ (normalizedFactors I).prod) := by rwa [he]
  have h := ideal_product_section_finrank (K := K)
    (normalizedFactors I) (by rwa [he])
  rwa [he] at h

private lemma count_weight_sum_le {α : Type*} [DecidableEq α] (s : Multiset α)
    (B : Finset α) (w : α → ℕ) :
    (∑ a ∈ B, s.count a * w a) ≤ (s.map w).sum := by
  classical
  have hcut : (∑ a ∈ B ∩ s.toFinset, s.count a * w a) =
      ∑ a ∈ B, s.count a * w a := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro a ha hnot
    have hzero : s.count a = 0 := by
      apply Multiset.count_eq_zero.mpr
      intro ham
      exact hnot (Finset.mem_inter.mpr ⟨ha, Multiset.mem_toFinset.mpr ham⟩)
    simp only [hzero, zero_mul]
  rw [← hcut, Finset.sum_multiset_map_count]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    (fun _ _ _ => Nat.zero_le _)

/-- Residue-weighted multiplicities from any finite collection of normalized
branches are bounded by the colength of the section. -/
theorem normalized_section_multiplicity_sum_le {K S : Type*} [Field K]
    [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] [Algebra K S]
    (I : Ideal S) (hI : I ≠ ⊥) [Module.Finite K (S ⧸ I)]
    (B : Finset (IsDedekindDomain.HeightOneSpectrum S)) :
    (∑ q ∈ B, multiplicity q.asIdeal I * Module.finrank K (S ⧸ q.asIdeal)) ≤
      Module.finrank K (S ⧸ I) := by
  classical
  rw [ideal_section_finrank_eq_factor_sum I hI]
  have he (q : IsDedekindDomain.HeightOneSpectrum S) :
      multiplicity q.asIdeal I = (normalizedFactors I).count q.asIdeal := by
    simpa using multiplicity_eq_count_normalizedFactors q.irreducible hI
  calc
    _ = ∑ q ∈ B.image IsDedekindDomain.HeightOneSpectrum.asIdeal,
        (normalizedFactors I).count q * Module.finrank K (S ⧸ q) := by
      rw [Finset.sum_image]
      · exact Finset.sum_congr rfl (fun q _ => by rw [he q])
      · intro q _ r _ h
        exact IsDedekindDomain.HeightOneSpectrum.ext h
    _ ≤ _ := count_weight_sum_le _ _ _

/-- If `m q` is at most the normalized order of `a` at each `q ∈ B`, then the
residue-weighted sum of the `m q` is at most the colength of `(a)`. -/
theorem normalized_section_order_sum_le {K S L : Type*} [Field K]
    [CommRing S] [IsDomain S] [IsPrincipalIdealRing S] [Algebra K S]
    [Field L] [Algebra S L] [IsFractionRing S L]
    (a : S) (ha : a ≠ 0) [Module.Finite K (S ⧸ Ideal.span {a})]
    (B : Finset (IsDedekindDomain.HeightOneSpectrum S))
    (m : IsDedekindDomain.HeightOneSpectrum S → ℕ)
    (hm : ∀ q ∈ B, ((m q : ℤ) : WithTop ℤ) ≤
      normalizedBranchOrder q L (algebraMap S L a)) :
    (∑ q ∈ B, m q * Module.finrank K (S ⧸ q.asIdeal)) ≤
      Module.finrank K (S ⧸ Ideal.span {a}) := by
  apply le_trans ?_ (normalized_section_multiplicity_sum_le
    (Ideal.span {a}) (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using ha) B)
  apply Finset.sum_le_sum
  intro q hq
  apply Nat.mul_le_mul_right
  have h := hm q hq
  rw [normalizedBranchOrder_eq_multiplicity q L ha] at h
  exact_mod_cast h

/-- On the normalization of a one-dimensional Noetherian local domain, the
residue-weighted orders of `a` are bounded by the colength of `(a)` in the
original local ring. -/
theorem local_normalization_order_sum_le {K R S L : Type*} [Field K]
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Algebra K R]
    [Module.Finite K (IsLocalRing.ResidueField R)]
    [CommRing S] [IsDedekindDomain S] [Algebra K S] [Algebra R S]
    [IsScalarTower K R S] [Module.Finite R S]
    [Field L] [Algebra R L] [IsFractionRing R L]
    [Algebra S L] [IsFractionRing S L] [IsScalarTower R S L]
    (a : R) (ha : a ≠ 0)
    (B : Finset (IsDedekindDomain.HeightOneSpectrum S))
    (m : IsDedekindDomain.HeightOneSpectrum S → ℕ)
    (hm : ∀ q ∈ B, ((m q : ℤ) : WithTop ℤ) ≤
      normalizedBranchOrder q L (algebraMap R L a)) :
    (∑ q ∈ B, m q * Module.finrank K (S ⧸ q.asIdeal)) ≤
      Module.finrank K (R ⧸ Ideal.span {a}) := by
  let : IsPrincipalIdealRing S := finite_local_normalization_isPrincipal (R := R)
  let := local_curve_section_finite (K := K) a ha
  let : Module.Finite K (S ⧸ Ideal.span {algebraMap R S a}) := by
    have h := finite_algebra_quotient (K := K) (S := S) (Ideal.span {a})
    rw [Ideal.map_span, Set.image_singleton] at h
    exact h
  have haS : algebraMap R S a ≠ 0 := by
    intro hz
    apply ha
    apply IsFractionRing.injective R L
    rw [map_zero, IsScalarTower.algebraMap_apply R S L a, hz, map_zero]
  rw [← local_normalization_section_finrank (S := S) (L := L) a ha]
  exact normalized_section_order_sum_le (L := L) (algebraMap R S a) haS B m
    (fun q hq => by simpa only [← IsScalarTower.algebraMap_apply R S L] using hm q hq)

end
end PierceLengthBound.FixedDividend
