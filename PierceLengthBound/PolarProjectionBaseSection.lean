/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionNormalizedSection
public import PierceLengthBound.PolarProjectionBaseDegree

/-! Comparing the actual scalar-zero common-base contribution with a local
hyperplane section. A valuation-center condition transports precisely the
branches where the common coordinates vanish to the local normalization. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open scoped IntermediateField

lemma branchCommonZeroOrder_le_coordinates {L ι : Type*} [Field L] [Fintype ι]
    (ν : AddValuation L (WithTop ℤ)) (V : ι → L) (hV : ∀ j, 0 ≤ ν (V j)) :
    ∀ j, ((branchCommonZeroOrder ν V : ℤ) : WithTop ℤ) ≤ ν (V j) := by
  have hnonneg : 0 ≤ branchCoordinateOrder ν V :=
    (le_branchCoordinateOrder_iff ν V 0).mpr hV
  by_cases ht : branchCoordinateOrder ν V = ⊤
  · simpa only [branchCommonZeroOrder, ht, WithTop.untopD_top, Int.toNat_zero,
      Nat.cast_zero, WithTop.coe_zero] using hV
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ht
    have hn0 : 0 ≤ n := by exact_mod_cast (hn ▸ hnonneg)
    have hl := (le_branchCoordinateOrder_iff ν V (n : WithTop ℤ)).mp (le_of_eq hn)
    simpa only [branchCommonZeroOrder, ← hn, WithTop.untopD_coe, Int.toNat_of_nonneg hn0]
      using hl

/-- Every member of the coordinate ideal has order at least the common
coordinate order at a branch regular on the coefficient ring. -/
theorem common_order_le_section_order {R L ι : Type*}
    [CommRing R] [Field L] [Fintype ι] (φ : R →+* L)
    (ν : AddValuation L (WithTop ℤ)) (hR : ∀ r, 0 ≤ ν (φ r))
    (V : ι → R) {a : R} (ha : a ∈ Ideal.span (Set.range V)) :
    ((branchCommonZeroOrder ν (fun j => φ (V j)) : ℤ) : WithTop ℤ) ≤ ν (φ a) := by
  let n := ((branchCommonZeroOrder ν (fun j => φ (V j)) : ℤ) : WithTop ℤ)
  have hl := branchCommonZeroOrder_le_coordinates ν (fun j => φ (V j)) (fun j => hR (V j))
  change n ≤ ν (φ a)
  induction ha using Submodule.span_induction with
  | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hl j
  | zero => rw [φ.map_zero, ν.map_zero]; exact le_top
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (le_min hx hy).trans (ν.map_add _ _)
  | smul r x _ hx =>
    change n ≤ ν (φ (r * x))
    rw [map_mul, ν.map_mul]
    simpa only [zero_add] using add_le_add (hR r) hx

/-- A local section through the common base point bounds the actual
residue-weighted common-base contribution. The center hypothesis concerns
regularity on the local curve ring; no multiplicity is assumed. -/
theorem functionCommonBaseDegree_le_local_section {R S L ι : Type*}
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Algebra ℚ R]
    [Module.Finite ℚ (IsLocalRing.ResidueField R)]
    [CommRing S] [IsDedekindDomain S] [Algebra ℚ S] [Algebra R S]
    [IsScalarTower ℚ R S] [Module.Finite R S]
    [Field L] [Algebra ℚ L] [Algebra R L] [IsFractionRing R L]
    [IsScalarTower ℚ R L] [Algebra S L] [IsFractionRing S L]
    [IsScalarTower R S L] [IsScalarTower ℚ S L] [Fintype ι]
    (D : L) (hD : Transcendental ℚ D) [FiniteDimensional ℚ⟮D⟯ L]
    (W : ι → L) (V : ι → R) (hV : ∀ j, algebraMap R L (V j) = D * W j)
    (a : R) (ha : a ≠ 0) (haV : a ∈ Ideal.span (Set.range V))
    (hcenter : ∀ ν : AddValuation L (WithTop ℤ),
      (∀ c : ℚ, 0 ≤ ν (algebraMap ℚ L c)) → (∃ π : L, ν π = 1) →
      0 < ν D →
      0 < branchCommonZeroOrder ν (fun j => D * W j) →
      ∀ r : R, 0 ≤ ν (algebraMap R L r)) :
    functionCommonBaseDegree D hD W ≤ Module.finrank ℚ (R ⧸ Ideal.span {a}) := by
  classical
  let C := functionParameterNormalization D
  let : IsDedekindDomain C := (function_parameter_normalization D hD).1
  let : IsFractionRing C L := (function_parameter_normalization D hD).2.2
  let ν := fun q : IsDedekindDomain.HeightOneSpectrum C => functionParameterBranchOrder D hD q
  let weight := fun q : IsDedekindDomain.HeightOneSpectrum C =>
    branchCommonZeroOrder (ν q) (fun j => D * W j)
  let B := (functionZeroBranches D hD).filter (fun q => 0 < weight q)
  have hreg (q : B) : ∀ r : R, 0 ≤ ν q.1 (algebraMap R L r) := by
    have hpos : 0 < ν q.1 D :=
      (functionParameterBranchOrder_center D hD q.1 (functionParameterElement D)).mpr
        (((functionZeroBranches_spec D hD).1 q.1).mp (Finset.mem_filter.mp q.2).1)
    apply hcenter (ν q.1) ?_ (normalizedBranchOrder_uniformizer q.1 L) hpos
      ((Finset.mem_filter.mp q.2).2)
    intro c
    rw [IsScalarTower.algebraMap_apply ℚ C L]
    exact normalizedBranchOrder_nonnegative q.1 L _
  have ht (q : B) : ∃ p : IsDedekindDomain.HeightOneSpectrum S,
      normalizedBranchOrder p L = ν q.1 ∧
      Module.finrank ℚ (C ⧸ q.1.asIdeal) = Module.finrank ℚ (S ⧸ p.asIdeal) := by
    have hS (x : S) : 0 ≤ ν q.1 (algebraMap S L x) :=
      branch_order_nonnegative_of_integral (ν q.1) (hreg q)
        ((Algebra.IsIntegral.isIntegral x).map (IsScalarTower.toAlgHom R S L))
    obtain ⟨p, hp⟩ := regular_branch_realized (ν q.1) hS
      (normalizedBranchOrder_uniformizer q.1 L)
    exact ⟨p, hp, branch_residue_degree_eq q.1 p hp.symm⟩
  choose f hford hfdegree using ht
  have hf : Function.Injective f := by
    intro q r h
    apply Subtype.ext
    apply normalizedBranchOrder_injective (L := L)
    change ν q.1 = ν r.1
    rw [← hford q, ← hford r, h]
  let m := fun p : IsDedekindDomain.HeightOneSpectrum S =>
    branchCommonZeroOrder (normalizedBranchOrder p L) (fun j => D * W j)
  have hm (p : IsDedekindDomain.HeightOneSpectrum S) :
      ((m p : ℤ) : WithTop ℤ) ≤ normalizedBranchOrder p L (algebraMap R L a) := by
    have hp (r : R) : 0 ≤ normalizedBranchOrder p L (algebraMap R L r) := by
      rw [IsScalarTower.algebraMap_apply R S L]
      exact normalizedBranchOrder_nonnegative p L _
    simpa only [hV] using common_order_le_section_order (algebraMap R L)
      (normalizedBranchOrder p L) hp V haV
  have hsum : functionCommonBaseDegree D hD W =
      ∑ q ∈ B, weight q * Module.finrank ℚ (C ⧸ q.asIdeal) := by
    unfold functionCommonBaseDegree
    apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro q hq hnot
    have hz : weight q = 0 := by
      by_contra h
      exact hnot (Finset.mem_filter.mpr ⟨hq, Nat.pos_of_ne_zero h⟩)
    change weight q * _ = 0
    rw [hz, zero_mul]
  rw [hsum]
  calc
    _ = ∑ q : B, weight q.1 * Module.finrank ℚ (C ⧸ q.1.asIdeal) :=
      (B.sum_coe_sort _).symm
    _ = ∑ q : B, m (f q) * Module.finrank ℚ (S ⧸ (f q).asIdeal) := by
      apply Finset.sum_congr rfl
      intro q _
      simp only [m, hford q, hfdegree q, weight]
    _ = ∑ p ∈ Finset.univ.image f, m p * Module.finrank ℚ (S ⧸ p.asIdeal) :=
      (Finset.sum_image (f := fun p => m p * Module.finrank ℚ (S ⧸ p.asIdeal))
        (fun q _ r _ h => hf h)).symm
    _ ≤ _ := local_normalization_order_sum_le (L := L) a ha _ m (fun p _ => hm p)

end
end PierceLengthBound.FixedDividend
