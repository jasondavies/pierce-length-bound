/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchPoleEnvelope
public import PierceLengthBound.NormalizationBranchCover
public import PierceLengthBound.BranchResidueComparison

/-! The degree `[L : ℚ(x)]` of a rational combination `x = ∑ cⱼ Wⱼ` is at most the pole
envelope degree of the coordinates `W` on a Dedekind model `R`, provided every pole of `x` lies on
`R`. This is the inequality `deg (φ)_∞ ≤ deg 𝓕` in the proof of Lemma 8.11. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open scoped IntermediateField BigOperators

/-- Let `x = ∑ cⱼ Wⱼ` with rational `cⱼ` be transcendental, and suppose every discrete order of
`L` that is nonnegative on `ℚ`, attains `1` and is negative at `x` is nonnegative on `R`. Then
`[L : ℚ(x)]` is at most `poleEnvelopeDegree R W`. -/
theorem function_degree_le_poleEnvelope {R L ι : Type*}
    [CommRing R] [IsDedekindDomain R] [Algebra ℚ R]
    [Field L] [Algebra ℚ L] [Algebra R L] [IsScalarTower ℚ R L] [IsFractionRing R L]
    [Fintype ι] (W : ι → L) (c : ι → ℚ)
    (x : L) (hx : Transcendental ℚ x) [FiniteDimensional ℚ⟮x⟯ L]
    (hexpr : x = ∑ j, algebraMap ℚ L (c j) * W j)
    (hcover : ∀ ν : AddValuation L (WithTop ℤ),
      (∀ a : ℚ, 0 ≤ ν (algebraMap ℚ L a)) → (∃ π : L, ν π = 1) →
      ν x < 0 → ∀ r : R, 0 ≤ ν (algebraMap R L r)) :
    Module.finrank ℚ⟮x⟯ L ≤ poleEnvelopeDegree R W := by
  classical
  let y := x⁻¹
  have hy : Transcendental ℚ y := fun h => hx (IsAlgebraic.inv_iff.mp h)
  have hfield : ℚ⟮y⟯ = ℚ⟮x⟯ := intermediateField_adjoin_inv x
  let : FiniteDimensional ℚ⟮y⟯ L := by rw [hfield]; infer_instance
  let C := functionParameterNormalization y
  let : IsDedekindDomain C := (function_parameter_normalization y hy).1
  let : IsFractionRing C L := (function_parameter_normalization y hy).2.2
  obtain ⟨Q, hQ, hsum⟩ := function_parameter_fiber_degree y hy
  let mult := fun q : IsDedekindDomain.HeightOneSpectrum C =>
    multiplicity q.asIdeal (Ideal.span {functionParameterElement y})
  have hbound (p : IsDedekindDomain.HeightOneSpectrum R) :
      discretePoleOrder (normalizedBranchOrder p L) x ≤
        branchPoleEnvelope (normalizedBranchOrder p L) W := by
    rw [hexpr]
    apply combination_pole_order_le_envelope
    intro a
    rw [IsScalarTower.algebraMap_apply ℚ R L]
    exact normalizedBranchOrder_nonnegative p L _
  have ht (q : Q) : ∃ p : IsDedekindDomain.HeightOneSpectrum R,
      normalizedBranchOrder p L = normalizedBranchOrder q.1 L ∧
      Module.finrank ℚ (C ⧸ q.1.asIdeal) = Module.finrank ℚ (R ⧸ p.asIdeal) ∧
      0 < discretePoleOrder (normalizedBranchOrder p L) x ∧
      mult q.1 = discretePoleOrder (normalizedBranchOrder p L) x := by
    let ν := normalizedBranchOrder q.1 L
    have hconst (a : ℚ) : 0 ≤ ν (algebraMap ℚ L a) := by
      rw [IsScalarTower.algebraMap_apply ℚ C L]
      exact normalizedBranchOrder_nonnegative q.1 L _
    have hpos : 0 < ν y :=
      (normalizedBranchOrder_positive_iff q.1 L (functionParameterElement y)).mpr
        ((hQ q.1).mp q.2)
    obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp (ν.ne_top_iff.mpr hy.ne_zero)
    have hepos : 0 < e := by rw [← he] at hpos; exact_mod_cast hpos
    have hneg : ν x < 0 := by
      rw [show x = y⁻¹ by simp [y], ν.map_inv, ← he]
      change ((-e : ℤ) : WithTop ℤ) < ((0 : ℤ) : WithTop ℤ)
      exact_mod_cast (show -e < 0 by omega)
    obtain ⟨p, hp⟩ := regular_branch_realized ν
      (hcover ν hconst (normalizedBranchOrder_uniformizer q.1 L) hneg)
      (normalizedBranchOrder_uniformizer q.1 L)
    refine ⟨p, hp, branch_residue_degree_eq q.1 p hp.symm, ?_, ?_⟩
    · rw [discretePoleOrder_pos_iff, hp]
      exact hneg
    · have hh := functionParameterBranchOrder_inverse y hy q.1
      change ν (y⁻¹) = ((-(mult q.1 : ℤ)) : WithTop ℤ) at hh
      have hh' : ν x = ((-(mult q.1 : ℤ)) : WithTop ℤ) := by
        simpa only [y, inv_inv] using hh
      rw [hp, discretePoleOrder_eq ν hh', neg_neg, Int.toNat_natCast]
  choose f hford hfdegree hfpos hfmult using ht
  have hf : Function.Injective f := by
    intro q r h
    apply Subtype.ext
    apply normalizedBranchOrder_injective (L := L)
    change normalizedBranchOrder q.1 L = normalizedBranchOrder r.1 L
    rw [← hford q, ← hford r, h]
  let weight := fun p : IsDedekindDomain.HeightOneSpectrum R =>
    branchPoleEnvelope (normalizedBranchOrder p L) W * Module.finrank ℚ (R ⧸ p.asIdeal)
  have hweight (q : Q) :
      mult q.1 * Module.finrank ℚ (C ⧸ q.1.asIdeal) ≤ weight (f q) := by
    rw [hfmult q, hfdegree q]
    exact Nat.mul_le_mul_right _ (hbound (f q))
  have hsub : Finset.univ.image f ⊆ poleEnvelopeBranches R W := by
    intro p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
    exact (mem_poleEnvelopeBranches W (f q)).mpr ((hfpos q).trans_le (hbound (f q)))
  calc
    Module.finrank ℚ⟮x⟯ L = Module.finrank ℚ⟮y⟯ L := by rw [hfield]
    _ = ∑ q ∈ Q, mult q * Module.finrank ℚ (C ⧸ q.asIdeal) := hsum.symm
    _ = ∑ q : Q, mult q.1 * Module.finrank ℚ (C ⧸ q.1.asIdeal) := (Q.sum_coe_sort _).symm
    _ ≤ ∑ q : Q, weight (f q) := Finset.sum_le_sum (fun q _ => hweight q)
    _ = ∑ p ∈ Finset.univ.image f, weight p :=
      (Finset.sum_image (fun q _ r _ h => hf h)).symm
    _ ≤ ∑ p ∈ poleEnvelopeBranches R W, weight p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    _ = poleEnvelopeDegree R W := rfl

end
end PierceLengthBound.FixedDividend
