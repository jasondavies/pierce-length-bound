/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionLinearSystem
public import PierceLengthBound.BranchPoleEnvelope
public import PierceLengthBound.NormalizationBranchCover
public import PierceLengthBound.BranchResidueComparison

/-! The common-zero contribution in the normalized zero fiber of a scalar
function. The fiber is constructed from the function parameter normalization;
its degree is the function-field degree, not an assumed divisor formula. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Finset
open scoped IntermediateField
noncomputable section

def branchCommonZeroOrder {L ι : Type*} [Field L] [Fintype ι]
    (ν : AddValuation L (WithTop ℤ)) (V : ι → L) : ℕ :=
  ((branchCoordinateOrder ν V).untopD 0).toNat

lemma branchCoordinateOrder_eq_of_bounds {L ι : Type*} [Field L] [Fintype ι]
    (ν : AddValuation L (WithTop ℤ)) (V : ι → L) (n : WithTop ℤ)
    (hlower : ∀ j, n ≤ ν (V j)) (hexact : ∃ j, ν (V j) = n) :
    branchCoordinateOrder ν V = n := by
  apply le_antisymm
  · obtain ⟨j, hj⟩ := hexact
    exact (Finset.inf_le (Finset.mem_univ j)).trans_eq hj
  · exact (le_branchCoordinateOrder_iff ν V n).mpr hlower

lemma branchCoordinateOrder_mul_of_order {L ι : Type*} [Field L] [Fintype ι]
    (ν : AddValuation L (WithTop ℤ)) (V : ι → L) (D : L) (n m : ℤ)
    (hD : ν D = (m : WithTop ℤ)) (hlower : ∀ j, (n : WithTop ℤ) ≤ ν (V j))
    (hexact : ∃ j, ν (V j) = (n : WithTop ℤ)) :
    branchCoordinateOrder ν (fun j => D * V j) = ((m + n : ℤ) : WithTop ℤ) := by
  apply branchCoordinateOrder_eq_of_bounds
  · intro j
    rw [ν.map_mul, hD, WithTop.coe_add]
    exact add_le_add le_rfl (hlower j)
  · obtain ⟨j, hj⟩ := hexact
    exact ⟨j, by rw [ν.map_mul, hD, hj, WithTop.coe_add]⟩

lemma branchPoleEnvelope_eq_of_common_order {L ι : Type*} [Field L] [Fintype ι]
    (ν : AddValuation L (WithTop ℤ)) (V : ι → L) (n : ℤ)
    (hlower : ∀ j, (n : WithTop ℤ) ≤ ν (V j))
    (hexact : ∃ j, ν (V j) = (n : WithTop ℤ)) :
    branchPoleEnvelope ν V = (-n).toNat := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j _
    rw [discretePoleOrder_le_iff]
    exact le_trans (by exact_mod_cast (show -((-n).toNat : ℤ) ≤ n by omega)) (hlower j)
  · obtain ⟨j, hj⟩ := hexact
    rw [← discretePoleOrder_eq ν hj]
    exact pole_order_le_envelope ν V j

/-- A scalar zero is accounted for by a pole of the quotient coordinates or
by a common zero of the multiplied coordinates. -/
theorem scalar_order_le_poles_add_common_zeros {L ι : Type*}
    [Field L] [Fintype ι] [Nonempty ι]
    (ν : AddValuation L (WithTop ℤ)) (W : ι → L) (hW : ∃ j, W j ≠ 0)
    (D : L) (m : ℕ) (hD : ν D = ((m : ℤ) : WithTop ℤ)) :
    m ≤ branchPoleEnvelope ν W + branchCommonZeroOrder ν (fun j => D * W j) := by
  classical
  obtain ⟨j, hj⟩ := hW
  have hlt : branchCoordinateOrder ν W < ⊤ :=
    (Finset.inf_le (Finset.mem_univ j)).trans_lt
      (lt_top_iff_ne_top.mpr (ν.ne_top_iff.mpr hj))
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hlt.ne
  have hlower := (le_branchCoordinateOrder_iff ν W (n : WithTop ℤ)).mp (le_of_eq hn)
  have hexact : ∃ j, ν (W j) = (n : WithTop ℤ) := by
    obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_inf Finset.univ Finset.univ_nonempty
      (fun j => ν (W j))
    exact ⟨k, hk.symm.trans hn.symm⟩
  rw [branchPoleEnvelope_eq_of_common_order ν W n hlower hexact,
    branchCommonZeroOrder, branchCoordinateOrder_mul_of_order ν W D n m hD hlower hexact]
  simp only [WithTop.untopD_coe]
  omega

/-- The complete normalized zero fiber of a transcendental scalar. -/
def functionZeroBranches {L : Type*} [Field L] [Algebra ℚ L]
    (D : L) (hD : Transcendental ℚ D) [FiniteDimensional ℚ⟮D⟯ L] :
    Finset (IsDedekindDomain.HeightOneSpectrum (functionParameterNormalization D)) :=
  (function_parameter_fiber_degree D hD).choose

theorem functionZeroBranches_spec {L : Type*} [Field L] [Algebra ℚ L]
    (D : L) (hD : Transcendental ℚ D) [FiniteDimensional ℚ⟮D⟯ L] :
    (∀ q, q ∈ functionZeroBranches D hD ↔ functionParameterElement D ∈ q.asIdeal) ∧
      (∑ q ∈ functionZeroBranches D hD,
        multiplicity q.asIdeal (Ideal.span {functionParameterElement D}) *
          Module.finrank ℚ (functionParameterNormalization D ⧸ q.asIdeal)) =
        Module.finrank ℚ⟮D⟯ L :=
  (function_parameter_fiber_degree D hD).choose_spec

/-- The residue-weighted common zero orders of `D W` above the zeros of `D`.
The polar identity identifies this with the polar base contribution in the application. -/
def functionCommonBaseDegree {L ι : Type*} [Field L] [Algebra ℚ L] [Fintype ι]
    (D : L) (hD : Transcendental ℚ D) [FiniteDimensional ℚ⟮D⟯ L] (W : ι → L) : ℕ :=
  ∑ q ∈ functionZeroBranches D hD,
    branchCommonZeroOrder (functionParameterBranchOrder D hD q) (fun j => D * W j) *
      Module.finrank ℚ (functionParameterNormalization D ⧸ q.asIdeal)

lemma sum_poleEnvelope_le_degree {R L ι : Type*}
    [CommRing R] [IsDedekindDomain R] [Algebra ℚ R]
    [Field L] [Algebra R L] [IsFractionRing R L] [Fintype ι]
    (W : ι → L) (B : Finset (IsDedekindDomain.HeightOneSpectrum R)) :
    (∑ p ∈ B, branchPoleEnvelope (normalizedBranchOrder p L) W *
      Module.finrank ℚ (R ⧸ p.asIdeal)) ≤ poleEnvelopeDegree R W := by
  classical
  let weight := fun p : IsDedekindDomain.HeightOneSpectrum R =>
    branchPoleEnvelope (normalizedBranchOrder p L) W * Module.finrank ℚ (R ⧸ p.asIdeal)
  change (∑ p ∈ B, weight p) ≤ ∑ p ∈ poleEnvelopeBranches R W, weight p
  have he : (∑ p ∈ B ∩ poleEnvelopeBranches R W, weight p) = ∑ p ∈ B, weight p := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro p hp hnot
    have hzero : branchPoleEnvelope (normalizedBranchOrder p L) W = 0 := by
      by_contra h
      exact hnot (Finset.mem_inter.mpr ⟨hp, (mem_poleEnvelopeBranches W p).mpr
        (Nat.pos_of_ne_zero h)⟩)
    simp only [weight, hzero, zero_mul]
  rw [← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    (fun _ _ _ => Nat.zero_le _)

set_option synthInstance.maxHeartbeats 200000 in
-- The scalar normalization and the target model introduce nested algebra and residue-field towers.
/-- The scalar's function-field degree is bounded by the coordinate pole
degree plus the actual common-zero contribution above its zero fiber. Every
zero branch is transported to the given Dedekind model, with residue degrees preserved. -/
theorem function_degree_le_poleEnvelope_add_baseDegree {R L ι : Type*}
    [CommRing R] [IsDedekindDomain R] [Algebra ℚ R]
    [Field L] [Algebra ℚ L] [Algebra R L] [IsScalarTower ℚ R L] [IsFractionRing R L]
    [Fintype ι] [Nonempty ι] (W : ι → L) (hW : ∃ j, W j ≠ 0)
    (D : L) (hD : Transcendental ℚ D) [FiniteDimensional ℚ⟮D⟯ L]
    (hcover : ∀ ν : AddValuation L (WithTop ℤ),
      (∀ a : ℚ, 0 ≤ ν (algebraMap ℚ L a)) → (∃ π : L, ν π = 1) →
      0 < ν D → ∀ r : R, 0 ≤ ν (algebraMap R L r)) :
    Module.finrank ℚ⟮D⟯ L ≤ poleEnvelopeDegree R W + functionCommonBaseDegree D hD W := by
  classical
  let C := functionParameterNormalization D
  let : IsDedekindDomain C := (function_parameter_normalization D hD).1
  let : IsFractionRing C L := (function_parameter_normalization D hD).2.2
  let B := functionZeroBranches D hD
  let mult := fun q : IsDedekindDomain.HeightOneSpectrum C =>
    multiplicity q.asIdeal (Ideal.span {functionParameterElement D})
  have ht (q : B) : ∃ p : IsDedekindDomain.HeightOneSpectrum R,
      normalizedBranchOrder p L = functionParameterBranchOrder D hD q.1 ∧
      Module.finrank ℚ (C ⧸ q.1.asIdeal) = Module.finrank ℚ (R ⧸ p.asIdeal) := by
    let ν := functionParameterBranchOrder D hD q.1
    have hconst (a : ℚ) : 0 ≤ ν (algebraMap ℚ L a) := by
      rw [IsScalarTower.algebraMap_apply ℚ C L]
      exact normalizedBranchOrder_nonnegative q.1 L _
    have hpos : 0 < ν D :=
      (functionParameterBranchOrder_center D hD q.1 (functionParameterElement D)).mpr
        (((functionZeroBranches_spec D hD).1 q.1).mp q.2)
    obtain ⟨p, hp⟩ := regular_branch_realized ν
      (hcover ν hconst (normalizedBranchOrder_uniformizer q.1 L) hpos)
      (normalizedBranchOrder_uniformizer q.1 L)
    exact ⟨p, hp, branch_residue_degree_eq q.1 p hp.symm⟩
  choose f hford hfdegree using ht
  have hf : Function.Injective f := by
    intro q r h
    apply Subtype.ext
    apply normalizedBranchOrder_injective (L := L)
    change functionParameterBranchOrder D hD q.1 = functionParameterBranchOrder D hD r.1
    rw [← hford q, ← hford r, h]
  have hpoles :
      (∑ q ∈ B, branchPoleEnvelope (functionParameterBranchOrder D hD q) W *
        Module.finrank ℚ (C ⧸ q.asIdeal)) ≤ poleEnvelopeDegree R W := by
    calc
      _ = ∑ q : B, branchPoleEnvelope (functionParameterBranchOrder D hD q.1) W *
          Module.finrank ℚ (C ⧸ q.1.asIdeal) := (B.sum_coe_sort _).symm
      _ = ∑ q : B, branchPoleEnvelope (normalizedBranchOrder (f q) L) W *
          Module.finrank ℚ (R ⧸ (f q).asIdeal) := by
        apply Finset.sum_congr rfl
        intro q _
        rw [hford q, hfdegree q]
      _ = ∑ p ∈ Finset.univ.image f, branchPoleEnvelope (normalizedBranchOrder p L) W *
          Module.finrank ℚ (R ⧸ p.asIdeal) :=
        (Finset.sum_image (f := fun p => branchPoleEnvelope (normalizedBranchOrder p L) W *
          Module.finrank ℚ (R ⧸ p.asIdeal)) (fun q _ r _ h => hf h)).symm
      _ ≤ _ := sum_poleEnvelope_le_degree W _
  calc
    Module.finrank ℚ⟮D⟯ L = ∑ q ∈ B, mult q * Module.finrank ℚ (C ⧸ q.asIdeal) :=
      (functionZeroBranches_spec D hD).2.symm
    _ ≤ ∑ q ∈ B,
        (branchPoleEnvelope (functionParameterBranchOrder D hD q) W +
          branchCommonZeroOrder (functionParameterBranchOrder D hD q) (fun j => D * W j)) *
            Module.finrank ℚ (C ⧸ q.asIdeal) := by
      apply Finset.sum_le_sum
      intro q _
      apply Nat.mul_le_mul_right
      exact scalar_order_le_poles_add_common_zeros (functionParameterBranchOrder D hD q)
        W hW D (mult q) (functionParameterBranchOrder_parameter D hD q)
    _ = (∑ q ∈ B, branchPoleEnvelope (functionParameterBranchOrder D hD q) W *
        Module.finrank ℚ (C ⧸ q.asIdeal)) + functionCommonBaseDegree D hD W := by
      simp only [add_mul, Finset.sum_add_distrib, functionCommonBaseDegree, B, C]
    _ ≤ _ := Nat.add_le_add_right hpoles _

end
end PierceLengthBound.FixedDividend
