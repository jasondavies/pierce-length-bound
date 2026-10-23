/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import PierceLengthBound.PolarProjectionLocalNormalization

/-! Local section bounds at a rational base point, with the normalization
and valuation-center conditions constructed from the affine coordinate ring. -/
@[expose] public section
namespace PierceLengthBound.FixedDividend
open MvPolynomial
open scoped IntermediateField
noncomputable section

/-- A rational point outside a component generates the unit centered ideal
in that component's coordinate ring. -/
theorem centered_ideal_eq_top_of_not_mem_zeroLocus {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (z : σ → K) (hz : z ∉ coordinateZeroLocus I) :
    Ideal.span (Set.range (fun j => Ideal.Quotient.mk I (X j) -
      algebraMap K (MvPolynomial σ K ⧸ I) (z j))) = ⊤ := by
  classical
  obtain ⟨f, hf, hfz⟩ : ∃ f ∈ I, eval z f ≠ 0 := by
    simpa only [coordinateZeroLocus, Set.mem_ofPred_eq, not_forall, exists_prop] using hz
  have h := polynomial_sub_value_mem_centered_ideal (Ideal.Quotient.mkₐ K I) z f
  have hzero : Ideal.Quotient.mk I f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hf
  simp only [Ideal.Quotient.mkₐ_eq_mk, hzero, zero_sub] at h
  exact Ideal.eq_top_of_isUnit_mem _ (h := (isUnit_iff_ne_zero.mpr hfz).map
    (algebraMap K (MvPolynomial σ K ⧸ I)) |>.neg) h

/-- A finite section of a ring containing a transcendental element cannot
be the zero equation. This also covers localizations of the affine curve. -/
theorem section_ne_zero_of_transcendental {K A R : Type*} [Field K]
    [CommRing A] [Algebra K A] [CommRing R] [Algebra K R]
    (φ : A →ₐ[K] R) (hφ : Function.Injective φ) (w : A) (hw : Transcendental K w)
    (a : R) [Module.Finite K (R ⧸ Ideal.span {a})] : a ≠ 0 := by
  intro ha
  have hzero : Ideal.span ({a} : Set R) = ⊥ := by simp [ha]
  let : Module.Finite K (R ⧸ (⊥ : Ideal R)) :=
    hzero ▸ (inferInstance : Module.Finite K (R ⧸ Ideal.span {a}))
  let : Module.Finite K R := Module.Finite.equiv (AlgEquiv.quotientBot K R).toLinearEquiv
  exact hw ((isAlgebraic_algHom_iff φ hφ).mp (Algebra.IsAlgebraic.isAlgebraic (φ w)))

/-- If the common coordinate ideal is the unit ideal, there is no positive
common-base contribution on any branch regular on the affine ring. -/
theorem functionCommonBaseDegree_eq_zero_of_unit_ideal {A L ι : Type*}
    [CommRing A] [Field L] [Algebra ℚ A] [Algebra ℚ L] [Algebra A L]
    [IsScalarTower ℚ A L] [Fintype ι]
    (D : L) (hD : Transcendental ℚ D) [FiniteDimensional ℚ⟮D⟯ L]
    (W : ι → L) (V : ι → A) (hV : ∀ j, algebraMap A L (V j) = D * W j)
    (htop : Ideal.span (Set.range V) = ⊤)
    (hreg : ∀ ν : AddValuation L (WithTop ℤ),
      (∀ c : ℚ, 0 ≤ ν (algebraMap ℚ L c)) → 0 < ν D →
      ∀ r : A, 0 ≤ ν (algebraMap A L r)) :
    functionCommonBaseDegree D hD W = 0 := by
  classical
  let C := functionParameterNormalization D
  let : IsDedekindDomain C := (function_parameter_normalization D hD).1
  let : IsFractionRing C L := (function_parameter_normalization D hD).2.2
  unfold functionCommonBaseDegree
  apply Finset.sum_eq_zero
  intro q hq
  let ν := functionParameterBranchOrder D hD q
  have hpos : 0 < ν D :=
    (functionParameterBranchOrder_center D hD q (functionParameterElement D)).mpr
      (((functionZeroBranches_spec D hD).1 q).mp hq)
  have hQ (c : ℚ) : 0 ≤ ν (algebraMap ℚ L c) := by
    rw [IsScalarTower.algebraMap_apply ℚ C L]
    exact normalizedBranchOrder_nonnegative q L _
  have h := common_order_le_section_order (algebraMap A L) ν (hreg ν hQ hpos)
    V (a := 1) (by rw [htop]; trivial)
  simp only [hV, map_one, ν.map_one] at h
  have hz : branchCommonZeroOrder ν (fun j => D * W j) = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact_mod_cast h
  change branchCommonZeroOrder ν (fun j => D * W j) * _ = 0
  rw [hz, zero_mul]

set_option synthInstance.maxHeartbeats 200000 in
-- The affine and local normalizations use distinct coherent scalar towers.
/-- At a rational point, an actual nonzero local section bounds the common
base contribution. All normalization and center properties follow from the
finite affine normalization and the coordinate ideal. -/
theorem functionCommonBaseDegree_le_at_rational_point {A R L ι : Type*}
    [CommRing A] [IsDomain A] [Algebra ℚ A]
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [Ring.KrullDimLE 1 R] [Algebra ℚ R] [Algebra A R] [IsScalarTower ℚ A R]
    [Field L] [Algebra ℚ L] [Algebra A L] [IsScalarTower ℚ A L]
    [IsFractionRing A L] [Algebra R L] [IsScalarTower A R L] [IsScalarTower ℚ R L]
    [IsFractionRing R L] [IsDedekindDomain (integralClosure A L)]
    [Module.Finite A (integralClosure A L)] [Fintype ι]
    (p : Ideal A) [p.IsMaximal] [IsLocalization.AtPrime R p]
    (ε : A →ₐ[ℚ] ℚ) (hp : RingHom.ker ε.toRingHom = p)
    (D : L) (hD : Transcendental ℚ D) [FiniteDimensional ℚ⟮D⟯ L]
    (W : ι → L) (V : ι → A) (hV : ∀ j, algebraMap A L (V j) = D * W j)
    (hVp : Ideal.span (Set.range V) = p)
    (a : R) (ha : a ≠ 0)
    (haV : a ∈ Ideal.span (Set.range (fun j => algebraMap A R (V j))))
    (hreg : ∀ ν : AddValuation L (WithTop ℤ),
      (∀ c : ℚ, 0 ≤ ν (algebraMap ℚ L c)) → 0 < ν D →
      ∀ r : A, 0 ≤ ν (algebraMap A L r)) :
    functionCommonBaseDegree D hD W ≤ Module.finrank ℚ (R ⧸ Ideal.span {a}) := by
  let S := integralClosure R L
  have hnormal := finite_normalization_localization (L := L)
    p.primeCompl p.primeCompl_le_nonZeroDivisors (R := R)
  let : IsDedekindDomain S := hnormal.1
  let : Module.Finite R S := hnormal.2
  let : IsFractionRing S L := IsIntegralClosure.isFractionRing_of_finite_extension R L L S
  have hrank := rational_point_local_residue_finrank (R := R) p ε hp
  let : Module.Finite ℚ (IsLocalRing.ResidueField R) :=
    Module.finite_of_finrank_pos (by rw [hrank]; omega)
  apply functionCommonBaseDegree_le_local_section (S := S) (L := L) D hD W
    (fun j => algebraMap A R (V j)) (fun j => by
      rw [← IsScalarTower.algebraMap_apply A R L, hV]) a ha haV
  intro ν hQ _ hDpos hpos
  apply common_base_branch_regular_at_localization p V hVp ν (hreg ν hQ hDpos)
  simpa only [hV] using hpos

end
end PierceLengthBound.FixedDividend
