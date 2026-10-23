/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import PierceLengthBound.PolarProjectionOrbitBase
public import PierceLengthBound.PolarProjectionLocalAxisBound

/-! The actual residue-weighted polar common-base contribution is at most
four on every retained component outside the fixed exceptional hypersurface. -/
@[expose] public section
namespace PierceLengthBound.FixedDividend
open MvPolynomial
open scoped IntermediateField
noncomputable section

set_option synthInstance.maxHeartbeats 400000 in
-- The affine component, its local ring and both normalizations share a fraction field.
set_option maxHeartbeats 400000 in
-- Constructing these scalar towers takes about 160000 heartbeats; keep a margin.
theorem retained_polar_base_degree_le_four
    {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hcut : ∀ j, orbitPolarIdentityPolynomial a b i j ∈ I)
    (hguard : polarChartGuard (orbitPolarParameters a b i) ≠ 0)
    (hminor : polarInitialMinor (orbitPolarParameters a b i) ≠ 0)
    {d N : ℕ} {c₀ : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c₀)
    (F : Type*) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsScalarTower ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin 3) ℚ ⧸ I) F] :
    let A := MvPolynomial (Fin 3) ℚ ⧸ I
    let ψ := (IsScalarTower.toAlgHom ℚ A F).comp (Ideal.Quotient.mkₐ ℚ I)
    let J := algebraMap A F (Ideal.Quotient.mk I (jointRankFivePolynomial a b i))
    let W := fun j : Fin 3 =>
      ψ (orbitJointNumerators a b i j.castSucc) / ψ (orbitJointDenominator a b i)
    let hJ := (retained_rank_five_degree_lower_bound hba hi hne I hf hg hd hdegree F).1
    let _ : Module.Finite ℚ⟮J⟯ F :=
      (retained_rank_five_degree_lower_bound hba hi hne I hf hg hd hdegree F).2.1
    functionCommonBaseDegree J hJ W ≤ 4 := by
  classical
  let A := MvPolynomial (Fin 3) ℚ ⧸ I
  let ι := IsScalarTower.toAlgHom ℚ A F
  let ψ := ι.comp (Ideal.Quotient.mkₐ ℚ I)
  let J := algebraMap A F (Ideal.Quotient.mk I (jointRankFivePolynomial a b i))
  let W := fun j : Fin 3 =>
    ψ (orbitJointNumerators a b i j.castSucc) / ψ (orbitJointDenominator a b i)
  let V := fun j : Fin 3 => Ideal.Quotient.mk I
    (C ((Lz a b i : ℚ) ^ 2) * orbitPolarPolynomial a b i j)
  let q := orbitPolarParameters a b i
  let z := polarBasePoint (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)
  let znode := polarCumulativeBasePoint (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)
  have hG := (polarChartGuard_conditions hguard).2.2.2.1
  have hJ := retained_rank_five_degree_lower_bound hba hi hne I hf hg hd hdegree F
  let : Module.Finite ℚ⟮J⟯ F := hJ.2.1
  change functionCommonBaseDegree J hJ.1 W ≤ 4
  by_cases hzbase : znode ∈ coordinateZeroLocus I
  · let ε := coordinatePoint I znode hzbase
    let p := RingHom.ker ε.toRingHom
    let : p.IsMaximal := coordinatePoint_kernel_isMaximal I znode hzbase
    let R := Localization.AtPrime p
    let : CommRing R := inferInstance
    let : IsNoetherianRing R := IsLocalization.isNoetherianRing p.primeCompl R inferInstance
    have hden (r : p.primeCompl) : IsUnit (algebraMap A F r) :=
      isUnit_iff_ne_zero.mpr ((map_ne_zero_iff (algebraMap A F)
        (IsFractionRing.injective A F)).mpr
          (nonZeroDivisors.ne_zero (p.primeCompl_le_nonZeroDivisors r.property)))
    let χ : R →+* F := IsLocalization.lift hden
    let : Algebra R F := χ.toAlgebra
    let : IsScalarTower A R F :=
      IsScalarTower.of_algebraMap_eq fun r => (IsLocalization.lift_eq hden r).symm
    let : IsScalarTower ℚ R F := IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply ℚ A R]
      change algebraMap ℚ F c = χ (algebraMap A R (algebraMap ℚ A c))
      rw [IsLocalization.lift_eq]
      exact IsScalarTower.algebraMap_apply ℚ A F c
    let : IsFractionRing R F :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl R F
    have hnormal := orbit_affine_normalization hba hi hne I hf hg hd hdegree F
    let : IsDedekindDomain (integralClosure A F) := hnormal.1
    let : Module.Finite A (integralClosure A F) := hnormal.2
    obtain ⟨hρ, hu, hv, hne', ha, hA⟩ := orbit_rational_nonexceptional_data hba hi hne
    obtain ⟨M, hs⟩ := nonexceptional_eventual_first_node_generation
      hρ hu hv hne' _ _ _ _ _ ha I hf hg
    let w := Ideal.Quotient.mk I (X 0)
    let : Module.Finite (Algebra.adjoin ℚ {w}) A := coordinateRing_finite_over_parameter I w hs
    have hw := coordinate_parameter_transcendental I w hd hdegree hs
    let : Ring.KrullDimLE 1 R := finite_parameter_local_dimension (R := R) w hw
      p.primeCompl p.primeCompl_le_nonZeroDivisors
    let ψR := (IsScalarTower.toAlgHom ℚ A R).comp (Ideal.Quotient.mkₐ ℚ I)
    let : IsLocalization.AtPrime R (RingHom.ker
        (coordinatePoint I ![z 0, z 0 + z 1, z 0 + z 1 + z 2] hzbase).toRingHom) := by
      change IsLocalization.AtPrime R p
      infer_instance
    obtain ⟨j, _, hfin, hdim⟩ := polar_local_component_axis_colength_le_four
      (R := R) q hguard hminor (Lz a b i : ℚ) (a : ℚ) hA I hf hg hzbase
    let f : R := polarCenteredNodeGaps (R := R) ψR z j
    let : Module.Finite ℚ (R ⧸ Ideal.span {f}) := hfin
    have hlocalinj : Function.Injective (algebraMap A R) :=
      IsLocalization.injective R p.primeCompl_le_nonZeroDivisors
    have hf0 : f ≠ 0 := section_ne_zero_of_transcendental
      (IsScalarTower.toAlgHom ℚ A R) hlocalinj w hw f
    have hVp : Ideal.span (Set.range V) = p :=
      (orbit_polar_coordinate_ideal a b i hA hG I).trans
        (coordinatePoint_ker_eq_centered_ideal I znode hzbase).symm
    let gapA := polarCenteredNodeGaps (Ideal.Quotient.mkₐ ℚ I) z
    have hgapA : gapA j ∈ Ideal.span (Set.range V) := by
      rw [hVp]
      change ε (gapA j) = 0
      fin_cases j <;> simp [gapA, polarCenteredNodeGaps, ε, coordinatePoint_mk,
        znode, polarCumulativeBasePoint, z]
    have hmap : algebraMap A R (gapA j) = f := by
      fin_cases j <;> simp only [gapA, f, ψR, polarCenteredNodeGaps, Ideal.Quotient.mkₐ_eq_mk,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, map_sub, AlgHom.comp_apply,
        IsScalarTower.coe_toAlgHom']
      all_goals rw [← IsScalarTower.algebraMap_apply ℚ A R]
      all_goals rfl
    have hfV : f ∈ Ideal.span (Set.range (fun j => algebraMap A R (V j))) := by
      have h := Ideal.mem_map_of_mem (algebraMap A R) hgapA
      rw [Ideal.map_span, ← Set.range_comp, hmap] at h
      exact h
    exact (functionCommonBaseDegree_le_at_rational_point p ε rfl J hJ.1 W V
      (retained_polar_coordinate_field_identity hba hi I hz hcut ι
        (IsFractionRing.injective A F)) hVp f hf0 hfV
      (retained_rank_five_zero_affine_regular hba hi hne I hf hg hd hdegree F)).trans hdim
  · have hz0 := retained_polar_base_degree_zero_of_missing_point hba hi hne I hf hg hz
      hcut hG hzbase hd hdegree F
    exact hz0.le.trans (by omega)

end
end PierceLengthBound.FixedDividend
