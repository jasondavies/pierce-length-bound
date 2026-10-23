/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.NormalizationPointBranch
public import PierceLengthBound.JointLiftPoleDegree
public import PierceLengthBound.ChartFunctionField

/-! The extra affine zero of a curvature combination survives normalization
and lies outside the old infinity fiber. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

def jointCurvatureNumerator (a b i : ℕ) (c : Fin 3 → ℚ) : MvPolynomial (Fin 3) ℚ :=
  ∑ j, C (c j) * orbitJointNumerators a b i j.castSucc

theorem jointCurvatureCombination_eq_fraction {F : Type*} [Field F] [Algebra ℚ F]
    (ψ : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] F) (a b i : ℕ) (c : Fin 3 → ℚ) :
    jointCurvatureCombination ψ a b i c =
      ψ (jointCurvatureNumerator a b i c) / ψ (orbitJointDenominator a b i) := by
  simp only [jointCurvatureCombination, jointCurvatureNumerator, map_sum, map_mul,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_div_assoc, show ψ (C (c j)) = algebraMap ℚ F (c j) from ψ.commutes _]

set_option synthInstance.maxHeartbeats 200000 in
-- The graph localization carries the quotient's scalar tower.
theorem jointGraph_curvature_combination_eq_numerator
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) (a b i : ℕ) (c : Fin 3 → ℚ) :
    (∑ j : Fin 3, algebraMap ℚ _ (c j) *
      jointGraphMap I (orbitJointNumerators a b i) (orbitJointDenominator a b i)
        (X (Sum.inr j.castSucc))) =
      algebraMap (MvPolynomial (Fin 3) ℚ ⧸ I) (graphLocalization I (orbitJointDenominator a b i))
        (Ideal.Quotient.mk I (jointCurvatureNumerator a b i c)) *
          IsLocalization.Away.invSelf (Ideal.Quotient.mk I (orbitJointDenominator a b i)) := by
  simp only [jointCurvatureNumerator, map_sum, map_mul, jointGraphMap, aeval_X,
    Sum.elim_inr, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [show Ideal.Quotient.mk I (C (c j)) =
      algebraMap ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) (c j) from rfl,
    ← IsScalarTower.algebraMap_apply ℚ (MvPolynomial (Fin 3) ℚ ⧸ I)
    (graphLocalization I (orbitJointDenominator a b i))]
  ring

/-- The chosen linear combination has a nonzero numerator on the component,
and that numerator vanishes at the actual orbit point. -/
theorem orbitJoint_exists_curvature_numerator_zero {a b i d : ℕ}
    (hba : b < a) (hi : i + 7 < P a b)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (Q : MvPolynomial (Fin 3) ℚ) (hQ : Prime Q) (hQdeg : Q.totalDegree = 2) (hQI : Q ∈ I)
    (hd3 : 3 ≤ d)
    (hd : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c) :
    ∃ c : Fin 3 → ℚ, jointCurvatureNumerator a b i c ∉ I ∧
      eval (orbitFreeNodesQ a b i) (jointCurvatureNumerator a b i c) = 0 := by
  obtain ⟨c, hc, hzero⟩ := orbitJoint_exists_curvature_combination_vanishing
    hba hi I hz Q hQ hQdeg hQI hd3 hd
  dsimp only at hc hzero
  rw [jointGraph_curvature_combination_eq_numerator] at hc hzero
  refine ⟨c, ?_, ?_⟩
  · intro hmem
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero, zero_mul] at hc
    exact hc rfl
  · rw [map_mul, graphPointMap_mk, graphPointMap_invSelf] at hzero
    exact (mul_eq_zero.mp hzero).resolve_right
      (inv_ne_zero (orbitJointDenominator_eval_ne_zero hba hi))

/-- The infinity chart has the component's function field and a finite
Dedekind normalization in that field. -/
theorem orbit_chart_normalization_in_field
    {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    {d N : ℕ} {c₀ : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c₀)
    (F : Type*) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsScalarTower ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin 3) ℚ ⧸ I) F] :
    let ι := IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F
    let S := projectiveChart I ι (Ideal.Quotient.mk I (X 0))
    IsFractionRing S F ∧ IsDedekindDomain (integralClosure S F) ∧
      Module.Finite S (integralClosure S F) := by
  let R := MvPolynomial (Fin 3) ℚ ⧸ I
  let ι := IsScalarTower.toAlgHom ℚ R F
  let l := Ideal.Quotient.mk I (X 0)
  let S := projectiveChart I ι l
  have hι : Function.Injective ι := IsFractionRing.injective R F
  obtain ⟨hρ, hu, hv, hne', ha, -⟩ := orbit_rational_nonexceptional_data hba hi hne
  obtain ⟨hl, M, hs⟩ := nonexceptional_first_node_generation hρ hu hv hne'
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι hι hd hdegree
  have hlmem : l ∈ filteredCoordinateSpace I 1 :=
    ⟨X 0, by simp [mem_restrictTotalDegree], rfl⟩
  let : IsFractionRing S F := projectiveChart_isFractionRing I ι l hl (fun z => by
    obtain ⟨x, y, _, hxy⟩ := IsFractionRing.div_surjective R z
    exact ⟨x, y, hxy.symm⟩)
  let : Module.Finite (Algebra.adjoin ℚ {chartInfinityCoordinate I ι l}) S :=
    projectiveChart_finite_over_parameter I ι l hlmem hl hs
  exact ⟨inferInstance, finite_parameter_normalization (chartInfinityCoordinate I ι l)
    (chartInfinityCoordinate_transcendental I ι hι l hlmem hl hd hdegree hs) F⟩

/-- The extra zero is an actual normalized branch, separate from old infinity;
the curvature combination is transcendental in the component function field. -/
theorem orbitJoint_exists_extra_normalized_zero {a b i d N : ℕ} {c₀ : ℤ}
    (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (Q : MvPolynomial (Fin 3) ℚ) (hQ : Prime Q) (hQdeg : Q.totalDegree = 2) (hQI : Q ∈ I)
    (hd3 : 3 ≤ d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c₀)
    (F : Type*) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsScalarTower ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin 3) ℚ ⧸ I) F] :
    let ι := IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F
    let S := projectiveChart I ι (Ideal.Quotient.mk I (X 0))
    let C := integralClosure S F
    let hn := orbit_chart_normalization_in_field hba hi hne I hf hg
      (by omega : 0 < d) hdegree F
    let : IsFractionRing S F := hn.1
    let : IsDedekindDomain C := hn.2.1
    let : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension S F F C
    ∃ c : Fin 3 → ℚ, ∃ q : IsDedekindDomain.HeightOneSpectrum C,
      Transcendental ℚ (jointCurvatureCombination (ι.comp (Ideal.Quotient.mkₐ ℚ I)) a b i c) ∧
      0 < normalizedBranchOrder q F
        (jointCurvatureCombination (ι.comp (Ideal.Quotient.mkₐ ℚ I)) a b i c) ∧
      algebraMap S C (chartInfinityCoordinate I ι (Ideal.Quotient.mk I (X 0))) ∉ q.asIdeal := by
  let R := MvPolynomial (Fin 3) ℚ ⧸ I
  let ι := IsScalarTower.toAlgHom ℚ R F
  let S := projectiveChart I ι (Ideal.Quotient.mk I (X 0))
  let C := integralClosure S F
  let w := chartInfinityCoordinate I ι (Ideal.Quotient.mk I (X 0))
  let hn := orbit_chart_normalization_in_field hba hi hne I hf hg
    (by omega : 0 < d) hdegree F
  let : IsFractionRing S F := hn.1
  let : IsDedekindDomain C := hn.2.1
  let : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension S F F C
  let : IsDedekindDomain (integralClosure R F) :=
    (orbit_affine_normalization hba hi hne I hf hg (by omega : 0 < d) hdegree F).1
  obtain ⟨hρ, hu, hv, hne', ha, -⟩ := orbit_rational_nonexceptional_data hba hi hne
  let : Module.Finite (Algebra.adjoin ℚ {w}) S :=
    nonexceptional_chart_finite_over_parameter hρ hu hv hne'
      (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
      (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι (IsFractionRing.injective R F)
      (by omega : 0 < d) hdegree
  let φ : R →ₐ[ℚ] ℚ := Ideal.Quotient.liftₐ I (MvPolynomial.aeval (orbitFreeNodesQ a b i))
    (by intro f hf; exact hz f hf)
  obtain ⟨c, hc, hcφ⟩ := orbitJoint_exists_curvature_numerator_zero hba hi I hz
    Q hQ hQdeg hQI hd3 ⟨N, c₀, hdegree⟩
  let r := Ideal.Quotient.mk I (jointCurvatureNumerator a b i c)
  let s := Ideal.Quotient.mk I (orbitJointDenominator a b i)
  let t := Ideal.Quotient.mk I (X 0)
  have hr : r ≠ 0 := by simpa only [r, ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hc
  have hrφ : φ r = 0 := hcφ
  have hsφ : φ s ≠ 0 := orbitJointDenominator_eval_ne_zero hba hi
  have htφ : φ t ≠ 0 := by
    change eval (orbitFreeNodesQ a b i) (X 0) ≠ 0
    rw [eval_X]
    change (qq a b (i + 1) : ℚ) - qq a b i ≠ 0
    have hlt : (qq a b i : ℚ) < qq a b (i + 1) :=
      by exact_mod_cast qq_lt (by omega : i + 1 < P a b)
    exact ne_of_gt (sub_pos.mpr hlt)
  obtain ⟨q, hpos, hout⟩ := rational_zero_on_reciprocal_parameter_model
    (L := F) φ hr hrφ hsφ htφ w rfl
  have he : jointCurvatureCombination (ι.comp (Ideal.Quotient.mkₐ ℚ I)) a b i c =
      algebraMap R F r / algebraMap R F s :=
    jointCurvatureCombination_eq_fraction _ a b i c
  have hx : jointCurvatureCombination (ι.comp (Ideal.Quotient.mkₐ ℚ I)) a b i c ≠ 0 := by
    rw [he]
    apply div_ne_zero
    · exact (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hr
    · apply (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr
      intro hs
      exact hsφ (by rw [hs, map_zero])
  have hpos' : 0 < normalizedBranchOrder q F
      (jointCurvatureCombination (ι.comp (Ideal.Quotient.mkₐ ℚ I)) a b i c) := by
    rwa [he]
  refine ⟨c, q, transcendental_of_positive_order (normalizedBranchOrder q F) ?_ hx hpos',
    hpos', hout⟩
  intro z
  rw [IsScalarTower.algebraMap_apply ℚ C F]
  exact normalizedBranchOrder_nonnegative q F _

end
end PierceLengthBound.FixedDividend
