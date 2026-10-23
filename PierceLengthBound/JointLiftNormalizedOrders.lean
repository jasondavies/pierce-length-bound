/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ChartParameterTranscendence
public import PierceLengthBound.CurveNormalization
public import PierceLengthBound.ChartFunctionField
public import PierceLengthBound.NormalizedBranchValuation
public import PierceLengthBound.JointLiftChartOrders

/-! Constructed, normalized branch orders for the actual joint graph. The
valuation and its chart center are proved from a prime of the normalization,
rather than supplied as local order assumptions. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- Every normalized branch above old infinity carries a normalized discrete
order with the proved joint-coordinate orders. The fraction presentation only
identifies F as the component function field; no valuation is assumed. -/
theorem retained_normalized_branch_joint_orders
    {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hx : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hnorm : jointNormalizationPolynomial a b i ∈ I)
    (hres : jointResolventPolynomial a b i ∈ I)
    {F : Type*} [Field F] [Algebra ℚ F]
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι)
    (hfrac : ∀ z : F, ∃ x y : MvPolynomial (Fin 3) ℚ ⧸ I, z = ι x / ι y)
    {d N : ℕ} {c₀ : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c₀)
    (p : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (projectiveChart I ι (Ideal.Quotient.mk I (X 0))) F))
    (hp : algebraMap (projectiveChart I ι (Ideal.Quotient.mk I (X 0)))
      (integralClosure (projectiveChart I ι (Ideal.Quotient.mk I (X 0))) F)
      (chartInfinityCoordinate I ι (Ideal.Quotient.mk I (X 0))) ∈ p.asIdeal) :
    let S := projectiveChart I ι (Ideal.Quotient.mk I (X 0))
    let ψ := ι.comp (Ideal.Quotient.mkₐ ℚ I)
    let W := fun j => ψ (orbitJointNumerators a b i j) / ψ (orbitJointDenominator a b i)
    ∃ ν : AddValuation F (WithTop ℤ),
      (∀ x : integralClosure S F, 0 < ν (x : F) ↔ x ∈ p.asIdeal) ∧
      (∀ r : S, 0 ≤ ν (r : F)) ∧ (∃ π : F, ν π = 1) ∧
      ∃ t : ℤ, 0 < t ∧
        ν ((ι (Ideal.Quotient.mk I (X 0)))⁻¹) = ((2 * t : ℤ) : WithTop ℤ) ∧
        ν (W 0) = ((3 * t : ℤ) : WithTop ℤ) ∧
        ((3 * t : ℤ) : WithTop ℤ) ≤ ν (W 1) ∧
        ν (W 2) = ((3 * t : ℤ) : WithTop ℤ) ∧
        ν (W 3) = ((-5 * t : ℤ) : WithTop ℤ) := by
  let l := Ideal.Quotient.mk I (X 0)
  let S := projectiveChart I ι l
  let C := integralClosure S F
  have ha : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  obtain ⟨hρ, hu, hv⟩ := orbit_rational_pattern_signs hba (by omega : i + 6 < P a b)
  have hne' : NonexceptionalPattern (patternRhoQ a b i : ℝ)
      (patternUQ a b i : ℝ) (patternVQ a b i : ℝ) := by simpa using hne
  obtain ⟨M, hs⟩ := rational_nonexceptional_eventual_first_node_generation hρ hu hv hne'
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i : ℚ) (a : ℚ) ha I hf hg
  have hl : ι l ≠ 0 := by
    intro hz
    apply first_node_ne_zero_of_generation I hd hdegree hs
    exact hι (by simpa using hz)
  have hlmem : l ∈ filteredCoordinateSpace I 1 :=
    ⟨X 0, by simp [mem_restrictTotalDegree], rfl⟩
  let : IsFractionRing S F := projectiveChart_isFractionRing I ι l hl hfrac
  let : Module.Finite (Algebra.adjoin ℚ {chartInfinityCoordinate I ι l}) S :=
    projectiveChart_finite_over_parameter I ι l hlmem hl hs
  have hnormal := finite_parameter_normalization (chartInfinityCoordinate I ι l)
    (chartInfinityCoordinate_transcendental I ι hι l hlmem hl hd hdegree hs) F
  let : IsDedekindDomain C := hnormal.1
  let : IsFractionRing C F :=
    IsIntegralClosure.isFractionRing_of_finite_extension S F F C
  let ν := normalizedBranchOrder p F
  have hregular (r : S) : 0 ≤ ν (r : F) := by
    have hh := normalizedBranchOrder_nonnegative p F (algebraMap S C r)
    change 0 ≤ ν (algebraMap C F (algebraMap S C r)) at hh
    rw [← IsScalarTower.algebraMap_apply S C F] at hh
    exact hh
  have hw0 : algebraMap S C (chartInfinityCoordinate I ι l) ≠ 0 := by
    intro hz
    have hh := congrArg (algebraMap C F) hz
    rw [← IsScalarTower.algebraMap_apply S C F, map_zero] at hh
    exact (inv_ne_zero hl) hh
  obtain ⟨e, he, hw⟩ := normalizedBranchOrder_parameter p F hw0 hp
  have hw' : ν ((ι l)⁻¹) = (e : WithTop ℤ) := by
    change ν (algebraMap C F (algebraMap S C (chartInfinityCoordinate I ι l))) = _ at hw
    rw [← IsScalarTower.algebraMap_apply S C F] at hw
    exact hw
  obtain ⟨t, ht, het, hW⟩ := retained_joint_coordinates_discrete_orders
    hba hi hne I hf hg hx hnorm hres ι hι hd hdegree ν hregular he hw'
  refine ⟨ν, ?_, hregular, normalizedBranchOrder_uniformizer p F, t, ht, ?_, hW⟩
  · intro x
    exact normalizedBranchOrder_positive_iff p F x
  · simpa only [het] using hw'

end
end PierceLengthBound.FixedDividend
