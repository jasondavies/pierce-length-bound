/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.AffineNormalization
public import PierceLengthBound.NormalizedBranchValuation
public import PierceLengthBound.JointLiftChartOrders

/-! Constructed orders above the original affine component. The curvature
functions may have poles, but they cannot all have positive order on any
normalized affine branch. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

theorem normalized_affine_curvature_order
    {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hx : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    {d N : ℕ} {c₀ : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c₀)
    (F : Type*) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsScalarTower ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    (p : IsDedekindDomain.HeightOneSpectrum (integralClosure (MvPolynomial (Fin 3) ℚ ⧸ I) F)) :
    let S := MvPolynomial (Fin 3) ℚ ⧸ I
    let ι := IsScalarTower.toAlgHom ℚ S F
    let ψ := ι.comp (Ideal.Quotient.mkₐ ℚ I)
    ∃ ν : AddValuation F (WithTop ℤ),
      (∀ x : integralClosure S F, 0 < ν (x : F) ↔ x ∈ p.asIdeal) ∧
      (∀ r : S, 0 ≤ ν (algebraMap S F r)) ∧ (∃ π : F, ν π = 1) ∧
      ∃ j : Fin 3, ν (ψ (orbitJointNumerators a b i j.castSucc) /
        ψ (orbitJointDenominator a b i)) ≤ 0 := by
  let S := MvPolynomial (Fin 3) ℚ ⧸ I
  let C := integralClosure S F
  let ι := IsScalarTower.toAlgHom ℚ S F
  have ha : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  obtain ⟨hρ, hu, hv⟩ := orbit_rational_pattern_signs hba (by omega : i + 6 < P a b)
  have hne' : NonexceptionalPattern (patternRhoQ a b i : ℝ)
      (patternUQ a b i : ℝ) (patternVQ a b i : ℝ) := by simpa using hne
  have hnormal := nonexceptional_affine_normalization hρ hu hv hne'
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i : ℚ) (a : ℚ) ha I hf hg hd hdegree F
  let : IsDedekindDomain C := hnormal.1
  let : IsFractionRing C F :=
    IsIntegralClosure.isFractionRing_of_finite_extension S F F C
  let ν := normalizedBranchOrder p F
  have hregular (r : S) : 0 ≤ ν (algebraMap S F r) := by
    have hh := normalizedBranchOrder_nonnegative p F (algebraMap S C r)
    change 0 ≤ ν (algebraMap C F (algebraMap S C r)) at hh
    rwa [← IsScalarTower.algebraMap_apply S C F] at hh
  refine ⟨ν, ?_, hregular, normalizedBranchOrder_uniformizer p F, ?_⟩
  · intro x
    exact normalizedBranchOrder_positive_iff p F x
  · exact orbit_curvature_finite_discrete_order hba hi I hx ι
      (IsFractionRing.injective S F) ν hregular

end
end PierceLengthBound.FixedDividend
