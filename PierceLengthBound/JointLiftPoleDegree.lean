/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchPoleDegree
public import PierceLengthBound.JointLiftPoleCoverage
public import PierceLengthBound.FunctionParameterChange

/-! The field degree of a transcendental curvature combination is bounded by
the actual curvature pole-envelope degree on the affine normalization. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial
open scoped IntermediateField

theorem orbit_affine_normalization
    {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    {d N : ℕ} {c₀ : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c₀)
    (F : Type*) [Field F] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin 3) ℚ ⧸ I) F] :
    IsDedekindDomain (integralClosure (MvPolynomial (Fin 3) ℚ ⧸ I) F) ∧
      Module.Finite (MvPolynomial (Fin 3) ℚ ⧸ I)
        (integralClosure (MvPolynomial (Fin 3) ℚ ⧸ I) F) := by
  obtain ⟨hρ, hu, hv, hne', ha, -⟩ := orbit_rational_nonexceptional_data hba hi hne
  exact nonexceptional_affine_normalization hρ hu hv hne'
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i : ℚ) (a : ℚ) ha I hf hg hd hdegree F

/-- This is the actual retained-component upper comparison for the curvature
pole envelope. Normalization, parameter finiteness and coverage of every pole
are proved from the component hypotheses. -/
theorem retained_curvature_function_degree_le_envelope
    {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hnorm : jointNormalizationPolynomial a b i ∈ I)
    (hres : jointResolventPolynomial a b i ∈ I)
    {d N : ℕ} {c₀ : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c₀)
    (F : Type*) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsScalarTower ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    (c : Fin 3 → ℚ) (x : F) (hx : Transcendental ℚ x)
    (hexpr : x = jointCurvatureCombination
      ((IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F).comp
        (Ideal.Quotient.mkₐ ℚ I)) a b i c) :
    let R := MvPolynomial (Fin 3) ℚ ⧸ I
    let C := integralClosure R F
    let : IsDedekindDomain C := (orbit_affine_normalization hba hi hne I hf hg hd hdegree F).1
    let : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension R F F C
    let ψ := (IsScalarTower.toAlgHom ℚ R F).comp (Ideal.Quotient.mkₐ ℚ I)
    Module.finrank ℚ⟮x⟯ F ≤ poleEnvelopeDegree C
      (fun j : Fin 3 =>
        ψ (orbitJointNumerators a b i j.castSucc) / ψ (orbitJointDenominator a b i)) := by
  let R := MvPolynomial (Fin 3) ℚ ⧸ I
  let C := integralClosure R F
  let : IsDedekindDomain C := (orbit_affine_normalization hba hi hne I hf hg hd hdegree F).1
  let : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension R F F C
  let l := Ideal.Quotient.mk I (X 0)
  obtain ⟨hρ, hu, hv, hne', ha, -⟩ := orbit_rational_nonexceptional_data hba hi hne
  obtain ⟨M, hs⟩ := nonexceptional_eventual_first_node_generation hρ hu hv hne'
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i : ℚ) (a : ℚ) ha I hf hg
  let : Module.Finite (Algebra.adjoin ℚ {l}) R := coordinateRing_finite_over_parameter I l hs
  let : FiniteDimensional ℚ⟮x⟯ F := finite_fraction_field_over_function l
    (coordinate_parameter_transcendental I l hd hdegree hs) x hx
  apply function_degree_le_poleEnvelope _ c x hx hexpr
  intro ν hQ hπ hpole
  have hh := retained_curvature_pole_affine_center hba hi hne I hf hg hz hnorm hres
    hd hdegree F ν hQ hπ c (by rwa [← hexpr])
  exact branch_order_nonnegative_on_normalization ν hh.1

end
end PierceLengthBound.FixedDividend
