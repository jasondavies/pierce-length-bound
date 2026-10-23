/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.NormalizationBranchCover
public import PierceLengthBound.JointLiftChartOrders
public import PierceLengthBound.AffineNormalization
public import PierceLengthBound.ChartParameterTranscendence

/-! Every pole of a rational constant combination of the retained curvature
coordinates lies on the original affine normalization. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

def jointCurvatureCombination {F : Type*} [Field F] [Algebra ℚ F]
    (ψ : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] F) (a b i : ℕ) (c : Fin 3 → ℚ) : F :=
  ∑ j, algebraMap ℚ F (c j) *
    (ψ (orbitJointNumerators a b i j.castSucc) / ψ (orbitJointDenominator a b i))

/-- A pole of the original first coordinate makes the infinity parameter
regular. Finiteness then makes the whole infinity chart regular, so the proved
joint-coordinate orders rule out poles of curvature combinations there. -/
theorem retained_curvature_combination_regular_at_infinity
    {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hx : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hnorm : jointNormalizationPolynomial a b i ∈ I)
    (hres : jointResolventPolynomial a b i ∈ I)
    {F : Type*} [Field F] [Algebra ℚ F]
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι)
    {d N : ℕ} {c₀ : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c₀)
    (ν : AddValuation F (WithTop ℤ)) (hQ : ∀ c : ℚ, 0 ≤ ν (algebraMap ℚ F c))
    (c : Fin 3 → ℚ) (hneg : ν (ι (Ideal.Quotient.mk I (X 0))) < 0) :
    0 ≤ ν (jointCurvatureCombination (ι.comp (Ideal.Quotient.mkₐ ℚ I)) a b i c) := by
  let l := Ideal.Quotient.mk I (X 0)
  let S := projectiveChart I ι l
  let w := chartInfinityCoordinate I ι l
  change ν (ι l) < 0 at hneg
  have hl0 : ι l ≠ 0 := by intro h; simp [h] at hneg
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (ν.ne_top_iff.mpr hl0)
  have hnneg : n < 0 := by rw [← hn] at hneg; exact_mod_cast hneg
  have he : 0 < -n := by omega
  have hw : ν ((ι l)⁻¹) = ((-n : ℤ) : WithTop ℤ) := by rw [ν.map_inv, ← hn]; rfl
  obtain ⟨hρ, hu, hv, hne', ha, -⟩ := orbit_rational_nonexceptional_data hba hi hne
  let : Module.Finite (Algebra.adjoin ℚ {w}) S :=
    nonexceptional_chart_finite_over_parameter hρ hu hv hne'
      (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
      (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι hι hd hdegree
  have hregular (r : S) : 0 ≤ ν (r : F) := by
    apply branch_order_nonnegative_of_finite_parameter w ν hQ _ r
    change 0 ≤ ν ((ι l)⁻¹)
    rw [hw]
    exact_mod_cast he.le
  obtain ⟨t, ht, _, h0, h1, h2, _⟩ := retained_joint_coordinates_discrete_orders
    hba hi hne I hf hg hx hnorm hres ι hι hd hdegree ν hregular he hw
  let ψ := ι.comp (Ideal.Quotient.mkₐ ℚ I)
  let W := fun j => ψ (orbitJointNumerators a b i j) / ψ (orbitJointDenominator a b i)
  have h3 : (0 : WithTop ℤ) ≤ ((3 * t : ℤ) : WithTop ℤ) := by
    exact_mod_cast (show (0 : ℤ) ≤ 3 * t by omega)
  have hW (j : Fin 3) : 0 ≤ ν (W j.castSucc) := by
    fin_cases j
    · exact h0.symm ▸ h3
    · exact h3.trans h1
    · exact h2.symm ▸ h3
  apply ν.map_le_sum
  intro j _
  rw [ν.map_mul]
  exact add_nonneg (hQ _) (hW j)

/-- Any normalized branch where a retained curvature combination has a pole
is represented on the original affine normalization. -/
theorem retained_curvature_pole_affine_center
    {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hx : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hnorm : jointNormalizationPolynomial a b i ∈ I)
    (hres : jointResolventPolynomial a b i ∈ I)
    {d N : ℕ} {c₀ : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c₀)
    (F : Type*) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsScalarTower ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    (ν : AddValuation F (WithTop ℤ)) (hQ : ∀ c : ℚ, 0 ≤ ν (algebraMap ℚ F c))
    (hπ : ∃ π : F, ν π = 1) (c : Fin 3 → ℚ)
    (hpole : ν (jointCurvatureCombination
      ((IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F).comp
        (Ideal.Quotient.mkₐ ℚ I)) a b i c) < 0) :
    (∀ r : MvPolynomial (Fin 3) ℚ ⧸ I, 0 ≤ ν (algebraMap _ F r)) ∧
    ∃ p : IsDedekindDomain.HeightOneSpectrum (integralClosure (MvPolynomial (Fin 3) ℚ ⧸ I) F),
      ∀ r : integralClosure (MvPolynomial (Fin 3) ℚ ⧸ I) F,
        r ∈ p.asIdeal ↔ 0 < ν (r : F) := by
  let R := MvPolynomial (Fin 3) ℚ ⧸ I
  let ι := IsScalarTower.toAlgHom ℚ R F
  let l := Ideal.Quotient.mk I (X 0)
  have hl : 0 ≤ ν (ι l) := by
    by_contra hn
    have hh := retained_curvature_combination_regular_at_infinity
      hba hi hne I hf hg hx hnorm hres ι (IsFractionRing.injective R F)
      hd hdegree ν hQ c (lt_of_not_ge hn)
    exact (not_lt_of_ge hh) hpole
  obtain ⟨hρ, hu, hv, hne', ha, -⟩ := orbit_rational_nonexceptional_data hba hi hne
  obtain ⟨M, hs⟩ := rational_nonexceptional_eventual_first_node_generation hρ hu hv hne'
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i : ℚ) (a : ℚ) ha I hf hg
  let : Module.Finite (Algebra.adjoin ℚ {l}) R := coordinateRing_finite_over_parameter I l hs
  have hregular := branch_order_nonnegative_of_finite_parameter l ν hQ hl
  exact ⟨hregular, regular_normalization_branch_center ν hregular hπ⟩

end
end PierceLengthBound.FixedDividend
