/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveComponentDegree

/-! The two branch signs exist in the residue fields of the normalized orbit
infinity branches. The fraction `wr/u²` is integral because its square is `cr`;
reducing it and dividing by the resultant unit gives the square root of `c/r`
in each residue field. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- The square/fourth-power chart equation gives an integral sign numerator. -/
theorem integral_sign_numerator_of_square_fourth
    {S F : Type*} [CommRing S] [IsDomain S] [Field F] [Algebra S F] [IsFractionRing S F]
    (w u r c : S) (hu : u ≠ 0) (heq : w ^ 2 * r = c * u ^ 4) :
    ∃ z : integralClosure S F,
      (z : F) = algebraMap S F w * algebraMap S F r / (algebraMap S F u) ^ 2 ∧
      z ^ 2 = algebraMap S (integralClosure S F) (c * r) := by
  let x := algebraMap S F w * algebraMap S F r / (algebraMap S F u) ^ 2
  have huF : algebraMap S F u ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective S F).ne hu
  have hsq : x ^ 2 = algebraMap S F (c * r) := by
    have heF := congrArg (algebraMap S F) heq
    simp only [map_mul, map_pow] at heF ⊢
    dsimp [x]
    field_simp
    linear_combination algebraMap S F r * heF
  have hi : IsIntegral S x := IsIntegral.of_pow (n := 2) (by norm_num)
    (hsq.symm ▸ isIntegral_algebraMap)
  refine ⟨⟨x, hi⟩, rfl, ?_⟩
  apply Subtype.ext
  exact hsq

/-- The integral sign numerator produces the branch-sign square root in every
residue where the homogenized resultant is nonzero. -/
theorem normalization_residue_sign_of_square_fourth
    {S F : Type*} [CommRing S] [IsDomain S] [Field F] [Algebra S F] [IsFractionRing S F]
    (w u r c : S) (hu : u ≠ 0) (heq : w ^ 2 * r = c * u ^ 4)
    (p : Ideal (integralClosure S F)) [p.IsMaximal]
    (hr : Ideal.Quotient.mk p (algebraMap S (integralClosure S F) r) ≠ 0) :
    let : Field (integralClosure S F ⧸ p) := Ideal.Quotient.field p
    ∃ β : integralClosure S F ⧸ p,
      β ^ 2 = Ideal.Quotient.mk p (algebraMap S (integralClosure S F) c) /
        Ideal.Quotient.mk p (algebraMap S (integralClosure S F) r) := by
  let : Field (integralClosure S F ⧸ p) := Ideal.Quotient.field p
  obtain ⟨z, _, hz⟩ := integral_sign_numerator_of_square_fourth (F := F) w u r c hu heq
  let rbar := Ideal.Quotient.mk p (algebraMap S (integralClosure S F) r)
  refine ⟨Ideal.Quotient.mk p z / rbar, ?_⟩
  have hz' := congrArg (Ideal.Quotient.mk p) hz
  simp only [map_pow, map_mul] at hz'
  rw [div_pow, hz']
  change _ / rbar ^ 2 = _ / rbar
  field_simp [show rbar ≠ 0 from hr]
  rfl

/-- A resultant unit on the original infinity section remains nonzero in every
normalized branch residue over that section. -/
theorem normalization_residue_ne_zero_of_unit_mod_parameter
    {S F : Type*} [CommRing S] [IsDomain S] [Field F] [Algebra S F] [IsFractionRing S F]
    (w r : S) (hr : IsUnit (Ideal.Quotient.mk (Ideal.span {w}) r))
    (p : Ideal (integralClosure S F)) [p.IsPrime]
    (hp : algebraMap S (integralClosure S F) w ∈ p) :
    Ideal.Quotient.mk p (algebraMap S (integralClosure S F) r) ≠ 0 := by
  let φ := (Ideal.Quotient.mk p).comp (algebraMap S (integralClosure S F))
  have hker : Ideal.span {w} ≤ RingHom.ker φ := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
  let ψ : (S ⧸ Ideal.span {w}) →+* (integralClosure S F ⧸ p) :=
    Ideal.Quotient.lift _ φ hker
  have hunit := hr.map ψ
  exact hunit.ne_zero

/-- Every orbit infinity branch residue contains a square root of `(a/A)/r`,
where `A = Lz a b i` and `r` is the homogenized resultant. This is the unscaled
branch sign. -/
theorem orbit_infinity_residue_sign
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
    let r := chartHomogeneousMap I (orbitChartEmbedding I F) (Ideal.Quotient.mk I (X 0))
      (curveHomogenize 10 (curveResultant (patternRhoQ a b i) (patternUQ a b i)
        (patternVQ a b i) (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1))
        (patternVQ a b (i + 1))))
    ∀ p ∈ orbitInfinityBranches I F, ∃ β : orbitChartClosure I F ⧸ p.asIdeal,
      β ^ 2 * Ideal.Quotient.mk p.asIdeal (algebraMap (orbitChart I F) _ r) =
        Ideal.Quotient.mk p.asIdeal (algebraMap ℚ _ ((a : ℚ) / (Lz a b i : ℚ))) := by
  classical
  let ι := orbitChartEmbedding I F
  let S := orbitChart I F
  let C := orbitChartClosure I F
  let w := orbitChartParameter I F
  obtain ⟨_, _, _, hι, ha, hA, hρ, hu, hv, hne', _, hw⟩ :=
    orbit_infinity_chart_setup hba hi hne I hf hg hd hdegree F
  let φ := chartHomogeneousMap I ι (Ideal.Quotient.mk I (X 0))
  let u : S := φ (curveHomogenize 3 (curveNorm (patternRhoQ a b i)
    (patternUQ a b i) (patternVQ a b i) (patternRhoQ a b (i + 1))
    (patternUQ a b (i + 1)) (patternVQ a b (i + 1))))
  let c : S := algebraMap ℚ S ((a : ℚ) / (Lz a b i : ℚ))
  intro r p hp
  have hrunit : IsUnit (Ideal.Quotient.mk (Ideal.span {w}) r) :=
    nonexceptional_chart_resultant_unit hρ hu hv hne'
      (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
      (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι hι hd hdegree
  have hrbar := normalization_residue_ne_zero_of_unit_mod_parameter
    (F := F) w r hrunit p.asIdeal hp
  have hr0 : r ≠ 0 := by
    intro he
    exact hrbar (by rw [he, map_zero, map_zero])
  have hl : ι (Ideal.Quotient.mk I (X 0)) ≠ 0 := by
    intro he
    apply hw.ne_zero
    apply Subtype.ext
    change (ι (Ideal.Quotient.mk I (X 0)))⁻¹ = 0
    rw [he, inv_zero]
  have he := chartHomogeneousMap_homogenize_eq_zero I ι (Ideal.Quotient.mk I (X 0)) hl hg
    (curveEquation_degree_le _ _ _ _ _ _ _ _)
  have heqA := map_curveEquation_homogenize φ (patternRhoQ a b i) (patternUQ a b i)
    (patternVQ a b i) (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1))
    (patternVQ a b (i + 1)) (Lz a b i : ℚ) (a : ℚ) he
  have hφ (q : ℚ) : φ (Polynomial.C (MvPolynomial.C q)) = algebraMap ℚ S q := by
    simp [φ, chartHomogeneousMap, S, ι]
  have hφX : φ Polynomial.X = w := chartHomogeneousMap_X I ι _
  rw [hφX] at heqA
  change φ (Polynomial.C (MvPolynomial.C (Lz a b i : ℚ))) * w ^ 2 * r =
    φ (Polynomial.C (MvPolynomial.C (a : ℚ))) * u ^ 4 at heqA
  rw [hφ, hφ] at heqA
  have hAinv : algebraMap ℚ S (Lz a b i : ℚ)⁻¹ * algebraMap ℚ S (Lz a b i : ℚ) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hA, map_one]
  have heq : w ^ 2 * r = c * u ^ 4 := by
    calc w ^ 2 * r = (algebraMap ℚ S (Lz a b i : ℚ)⁻¹ *
        algebraMap ℚ S (Lz a b i : ℚ)) * (w ^ 2 * r) := by rw [hAinv, one_mul]
      _ = algebraMap ℚ S (Lz a b i : ℚ)⁻¹ * (algebraMap ℚ S (a : ℚ) * u ^ 4) := by
        rw [mul_assoc, ← mul_assoc (algebraMap ℚ S (Lz a b i : ℚ)), heqA]
      _ = c * u ^ 4 := by simp only [c, div_eq_mul_inv, map_mul]; ring
  have hu0 : u ≠ 0 := by
    intro hu0
    rw [hu0, zero_pow (by norm_num : 4 ≠ 0), mul_zero] at heq
    exact (mul_ne_zero (pow_ne_zero 2 hw.ne_zero) hr0) heq
  let : Field (C ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
  obtain ⟨β, hβ⟩ := normalization_residue_sign_of_square_fourth
    (F := F) w u r c hu0 heq p.asIdeal hrbar
  refine ⟨β, ?_⟩
  have hβ' := (eq_div_iff hrbar).mp hβ
  change β ^ 2 * Ideal.Quotient.mk p.asIdeal (algebraMap S C r) =
    Ideal.Quotient.mk p.asIdeal (algebraMap S C c) at hβ'
  rw [hβ']
  congr 1

end
end PierceLengthBound.FixedDividend
