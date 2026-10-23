/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveResidueSigns

/-! The barycentric identity converts the actual normalized branch sign to the
quadratic extension used by the specialization sieve. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Matrix MvPolynomial
noncomputable section

/-- The Vandermonde factor of the first four locations, including location zero. -/
def branchLocationDelta {K : Type*} [CommRing K] (z₁ z₂ z₃ : K) : K :=
  z₁ * z₂ * z₃ * (z₂ - z₁) * (z₃ - z₁) * (z₃ - z₂)

/-- The four factors involving the fifth location. -/
def branchFifthLocationProduct {K : Type*} [CommRing K] (z₁ z₂ z₃ z₄ : K) : K :=
  z₄ * (z₄ - z₁) * (z₄ - z₂) * (z₄ - z₃)

/-- Four moment relations give the exact resultant/Vandermonde identity. This
is polynomial and does not divide by any node difference. -/
theorem branch_barycentric_resultant_identity {K : Type*} [CommRing K]
    (c₀ c₁ c₂ c₃ z₁ z₂ z₃ z₄ : K)
    (h0 : c₀ + c₁ + c₂ + c₃ + 1 = 0)
    (h1 : c₁ * z₁ + c₂ * z₂ + c₃ * z₃ + z₄ = 0)
    (h2 : c₁ * z₁ ^ 2 + c₂ * z₂ ^ 2 + c₃ * z₃ ^ 2 + z₄ ^ 2 = 0)
    (h3 : c₁ * z₁ ^ 3 + c₂ * z₂ ^ 3 + c₃ * z₃ ^ 3 + z₄ ^ 3 = 0) :
    (c₀ * c₁ * c₂ * c₃ * nodeVandermonde ![z₁, z₂, z₃, z₄]) *
      branchLocationDelta z₁ z₂ z₃ = (branchFifthLocationProduct z₁ z₂ z₃ z₄) ^ 4 := by
  let V := branchFifthLocationProduct z₁ z₂ z₃ z₄
  have hc0 : c₀ * (z₁ * z₂ * z₃ * z₄) = V := by
    dsimp [V, branchFifthLocationProduct]
    linear_combination -z₄ * (h3 - (z₁ + z₂ + z₃) * h2 +
      (z₁ * z₂ + z₁ * z₃ + z₂ * z₃) * h1 - (z₁ * z₂ * z₃) * h0)
  have hc1 : c₁ * (z₁ * (z₁ - z₂) * (z₁ - z₃) * (z₁ - z₄)) = V := by
    dsimp [V, branchFifthLocationProduct]
    linear_combination (z₁ - z₄) * (h3 - (z₂ + z₃) * h2 + z₂ * z₃ * h1)
  have hc2 : c₂ * (z₂ * (z₂ - z₁) * (z₂ - z₃) * (z₂ - z₄)) = V := by
    dsimp [V, branchFifthLocationProduct]
    linear_combination (z₂ - z₄) * (h3 - (z₁ + z₃) * h2 + z₁ * z₃ * h1)
  have hc3 : c₃ * (z₃ * (z₃ - z₁) * (z₃ - z₂) * (z₃ - z₄)) = V := by
    dsimp [V, branchFifthLocationProduct]
    linear_combination (z₃ - z₄) * (h3 - (z₁ + z₂) * h2 + z₁ * z₂ * h1)
  calc _ = (c₀ * (z₁ * z₂ * z₃ * z₄)) *
      (c₁ * (z₁ * (z₁ - z₂) * (z₁ - z₃) * (z₁ - z₄))) *
      (c₂ * (z₂ * (z₂ - z₁) * (z₂ - z₃) * (z₂ - z₄))) *
      (c₃ * (z₃ * (z₃ - z₁) * (z₃ - z₂) * (z₃ - z₄))) := by
        simp only [nodeVandermonde, branchLocationDelta, Matrix.cons_val]
        ring
    _ = V ^ 4 := by rw [hc0, hc1, hc2, hc3]; ring

/-- Scaling the actual sign by the square of the fifth-node product gives
exactly the quadratic relation used by the degree-twelve branch algebra. -/
theorem branch_scaled_sign_square {K : Type*} [CommRing K] (β r c Δ V : K)
    (hβ : β ^ 2 * r = c) (hres : r * Δ = V ^ 4) :
    (V ^ 2 * β) ^ 2 = c * Δ := by
  calc (V ^ 2 * β) ^ 2 = β ^ 2 * (r * Δ) := by rw [hres]; ring
    _ = (β ^ 2 * r) * Δ := by ring
    _ = c * Δ := by rw [hβ]

/-- The second and third location moments vanish in every actual infinity
residue. Together with the linear elimination they give the two specialized
location equations used by the branch sieve. -/
theorem chart_infinity_moment_equations
    {F K : Type*} [Field F] [Algebra ℚ F] [Field K] [Algebra ℚ K]
    (ρ u v ρ' u' v' A a : ℚ) (ha : a ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℚ))
    (hf : curveQuadratic ρ u v ρ' u' v' ∈ I)
    (hg : curveEquation ρ u v ρ' u' v' A a ∈ I)
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F)
    (l : MvPolynomial (Fin 3) ℚ ⧸ I) (hl : ι l ≠ 0)
    (ψ : projectiveChart I ι l →ₐ[ℚ] K)
    (hw : ψ (chartInfinityCoordinate I ι l) = 0) :
    let z := fun j => ψ (chartNode I ι l j)
    let z₄ := fourthNode (algebraMap ℚ K ρ) (algebraMap ℚ K u) (algebraMap ℚ K v)
      (z 0) (z 1) (z 2)
    ((-algebraMap ℚ K ρ - algebraMap ℚ K u) * z 0 ^ 2 +
      (algebraMap ℚ K u - algebraMap ℚ K v) * z 1 ^ 2 +
      (algebraMap ℚ K v - 1) * z 2 ^ 2 + z₄ ^ 2 = 0) ∧
    ((-algebraMap ℚ K ρ - algebraMap ℚ K u) * z 0 ^ 3 +
      (algebraMap ℚ K u - algebraMap ℚ K v) * z 1 ^ 3 +
      (algebraMap ℚ K v - 1) * z 2 ^ 3 + z₄ ^ 3 = 0) := by
  let φ := chartHomogeneousMap I ι l
  let z := fun j => ψ (chartNode I ι l j)
  let rρ := algebraMap ℚ K ρ
  let ru := algebraMap ℚ K u
  let rv := algebraMap ℚ K v
  let z₄ := fourthNode rρ ru rv (z 0) (z 1) (z 2)
  have hq := congrArg ψ (chartHomogeneousMap_homogenize_eq_zero I ι l hl hf
    (curveQuadratic_degree_le_two _ _ _ _ _ _))
  rw [chartHomogeneousMap_closed_residue I ι l ψ hw, map_zero] at hq
  simp only [map_curveHomogenize, map_curveQuadratic, curveQuadratic_at_infinity] at hq
  have he := map_curveEquation_homogenize φ ρ u v ρ' u' v' A a
    (chartHomogeneousMap_homogenize_eq_zero I ι l hl hg
      (curveEquation_degree_le _ _ _ _ _ _ _ _))
  have heψ := congrArg ψ he
  have hc (c : ℚ) : ψ (φ (Polynomial.C (MvPolynomial.C c))) = algebraMap ℚ K c := by
    simp [φ, chartHomogeneousMap, ψ.commutes]
  simp only [map_mul, map_pow, show φ Polynomial.X = chartInfinityCoordinate I ι l from
    chartHomogeneousMap_X I ι l, hw, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
    zero_mul, hc] at heψ
  have haK : algebraMap ℚ K a ≠ 0 := by
    simpa only [map_zero] using (algebraMap ℚ K).injective.ne ha
  have hu0 : ψ (φ (curveHomogenize 3 (curveNorm ρ u v ρ' u' v'))) = 0 :=
    (pow_eq_zero_iff (by norm_num : 4 ≠ 0)).mp ((mul_eq_zero.mp heψ.symm).resolve_left haK)
  change ψ (chartHomogeneousMap I ι l _) = 0 at hu0
  rw [chartHomogeneousMap_closed_residue I ι l ψ hw] at hu0
  simp only [map_curveHomogenize, map_curveNorm, curveNorm_at_infinity] at hu0
  rw [eval_leadingQuadratic_moment] at hq
  rw [eval_leadingCubic_moment] at hu0
  have h2 : (-rρ - ru) * z 0 ^ 2 + (ru - rv) * z 1 ^ 2 +
      (rv - 1) * z 2 ^ 2 + z₄ ^ 2 = 0 := by
    simpa [coeffs, completeDirection, Fin.sum_univ_succ, add_assoc,
      z, rρ, ru, rv, z₄] using hq
  have h3 : (-rρ - ru) * z 0 ^ 3 + (ru - rv) * z 1 ^ 3 +
      (rv - 1) * z 2 ^ 3 + z₄ ^ 3 = 0 := by
    simpa [coeffs, completeDirection, Fin.sum_univ_succ, add_assoc,
      z, rρ, ru, rv, z₄] using hu0
  exact ⟨h2, h3⟩

/-- The barycentric identity holds in every actual infinity residue of a
component, without assumptions on smoothness or geometric irreducibility. -/
theorem chart_infinity_barycentric_identity
    {F K : Type*} [Field F] [Algebra ℚ F] [Field K] [Algebra ℚ K]
    (ρ u v ρ' u' v' A a : ℚ) (ha : a ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℚ))
    (hf : curveQuadratic ρ u v ρ' u' v' ∈ I)
    (hg : curveEquation ρ u v ρ' u' v' A a ∈ I)
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F)
    (l : MvPolynomial (Fin 3) ℚ ⧸ I) (hl : ι l ≠ 0)
    (ψ : projectiveChart I ι l →ₐ[ℚ] K)
    (hw : ψ (chartInfinityCoordinate I ι l) = 0) :
    let z := fun j => ψ (chartNode I ι l j)
    let z₄ := fourthNode (algebraMap ℚ K ρ) (algebraMap ℚ K u) (algebraMap ℚ K v)
      (z 0) (z 1) (z 2)
    ψ (chartHomogeneousMap I ι l (curveHomogenize 10 (curveResultant ρ u v ρ' u' v'))) *
      branchLocationDelta (z 0) (z 1) (z 2) =
        (branchFifthLocationProduct (z 0) (z 1) (z 2) z₄) ^ 4 := by
  let φ := chartHomogeneousMap I ι l
  let z := fun j => ψ (chartNode I ι l j)
  let rρ := algebraMap ℚ K ρ
  let ru := algebraMap ℚ K u
  let rv := algebraMap ℚ K v
  let z₄ := fourthNode rρ ru rv (z 0) (z 1) (z 2)
  obtain ⟨h2, h3⟩ := chart_infinity_moment_equations ρ u v ρ' u' v' A a ha
    I hf hg ι l hl ψ hw
  have hb := branch_barycentric_resultant_identity rρ (-rρ - ru) (ru - rv) (rv - 1)
    (z 0) (z 1) (z 2) z₄ (by ring) (by dsimp [z₄, fourthNode]; ring) h2 h3
  rw [chartHomogeneousMap_closed_residue I ι l ψ hw]
  simp only [map_curveHomogenize, map_curveResultant, curveResultant_at_infinity,
    map_mul, MvPolynomial.eval_C, nodeVandermonde, completeNodes, fourthNode,
    MvPolynomial.eval_X, map_sub, map_add, Matrix.cons_val] at hb ⊢
  simpa only [map_one, z₄, fourthNode, z, rρ, ru, rv] using hb

/-- The actual normalized infinity residue contains the branch sign used by
the specialization polynomial, with first location normalized to one. -/
theorem orbit_infinity_residue_scaled_sign
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
    ∀ p ∈ orbitInfinityBranches I F,
      let ψ := (Ideal.Quotient.mkₐ ℚ p.asIdeal).comp
        (IsScalarTower.toAlgHom ℚ (orbitChart I F) (orbitChartClosure I F))
      let z := fun j =>
        ψ (chartNode I (orbitChartEmbedding I F) (Ideal.Quotient.mk I (MvPolynomial.X 0)) j)
      z 0 = 1 ∧ ∃ β : orbitChartClosure I F ⧸ p.asIdeal,
        β ^ 2 = algebraMap ℚ _ ((a : ℚ) / (Lz a b i : ℚ)) *
          branchLocationDelta (z 0) (z 1) (z 2) := by
  classical
  let ι := orbitChartEmbedding I F
  let S := orbitChart I F
  let C := orbitChartClosure I F
  let w := orbitChartParameter I F
  obtain ⟨_, _, _, -, ha, -, -, -, -, -, -, hw⟩ :=
    orbit_infinity_chart_setup hba hi hne I hf hg hd hdegree F
  intro p hp
  let : Field (C ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
  let ψ := (Ideal.Quotient.mkₐ ℚ p.asIdeal).comp (IsScalarTower.toAlgHom ℚ S C)
  let z := fun j => ψ (chartNode I ι (Ideal.Quotient.mk I (MvPolynomial.X 0)) j)
  let z₄ := fourthNode (algebraMap ℚ (C ⧸ p.asIdeal) (patternRhoQ a b i))
    (algebraMap ℚ (C ⧸ p.asIdeal) (patternUQ a b i))
    (algebraMap ℚ (C ⧸ p.asIdeal) (patternVQ a b i)) (z 0) (z 1) (z 2)
  let r : S := chartHomogeneousMap I ι (Ideal.Quotient.mk I (MvPolynomial.X 0))
    (curveHomogenize 10 (curveResultant (patternRhoQ a b i) (patternUQ a b i)
      (patternVQ a b i) (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1))
      (patternVQ a b (i + 1))))
  have hl : ι (Ideal.Quotient.mk I (MvPolynomial.X 0)) ≠ 0 := by
    intro he
    apply hw.ne_zero
    apply Subtype.ext
    change (ι (Ideal.Quotient.mk I (MvPolynomial.X 0)))⁻¹ = 0
    rw [he, _root_.inv_zero]
  have hψw : ψ w = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
  have hres := chart_infinity_barycentric_identity (patternRhoQ a b i) (patternUQ a b i)
    (patternVQ a b i) (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1))
    (patternVQ a b (i + 1)) (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι _ hl ψ hψw
  change ψ r * branchLocationDelta (z 0) (z 1) (z 2) =
    (branchFifthLocationProduct (z 0) (z 1) (z 2) z₄) ^ 4 at hres
  obtain ⟨γ, hγ⟩ := orbit_infinity_residue_sign hba hi hne I hf hg hd hdegree F p hp
  change γ ^ 2 * ψ r = algebraMap ℚ (C ⧸ p.asIdeal)
    ((a : ℚ) / (Lz a b i : ℚ)) at hγ
  change z 0 = 1 ∧ ∃ β : C ⧸ p.asIdeal, β ^ 2 =
    algebraMap ℚ (C ⧸ p.asIdeal) ((a : ℚ) / (Lz a b i : ℚ)) *
      branchLocationDelta (z 0) (z 1) (z 2)
  refine ⟨?_, _, branch_scaled_sign_square γ (ψ r) _ _ _ hγ hres⟩
  change ψ (chartNode I ι (Ideal.Quotient.mk I (MvPolynomial.X 0)) 0) = 1
  rw [chartNode_first_eq_one I ι hl, map_one]

end
end PierceLengthBound.FixedDividend
