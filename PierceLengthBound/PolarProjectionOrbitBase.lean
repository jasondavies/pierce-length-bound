/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import PierceLengthBound.PolarProjectionCoordinateIdeal
public import PierceLengthBound.PolarProjectionRankFiveDegree
public import PierceLengthBound.PolarProjectionExceptionalPolynomial
public import PierceLengthBound.PolarProjectionPointSection

/-! Specialization of the base-point and local-normalization comparisons
to the actual orbit component and its scalar-cleared polar coordinates. -/
@[expose] public section
namespace PierceLengthBound.FixedDividend
open MvPolynomial
open scoped IntermediateField
noncomputable section

def orbitPolarParameters (a b i : ℕ) : Fin 6 → ℚ :=
  ![patternRhoQ a b i, patternUQ a b i, patternVQ a b i,
    patternRhoQ a b (i + 1), patternUQ a b (i + 1), patternVQ a b (i + 1)]

theorem orbitPolarParameters_eq_minor (a b i : ℕ) :
    orbitPolarParameters a b i = polarMinorParameters (fun j => (plk (Mi a b i) j : ℚ)) := by
  have ht := fun j => congrFun (theta_eq (a := a) (b := b) i) j
  have h0 := ht 0
  have h1 := ht 1
  have h2 := ht 2
  have h3 := ht 3
  have h4 := ht 4
  have h5 := ht 5
  have h6 := ht 6
  simp only [theta, projθ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons] at h0 h1 h2 h3 h4 h5 h6
  change U2z a b i = -plk (Mi a b i) 1 at h4
  change U1z a b (i + 1) = plk (Mi a b i) 8 at h5
  change U2z a b (i + 1) = -plk (Mi a b i) 7 at h6
  ext j
  fin_cases j <;> simp [orbitPolarParameters, polarMinorParameters,
    patternRhoQ, patternUQ, patternVQ, h0, h1, h2, h3, h4, h5, h6, Nat.add_assoc]

/-- The retained scalar-zero branches are regular on the actual affine
coordinate ring; the already proved normalization coverage supplies this. -/
theorem retained_rank_five_zero_affine_regular
    {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    {d N : ℕ} {c₀ : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c₀)
    (F : Type*) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsScalarTower ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    (ν : AddValuation F (WithTop ℤ)) (hQ : ∀ c : ℚ, 0 ≤ ν (algebraMap ℚ F c))
    (hJ : 0 < ν (algebraMap (MvPolynomial (Fin 3) ℚ ⧸ I) F
      (Ideal.Quotient.mk I (jointRankFivePolynomial a b i)))) :
    ∀ r : MvPolynomial (Fin 3) ℚ ⧸ I,
      0 ≤ ν (algebraMap (MvPolynomial (Fin 3) ℚ ⧸ I) F r) := by
  let A := MvPolynomial (Fin 3) ℚ ⧸ I
  let C := integralClosure A F
  have h := retained_rank_five_zero_normalization_regular hba hi hne I hf hg
    hd hdegree F ν hQ hJ
  intro r
  have hr := h (algebraMap A C r)
  change 0 ≤ ν (algebraMap C F (algebraMap A C r)) at hr
  rwa [← IsScalarTower.algebraMap_apply A C F] at hr

/-- The actual retained polar cuts give the coordinate family used by the
local intersection comparison, over the component's fraction field. -/
theorem retained_polar_coordinate_field_identity {a b i : ℕ}
    (hba : b < a) (hi : i + 7 < P a b)
    (I : Ideal (MvPolynomial (Fin 3) ℚ))
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hcut : ∀ j, orbitPolarIdentityPolynomial a b i j ∈ I)
    {F : Type*} [Field F] [Algebra ℚ F]
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι) :
    let ψ := ι.comp (Ideal.Quotient.mkₐ ℚ I)
    ∀ j : Fin 3, ι (Ideal.Quotient.mk I (C ((Lz a b i : ℚ) ^ 2) *
      orbitPolarPolynomial a b i j)) = ψ (jointRankFivePolynomial a b i) *
        (ψ (orbitJointNumerators a b i j.castSucc) / ψ (orbitJointDenominator a b i)) := by
  let ψ := ι.comp (Ideal.Quotient.mkₐ ℚ I)
  have hD : ψ (orbitJointDenominator a b i) ≠ 0 := by
    intro hz'
    apply orbitJoint_denominator_not_mem hba hi I hz
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact hι (hz'.trans (map_zero ι).symm)
  change ∀ j : Fin 3, ι (Ideal.Quotient.mk I
    (C ((Lz a b i : ℚ) ^ 2) * orbitPolarPolynomial a b i j)) =
      ψ (jointRankFivePolynomial a b i) *
        (ψ (orbitJointNumerators a b i j.castSucc) / ψ (orbitJointDenominator a b i))
  intro j
  have hc : ψ (orbitPolarIdentityPolynomial a b i j) = 0 := by
    change ι (Ideal.Quotient.mk I _) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hcut j), map_zero]
  have he := orbitPolarIdentityPolynomial_field_identity ψ.toRingHom j hD hc
  change ψ (jointRankFivePolynomial a b i) *
    (ψ (orbitJointNumerators a b i j.castSucc) / ψ (orbitJointDenominator a b i)) =
      ψ (C ((Lz a b i : ℚ) ^ 2)) * ψ (orbitPolarPolynomial a b i j) at he
  rw [← map_mul] at he
  exact he.symm

/-- A retained component missing the unique polar base point contributes
zero to the common-base divisor. This case needs no containment theorem. -/
theorem retained_polar_base_degree_zero_of_missing_point
    {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hcut : ∀ j, orbitPolarIdentityPolynomial a b i j ∈ I)
    (hG : (polarMatrix (patternRhoQ a b i) (patternUQ a b i) (patternVQ a b i)).det ≠ 0)
    (hmiss : polarCumulativeBasePoint (patternRhoQ a b i) (patternUQ a b i)
      (patternVQ a b i) (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1))
      (patternVQ a b (i + 1)) ∉ coordinateZeroLocus I)
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
    functionCommonBaseDegree J hJ W = 0 := by
  let A := MvPolynomial (Fin 3) ℚ ⧸ I
  let ι := IsScalarTower.toAlgHom ℚ A F
  let ψ := ι.comp (Ideal.Quotient.mkₐ ℚ I)
  let J := algebraMap A F (Ideal.Quotient.mk I (jointRankFivePolynomial a b i))
  let W := fun j : Fin 3 =>
    ψ (orbitJointNumerators a b i j.castSucc) / ψ (orbitJointDenominator a b i)
  let V := fun j : Fin 3 => Ideal.Quotient.mk I
    (C ((Lz a b i : ℚ) ^ 2) * orbitPolarPolynomial a b i j)
  have hJ := retained_rank_five_degree_lower_bound hba hi hne I hf hg hd hdegree F
  let : Module.Finite ℚ⟮J⟯ F := hJ.2.1
  change functionCommonBaseDegree J hJ.1 W = 0
  have hA : (Lz a b i : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Lz_pos hba (by omega : i + 5 < P a b)))
  have htop : Ideal.span (Set.range V) = ⊤ :=
    (orbit_polar_coordinate_ideal a b i hA hG I).trans
      (centered_ideal_eq_top_of_not_mem_zeroLocus I _ hmiss)
  apply functionCommonBaseDegree_eq_zero_of_unit_ideal J hJ.1 W V
    (retained_polar_coordinate_field_identity hba hi I hz hcut ι (IsFractionRing.injective A F))
    htop
  exact retained_rank_five_zero_affine_regular hba hi hne I hf hg hd hdegree F

end
end PierceLengthBound.FixedDividend
