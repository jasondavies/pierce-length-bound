/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionBaseDegree
public import PierceLengthBound.JointLiftPoleDegree
public import PierceLengthBound.PolarProjectionRankFiveDegree

/-! The retained-component reduction of the curvature degree to the local
weighted common-base contribution. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open MvPolynomial
open scoped IntermediateField
noncomputable section

/-- The actual curvature coordinates cannot vanish together as rational
functions: their pairing with the polynomial moment row is the nonzero label. -/
theorem orbit_curvature_field_nonzero {F : Type*} [Field F] [Algebra ℚ F]
    {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (I : Ideal (MvPolynomial (Fin 3) ℚ))
    (hx : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι) :
    let ψ := ι.comp (Ideal.Quotient.mkₐ ℚ I)
    ∃ j : Fin 3, ψ (orbitJointNumerators a b i j.castSucc) /
      ψ (orbitJointDenominator a b i) ≠ 0 := by
  let ψ := ι.comp (Ideal.Quotient.mkₐ ℚ I)
  have hD : ψ (orbitJointDenominator a b i) ≠ 0 := by
    intro hz
    change ι (Ideal.Quotient.mk I (orbitJointDenominator a b i)) = 0 at hz
    exact orbitJoint_denominator_not_mem hba hi I hx
      (Ideal.Quotient.eq_zero_iff_mem.mp (hι (by simpa only [map_zero] using hz)))
  have hA : (Lz a b i : ℚ) ≠ 0 := by
    exact_mod_cast (show Lz a b i ≠ 0 by
      have := Lz_pos hba (by omega : i + 5 < P a b)
      omega)
  have hA' : ψ (C (Lz a b i : ℚ)) ≠ 0 := by
    rw [show ψ (C (Lz a b i : ℚ)) = algebraMap ℚ F (Lz a b i : ℚ) from ψ.commutes _]
    simpa only [map_zero] using (algebraMap ℚ F).injective.ne hA
  have he := jointLift_field_dot_row ψ.toRingHom (orbitLiftNumeratorQ a b i)
    (orbitLiftDenominatorQ a b i) (C (Lz a b i : ℚ))
    (jointRankFivePolynomial a b i) (jointGapPolynomials a b i) hD
  change (∑ j : Fin 3, (ψ (orbitJointNumerators a b i j.castSucc) /
    ψ (orbitJointDenominator a b i)) * ψ (curvatureRow (jointGapPolynomials a b i) j)) =
      ψ (C (Lz a b i : ℚ)) at he
  change ∃ j : Fin 3, ψ (orbitJointNumerators a b i j.castSucc) /
    ψ (orbitJointDenominator a b i) ≠ 0
  by_contra! h
  simp only [h, zero_mul, Finset.sum_const_zero] at he
  exact hA' he.symm

set_option synthInstance.maxHeartbeats 200000 in
-- The affine normalization and the rank-five parameter give several nested scalar towers.
set_option maxHeartbeats 800000 in
-- Constructing both normalized models needs more elaboration than the final degree arithmetic.
/-- On a degree-24 component the actual curvature pole envelope has degree
at least 56 once the weighted common-base contribution of `J W` is at most four.
Subtracting the old-infinity curvature zero degree 36 leaves at least 20.
The rank-five degree bound and coverage of every zero are proved from the
component hypotheses; the common-base contribution is the only new numerical premise. -/
theorem retained_curvature_degree_lower_bound_of_base_degree_le_four
    {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    {N : ℕ} {c₀ : ℤ}
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = 24 * n + c₀)
    (F : Type*) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsScalarTower ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin 3) ℚ ⧸ I) F] :
    let R := MvPolynomial (Fin 3) ℚ ⧸ I
    let C := integralClosure R F
    let : IsDedekindDomain C :=
      (orbit_affine_normalization hba hi hne I hf hg (by norm_num : 0 < 24) hdegree F).1
    let : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension R F F C
    let ψ := (IsScalarTower.toAlgHom ℚ R F).comp (Ideal.Quotient.mkₐ ℚ I)
    let W := fun j : Fin 3 =>
      ψ (orbitJointNumerators a b i j.castSucc) / ψ (orbitJointDenominator a b i)
    let J := algebraMap R F (Ideal.Quotient.mk I (jointRankFivePolynomial a b i))
    let hJ := (retained_rank_five_degree_twenty_four hba hi hne I hf hg hdegree F).1
    let : Module.Finite ℚ⟮J⟯ F :=
      (retained_rank_five_degree_twenty_four hba hi hne I hf hg hdegree F).2.1
    functionCommonBaseDegree J hJ W ≤ 4 →
      56 ≤ poleEnvelopeDegree C W ∧ 20 ≤ poleEnvelopeDegree C W - 36 := by
  let R := MvPolynomial (Fin 3) ℚ ⧸ I
  let C := integralClosure R F
  let : IsDedekindDomain C :=
    (orbit_affine_normalization hba hi hne I hf hg (by norm_num : 0 < 24) hdegree F).1
  let : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension R F F C
  let ι := IsScalarTower.toAlgHom ℚ R F
  let ψ := ι.comp (Ideal.Quotient.mkₐ ℚ I)
  let W := fun j : Fin 3 =>
    ψ (orbitJointNumerators a b i j.castSucc) / ψ (orbitJointDenominator a b i)
  let J := algebraMap R F (Ideal.Quotient.mk I (jointRankFivePolynomial a b i))
  have hJdata := retained_rank_five_degree_twenty_four hba hi hne I hf hg hdegree F
  let : Module.Finite ℚ⟮J⟯ F := hJdata.2.1
  change functionCommonBaseDegree J hJdata.1 W ≤ 4 →
    56 ≤ poleEnvelopeDegree C W ∧ 20 ≤ poleEnvelopeDegree C W - 36
  intro hbase
  have hW : ∃ j, W j ≠ 0 :=
    orbit_curvature_field_nonzero hba hi I hz ι (IsFractionRing.injective R F)
  have hcover (ν : AddValuation F (WithTop ℤ))
      (hQ : ∀ c : ℚ, 0 ≤ ν (algebraMap ℚ F c)) (_hπ : ∃ π : F, ν π = 1)
      (hpos : 0 < ν J) : ∀ r : C, 0 ≤ ν (algebraMap C F r) :=
    retained_rank_five_zero_normalization_regular hba hi hne I hf hg
      (by norm_num : 0 < 24) hdegree F ν hQ hpos
  have hh := function_degree_le_poleEnvelope_add_baseDegree (R := C) W hW J hJdata.1 hcover
  have h60 : 60 ≤ Module.finrank ℚ⟮J⟯ F := hJdata.2.2
  constructor <;> omega

set_option synthInstance.maxHeartbeats 200000 in
-- The scalar normalization and affine curvature model use different algebra towers over the field.
set_option maxHeartbeats 800000 in
-- Elaborating the two constructed normalized models dominates the final degree arithmetic.
/-- The actual powered graph, including an arbitrary invertible constant
change of curvature coordinates, has degree at least `56m + 60n` on a
retained degree-24 component with weighted common-base contribution at most four. -/
theorem retained_polar_linearJointGraph_degree_of_base_degree_le_four
    {a b i δ N m n : ℕ} {c₀ : ℤ}
    (G : Matrix (Fin 3) (Fin 3) ℚ) (hG : IsUnit G.det) (hm : 0 < m) (hn : 0 < n)
    (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hnorm : jointNormalizationPolynomial a b i ∈ I)
    (hres : jointResolventPolynomial a b i ∈ I)
    (hdegree : ∀ j ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I j) : ℤ) = 24 * j + c₀)
    (hgraph : ∃ M : ℕ, ∃ c : ℤ, ∀ j ≥ M,
      (Module.finrank ℚ
        (filteredCoordinateSpace (orbitLinearJointGraphIdeal G a b i m n I) j) : ℤ) =
          (δ : ℤ) * j + c)
    (F : Type*) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsScalarTower ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin 3) ℚ ⧸ I) F] :
    let R := MvPolynomial (Fin 3) ℚ ⧸ I
    let ψ := (IsScalarTower.toAlgHom ℚ R F).comp (Ideal.Quotient.mkₐ ℚ I)
    let W := fun j : Fin 3 =>
      ψ (orbitJointNumerators a b i j.castSucc) / ψ (orbitJointDenominator a b i)
    let J := algebraMap R F (Ideal.Quotient.mk I (jointRankFivePolynomial a b i))
    let hJ := (retained_rank_five_degree_twenty_four hba hi hne I hf hg hdegree F).1
    let : Module.Finite ℚ⟮J⟯ F :=
      (retained_rank_five_degree_twenty_four hba hi hne I hf hg hdegree F).2.1
    functionCommonBaseDegree J hJ W ≤ 4 → 56 * m + 60 * n ≤ δ := by
  let R := MvPolynomial (Fin 3) ℚ ⧸ I
  let C := integralClosure R F
  let : IsDedekindDomain C :=
    (orbit_affine_normalization hba hi hne I hf hg (by norm_num : 0 < 24) hdegree F).1
  let : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension R F F C
  let ψ := (IsScalarTower.toAlgHom ℚ R F).comp (Ideal.Quotient.mkₐ ℚ I)
  let W := fun j : Fin 3 =>
    ψ (orbitJointNumerators a b i j.castSucc) / ψ (orbitJointDenominator a b i)
  let J := algebraMap R F (Ideal.Quotient.mk I (jointRankFivePolynomial a b i))
  have hJdata := retained_rank_five_degree_twenty_four hba hi hne I hf hg hdegree F
  let : Module.Finite ℚ⟮J⟯ F := hJdata.2.1
  change functionCommonBaseDegree J hJdata.1 W ≤ 4 → 56 * m + 60 * n ≤ δ
  intro hbase
  have hpoles : 56 ≤ poleEnvelopeDegree C W :=
    (retained_curvature_degree_lower_bound_of_base_degree_le_four
      hba hi hne I hf hg hz hdegree F hbase).1
  have hbound := retained_linearJointGraph_degree_lower_bound_from_envelope G hG hm hn
    hba hi hne I hf hg hz hnorm hres (by norm_num : 0 < 24) hdegree hgraph F
  change 5 * n * 24 + 2 * m * poleEnvelopeDegree C W ≤ 2 * δ at hbound
  nlinarith [Nat.mul_le_mul_left (2 * m) hpoles]

/-- Compatibility wrapper for an exact common-base degree of four. -/
theorem retained_curvature_degree_lower_bound_of_base_degree_four
    {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    {N : ℕ} {c₀ : ℤ}
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = 24 * n + c₀)
    (F : Type*) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsScalarTower ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin 3) ℚ ⧸ I) F] :
    let R := MvPolynomial (Fin 3) ℚ ⧸ I
    let C := integralClosure R F
    let : IsDedekindDomain C :=
      (orbit_affine_normalization hba hi hne I hf hg (by norm_num : 0 < 24) hdegree F).1
    let : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension R F F C
    let ψ := (IsScalarTower.toAlgHom ℚ R F).comp (Ideal.Quotient.mkₐ ℚ I)
    let W := fun j : Fin 3 =>
      ψ (orbitJointNumerators a b i j.castSucc) / ψ (orbitJointDenominator a b i)
    let J := algebraMap R F (Ideal.Quotient.mk I (jointRankFivePolynomial a b i))
    let hJ := (retained_rank_five_degree_twenty_four hba hi hne I hf hg hdegree F).1
    let : Module.Finite ℚ⟮J⟯ F :=
      (retained_rank_five_degree_twenty_four hba hi hne I hf hg hdegree F).2.1
    functionCommonBaseDegree J hJ W = 4 →
      56 ≤ poleEnvelopeDegree C W ∧ 20 ≤ poleEnvelopeDegree C W - 36 := by
  dsimp only
  intro hbase
  exact retained_curvature_degree_lower_bound_of_base_degree_le_four
    hba hi hne I hf hg hz hdegree F (le_of_eq hbase)

/-- Compatibility wrapper for an exact common-base degree of four. -/
theorem retained_polar_linearJointGraph_degree_of_base_degree_four
    {a b i δ N m n : ℕ} {c₀ : ℤ}
    (G : Matrix (Fin 3) (Fin 3) ℚ) (hG : IsUnit G.det) (hm : 0 < m) (hn : 0 < n)
    (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hnorm : jointNormalizationPolynomial a b i ∈ I)
    (hres : jointResolventPolynomial a b i ∈ I)
    (hdegree : ∀ j ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I j) : ℤ) = 24 * j + c₀)
    (hgraph : ∃ M : ℕ, ∃ c : ℤ, ∀ j ≥ M,
      (Module.finrank ℚ
        (filteredCoordinateSpace (orbitLinearJointGraphIdeal G a b i m n I) j) : ℤ) =
          (δ : ℤ) * j + c)
    (F : Type*) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsScalarTower ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin 3) ℚ ⧸ I) F] :
    let R := MvPolynomial (Fin 3) ℚ ⧸ I
    let ψ := (IsScalarTower.toAlgHom ℚ R F).comp (Ideal.Quotient.mkₐ ℚ I)
    let W := fun j : Fin 3 =>
      ψ (orbitJointNumerators a b i j.castSucc) / ψ (orbitJointDenominator a b i)
    let J := algebraMap R F (Ideal.Quotient.mk I (jointRankFivePolynomial a b i))
    let hJ := (retained_rank_five_degree_twenty_four hba hi hne I hf hg hdegree F).1
    let : Module.Finite ℚ⟮J⟯ F :=
      (retained_rank_five_degree_twenty_four hba hi hne I hf hg hdegree F).2.1
    functionCommonBaseDegree J hJ W = 4 → 56 * m + 60 * n ≤ δ := by
  dsimp only
  intro hbase
  exact retained_polar_linearJointGraph_degree_of_base_degree_le_four
    G hG hm hn hba hi hne I hf hg hz hnorm hres hdegree hgraph F (le_of_eq hbase)

end
end PierceLengthBound.FixedDividend
