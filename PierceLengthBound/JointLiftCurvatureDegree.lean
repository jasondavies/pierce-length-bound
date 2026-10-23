/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftFiniteZero
public import PierceLengthBound.JointLiftNormalizedOrders
public import PierceLengthBound.NormalizationInfinityDegree
public import PierceLengthBound.BranchZeroDegree

/-! # The curvature pole degree

Lemma 8.11 of the paper. On a retained nonexceptional component of degree `d ≥ 3`, each branch
above infinity has multiplicity `2t` and every rational curvature combination vanishes there to
order at least `3t`; together with the additional affine zero of Lemma 8.10 this gives a
curvature combination of function-field degree at least `3d/2 + 1`, and hence the same lower
bound for the degree of the curvature pole envelope. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial
open scoped IntermediateField

/-- At a height-one prime `p` of the normalized infinity chart of a retained nonexceptional
component that contains the infinity coordinate `w`, the multiplicity of `w` is `2t` with
`t > 0`, and every rational combination of the curvature coordinates has order at least `3t`. -/
theorem retained_curvature_normalized_zero_order
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
    {F : Type*} [Field F] [Algebra ℚ F]
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι)
    (hfrac : ∀ z : F, ∃ x y : MvPolynomial (Fin 3) ℚ ⧸ I, z = ι x / ι y)
    [IsFractionRing (projectiveChart I ι (Ideal.Quotient.mk I (X 0))) F]
    [IsDedekindDomain (integralClosure
      (projectiveChart I ι (Ideal.Quotient.mk I (X 0))) F)]
    (c : Fin 3 → ℚ)
    (p : IsDedekindDomain.HeightOneSpectrum
      (integralClosure (projectiveChart I ι (Ideal.Quotient.mk I (X 0))) F))
    (hp : algebraMap (projectiveChart I ι (Ideal.Quotient.mk I (X 0)))
      (integralClosure (projectiveChart I ι (Ideal.Quotient.mk I (X 0))) F)
      (chartInfinityCoordinate I ι (Ideal.Quotient.mk I (X 0))) ∈ p.asIdeal) :
    let S := projectiveChart I ι (Ideal.Quotient.mk I (X 0))
    let C := integralClosure S F
    let w := algebraMap S C (chartInfinityCoordinate I ι (Ideal.Quotient.mk I (X 0)))
    let : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension S F F C
    ∃ t : ℕ, 0 < t ∧ multiplicity p.asIdeal (Ideal.span {w}) = 2 * t ∧
      (((3 * t : ℕ) : ℤ) : WithTop ℤ) ≤ normalizedBranchOrder p F
        (jointCurvatureCombination (ι.comp (Ideal.Quotient.mkₐ ℚ I)) a b i c) := by
  let S := projectiveChart I ι (Ideal.Quotient.mk I (X 0))
  let C := integralClosure S F
  let w := algebraMap S C (chartInfinityCoordinate I ι (Ideal.Quotient.mk I (X 0)))
  let : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension S F F C
  obtain ⟨ν, hcenter, hregular, hπ, t, ht, hw, hW0, hW1, hW2, _⟩ :=
    retained_normalized_branch_joint_orders hba hi hne I hf hg hz hnorm hres
      ι hι hfrac hd hdegree p hp
  have hν : normalizedBranchOrder p F = ν := centered_branch_order_eq p ν
    (branch_order_nonnegative_on_normalization ν hregular) (fun r => (hcenter r).symm) hπ
  have hw' : ν (algebraMap C F w) = ((2 * t : ℤ) : WithTop ℤ) := hw
  have hw0 : w ≠ 0 := by
    intro he
    rw [he, map_zero, ν.map_zero] at hw'
    exact WithTop.coe_ne_top hw'.symm
  have hm := normalizedBranchOrder_eq_multiplicity p F hw0
  rw [hν, hw'] at hm
  have hmult : multiplicity p.asIdeal (Ideal.span {w}) = 2 * t.toNat := by
    have he : 2 * t = (multiplicity p.asIdeal (Ideal.span {w}) : ℤ) := by
      exact_mod_cast hm
    omega
  refine ⟨t.toNat, by omega, hmult, ?_⟩
  rw [hν]
  have hcast : (((3 * t.toNat : ℕ) : ℤ) : WithTop ℤ) = ((3 * t : ℤ) : WithTop ℤ) := by
    congr 1
    omega
  rw [hcast]
  apply ν.map_le_sum
  intro j _
  rw [ν.map_mul]
  have hc : 0 ≤ ν (algebraMap ℚ F (c j)) := by
    rw [IsScalarTower.algebraMap_apply ℚ S F]
    exact hregular _
  have hj : ((3 * t : ℤ) : WithTop ℤ) ≤ ν
      ((ι.comp (Ideal.Quotient.mkₐ ℚ I)) (orbitJointNumerators a b i j.castSucc) /
        (ι.comp (Ideal.Quotient.mkₐ ℚ I)) (orbitJointDenominator a b i)) := by
    fin_cases j
    · exact le_of_eq hW0.symm
    · exact hW1
    · exact le_of_eq hW2.symm
  simpa only [zero_add] using add_le_add hc hj

set_option synthInstance.maxHeartbeats 200000 in
-- The parameter algebra, chart, normalization and residue fields form nested scalar towers.
/-- On a retained nonexceptional component of degree `d ≥ 3` lying on an irreducible quadric,
some rational curvature combination `x` is transcendental with `3d + 2 ≤ 2 [F : ℚ(x)]`. -/
theorem retained_curvature_function_degree_lower_bound {a b i d N : ℕ} {c₀ : ℤ}
    (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hnorm : jointNormalizationPolynomial a b i ∈ I)
    (hres : jointResolventPolynomial a b i ∈ I)
    (Q : MvPolynomial (Fin 3) ℚ) (hQ : Prime Q) (hQdeg : Q.totalDegree = 2) (hQI : Q ∈ I)
    (hd3 : 3 ≤ d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c₀)
    (F : Type*) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsScalarTower ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin 3) ℚ ⧸ I) F] :
    let ι := IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F
    ∃ c : Fin 3 → ℚ,
      let x := jointCurvatureCombination (ι.comp (Ideal.Quotient.mkₐ ℚ I)) a b i c
      Transcendental ℚ x ∧ 3 * d + 2 ≤ 2 * Module.finrank ℚ⟮x⟯ F := by
  classical
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
  let : Module.Finite S C := hn.2.2
  obtain ⟨hρ, hu, hv, hne', ha, -⟩ := orbit_rational_nonexceptional_data hba hi hne
  let : Module.Finite (Algebra.adjoin ℚ {w}) S :=
    nonexceptional_chart_finite_over_parameter hρ hu hv hne'
      (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
      (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι (IsFractionRing.injective R F)
      (by omega : 0 < d) hdegree
  have hw : Transcendental ℚ w := nonexceptional_chart_parameter_transcendental hρ hu hv hne'
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι (IsFractionRing.injective R F)
    (by omega : 0 < d) hdegree
  let T := Algebra.adjoin ℚ {w}
  let : Algebra.FiniteType ℚ S := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType ℚ T) (inferInstance : Algebra.FiniteType T S)
  let : Algebra.FiniteType ℚ C := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType ℚ S) (inferInstance : Algebra.FiniteType S C)
  obtain ⟨c, p, hx, hpos, hout⟩ := orbitJoint_exists_extra_normalized_zero
    hba hi hne I hf hg hz Q hQ hQdeg hQI hd3 hdegree F
  let x := jointCurvatureCombination (ι.comp (Ideal.Quotient.mkₐ ℚ I)) a b i c
  let : FiniteDimensional ℚ⟮x⟯ F := finite_fraction_field_over_function w hw x hx
  obtain ⟨B, hB, hsum⟩ := normalized_parameter_branches (L := F) w hw
  have hdim : Module.finrank ℚ (S ⧸ Ideal.span {w}) = d :=
    (nonexceptional_chart_infinity_dimension hρ hu hv hne'
      (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
      (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι (IsFractionRing.injective R F)
      (by omega : 0 < d) hdegree).2
  have hfrac (z : F) : ∃ r s : R, z = ι r / ι s := by
    obtain ⟨r, s, _, hrs⟩ := IsFractionRing.div_surjective R z
    exact ⟨r, s, hrs.symm⟩
  have ht : ∀ q : IsDedekindDomain.HeightOneSpectrum C, ∃ t : ℕ, q ∈ B →
      0 < t ∧ multiplicity q.asIdeal (Ideal.span {algebraMap S C w}) = 2 * t ∧
        (((3 * t : ℕ) : ℤ) : WithTop ℤ) ≤ normalizedBranchOrder q F x := by
    intro q
    by_cases hq : q ∈ B
    · obtain ⟨t, ht⟩ := retained_curvature_normalized_zero_order hba hi hne I hf hg hz
        hnorm hres (by omega : 0 < d) hdegree ι (IsFractionRing.injective R F) hfrac c q
        ((hB q).mp hq)
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h => False.elim (hq h)⟩
  choose t ht using ht
  refine ⟨c, hx, branch_zero_degree_three_halves x hx B t
    (fun q hq => (ht q hq).1) ?_ (fun q hq => (ht q hq).2.2) p ?_ hpos⟩
  · calc
      ∑ q ∈ B, (2 * t q) * Module.finrank ℚ (C ⧸ q.asIdeal) =
          ∑ q ∈ B, multiplicity q.asIdeal (Ideal.span {algebraMap S C w}) *
            Module.finrank ℚ (C ⧸ q.asIdeal) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [(ht q hq).2.1]
      _ = d := hsum.trans hdim
  · exact fun hp => hout ((hB p).mp hp)

/-- Lemma 8.11: on a retained nonexceptional component of degree `d ≥ 3` lying on an
irreducible quadric, the pole envelope of the three curvature coordinates on the affine
normalization has degree at least `3d/2 + 1`. -/
theorem retained_curvature_pole_degree_lower_bound {a b i d N : ℕ} {c₀ : ℤ}
    (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hnorm : jointNormalizationPolynomial a b i ∈ I)
    (hres : jointResolventPolynomial a b i ∈ I)
    (Q : MvPolynomial (Fin 3) ℚ) (hQ : Prime Q) (hQdeg : Q.totalDegree = 2) (hQI : Q ∈ I)
    (hd3 : 3 ≤ d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c₀)
    (F : Type*) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsScalarTower ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin 3) ℚ ⧸ I) F] :
    let R := MvPolynomial (Fin 3) ℚ ⧸ I
    let C := integralClosure R F
    let : IsDedekindDomain C :=
      (orbit_affine_normalization hba hi hne I hf hg (by omega : 0 < d) hdegree F).1
    let : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension R F F C
    let ψ := (IsScalarTower.toAlgHom ℚ R F).comp (Ideal.Quotient.mkₐ ℚ I)
    3 * d + 2 ≤ 2 * poleEnvelopeDegree C
      (fun j : Fin 3 =>
        ψ (orbitJointNumerators a b i j.castSucc) / ψ (orbitJointDenominator a b i)) := by
  obtain ⟨c, hx, hlower⟩ := retained_curvature_function_degree_lower_bound
    hba hi hne I hf hg hz hnorm hres Q hQ hQdeg hQI hd3 hdegree F
  have hupper := retained_curvature_function_degree_le_envelope hba hi hne I hf hg hz
    hnorm hres (by omega : 0 < d) hdegree F c _ hx rfl
  exact hlower.trans (Nat.mul_le_mul_left 2 hupper)

end
end PierceLengthBound.FixedDividend
