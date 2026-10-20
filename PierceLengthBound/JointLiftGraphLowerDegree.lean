/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.GraphPoleDegree
public import PierceLengthBound.JointLiftCurvatureDegree
public import PierceLengthBound.JointLiftGraphDegree

/-! The old infinity poles of the rank-five coordinate and the finite curvature
poles are distinct normalized branches. Together they force graph degree 4d+1. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial
attribute [local instance] FractionRing.liftAlgebra

set_option synthInstance.maxHeartbeats 200000 in
-- The two normalized chart models and their residue fields have nested scalar towers.
set_option maxHeartbeats 1200000 in
theorem retained_jointGraph_degree_lower_bound {a b i d δ N : ℕ} {c₀ : ℤ}
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
    (hgraph : ∃ M : ℕ, ∃ c : ℤ, ∀ n ≥ M,
      (Module.finrank ℚ (filteredCoordinateSpace (orbitJointGraphIdeal a b i I) n) : ℤ) =
        (δ : ℤ) * n + c)
    (F : Type*) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsScalarTower ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin 3) ℚ ⧸ I) F] : 4 * d + 1 ≤ δ := by
  classical
  let R := MvPolynomial (Fin 3) ℚ ⧸ I
  let ι := IsScalarTower.toAlgHom ℚ R F
  let ψ := ι.comp (Ideal.Quotient.mkₐ ℚ I)
  let S := projectiveChart I ι (Ideal.Quotient.mk I (X 0))
  let C := integralClosure S F
  let A := integralClosure R F
  let w := chartInfinityCoordinate I ι (Ideal.Quotient.mk I (X 0))
  let hn := orbit_chart_normalization_in_field hba hi hne I hf hg
    (by omega : 0 < d) hdegree F
  let : IsFractionRing S F := hn.1
  let : IsDedekindDomain C := hn.2.1
  let : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension S F F C
  let : IsDedekindDomain A :=
    (orbit_affine_normalization hba hi hne I hf hg (by omega : 0 < d) hdegree F).1
  let : IsFractionRing A F := IsIntegralClosure.isFractionRing_of_finite_extension R F F A
  have hι : Function.Injective ι := IsFractionRing.injective R F
  have hfrac (z : F) : ∃ r s : R, z = ι r / ι s := by
    obtain ⟨r, s, _, hrs⟩ := IsFractionRing.div_surjective R z
    exact ⟨r, s, hrs.symm⟩
  have hD : ι (Ideal.Quotient.mk I (orbitJointDenominator a b i)) ≠ 0 := by
    apply (map_ne_zero_iff _ hι).mpr
    intro hzero
    exact orbitJoint_denominator_not_mem hba hi I hz (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  have ha : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  obtain ⟨hρ, hu, hv⟩ := orbit_rational_pattern_signs hba (by omega : i + 6 < P a b)
  have hne' : NonexceptionalPattern (patternRhoQ a b i : ℝ)
      (patternUQ a b i : ℝ) (patternVQ a b i : ℝ) := by simpa using hne
  let : Module.Finite (Algebra.adjoin ℚ {w}) S :=
    nonexceptional_chart_finite_over_parameter hρ hu hv hne'
      (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
      (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι hι (by omega : 0 < d) hdegree
  have hw : Transcendental ℚ w := nonexceptional_chart_parameter_transcendental hρ hu hv hne'
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι hι (by omega : 0 < d) hdegree
  obtain ⟨B, hB, hsum⟩ := normalized_parameter_branches (L := F) w hw
  have hdim : Module.finrank ℚ (S ⧸ Ideal.span {w}) = d :=
    (rational_nonexceptional_chart_infinity_dimension hρ hu hv hne'
      (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
      (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι hι (by omega : 0 < d) hdegree).2
  let V := fun j : Fin 3 => ψ (orbitJointNumerators a b i j.castSucc) /
    ψ (orbitJointDenominator a b i)
  let W := jointGraphFieldCoordinates I (orbitJointNumerators a b i) (orbitJointDenominator a b i) ι
  have ht : ∀ p : IsDedekindDomain.HeightOneSpectrum C, ∃ t : ℕ, p ∈ B →
      0 < t ∧ multiplicity p.asIdeal (Ideal.span {algebraMap S C w}) = 2 * t ∧
        normalizedBranchOrder p F (ι (Ideal.Quotient.mk I (X 0))) < 0 ∧
        discretePoleOrder (normalizedBranchOrder p F) (W (Sum.inr 3)) = 5 * t := by
    intro p
    by_cases hp : p ∈ B
    · obtain ⟨ν, hcenter, hregular, hπ, t, ht, hwν, _, _, _, hJ⟩ :=
        retained_normalized_branch_joint_orders hba hi hne I hf hg hz hnorm hres
          ι hι hfrac (by omega : 0 < d) hdegree p ((hB p).mp hp)
      have hν : normalizedBranchOrder p F = ν := centered_branch_order_eq p ν
        (branch_order_nonnegative_on_normalization ν hregular) (fun r => (hcenter r).symm) hπ
      have hw' : ν (algebraMap C F (algebraMap S C w)) = ((2 * t : ℤ) : WithTop ℤ) := hwν
      have hw0 : algebraMap S C w ≠ 0 := by
        intro he
        rw [he, map_zero, ν.map_zero] at hw'
        exact WithTop.coe_ne_top hw'.symm
      have hmult := normalizedBranchOrder_eq_multiplicity p F hw0
      rw [hν, hw'] at hmult
      have hm : multiplicity p.asIdeal (Ideal.span {algebraMap S C w}) = 2 * t.toNat := by
        have he : 2 * t = (multiplicity p.asIdeal (Ideal.span {algebraMap S C w}) : ℤ) := by
          exact_mod_cast hmult
        omega
      refine ⟨t.toNat, fun _ => ⟨by omega, hm, ?_, ?_⟩⟩
      · rw [hν]
        have hl := congrArg (fun z : WithTop ℤ => -z) hwν
        rw [ν.map_inv, neg_neg] at hl
        rw [hl, ← WithTop.LinearOrderedAddCommGroup.coe_neg]
        exact_mod_cast (show -(2 * t) < 0 by omega)
      · rw [hν]
        have hJ' : ν (W (Sum.inr 3)) = ((-5 * t : ℤ) : WithTop ℤ) := hJ
        rw [discretePoleOrder_eq ν hJ']
        omega
    · exact ⟨0, fun h => False.elim (hp h)⟩
  choose t ht using ht
  have htwice : (∑ p ∈ B, (2 * t p) * Module.finrank ℚ (C ⧸ p.asIdeal)) = d := by
    calc
      _ = ∑ p ∈ B, multiplicity p.asIdeal (Ideal.span {algebraMap S C w}) *
          Module.finrank ℚ (C ⧸ p.asIdeal) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [(ht p hp).2.1]
      _ = d := hsum.trans hdim
  let E := poleEnvelopeBranches A V
  let n := fun q : IsDedekindDomain.HeightOneSpectrum A =>
    branchPoleEnvelope (normalizedBranchOrder q F) V
  have hnpos (q) (hq : q ∈ E) : 0 < n q := (mem_poleEnvelopeBranches V q).mp hq
  have hdisjoint (p) (hp : p ∈ B) (q) (_ : q ∈ E) :
      normalizedBranchOrder p F ≠ normalizedBranchOrder q F := by
    intro he
    have hneg := (ht p hp).2.2.1
    rw [he] at hneg
    have hnonneg := normalizedBranchOrder_nonnegative q F
      (algebraMap R A (Ideal.Quotient.mk I (X 0)))
    rw [← IsScalarTower.algebraMap_apply R A F] at hnonneg
    exact (not_lt_of_ge hnonneg) hneg
  have hfinitePole (q) (hq : q ∈ E) : ∃ j, n q ≤
      discretePoleOrder (normalizedBranchOrder q F) (W j) := by
    obtain ⟨j, hj⟩ := branchPoleEnvelope_attained (normalizedBranchOrder q F) V (hnpos q hq)
    refine ⟨Sum.inr j.castSucc, le_of_eq ?_⟩
    exact ((discretePoleOrder_eq_iff_of_pos (normalizedBranchOrder q F) (V j)
      (hnpos q hq)).mpr hj).symm
  have hbound := jointGraph_two_model_poles_degree_le I (orbitJointNumerators a b i)
    (orbitJointDenominator a b i) ι hι hD hfrac hgraph B E (fun p => 5 * t p) n
    (fun p hp => Nat.mul_pos (by decide) (ht p hp).1) hnpos hdisjoint
    (fun p hp => ⟨Sum.inr 3, le_of_eq (ht p hp).2.2.2.symm⟩) hfinitePole
  have hcurv := retained_curvature_pole_degree_lower_bound hba hi hne I hf hg hz hnorm hres
    Q hQ hQdeg hQI hd3 hdegree F
  change 3 * d + 2 ≤ 2 * ∑ q ∈ E, n q * Module.finrank ℚ (A ⧸ q.asIdeal) at hcurv
  simp_rw [mul_assoc] at htwice hbound
  rw [← Finset.mul_sum] at htwice hbound
  let e := ∑ p ∈ B, t p * Module.finrank ℚ (C ⧸ p.asIdeal)
  change 2 * e = d at htwice
  change 5 * e + (∑ q ∈ E, n q * Module.finrank ℚ (A ⧸ q.asIdeal)) ≤ δ at hbound
  omega

/-- The retained degree-at-least-four components have the actual graph-degree
range required by the proved seven-dimensional point-counting bound. -/
theorem orbitJointGraph_retained_degree_range {a b i d : ℕ}
    (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hnorm : jointNormalizationPolynomial a b i ∈ I)
    (hres : jointResolventPolynomial a b i ∈ I)
    (Q : MvPolynomial (Fin 3) ℚ) (hQ : Prime Q) (hQdeg : Q.totalDegree = 2) (hQI : Q ∈ I)
    (hd4 : 4 ≤ d)
    (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c) :
    ∃ δ : ℕ, 17 ≤ δ ∧ δ ≤ 247 * d ∧ ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace (orbitJointGraphIdeal a b i I) n) : ℤ) =
        (δ : ℤ) * n + c := by
  obtain ⟨δ, _, hupper, hgraph⟩ := orbitJointGraph_degree_bounds hba hi I hz hdegree
  obtain ⟨N, c₀, hbase⟩ := hdegree
  have hlower := retained_jointGraph_degree_lower_bound hba hi hne I hf hg hz hnorm hres
    Q hQ hQdeg hQI (by omega : 3 ≤ d) hbase hgraph
    (FractionRing (MvPolynomial (Fin 3) ℚ ⧸ I))
  exact ⟨δ, by omega, hupper, hgraph⟩

end
end PierceLengthBound.FixedDividend
