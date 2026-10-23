/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchFamilyDegree
public import PierceLengthBound.JointLiftFiniteZero
public import PierceLengthBound.NormalizationInfinityDegree

/-!
# Degree and zero coverage of the rank-five function

On a nonexceptional component of degree `d`, the rank-five function `J` has
order `-5t` at each infinity branch where `1/x₀` has order `2t`, so
`2 [F : ℚ(J)] ≥ 5d`. Every branch at which `J` vanishes is regular on the
normalization of the affine coordinate ring.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial
open scoped IntermediateField
attribute [local instance] FractionRing.liftAlgebra

/-- At any branch where the first coordinate `x₀` has a pole, the rank-five function has
negative order. -/
theorem retained_rank_five_negative_at_infinity
    {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    {F : Type*} [Field F] [Algebra ℚ F]
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι)
    {d N : ℕ} {c₀ : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c₀)
    (ν : AddValuation F (WithTop ℤ)) (hQ : ∀ c : ℚ, 0 ≤ ν (algebraMap ℚ F c))
    (hneg : ν (ι (Ideal.Quotient.mk I (X 0))) < 0) :
    ν (ι (Ideal.Quotient.mk I (jointRankFivePolynomial a b i))) < 0 := by
  let l := Ideal.Quotient.mk I (X 0)
  let S := projectiveChart I ι l
  let w := chartInfinityCoordinate I ι l
  change ν (ι l) < 0 at hneg
  have hl0 : ι l ≠ 0 := by intro h; simp [h] at hneg
  obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp (ν.ne_top_iff.mpr hl0)
  have heneg : e < 0 := by rw [← he] at hneg; exact_mod_cast hneg
  have hw : ν ((ι l)⁻¹) = ((-e : ℤ) : WithTop ℤ) := by rw [ν.map_inv, ← he]; rfl
  obtain ⟨hρ, hu, hv, hne', ha, hA⟩ := orbit_rational_nonexceptional_data hba hi hne
  let : Module.Finite (Algebra.adjoin ℚ {w}) S :=
    nonexceptional_chart_finite_over_parameter hρ hu hv hne' _ _ _ _ _ ha I hf hg ι hι hd hdegree
  have hregular (r : S) : 0 ≤ ν (r : F) := by
    apply branch_order_nonnegative_of_finite_parameter w ν hQ _ r
    change 0 ≤ ν ((ι l)⁻¹)
    rw [hw]
    exact_mod_cast (show (0 : ℤ) ≤ -e by omega)
  obtain ⟨t, ht, _, hJ⟩ := nonexceptional_rank_five_discrete_order hρ hu hv hne' _ _ _ _ _
    hA ha I hf hg ι hι hd hdegree ν hregular
    (show (0 : ℤ) < -e by omega) hw
  change ν (ι (Ideal.Quotient.mk I (jointRankFivePolynomial a b i))) = _ at hJ
  rw [hJ]
  exact_mod_cast (show -5 * t < 0 by omega)

/-- Every branch at which the rank-five function vanishes is regular on the
normalization of the affine coordinate ring, since a pole of `x₀` would force a
pole of `J`. -/
theorem retained_rank_five_zero_normalization_regular
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
    ∀ r : integralClosure (MvPolynomial (Fin 3) ℚ ⧸ I) F, 0 ≤ ν (r : F) := by
  let R := MvPolynomial (Fin 3) ℚ ⧸ I
  let ι := IsScalarTower.toAlgHom ℚ R F
  let l := Ideal.Quotient.mk I (X 0)
  have hl : 0 ≤ ν (ι l) := by
    by_contra h
    have hh := retained_rank_five_negative_at_infinity hba hi hne I hf hg
      ι (IsFractionRing.injective R F) hd hdegree ν hQ (lt_of_not_ge h)
    exact (not_lt_of_ge hJ.le) hh
  obtain ⟨hρ, hu, hv, hne', ha, -⟩ := orbit_rational_nonexceptional_data hba hi hne
  obtain ⟨M, hs⟩ := nonexceptional_eventual_first_node_generation
    hρ hu hv hne' _ _ _ _ _ ha I hf hg
  let : Module.Finite (Algebra.adjoin ℚ {l}) R := coordinateRing_finite_over_parameter I l hs
  exact branch_order_nonnegative_on_normalization ν
    (branch_order_nonnegative_of_finite_parameter l ν hQ hl)

set_option synthInstance.maxHeartbeats 200000 in
-- The normalized infinity chart and the function-parameter field have nested scalar towers.
set_option maxHeartbeats 400000 in
-- This proof uses about 190000 heartbeats, just under the default 200000; the limit is doubled
-- for margin.
/-- The rank-five function `J` is transcendental, the function field is finite
over `ℚ(J)`, and `J` has degree at least `5d/2`. The proof sums the pole orders
`5t` of `J` against the multiplicities `2t` of `1/x₀` at the infinity branches. -/
theorem retained_rank_five_degree_lower_bound
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
    let J := algebraMap (MvPolynomial (Fin 3) ℚ ⧸ I) F
      (Ideal.Quotient.mk I (jointRankFivePolynomial a b i))
    Transcendental ℚ J ∧ Module.Finite ℚ⟮J⟯ F ∧
      5 * d ≤ 2 * Module.finrank ℚ⟮J⟯ F := by
  classical
  let R := MvPolynomial (Fin 3) ℚ ⧸ I
  let ι := IsScalarTower.toAlgHom ℚ R F
  let S := projectiveChart I ι (Ideal.Quotient.mk I (X 0))
  let C := integralClosure S F
  let w := chartInfinityCoordinate I ι (Ideal.Quotient.mk I (X 0))
  let J := ι (Ideal.Quotient.mk I (jointRankFivePolynomial a b i))
  let hnormal := orbit_chart_normalization_in_field hba hi hne I hf hg hd hdegree F
  let : IsFractionRing S F := hnormal.1
  let : IsDedekindDomain C := hnormal.2.1
  let : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension S F F C
  have hι : Function.Injective ι := IsFractionRing.injective R F
  obtain ⟨hρ, hu, hv, hne', ha, hA⟩ := orbit_rational_nonexceptional_data hba hi hne
  let : Module.Finite (Algebra.adjoin ℚ {w}) S :=
    nonexceptional_chart_finite_over_parameter hρ hu hv hne' _ _ _ _ _ ha I hf hg ι hι hd hdegree
  have hw : Transcendental ℚ w := nonexceptional_chart_parameter_transcendental
    hρ hu hv hne' _ _ _ _ _ ha I hf hg ι hι hd hdegree
  obtain ⟨B, hB, hsum⟩ := normalized_parameter_branches (L := F) w hw
  have hdim : Module.finrank ℚ (S ⧸ Ideal.span {w}) = d :=
    (nonexceptional_chart_infinity_dimension hρ hu hv hne' _ _ _ _ _
      ha I hf hg ι hι hd hdegree).2
  have hwC0 : algebraMap S C w ≠ 0 := by
    intro hz
    have hh := congrArg (algebraMap C F) hz
    rw [← IsScalarTower.algebraMap_apply S C F, map_zero] at hh
    exact hw.ne_zero ((IsFractionRing.injective S F) (hh.trans (map_zero _).symm))
  have ht : ∀ p : IsDedekindDomain.HeightOneSpectrum C, ∃ t : ℕ, p ∈ B →
      0 < t ∧ multiplicity p.asIdeal (Ideal.span {algebraMap S C w}) = 2 * t ∧
      normalizedBranchOrder p F J = ((-(5 * t : ℕ) : ℤ) : WithTop ℤ) := by
    intro p
    by_cases hp : p ∈ B
    · let ν := normalizedBranchOrder p F
      have hregular (r : S) : 0 ≤ ν (r : F) := by
        have hh := normalizedBranchOrder_nonnegative p F (algebraMap S C r)
        rw [← IsScalarTower.algebraMap_apply S C F] at hh
        exact hh
      obtain ⟨e, he, hwν⟩ := normalizedBranchOrder_parameter p F hwC0 ((hB p).mp hp)
      have hwν' : ν ((ι (Ideal.Quotient.mk I (X 0)))⁻¹) = (e : WithTop ℤ) := by
        change ν (algebraMap C F (algebraMap S C w)) = _ at hwν
        rw [← IsScalarTower.algebraMap_apply S C F] at hwν
        exact hwν
      obtain ⟨t, ht, het, hJ⟩ := nonexceptional_rank_five_discrete_order
        hρ hu hv hne' _ _ _ _ _ hA ha I hf hg ι hι hd hdegree ν hregular he hwν'
      have hmult := normalizedBranchOrder_eq_multiplicity p F hwC0
      rw [hwν] at hmult
      have hmult' : multiplicity p.asIdeal (Ideal.span {algebraMap S C w}) = 2 * t.toNat := by
        have hm : e = (multiplicity p.asIdeal (Ideal.span {algebraMap S C w}) : ℤ) := by
          exact_mod_cast hmult
        omega
      refine ⟨t.toNat, fun _ => ⟨by omega, hmult', ?_⟩⟩
      change ν J = _ at hJ ⊢
      rw [hJ]
      congr 1
      push_cast
      rw [Int.toNat_of_nonneg ht.le]
      ring
    · exact ⟨0, fun h => False.elim (hp h)⟩
  choose t ht using ht
  have hBne : B.Nonempty := by
    by_contra h
    have hh := hsum.trans hdim
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hh
    omega
  have hJtrans : Transcendental ℚ J := by
    obtain ⟨p, hp⟩ := hBne
    apply transcendental_of_negative_order (normalizedBranchOrder p F) (fun c => ?_)
    · rw [(ht p hp).2.2]
      exact_mod_cast (show -(5 * t p : ℕ) < (0 : ℤ) by
        have := (ht p hp).1
        omega)
    · rw [IsScalarTower.algebraMap_apply ℚ C F]
      exact normalizedBranchOrder_nonnegative p F _
  let : Module.Finite ℚ⟮J⟯ F := finite_fraction_field_over_function w hw J hJtrans
  have hbound := branch_family_pole_degree_le (fun _ : B => C) (fun p => p.1)
    (fun p q he => Subtype.ext (normalizedBranchOrder_injective (L := F) he))
    J hJtrans (fun p => 5 * t p.1) (fun p => by have := (ht p.1 p.2).1; omega)
    (fun p => (ht p.1 p.2).2.2)
  have hbound' : ∑ p ∈ B, (5 * t p) * Module.finrank ℚ (C ⧸ p.asIdeal) ≤
      Module.finrank ℚ⟮J⟯ F := by
    rwa [B.sum_coe_sort (fun p => (5 * t p) * Module.finrank ℚ (C ⧸ p.asIdeal))] at hbound
  have htwice : ∑ p ∈ B, (2 * t p) * Module.finrank ℚ (C ⧸ p.asIdeal) = d := by
    calc _ = ∑ p ∈ B, multiplicity p.asIdeal (Ideal.span {algebraMap S C w}) *
        Module.finrank ℚ (C ⧸ p.asIdeal) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(ht p hp).2.1]
      _ = d := hsum.trans hdim
  simp_rw [mul_assoc, ← Finset.mul_sum] at htwice hbound'
  change Transcendental ℚ J ∧ Module.Finite ℚ⟮J⟯ F ∧
    5 * d ≤ 2 * Module.finrank ℚ⟮J⟯ F
  exact ⟨hJtrans, inferInstance, by omega⟩

/-- Specializing to a retained degree-24 component gives the lower bound sixty. -/
theorem retained_rank_five_degree_twenty_four
    {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    {N : ℕ} {c₀ : ℤ}
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = 24 * n + c₀)
    (F : Type*) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsScalarTower ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin 3) ℚ ⧸ I) F] :
    let J := algebraMap (MvPolynomial (Fin 3) ℚ ⧸ I) F
      (Ideal.Quotient.mk I (jointRankFivePolynomial a b i))
    Transcendental ℚ J ∧ Module.Finite ℚ⟮J⟯ F ∧ 60 ≤ Module.finrank ℚ⟮J⟯ F := by
  obtain ⟨hJ, hfinite, hdeg⟩ := retained_rank_five_degree_lower_bound
    hba hi hne I hf hg (by norm_num : 0 < 24) hdegree F
  exact ⟨hJ, hfinite, by omega⟩

end
end PierceLengthBound.FixedDividend
