/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionRankFiveDegree

/-! Residue-field branch labels force the full component degree. This avoids
introducing an absolute Galois action: an irreducible label of degree r in a
normalized infinity residue already costs at least 2r in the hyperplane fiber. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- A root of an irreducible polynomial forces the corresponding residue degree. -/
lemma irreducible_root_natDegree_le_finrank {K E : Type*} [Field K] [Ring E]
    [Algebra K E] [Nontrivial E] [Module.Finite K E]
    {p : Polynomial K} (hp : Irreducible p) (z : E)
    (hz : Polynomial.aeval z p = 0) : p.natDegree ≤ Module.finrank K E := by
  have h := minpoly.natDegree_le (A := K) z
  rw [← minpoly.eq_of_irreducible hp hz,
    Polynomial.natDegree_mul_C (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp.ne_zero))] at h
  exact h

set_option synthInstance.maxHeartbeats 200000 in
-- The branch residue and the two normalization towers use several compatible scalar structures.
set_option maxHeartbeats 1200000 in
/-- On an actual nonexceptional component, an irreducible polynomial whose
roots label the normalized infinity residues forces twice its degree into the
original curve degree. The infinity multiplicities and their weighted sum are
constructed by the existing normalization theorems, not assumed. -/
theorem component_degree_lower_of_irreducible_infinity_labels
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
    (f : Polynomial ℚ) (hirr : Irreducible f) :
    let R := MvPolynomial (Fin 3) ℚ ⧸ I
    let ι := IsScalarTower.toAlgHom ℚ R F
    let S := projectiveChart I ι (Ideal.Quotient.mk I (X 0))
    let C := integralClosure S F
    let w := chartInfinityCoordinate I ι (Ideal.Quotient.mk I (X 0))
    (∀ p : IsDedekindDomain.HeightOneSpectrum C, algebraMap S C w ∈ p.asIdeal →
      ∃ z : C ⧸ p.asIdeal, Polynomial.aeval z f = 0) →
      2 * f.natDegree ≤ d := by
  classical
  let R := MvPolynomial (Fin 3) ℚ ⧸ I
  let ι := IsScalarTower.toAlgHom ℚ R F
  let S := projectiveChart I ι (Ideal.Quotient.mk I (X 0))
  let C := integralClosure S F
  let w := chartInfinityCoordinate I ι (Ideal.Quotient.mk I (X 0))
  let hnormal := orbit_chart_normalization_in_field hba hi hne I hf hg hd hdegree F
  let : IsFractionRing S F := hnormal.1
  let : IsDedekindDomain C := hnormal.2.1
  let : IsFractionRing C F := IsIntegralClosure.isFractionRing_of_finite_extension S F F C
  have hι : Function.Injective ι := IsFractionRing.injective R F
  have ha : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hA : (Lz a b i : ℚ) ≠ 0 := by
    exact_mod_cast (show Lz a b i ≠ 0 by
      have := Lz_pos hba (by omega : i + 5 < P a b)
      omega)
  obtain ⟨hρ, hu, hv⟩ := orbit_rational_pattern_signs hba (by omega : i + 6 < P a b)
  have hne' : NonexceptionalPattern (patternRhoQ a b i : ℝ)
      (patternUQ a b i : ℝ) (patternVQ a b i : ℝ) := by simpa using hne
  let : Module.Finite (Algebra.adjoin ℚ {w}) S :=
    nonexceptional_chart_finite_over_parameter hρ hu hv hne'
      (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
      (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι hι hd hdegree
  have hw : Transcendental ℚ w := nonexceptional_chart_parameter_transcendental hρ hu hv hne'
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι hι hd hdegree
  obtain ⟨B, hB, hsum⟩ := normalized_parameter_branches (L := F) w hw
  have hdim : Module.finrank ℚ (S ⧸ Ideal.span {w}) = d :=
    (rational_nonexceptional_chart_infinity_dimension hρ hu hv hne'
      (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
      (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι hι hd hdegree).2
  have hwC0 : algebraMap S C w ≠ 0 := by
    intro hz
    have hh := congrArg (algebraMap C F) hz
    rw [← IsScalarTower.algebraMap_apply S C F, map_zero] at hh
    exact hw.ne_zero ((IsFractionRing.injective S F) (hh.trans (map_zero _).symm))
  change (∀ p : IsDedekindDomain.HeightOneSpectrum C,
    algebraMap S C w ∈ p.asIdeal → ∃ z : C ⧸ p.asIdeal, Polynomial.aeval z f = 0) →
      2 * f.natDegree ≤ d
  intro hlabels
  have hsumd := hsum.trans hdim
  obtain ⟨p, hp, hpterm⟩ := Finset.sum_pos_iff.mp
    (show 0 < ∑ p ∈ B, multiplicity p.asIdeal (Ideal.span {algebraMap S C w}) *
      Module.finrank ℚ (C ⧸ p.asIdeal) by rw [hsumd]; exact hd)
  let : Module.Finite ℚ (C ⧸ p.asIdeal) :=
    Module.finite_of_finrank_pos (Nat.pos_of_mul_pos_left hpterm)
  obtain ⟨z, hz⟩ := hlabels p ((hB p).mp hp)
  have hfdeg := irreducible_root_natDegree_le_finrank hirr z hz
  let ν := normalizedBranchOrder p F
  have hregular (r : S) : 0 ≤ ν (r : F) := by
    have hh := normalizedBranchOrder_nonnegative p F (algebraMap S C r)
    rw [← IsScalarTower.algebraMap_apply S C F] at hh
    exact hh
  obtain ⟨e, he, hwν⟩ := normalizedBranchOrder_parameter p F hwC0 ((hB p).mp hp)
  have hwν' : ν ((ι (Ideal.Quotient.mk I (X 0)))⁻¹) = (e : WithTop ℤ) := by
    change ν (algebraMap C F (algebraMap S C w)) = _ at hwν
    rw [← IsScalarTower.algebraMap_apply S C F] at hwν
    exact hwν
  obtain ⟨t, ht, het, _⟩ := nonexceptional_rank_five_discrete_order hρ hu hv hne'
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i : ℚ) (a : ℚ) hA ha I hf hg ι hι hd hdegree ν hregular he hwν'
  have hmult := normalizedBranchOrder_eq_multiplicity p F hwC0
  rw [hwν] at hmult
  have hmult' : 2 ≤ multiplicity p.asIdeal (Ideal.span {algebraMap S C w}) := by
    have he' : e = (multiplicity p.asIdeal (Ideal.span {algebraMap S C w}) : ℤ) := by
      exact_mod_cast hmult
    omega
  have hterm := Finset.single_le_sum
    (fun p (_hp : p ∈ B) => Nat.zero_le (multiplicity p.asIdeal
      (Ideal.span {algebraMap S C w}) * Module.finrank ℚ (C ⧸ p.asIdeal))) hp
  rw [hsumd] at hterm
  exact (Nat.mul_le_mul hmult' hfdeg).trans hterm

set_option synthInstance.maxHeartbeats 200000 in
-- The residue-label hypothesis names the actual integral closure of the infinity chart.
set_option maxHeartbeats 800000 in
/-- A degree-twelve irreducible branch label forces every such component to
have degree exactly twenty-four, using the already proved total degree bound. -/
theorem component_degree_twenty_four_of_irreducible_infinity_labels
    {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    {d N : ℕ} {c₀ : ℤ} (hd : 0 < d) (hd24 : d ≤ 24)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c₀)
    (F : Type*) [Field F] [Algebra ℚ F] [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsScalarTower ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin 3) ℚ ⧸ I) F]
    (f : Polynomial ℚ) (hirr : Irreducible f) (hdeg : f.natDegree = 12) :
    let R := MvPolynomial (Fin 3) ℚ ⧸ I
    let ι := IsScalarTower.toAlgHom ℚ R F
    let S := projectiveChart I ι (Ideal.Quotient.mk I (X 0))
    let C := integralClosure S F
    let w := chartInfinityCoordinate I ι (Ideal.Quotient.mk I (X 0))
    (∀ p : IsDedekindDomain.HeightOneSpectrum C, algebraMap S C w ∈ p.asIdeal →
      ∃ z : C ⧸ p.asIdeal, Polynomial.aeval z f = 0) →
      d = 24 := by
  have h := component_degree_lower_of_irreducible_infinity_labels
    hba hi hne I hf hg hd hdegree F f hirr
  dsimp only at h ⊢
  intro hlabels
  have hlower := h hlabels
  omega

end
end PierceLengthBound.FixedDividend
