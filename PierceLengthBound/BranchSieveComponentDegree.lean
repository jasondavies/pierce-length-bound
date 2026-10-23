/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftFiniteZero
public import PierceLengthBound.NormalizationInfinityDegree

/-! Residue-field labels at infinity bound the degree of an orbit component
from below (the second part of Lemma 10.3). The file sets up the chart at
infinity of the first coordinate, its normalization in the function field and
the normalized branches over infinity. If every such branch has a residue root
of an irreducible polynomial of degree `r`, the component has degree at least
`2r`: the branch multiplicities times residue degrees sum to the degree, every
multiplicity is even (Corollary 8.4) and every residue degree is at least `r`. -/

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

section InfinityChart

variable (I : Ideal (MvPolynomial (Fin 3) ℚ)) (F : Type*) [Field F] [Algebra ℚ F]
  [Algebra (MvPolynomial (Fin 3) ℚ ⧸ I) F] [IsScalarTower ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F]

/-- The coordinate ring of an orbit component inside its function field. -/
abbrev orbitChartEmbedding : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F :=
  IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) F

/-- The affine chart at infinity of the first coordinate. -/
abbrev orbitChart : Subalgebra ℚ F :=
  projectiveChart I (orbitChartEmbedding I F) (Ideal.Quotient.mk I (X 0))

/-- The normalization of the infinity chart in the function field. -/
abbrev orbitChartClosure : Subalgebra (orbitChart I F) F :=
  integralClosure (orbitChart I F) F

/-- The chart parameter whose zeros are the branches at infinity. -/
abbrev orbitChartParameter : orbitChart I F :=
  chartInfinityCoordinate I (orbitChartEmbedding I F) (Ideal.Quotient.mk I (X 0))

/-- The normalized branches lying over infinity. -/
def orbitInfinityBranches : Set (IsDedekindDomain.HeightOneSpectrum (orbitChartClosure I F)) :=
  {p | algebraMap (orbitChart I F) (orbitChartClosure I F) (orbitChartParameter I F) ∈ p.asIdeal}

/-- Every normalized branch at infinity has a residue root of `f`. -/
def orbitInfinityLabels (f : Polynomial ℚ) : Prop :=
  ∀ p ∈ orbitInfinityBranches I F,
    ∃ z : orbitChartClosure I F ⧸ p.asIdeal, Polynomial.aeval z f = 0

end InfinityChart

/-- The common setup on a nonexceptional component: the infinity chart has a
Dedekind normalization in the function field, finite over the transcendental
chart parameter, and the rational pattern signs hold. -/
theorem orbit_infinity_chart_setup
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
    IsFractionRing (orbitChart I F) F ∧ IsDedekindDomain (orbitChartClosure I F) ∧
      IsFractionRing (orbitChartClosure I F) F ∧
      Function.Injective (orbitChartEmbedding I F) ∧ (a : ℚ) ≠ 0 ∧ (Lz a b i : ℚ) ≠ 0 ∧
      0 < patternRhoQ a b i ∧ 0 < patternUQ a b i ∧ patternVQ a b i < 0 ∧
      NonexceptionalPattern (patternRhoQ a b i : ℝ) (patternUQ a b i : ℝ)
        (patternVQ a b i : ℝ) ∧
      Module.Finite (Algebra.adjoin ℚ {orbitChartParameter I F}) (orbitChart I F) ∧
      Transcendental ℚ (orbitChartParameter I F) := by
  obtain ⟨h₁, h₂, -⟩ := orbit_chart_normalization_in_field hba hi hne I hf hg hd hdegree F
  have hι : Function.Injective (orbitChartEmbedding I F) :=
    IsFractionRing.injective (MvPolynomial (Fin 3) ℚ ⧸ I) F
  obtain ⟨hρ, hu, hv, hne', ha, hA⟩ := orbit_rational_nonexceptional_data hba hi hne
  exact ⟨h₁, h₂, IsIntegralClosure.isFractionRing_of_finite_extension (orbitChart I F) F F
      (orbitChartClosure I F), hι, ha, hA, hρ, hu, hv, hne',
    nonexceptional_chart_finite_over_parameter hρ hu hv hne'
      (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
      (Lz a b i : ℚ) (a : ℚ) ha I hf hg _ hι hd hdegree,
    nonexceptional_chart_parameter_transcendental hρ hu hv hne'
      (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
      (Lz a b i : ℚ) (a : ℚ) ha I hf hg _ hι hd hdegree⟩

/-- On a nonexceptional orbit component of degree `d`, if every normalized
infinity residue contains a root of an irreducible `f`, then `2 deg f ≤ d`. -/
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
    orbitInfinityLabels I F f →
      2 * f.natDegree ≤ d := by
  classical
  let ι := orbitChartEmbedding I F
  let S := orbitChart I F
  let C := orbitChartClosure I F
  let w := orbitChartParameter I F
  -- Fixing the tower instances keeps typeclass search out of the normalization tower.
  let : Algebra S C := C.algebra
  let : IsScalarTower S C F := IsScalarTower.subalgebra' S F F C
  obtain ⟨_, _, _, hι, ha, hA, hρ, hu, hv, hne', _, hw⟩ :=
    orbit_infinity_chart_setup hba hi hne I hf hg hd hdegree F
  obtain ⟨B, hB, hsum⟩ := normalized_parameter_branches (L := F) w hw
  have hdim : Module.finrank ℚ (S ⧸ Ideal.span {w}) = d :=
    (nonexceptional_chart_infinity_dimension hρ hu hv hne'
      (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
      (Lz a b i : ℚ) (a : ℚ) ha I hf hg ι hι hd hdegree).2
  have hwC0 : algebraMap S C w ≠ 0 := by
    intro hz
    have hh := congrArg (algebraMap C F) hz
    rw [← IsScalarTower.algebraMap_apply S C F, map_zero] at hh
    exact hw.ne_zero ((IsFractionRing.injective S F) (hh.trans (map_zero _).symm))
  intro hlabels
  have hsumd := hsum.trans hdim
  obtain ⟨p, hp, hpterm⟩ := Finset.sum_pos_iff.mp (hd.trans_eq hsumd.symm)
  let : Module ℚ (C ⧸ p.asIdeal) := Submodule.Quotient.module' p.asIdeal
  let : Module.Free ℚ (C ⧸ p.asIdeal) := Module.Free.of_divisionRing ℚ _
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
  exact (Nat.mul_le_mul hmult' hfdeg).trans
    ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) hp).trans_eq hsumd)

/-- Together with the degree bound `d ≤ 24` (Lemma 8.1), an irreducible
degree-twelve label at infinity forces the component degree to be exactly
twenty-four. -/
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
    orbitInfinityLabels I F f →
      d = 24 := by
  intro hlabels
  have := component_degree_lower_of_irreducible_infinity_labels
    hba hi hne I hf hg hd hdegree F f hirr hlabels
  omega

end
end PierceLengthBound.FixedDividend
