/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionRetainedBase
public import PierceLengthBound.PolarProjectionDegreeReduction
public import PierceLengthBound.BranchSieveResultantLabel

/-! The polar graph degree on actual retained components. The local
intersection contribution is proved from the explicit nonvanishing conditions;
the degree-twelve branch polynomial supplies the component degree. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open MvPolynomial
noncomputable section

/-- On a degree-24 component the actual polar cuts and the explicit chart
and quartic conditions imply the full powered graph degree bound. -/
theorem retained_polar_linearJointGraph_degree
    {a b i δ N m n : ℕ} {c₀ : ℤ}
    (G : Matrix (Fin 3) (Fin 3) ℚ) (hG : IsUnit G.det) (hm : 0 < m) (hn : 0 < n)
    (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hnorm : jointNormalizationPolynomial a b i ∈ I)
    (hres : jointResolventPolynomial a b i ∈ I)
    (hcut : ∀ j, orbitPolarIdentityPolynomial a b i j ∈ I)
    (hguard : polarChartGuard (orbitPolarParameters a b i) ≠ 0)
    (hminor : polarInitialMinor (orbitPolarParameters a b i) ≠ 0)
    (hdegree : ∀ j ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I j) : ℤ) = 24 * j + c₀)
    (hgraph : ∃ M : ℕ, ∃ c : ℤ, ∀ j ≥ M,
      (Module.finrank ℚ
        (filteredCoordinateSpace (orbitLinearJointGraphIdeal G a b i m n I) j) : ℤ) =
          (δ : ℤ) * j + c) :
    56 * m + 60 * n ≤ δ := by
  let F := FractionRing (MvPolynomial (Fin 3) ℚ ⧸ I)
  exact retained_polar_linearJointGraph_degree_of_base_degree_le_four G hG hm hn
    hba hi hne I hf hg hz hnorm hres hdegree hgraph F
    (retained_polar_base_degree_le_four hba hi hne I hf hg hz hcut hguard hminor
      (by norm_num : 0 < 24) hdegree F)

/-- Irreducibility of the actual degree-twelve label polynomial forces
component degree 24, and hence the polar graph bound. -/
theorem retained_polar_linearJointGraph_degree_of_irreducible_label
    {a b i d δ N m n : ℕ} {c₀ : ℤ}
    (G : Matrix (Fin 3) (Fin 3) ℚ) (hG : IsUnit G.det) (hm : 0 < m) (hn : 0 < n)
    (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hnorm : jointNormalizationPolynomial a b i ∈ I)
    (hres : jointResolventPolynomial a b i ∈ I)
    (hcut : ∀ j, orbitPolarIdentityPolynomial a b i j ∈ I)
    (hguard : polarChartGuard (orbitPolarParameters a b i) ≠ 0)
    (hminor : polarInitialMinor (orbitPolarParameters a b i) ≠ 0)
    (hd : 0 < d) (hd24 : d ≤ 24)
    (hdegree : ∀ j ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I j) : ℤ) = (d : ℤ) * j + c₀)
    (hgraph : ∃ M : ℕ, ∃ c : ℤ, ∀ j ≥ M,
      (Module.finrank ℚ
        (filteredCoordinateSpace (orbitLinearJointGraphIdeal G a b i m n I) j) : ℤ) =
          (δ : ℤ) * j + c)
    (c : ℚ) (hirr : Irreducible (orbitBranchLabelPolynomial a b i c))
    (hdeg : (orbitBranchLabelPolynomial a b i c).natDegree = 12) :
    56 * m + 60 * n ≤ δ := by
  let F := FractionRing (MvPolynomial (Fin 3) ℚ ⧸ I)
  have he := component_degree_twenty_four_of_irreducible_infinity_labels
    hba hi hne I hf hg hd hd24 hdegree F (orbitBranchLabelPolynomial a b i c)
    hirr hdeg (orbit_infinity_residue_label_root hba hi hne I hf hg hd hdegree F c)
  subst d
  exact retained_polar_linearJointGraph_degree G hG hm hn hba hi hne I hf hg hz
    hnorm hres hcut hguard hminor hdegree hgraph

end
end PierceLengthBound.FixedDividend
