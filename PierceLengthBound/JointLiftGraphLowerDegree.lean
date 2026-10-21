/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.LinearJointGraph

/-! The old infinity poles of the rank-five coordinate and the finite curvature
poles are distinct normalized branches. Together they force graph degree 4d+1. The argument is
the one of `LinearJointGraph` with first powers and `G = 1`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial
attribute [local instance] FractionRing.liftAlgebra

/-- The old infinity poles of the rank-five coordinate and the finite curvature poles force
graph degree `4d + 1`: the case `G = 1`, `m = k = 1` of
`retained_linearJointGraph_degree_lower_bound`. -/
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
  rw [← orbitPoweredJointGraphIdeal_one_one I (orbitJoint_denominator_not_mem hba hi I hz),
    ← orbitLinearJointGraphIdeal_one] at hgraph
  have h := retained_linearJointGraph_degree_lower_bound 1 (by simp) one_pos one_pos hba hi hne
    I hf hg hz hnorm hres Q hQ hQdeg hQI hd3 hdegree hgraph F
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
