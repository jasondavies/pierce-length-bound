/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.LinearJointGraph

/-! Integer powers multiply the two disjoint pole contributions, giving the
actual degree lower bound for every fixed pair of positive coordinate powers. The powered graph
is the linearly changed graph of `LinearJointGraph` with `G = 1`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- The actual retained powered graph has the degree range required by the
curve theorem, uniformly over components of degree at least four. -/
theorem orbitPoweredJointGraph_retained_degree_range {a b i d m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hnorm : jointNormalizationPolynomial a b i ∈ I)
    (hres : jointResolventPolynomial a b i ∈ I)
    (Q : MvPolynomial (Fin 3) ℚ) (hQ : Prime Q) (hQdeg : Q.totalDegree = 2) (hQI : Q ∈ I)
    (hd4 : 4 ≤ d)
    (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ j ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I j) : ℤ) = (d : ℤ) * j + c) :
    ∃ δ : ℕ, 10 * n + 7 * m ≤ δ ∧ δ ≤ ((m + n) * 247 + 1) * d ∧
      ∃ N : ℕ, ∃ c : ℤ, ∀ j ≥ N,
        (Module.finrank ℚ (filteredCoordinateSpace (orbitPoweredJointGraphIdeal a b i m n I) j)
          : ℤ) = (δ : ℤ) * j + c := by
  have h := orbitLinearJointGraph_retained_degree_range 1 (by simp) hm hn hba hi hne I hf hg hz
    hnorm hres Q hQ hQdeg hQI hd4 hdegree
  rwa [orbitLinearJointGraphIdeal_one] at h

end
end PierceLengthBound.FixedDividend
