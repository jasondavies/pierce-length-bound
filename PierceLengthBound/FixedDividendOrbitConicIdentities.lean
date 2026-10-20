/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendConicPolynomialIdentities

/-! Symbolic actual conic parametrizations and leading degrees after a bounded point exception. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial
set_option maxHeartbeats 1000000

/-- At least twenty-five integral points force the actual polynomial equations
and the exact determinant degrees along the bounded integer parameter. -/
theorem orbit_conic_symbolic_parameter {a b i : ℕ} (hba : b < a)
    (hi : i + 7 < P a b) {X L : ℕ} (hX : 1 ≤ X) (hL : 1 ≤ L)
    (ht : ∀ j, |theta a b i j| ≤ X)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : orbitCurveQuadraticQ a b i ∈ I) (hg : orbitCurveEquationQ a b i ∈ I)
    (n : Fin 3 → ℤ) (e : ℤ) (hn : n ≠ 0) (hnb : ∀ j, |n j| ≤ L) (heb : |e| ≤ L)
    (hplane : integerPlanePolynomial n e ∈ I)
    {N : ℕ} {c : ℤ}
    (hdegree : ∀ m ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I m) : ℤ) = 2 * m + c)
    (hx : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (S : Finset (Fin 3 → ℤ))
    (hS : ∀ z ∈ S, (fun j => (z j : ℚ)) ∈ coordinateZeroLocus I)
    (hcard : 24 < S.card) :
    ∃ (p : (Fin 3 → ℤ) → ℤ) (Q : Fin 3 → Polynomial ℚ),
      Set.InjOn p {z | (fun j => (z j : ℚ)) ∈ coordinateZeroLocus I} ∧
      (∀ z : Fin 3 → ℤ, (fun j => (z j : ℚ)) ∈ coordinateZeroLocus I →
        ∀ j, (Q j).eval (p z : ℚ) = (z j : ℚ)) ∧
      (∀ j, (Q j).natDegree ≤ 2) ∧ (Q 0).coeff 2 ≠ 0 ∧
      MvPolynomial.aeval Q (orbitCurveQuadraticQ a b i) = 0 ∧
      MvPolynomial.aeval Q (orbitCurveEquationQ a b i) = 0 ∧
      Function.Injective (completeDirection (patternRhoQ a b i) (patternUQ a b i)
        (patternVQ a b i) (fun j => (Q j).coeff 2)) ∧
      (let k := lineGaps (Polynomial.C (patternRhoQ a b i))
        (Polynomial.C (patternUQ a b i)) (Polynomial.C (patternVQ a b i))
        (Polynomial.C (patternRhoQ a b (i + 1))) (Polynomial.C (patternUQ a b (i + 1)))
        (Polynomial.C (patternVQ a b (i + 1))) (Q 0) (Q 1) (Q 2)
       (rawHankelThree (k 0) (k 1) (k 2)).natDegree = 6 ∧
         (muH4 (k 0) (k 1) (k 2) (k 3) (k 4)).natDegree = 12 ∧
         (rawHankelMixed (k 0) (k 1) (k 2) (k 3)).natDegree ≤ 8) := by
  obtain ⟨σ, v, E, F, hσ, hE, hvb, hEb, hFd, hFb, hF2, hrepr, hinj⟩ :=
    orbit_bounded_integer_parameter hba hi hX hL ht hne I hf hg n e hn hnb heb hplane hdegree hx
  let p : (Fin 3 → ℤ) → ℤ := fun z => 2 * v 0 * z (σ 0) + v 1 * z (σ 1) + v 3
  let Q := normalizedParameter σ E F
  have hQd : ∀ j, (Q j).natDegree ≤ 2 := normalizedParameter_degree σ E F hFd
  have hQ0 : (Q 0).coeff 2 ≠ 0 := normalizedParameter_first_coeff σ hσ hE F hF2
  have hpoint : ∀ z : Fin 3 → ℤ, (fun j => (z j : ℚ)) ∈ coordinateZeroLocus I →
      ∀ j, (Q j).eval (p z : ℚ) = (z j : ℚ) := by
    intro z hz
    exact normalizedParameter_eval σ hE F z (p z) (hrepr z hz)
  have hident := normalizedParameter_curve_identities
    (patternRhoQ a b i) (patternUQ a b i) (patternVQ a b i)
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i) a I hf hg σ hE F hFd p hrepr hinj S hS hcard
  have hsign := orbit_rational_pattern_signs hba (by omega : i + 6 < P a b)
  have hneq : NonexceptionalPattern (patternRhoQ a b i : ℝ)
      (patternUQ a b i : ℝ) (patternVQ a b i : ℝ) := by simpa using hne
  have ha : (a : ℚ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  have hlead := rational_quadratic_parameter_leading_nodes hsign.1 hsign.2.1 hsign.2.2 hneq
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i) a ha Q hQd hQ0 hident.1 hident.2
  have hraw := quadratic_parameter_raw_degrees hsign.1 hsign.2.1 hsign.2.2 hneq
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i) a ha Q hQd hQ0 hident.1 hident.2
  exact ⟨p, Q, hinj, hpoint, hQd, hQ0, hident.1, hident.2, hlead, hraw⟩

end
end PierceLengthBound.FixedDividend
