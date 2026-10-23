/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendSelection
public import PierceLengthBound.IntegralLiftNormalizationCut

/-! The curve polynomials and nonexceptionality depend on a start only through its pattern;
the quadratic of the pattern curve is prime of degree two (the prime quadratic input of the
retained graph theorems); and the pattern coordinates of a selected start have height at most
`selectedMinorHeight`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- Starts with the same pattern have the same curve polynomials. -/
lemma orbitCurve_polynomials_congr {a b i j : ℕ} (h : theta a b i = theta a b j) :
    orbitCurveQuadraticQ a b i = orbitCurveQuadraticQ a b j ∧
      orbitCurveEquationQ a b i = orbitCurveEquationQ a b j := by
  obtain ⟨h0, hρ, hu, hv, hρ', hu', hv'⟩ := orbit_pattern_eq_of_theta h
  simp only [orbitCurveQuadraticQ, orbitCurveEquationQ, h0, hρ, hu, hv, hρ', hu', hv', and_self]

lemma orbit_nonexceptional_congr {a b i j : ℕ} (h : theta a b i = theta a b j) :
    NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i) ↔
      NonexceptionalPattern (patternRho a b j) (patternU a b j) (patternV a b j) := by
  obtain ⟨_, hρ, hu, hv, _⟩ := orbit_pattern_eq_of_theta h
  rw [← patternRhoQ_cast, ← patternUQ_cast, ← patternVQ_cast,
    hρ, hu, hv, patternRhoQ_cast, patternUQ_cast, patternVQ_cast]

lemma rational_curveQuadratic_degree_two {ρ u v : ℚ}
    (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0) (ρ' u' v' : ℚ) :
    (curveQuadratic ρ u v ρ' u' v').totalDegree = 2 := by
  have hle := curveQuadratic_degree_le_two ρ u v ρ' u' v'
  have hn : ¬(curveQuadratic ρ u v ρ' u' v').totalDegree ≤ 1 := by
    intro hd
    have hh := hessian_eq_zero_of_degree_le_one hd
    have hdet : (hessianAtZero (curveQuadratic ρ u v ρ' u' v')).det = 0 := by
      rw [hh, Matrix.det_zero]
    rw [curveQuadratic, lineQuadratic_eq_ternary, ternaryQuadratic_hessian_det] at hdet
    have he : 1 + (-ρ - u) + (u - v) + (v - 1) = -ρ := by ring
    rw [he] at hdet
    have h1 : -ρ - u ≠ 0 := by linarith
    have h2 : u - v ≠ 0 := by linarith
    have h3 : v - 1 ≠ 0 := by linarith
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h1) h2) h3)
      (neg_ne_zero.mpr hρ.ne')) hdet
  omega

/-- The quadratic of the pattern curve is prime of total degree two. -/
theorem orbitCurveQuadraticQ_prime_degree {a b i : ℕ} (hba : b < a)
    (hi : i + 7 < P a b) :
    Prime (orbitCurveQuadraticQ a b i) ∧ (orbitCurveQuadraticQ a b i).totalDegree = 2 := by
  obtain ⟨hρ, hu, hv⟩ := orbit_rational_pattern_signs hba (by omega : i + 6 < P a b)
  exact ⟨rational_curveQuadratic_prime hρ hu hv _ _ _,
    rational_curveQuadratic_degree_two hρ hu hv _ _ _⟩

lemma projθ_abs_le {p : Fin 10 → ℤ} {X : ℤ} (h : ∀ t, |p t| ≤ X) (j : Fin 7) :
    |projθ p j| ≤ X := by
  fin_cases j
  · exact h 0
  · exact h 6
  · exact h 9
  · exact h 3
  · change |-p 1| ≤ X
    simpa only [abs_neg] using h 1
  · exact h 8
  · change |-p 7| ≤ X
    simpa only [abs_neg] using h 7

/-- The pattern coordinates `theta` of a selected start have height at most
`selectedMinorHeight a A T`. -/
lemma selectedStart_theta_height {a b s T A i : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hi : i ∈ selectedStarts a b s T A) (j : Fin 7) :
    |theta a b i j| ≤ (selectedMinorHeight a A T : ℤ) := by
  rw [theta_eq]
  exact projθ_abs_le (selectedStart_minor_height hba hmem hsT hi) j

end
end PierceLengthBound.FixedDividend
