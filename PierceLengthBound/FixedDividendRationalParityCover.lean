/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendRationalDegreeParity
public import PierceLengthBound.FixedDividendRationalOrbit

/-!
# Rational curve covers with the nonexceptional parity split

The actual rational prime cover has only conic components and components of
even degree at least four in a nonexceptional pattern. The cover has at most
twenty-four members and uses their genuine affine Hilbert degrees.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- The rational cover directly supplies the conic versus degree-at-least-four
split. Positive even degree also excludes lines without a large-scale premise. -/
theorem rational_nonexceptional_curve_decomposition {ρ u v : ℚ}
    (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ))
    (ρ' u' v' A a : ℚ) (hA : A ≠ 0) (ha : a ≠ 0) :
    ∃ S : Finset (Ideal (MvPolynomial (Fin 3) ℚ)), S.card ≤ 24 ∧
      (∀ p ∈ S, p.IsPrime ∧ p.height = 2 ∧
        curveQuadratic ρ u v ρ' u' v' ∈ p ∧ curveEquation ρ u v ρ' u' v' A a ∈ p ∧
        ∃ d : ℕ, 2 ≤ d ∧ d ≤ 24 ∧ Even d ∧ (d = 2 ∨ 4 ≤ d) ∧
          ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
            (Module.finrank ℚ (filteredCoordinateSpace p n) : ℤ) = (d : ℤ) * n + c) ∧
      (∀ x, (MvPolynomial.eval x (curveQuadratic ρ u v ρ' u' v') = 0 ∧
        MvPolynomial.eval x (curveEquation ρ u v ρ' u' v' A a) = 0) ↔
        ∃ p ∈ S, x ∈ coordinateZeroLocus p) := by
  obtain ⟨S, hS, hp, hc⟩ := rational_curve_decomposition_with_degrees
    hρ hu hv ρ' u' v' A a ha
  refine ⟨S, hS, ?_, hc⟩
  intro p hmem
  obtain ⟨hprime, hheight, hf, hg, d, hd, hd24, N, c, hdegree⟩ := hp p hmem
  let : p.IsPrime := hprime
  have heven := rational_nonexceptional_component_degree_even
    hρ hu hv hne ρ' u' v' A a hA ha p hf hg hd hdegree
  obtain ⟨m, hm⟩ := heven
  refine ⟨hprime, hheight, hf, hg, d, by omega, hd24, ⟨m, hm⟩,
    by omega, N, c, hdegree⟩

/-- The existing actual-window rational component interface gains the exact
parity split required by the quarter-root branch of the counting argument. -/
theorem orbit_rational_component_parity_range {a b i : ℕ}
    (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i))
    {H X₀ : ℤ} (hX : 1 ≤ X₀) (hgaps : ∀ m < 5, kq a b (i + m) ≤ H)
    (hU : |U1z a b i| ≤ X₀) (hV : |U2z a b i| ≤ X₀)
    (hscale : (a : ℤ) * H ^ 5 * (24 * X₀ + 464) < (qq a b i : ℤ) ^ 4)
    (p : Ideal (MvPolynomial (Fin 3) ℚ)) [p.IsPrime] (hp : p.height = 2)
    (hf : orbitCurveQuadraticQ a b i ∈ p) (he : orbitCurveEquationQ a b i ∈ p)
    (hx : orbitFreeNodesQ a b i ∈ coordinateZeroLocus p) :
    ∃ d : ℕ, 2 ≤ d ∧ d ≤ 24 ∧ Even d ∧ (d = 2 ∨ 4 ≤ d) ∧
      ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
        (Module.finrank ℚ (filteredCoordinateSpace p n) : ℤ) = (d : ℤ) * n + c := by
  obtain ⟨d, hd, hd24, N, c, hdegree⟩ :=
    orbit_rational_component_degree_range hba hi hX hgaps hU hV hscale p hp hf he hx
  obtain ⟨hρ, hu, hv⟩ := orbit_rational_pattern_signs hba (by omega : i + 6 < P a b)
  have hL : (Lz a b i : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Lz_pos hba (by omega : i + 5 < P a b)))
  have hneQ : NonexceptionalPattern (patternRhoQ a b i : ℝ)
      (patternUQ a b i : ℝ) (patternVQ a b i : ℝ) := by simpa using hne
  have heven := rational_nonexceptional_component_degree_even hρ hu hv hneQ
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i) a hL (by exact_mod_cast (show a ≠ 0 by omega)) p hf he
    (by omega : 0 < d) hdegree
  obtain ⟨m, hm⟩ := heven
  exact ⟨d, hd, hd24, ⟨m, hm⟩, by omega, N, c, hdegree⟩

end
end PierceLengthBound.FixedDividend
