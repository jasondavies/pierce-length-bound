/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendDegreeParity

/-!
# Rational curve covers with the nonexceptional parity split

For a nonexceptional pattern, the rational fixed-dividend equations are covered by
at most twenty-four prime components, each of even affine Hilbert degree `d` with
`d = 2` or `4 ≤ d ≤ 24`.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- The rational prime cover of a nonexceptional pattern: at most twenty-four
height-two prime components containing both equations, each of even affine Hilbert
degree `d` with `d = 2` or `4 ≤ d ≤ 24`, whose zero loci cover the common zeros. -/
theorem nonexceptional_curve_decomposition {ρ u v : ℚ}
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
  have heven := nonexceptional_component_degree_even
    hρ hu hv hne ρ' u' v' A a hA ha p hf hg hd hdegree
  obtain ⟨m, hm⟩ := heven
  refine ⟨hprime, hheight, hf, hg, d, by omega, hd24, ⟨m, hm⟩,
    by omega, N, c, hdegree⟩

end
end PierceLengthBound.FixedDividend
