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

end
end PierceLengthBound.FixedDividend
