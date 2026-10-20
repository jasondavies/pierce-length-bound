/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendSecondParabolicModel
public import PierceLengthBound.FixedDividendConicPlanePivot

/-! The two explicit parabolic charts cover every actual nonexceptional conic. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- Every nonzero containing plane admits one of the two fully certified
parabolic models. No choice of a nonzero pivot is required as an extra premise. -/
theorem rational_nonexceptional_parabolic_chart
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ)
    (hA : A ≠ 0) (ha : a ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : curveQuadratic (ρ : ℚ) u v ρ' u' v' ∈ I)
    (hg : curveEquation (ρ : ℚ) u v ρ' u' v' A a ∈ I)
    (n0 n1 n2 e : ℚ) (hn : n0 ≠ 0 ∨ n1 ≠ 0 ∨ n2 ≠ 0)
    (hplane : C n0 * X 0 + C n1 * X 1 + C n2 * X 2 + C e ∈ I)
    {N : ℕ} {b : ℤ}
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = 2 * n + b)
    (x : Fin 3 → ℚ) (hx : x ∈ coordinateZeroLocus I) :
    ∃ (j : Fin 3) (c : Fin 6 → ℚ),
      ((j = 1 ∧ n2 ≠ 0 ∧ c = rationalPlaneConicCoefficients ρ u v ρ' u' v' n0 n1 n2 e) ∨
       (j = 2 ∧ n1 ≠ 0 ∧ c = rationalSecondPlaneConicCoefficients ρ u v ρ' u' v'
         n0 n1 n2 e)) ∧
      c 0 ≠ 0 ∧ (c 1) ^ 2 - 4 * c 0 * c 2 = 0 ∧
      2 * c 1 * c 3 - 4 * c 0 * c 4 ≠ 0 ∧
      ∀ y ∈ coordinateZeroLocus I,
        conicValue (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (y j) (y 0) = 0 := by
  by_cases hn2 : n2 ≠ 0
  · have h := rational_nonexceptional_parabolic_model hρ hu hv hne ρ' u' v' A a
      hA ha I hf hg n0 n1 n2 e hn2 hplane hdegree x hx
    exact ⟨1, _, Or.inl ⟨rfl, hn2, rfl⟩, h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩
  · have hn1 : n1 ≠ 0 :=
      (rational_nonexceptional_plane_pivot hρ hu hv hne ρ' u' v' A a ha I hf hg
        n0 n1 n2 e hn hplane (by decide : 0 < 2) hdegree).resolve_right hn2
    have h := rational_nonexceptional_second_parabolic_model hρ hu hv hne ρ' u' v' A a
      hA ha I hf hg n0 n1 n2 e hn1 hplane hdegree x hx
    exact ⟨2, _, Or.inr ⟨rfl, hn1, rfl⟩, h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩

end
end PierceLengthBound.FixedDividend
