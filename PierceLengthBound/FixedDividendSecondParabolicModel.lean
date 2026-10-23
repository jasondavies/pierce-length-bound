/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendSecondPlaneModel

/-!
# Actual rational parabolic plane models

The coefficients below restrict the actual fixed-dividend quadratic to a
containing plane. For a nonexceptional component of Hilbert degree two with a
rational point, both denominators required for parabolic reconstruction are
nonzero. The only coordinate choice is a nonzero third plane coefficient.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- Exact binary coefficients obtained by eliminating the third node. -/
def rationalSecondPlaneConicCoefficients (ρ u v ρ' u' v' n0 n1 n2 e : ℚ) : Fin 6 → ℚ :=
  planeConicCoefficients (-ρ - u) (v - 1) (u - v)
    (ρ - (-ρ - u) - ρ' - (-ρ - u) * (v - 1 - v'))
    ((u - v) - (v - 1) - u' + v' - (v - 1) * (v - 1 - v'))
    ((-ρ - u) - (u - v) + ρ' + u' - (u - v) * (v - 1 - v'))
    (-n0 / n1) (-n2 / n1) (-e / n1)

lemma eval_secondPlaneConicPolynomial {K : Type*} [CommRing K] (c : Fin 6 → K)
    (x : Fin 3 → K) :
    eval x (secondPlaneConicPolynomial c) =
      conicValue (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (x 2) (x 0) := by
  simp [secondPlaneConicPolynomial, conicValue]

/-- An actual rational degree-two component has a nondegenerate parabolic plane
model; its rational points satisfy the exact binary equation. -/
theorem rational_nonexceptional_second_parabolic_model
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ)
    (hA : A ≠ 0) (ha : a ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : curveQuadratic (ρ : ℚ) u v ρ' u' v' ∈ I)
    (hg : curveEquation (ρ : ℚ) u v ρ' u' v' A a ∈ I)
    (n0 n1 n2 e : ℚ) (hn1 : n1 ≠ 0)
    (hplane : C n0 * X 0 + C n1 * X 1 + C n2 * X 2 + C e ∈ I)
    {N : ℕ} {b : ℤ}
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = 2 * n + b)
    (x : Fin 3 → ℚ) (hx : x ∈ coordinateZeroLocus I) :
    let c := rationalSecondPlaneConicCoefficients ρ u v ρ' u' v' n0 n1 n2 e
    c 0 ≠ 0 ∧ (c 1) ^ 2 - 4 * c 0 * c 2 = 0 ∧
      2 * c 1 * c 3 - 4 * c 0 * c 4 ≠ 0 ∧
      secondPlaneConicPolynomial c ∈ I ∧
      ∀ y ∈ coordinateZeroLocus I,
        conicValue (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (y 2) (y 0) = 0 := by
  let c := rationalSecondPlaneConicCoefficients ρ u v ρ' u' v' n0 n1 n2 e
  have hgeom := rational_nonexceptional_conic_plane_geometry_second hρ hu hv hne
    ρ' u' v' A a hA ha I hf hg n0 n1 n2 e hn1 hplane hdegree
  have hα : c 0 ≠ 0 := hgeom.1
  have hΔ : (c 1) ^ 2 - 4 * c 0 * c 2 = 0 := hgeom.2.1
  have hf' := hf
  rw [curveQuadratic, lineQuadratic_eq_ternary] at hf'
  have hc : secondPlaneConicPolynomial c ∈ I :=
    secondPlaneConicPolynomial_mem I _ _ _ _ _ _ n0 n2 n1 e hn1 hf' (by
      convert hplane using 1
      ring)
  have hpoints : ∀ y ∈ coordinateZeroLocus I,
      conicValue (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (y 2) (y 0) = 0 := by
    intro y hy
    exact (eval_secondPlaneConicPolynomial c y).symm.trans (hy _ hc)
  have hc' : secondPlaneConicPolynomial ![c 0, c 1, c 2, c 3, c 4, c 5] ∈ I := by
    have he : ![c 0, c 1, c 2, c 3, c 4, c 5] = c := by ext j; fin_cases j <;> rfl
    rw [he]
    exact hc
  exact ⟨hα, hΔ, second_parabola_denominator_ne_zero_of_no_line I _ _ _ _ _ _ hα hΔ hc'
    (x 2) (x 0) (hpoints x hx) hgeom.2.2, hc, hpoints⟩

end
end PierceLengthBound.FixedDividend
