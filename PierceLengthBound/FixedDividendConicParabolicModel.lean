/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendConicPlaneModel
public import PierceLengthBound.FixedDividendRationalConicDiscriminant

/-!
# Rational parabolic plane models

The coefficients below restrict the fixed-dividend quadratic to a
containing plane. For a nonexceptional component of Hilbert degree two with a
rational point, both denominators required for parabolic reconstruction are
nonzero. The only coordinate choice is a nonzero third or second plane
coefficient; the second chart is the first with the last two coordinates
exchanged.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- Exact binary coefficients obtained by eliminating the third node. -/
def rationalPlaneConicCoefficients (ρ u v ρ' u' v' n0 n1 n2 e : ℚ) : Fin 6 → ℚ :=
  planeConicCoefficients (-ρ - u) (u - v) (v - 1)
    (ρ - (-ρ - u) - ρ' - (-ρ - u) * (v - 1 - v'))
    ((-ρ - u) - (u - v) + ρ' + u' - (u - v) * (v - 1 - v'))
    ((u - v) - (v - 1) - u' + v' - (v - 1) * (v - 1 - v'))
    (-n0 / n2) (-n1 / n2) (-e / n2)

/-- Evaluating the plane conic polynomial gives the binary conic value. -/
lemma eval_planeConicPolynomial {K : Type*} [CommRing K] (c : Fin 6 → K)
    (x : Fin 3 → K) :
    eval x (planeConicPolynomial c) =
      conicValue (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (x 1) (x 0) := by
  simp [planeConicPolynomial, conicValue]

/-- A prime nonexceptional component of Hilbert degree two in a plane with `n2 ≠ 0`
has a nondegenerate parabolic plane model; its points satisfy the binary equation. -/
theorem nonexceptional_parabolic_model
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ)
    (hA : A ≠ 0) (ha : a ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : curveQuadratic (ρ : ℚ) u v ρ' u' v' ∈ I)
    (hg : curveEquation (ρ : ℚ) u v ρ' u' v' A a ∈ I)
    (n0 n1 n2 e : ℚ) (hn2 : n2 ≠ 0)
    (hplane : C n0 * X 0 + C n1 * X 1 + C n2 * X 2 + C e ∈ I)
    {N : ℕ} {b : ℤ}
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = 2 * n + b)
    (x : Fin 3 → ℚ) (hx : x ∈ coordinateZeroLocus I) :
    let c := rationalPlaneConicCoefficients ρ u v ρ' u' v' n0 n1 n2 e
    c 0 ≠ 0 ∧ (c 1) ^ 2 - 4 * c 0 * c 2 = 0 ∧
      2 * c 1 * c 3 - 4 * c 0 * c 4 ≠ 0 ∧
      planeConicPolynomial c ∈ I ∧
      ∀ y ∈ coordinateZeroLocus I,
        conicValue (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (y 1) (y 0) = 0 := by
  let c := rationalPlaneConicCoefficients ρ u v ρ' u' v' n0 n1 n2 e
  have hgeom := nonexceptional_conic_plane_geometry hρ hu hv hne
    ρ' u' v' A a hA ha I hf hg n0 n1 n2 e hn2 hplane hdegree
  have hα : c 0 ≠ 0 := hgeom.1
  have hΔ : (c 1) ^ 2 - 4 * c 0 * c 2 = 0 := hgeom.2.1
  have hf' := hf
  rw [curveQuadratic, lineQuadratic_eq_ternary] at hf'
  have hc : planeConicPolynomial c ∈ I :=
    planeConicPolynomial_mem I _ _ _ _ _ _ n0 n1 n2 e hn2 hf' hplane
  have hpoints : ∀ y ∈ coordinateZeroLocus I,
      conicValue (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (y 1) (y 0) = 0 := by
    intro y hy
    exact (eval_planeConicPolynomial c y).symm.trans (hy _ hc)
  have hc' : planeConicPolynomial ![c 0, c 1, c 2, c 3, c 4, c 5] ∈ I := by
    have he : ![c 0, c 1, c 2, c 3, c 4, c 5] = c := by ext j; fin_cases j <;> rfl
    rw [he]
    exact hc
  exact ⟨hα, hΔ, parabola_denominator_ne_zero_of_no_line I _ _ _ _ _ _ hα hΔ hc'
    (x 1) (x 0) (hpoints x hx) hgeom.2.2, hc, hpoints⟩

/-- Exact binary coefficients obtained by eliminating the second node. -/
def rationalSecondPlaneConicCoefficients (ρ u v ρ' u' v' n0 n1 n2 e : ℚ) : Fin 6 → ℚ :=
  planeConicCoefficients (-ρ - u) (v - 1) (u - v)
    (ρ - (-ρ - u) - ρ' - (-ρ - u) * (v - 1 - v'))
    ((u - v) - (v - 1) - u' + v' - (v - 1) * (v - 1 - v'))
    ((-ρ - u) - (u - v) + ρ' + u' - (u - v) * (v - 1 - v'))
    (-n0 / n1) (-n2 / n1) (-e / n1)

/-- Exchanging the last two coordinates of a ternary quadratic. -/
lemma rename_swap_ternaryQuadratic {K : Type*} [CommRing K] (a b c l0 l1 l2 : K) :
    rename (Equiv.swap (1 : Fin 3) 2) (ternaryQuadratic a b c l0 l1 l2) =
      ternaryQuadratic a c b l0 l2 l1 := by
  simp only [ternaryQuadratic, map_add, map_mul, map_pow, rename_C, rename_X,
    Equiv.swap_apply_left, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)]
  ring

/-- The complementary parabolic plane model, eliminating the second node. It is
the first model for the ideal with its last two coordinates exchanged. -/
theorem nonexceptional_second_parabolic_model
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
      rename (Equiv.swap 1 2) (planeConicPolynomial c) ∈ I ∧
      ∀ y ∈ coordinateZeroLocus I,
        conicValue (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (y 2) (y 0) = 0 := by
  let c := rationalSecondPlaneConicCoefficients ρ u v ρ' u' v' n0 n1 n2 e
  let J := I.comap (rename (Equiv.swap (1 : Fin 3) 2))
  have hgeom := nonexceptional_second_conic_plane_geometry hρ hu hv hne
    ρ' u' v' A a hA ha I hf hg n0 n1 n2 e hn1 hplane hdegree
  have hswap (y : Fin 3 → ℚ) : y ∘ Equiv.swap 1 2 = ![y 0, y 2, y 1] := by
    funext j
    fin_cases j <;> rfl
  have hf' := hf
  rw [curveQuadratic, lineQuadratic_eq_ternary, ← rename_swap_ternaryQuadratic] at hf'
  have hc : planeConicPolynomial c ∈ J :=
    planeConicPolynomial_mem J _ _ _ _ _ _ n0 n2 n1 e hn1 hf' (by
      change rename _ _ ∈ I
      convert hplane using 1
      simp only [map_add, map_mul, rename_C, rename_X, Equiv.swap_apply_left,
        Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)]
      ring)
  have hpoints : ∀ y ∈ coordinateZeroLocus I,
      conicValue (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (y 2) (y 0) = 0 := by
    intro y hy
    have hh := hy _ hc
    rw [eval_rename, eval_planeConicPolynomial, hswap] at hh
    exact hh
  have hline : ∀ a0 a1 c : ℚ, a1 ≠ 0 → C a0 * X 0 + C a1 * X 1 + C c ∉ J := by
    intro a0 a1 c ha1 hm
    apply hgeom.2.2 a0 a1 c ha1
    change rename _ _ ∈ I at hm
    simpa only [map_add, map_mul, rename_C, rename_X, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 3) ≠ 1)
        (by decide : (0 : Fin 3) ≠ 2)] using hm
  have hc' : planeConicPolynomial ![c 0, c 1, c 2, c 3, c 4, c 5] ∈ J := by
    have he : ![c 0, c 1, c 2, c 3, c 4, c 5] = c := by ext j; fin_cases j <;> rfl
    rw [he]
    exact hc
  exact ⟨hgeom.1, hgeom.2.1, parabola_denominator_ne_zero_of_no_line J _ _ _ _ _ _
    hgeom.1 hgeom.2.1 hc' (x 2) (x 0) (hpoints x hx) hline, hc, hpoints⟩

end
end PierceLengthBound.FixedDividend
