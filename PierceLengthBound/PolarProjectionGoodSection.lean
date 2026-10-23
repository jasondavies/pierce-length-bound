/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import PierceLengthBound.PolarProjectionExceptionalPolynomial

/-! Every pattern outside the fixed exceptional hypersurface has an actual
smooth coordinate-axis section with a nonzero quartic initial coefficient. -/
@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

theorem polarChartGuard_conditions {q : Fin 6 → ℚ} (h : polarChartGuard q ≠ 0) :
    -q 0 - q 1 ≠ 0 ∧ q 1 - q 2 ≠ 0 ∧ q 2 - 1 ≠ 0 ∧
      (polarMatrix (q 0) (q 1) (q 2)).det ≠ 0 ∧
      polarMatrix (q 0) (q 1) (q 2) 0 0 ≠ 0 ∧
      polarLinear (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) 0 ≠ 0 := by
  simpa only [polarChartGuard, mul_ne_zero_iff, and_assoc] using h

/-- The fixed rational initial expressions apply to every formal section
with the prescribed tangent direction, including its higher-order corrections. -/
theorem polar_curve_initial_of_jets (q : Fin 6 → ℚ)
    (hguard : polarChartGuard q ≠ 0) (A b s t : ℚ)
    (x : Fin 3 → PowerSeries ℚ)
    (hx0 : ∀ j, PowerSeries.constantCoeff (x j) =
      polarBasePoint (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) j)
    (hx1 : ∀ j, PowerSeries.coeff 1 (x j) =
      polarTangentDirection (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) s t j) :
    let E := MvPolynomial.eval ![x 0, x 0 + x 1, x 0 + x 1 + x 2]
      (curveEquation (PowerSeries.C (q 0)) (PowerSeries.C (q 1)) (PowerSeries.C (q 2))
        (PowerSeries.C (q 3)) (PowerSeries.C (q 4)) (PowerSeries.C (q 5))
        (PowerSeries.C A) (PowerSeries.C b))
    (∀ k < 4, PowerSeries.coeff k E = 0) ∧
      PowerSeries.coeff 4 E = A * polarInitialResultant q s t - b * polarInitialNorm q s t ^ 4 := by
  obtain ⟨h1, h2, h3, hG, _, _⟩ := polarChartGuard_conditions hguard
  have hz (j : Fin 3) : PowerSeries.constantCoeff (x j) =
      PowerSeries.constantCoeff (polarStraightGapPath q s t j) := by
    simp only [polarStraightGapPath, map_add, PowerSeries.constantCoeff_C, map_mul,
      PowerSeries.constantCoeff_X, mul_zero, add_zero, hx0,
      polarBaseGaps_eq_basePoint _ _ _ _ _ _ hG h1 h2 h3]
  have ho (j : Fin 3) : PowerSeries.coeff 1 (x j) =
      PowerSeries.coeff 1 (polarStraightGapPath q s t j) := by
    simp [polarStraightGapPath, hx1]
  have hr := fun j => polar_formal_remainder_linear_eq_of_jets
    (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) x (polarStraightGapPath q s t) hz ho j
  have hD := polar_formal_norm_linear_eq_of_jets
    (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) x (polarStraightGapPath q s t) hz ho
  have he := polar_curve_formal_initial (q 0) (q 1) (q 2) (q 3) (q 4) (q 5)
    A b hG h1 h2 h3 x hx0
  dsimp only at he ⊢
  refine ⟨he.1, he.2.trans ?_⟩
  exact congrArg₂ (fun r D => A * Polynomial.resultant
    (firstNewtonQuartic (fun j : Fin 4 => coeffs (q 0) (q 1) (q 2) j.castSucc)
      (polarBaseNodes (q 0) (q 1) (q 2) (q 3) (q 4) (q 5))) (polarCubic r) 4 4 -
        b * D ^ 4) (funext hr) hD

/-- One of the two coordinate-axis sections has order exactly four, uniformly
for every dividend and every nonzero leading minor. The section is constructed. -/
theorem polar_good_axis_formal_section (q : Fin 6 → ℚ)
    (hguard : polarChartGuard q ≠ 0) (hminor : polarInitialMinor q ≠ 0)
    (A b : ℚ) (hA : A ≠ 0) :
    ∃ (s t : ℚ) (x : Fin 3 → PowerSeries ℚ),
      ((s = 1 ∧ t = 0) ∨ (s = 0 ∧ t = 1)) ∧
      (∀ j, PowerSeries.constantCoeff (x j) =
        polarBasePoint (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) j) ∧
      (∀ j, PowerSeries.coeff 1 (x j) =
        polarTangentDirection (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) s t j) ∧
      lineQuadratic (PowerSeries.C (q 0)) (PowerSeries.C (q 1)) (PowerSeries.C (q 2))
        (PowerSeries.C (q 3)) (PowerSeries.C (q 4)) (PowerSeries.C (q 5))
        (x 0) (x 0 + x 1) (x 0 + x 1 + x 2) = 0 ∧
      x 1 = PowerSeries.C (polarBasePoint (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) 1) +
        PowerSeries.C s * PowerSeries.X ∧
      x 2 = PowerSeries.C (polarBasePoint (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) 2) +
        PowerSeries.C t * PowerSeries.X ∧
      let E := MvPolynomial.eval ![x 0, x 0 + x 1, x 0 + x 1 + x 2]
        (curveEquation (PowerSeries.C (q 0)) (PowerSeries.C (q 1)) (PowerSeries.C (q 2))
          (PowerSeries.C (q 3)) (PowerSeries.C (q 4)) (PowerSeries.C (q 5))
          (PowerSeries.C A) (PowerSeries.C b))
      (∀ k < 4, PowerSeries.coeff k E = 0) ∧ PowerSeries.coeff 4 E ≠ 0 := by
  obtain ⟨_, _, _, hG, h00, hℓ⟩ := polarChartGuard_conditions hguard
  have haxis := polar_initial_axes_nonzero
    (polarInitialResultant q 1 0) (polarInitialResultant q 0 1)
    (polarInitialNorm q 1 0) (polarInitialNorm q 0 1) A b hA hminor
  have hex : ∃ s t : ℚ, ((s = 1 ∧ t = 0) ∨ (s = 0 ∧ t = 1)) ∧
      A * polarInitialResultant q s t - b * polarInitialNorm q s t ^ 4 ≠ 0 := by
    rcases haxis with h | h
    · exact ⟨1, 0, Or.inl ⟨rfl, rfl⟩, h⟩
    · exact ⟨0, 1, Or.inr ⟨rfl, rfl⟩, h⟩
  obtain ⟨s, t, haxis, hn⟩ := hex
  obtain ⟨x, hx0, hx1, hq, hxs, hxt⟩ := exists_polar_formal_section
    (q 0) (q 1) (q 2) (q 3) (q 4) (q 5) hG h00 hℓ s t
  obtain ⟨hlower, hfirst⟩ := polar_curve_initial_of_jets q hguard A b s t x hx0 hx1
  exact ⟨s, t, x, haxis, hx0, hx1, hq, hxs, hxt, hlower, hfirst ▸ hn⟩

end
end PierceLengthBound.FixedDividend
