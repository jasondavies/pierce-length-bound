/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionCurveInitial
public import PierceLengthBound.PolarProjectionBaseMultiplicity

/-! The rational independence certificate applies to actual smooth formal
sections, including their higher-order Hensel corrections. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Polynomial Matrix
noncomputable section

set_option maxHeartbeats 1200000 in
-- The cubic norm contains nested products whose linear coefficient is expanded here.
theorem polar_certificate_formal_norm_linear (x : Fin 3 → PowerSeries ℚ) (s t : ℚ)
    (hx0 : ∀ j, PowerSeries.constantCoeff (x j) = ![-1 / 7, -3 / 28, -1 / 2] j)
    (hx1 : ∀ j, PowerSeries.coeff 1 (x j) = ![(9 * s - 5 * t) / 4, s, t] j) :
    PowerSeries.coeff 1 (lineNorm
      (PowerSeries.C 2) (PowerSeries.C 5) (PowerSeries.C (-3))
      (PowerSeries.C 3) (PowerSeries.C 6) (PowerSeries.C (-5))
      (x 0) (x 0 + x 1) (x 0 + x 1 + x 2)) = polarCertificateNormLinear s t := by
  norm_num [lineNorm, lineNodes, extendedLineGaps, lineGaps, fourthNode, coeffs,
    Fin.sum_univ_succ, PowerSeries.coeff_one_mul, PowerSeries.coeff_one_pow,
    hx0, hx1, polarCertificateNormLinear, map_ofNat]
  ring

set_option maxHeartbeats 1200000 in
-- The monomial coefficients are obtained from the Newton remainder before taking first jets.
theorem polar_certificate_formal_remainder_linear (x : Fin 3 → PowerSeries ℚ) (s t : ℚ)
    (hx0 : ∀ j, PowerSeries.constantCoeff (x j) = ![-1 / 7, -3 / 28, -1 / 2] j)
    (hx1 : ∀ j, PowerSeries.coeff 1 (x j) = ![(9 * s - 5 * t) / 4, s, t] j) :
    let nodes := completeNodes (PowerSeries.C 2) (PowerSeries.C 5) (PowerSeries.C (-3))
      ![x 0, x 0 + x 1, x 0 + x 1 + x 2]
    let rem := polarRemainderMonomialCoeffs
      (PowerSeries.C 2) (PowerSeries.C 5) (PowerSeries.C (-3))
      (PowerSeries.C 3) (PowerSeries.C 6) (PowerSeries.C (-5)) nodes
    polarCubic (fun j => PowerSeries.coeff 1 (rem j)) = polarCertificateRemainder s t := by
  dsimp only
  have htwo : PowerSeries.coeff 1 (2 : PowerSeries ℚ) = 0 := by
    rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 from (map_ofNat PowerSeries.C 2).symm]
    simp
  have hthree : PowerSeries.coeff 1 (3 : PowerSeries ℚ) = 0 := by
    rw [show (3 : PowerSeries ℚ) = PowerSeries.C 3 from (map_ofNat PowerSeries.C 3).symm]
    simp
  have hr : (fun j => PowerSeries.coeff 1 (polarRemainderMonomialCoeffs
      (PowerSeries.C 2) (PowerSeries.C 5) (PowerSeries.C (-3))
      (PowerSeries.C 3) (PowerSeries.C 6) (PowerSeries.C (-5))
      (completeNodes (PowerSeries.C 2) (PowerSeries.C 5) (PowerSeries.C (-3))
        ![x 0, x 0 + x 1, x 0 + x 1 + x 2]) j)) =
      ![(77 * s + 7 * t) / 14, (-56 * s - 124 * t) / 14,
        (-45 * s + 157 * t) / 14, (28 * s - 28 * t) / 14] := by
    funext j
    fin_cases j <;>
      norm_num [polarRemainderMonomialCoeffs, polarRemainderCoefficients,
        polarQuotientConstant, completeNodes, fourthNode, PowerSeries.coeff_one_mul,
        PowerSeries.coeff_one_pow, hx0, hx1, map_ofNat, htwo, hthree] <;> ring
  rw [hr]
  rfl

set_option maxHeartbeats 800000 in
-- The actual curve equation contains the quartic resultant as a nested polynomial expression.
/-- For every nonzero leading label and every dividend, the rational
certificate admits a smooth formal section whose actual curve equation has
colength four. This uses the constructed Hensel section, not its tangent line. -/
theorem exists_polar_certificate_section_colength_four (A b : ℚ) (hA : A ≠ 0) :
    ∃ (s t : ℚ) (x : Fin 3 → PowerSeries ℚ),
      (∀ j, PowerSeries.constantCoeff (x j) = ![-1 / 7, -3 / 28, -1 / 2] j) ∧
      (∀ j, PowerSeries.coeff 1 (x j) = ![(9 * s - 5 * t) / 4, s, t] j) ∧
      lineQuadratic (PowerSeries.C 2) (PowerSeries.C 5) (PowerSeries.C (-3))
        (PowerSeries.C 3) (PowerSeries.C 6) (PowerSeries.C (-5))
        (x 0) (x 0 + x 1) (x 0 + x 1 + x 2) = 0 ∧
      Module.finrank ℚ (PowerSeries ℚ ⧸ Ideal.span
        {MvPolynomial.eval ![x 0, x 0 + x 1, x 0 + x 1 + x 2]
          (curveEquation (PowerSeries.C 2) (PowerSeries.C 5) (PowerSeries.C (-3))
            (PowerSeries.C 3) (PowerSeries.C 6) (PowerSeries.C (-5))
            (PowerSeries.C A) (PowerSeries.C b))}) = 4 := by
  obtain ⟨s, t, hfirst⟩ := polarCertificate_initial_nonzero A b hA
  have hG : (polarMatrix (2 : ℚ) 5 (-3)).det ≠ 0 := by rw [polarMatrix_det]; norm_num
  obtain ⟨x, hx0, hx1, hq, _, _⟩ := exists_polar_formal_section
    (2 : ℚ) 5 (-3) 3 6 (-5) hG
    (by norm_num [polarMatrix]) (by norm_num [polarLinear]) s t
  have hx0' : ∀ j, PowerSeries.constantCoeff (x j) = ![-1 / 7, -3 / 28, -1 / 2] j := by
    simpa only [polarBasePoint_certificate] using hx0
  have hx1' : ∀ j, PowerSeries.coeff 1 (x j) = ![(9 * s - 5 * t) / 4, s, t] j := by
    intro j
    rw [hx1 j]
    fin_cases j <;> norm_num [polarTangentDirection, polarLinear]
    ring
  have he := polar_curve_formal_initial (2 : ℚ) 5 (-3) 3 6 (-5) A b hG
    (by norm_num) (by norm_num) (by norm_num) x hx0
  dsimp only at he
  rw [← polarCertificateQuartic_eq_newton,
    polar_certificate_formal_remainder_linear x s t hx0' hx1'] at he
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at he
  rw [polar_certificate_formal_norm_linear x s t hx0' hx1'] at he
  refine ⟨s, t, x, hx0', hx1', hq, ?_⟩
  exact formal_section_colength_of_coefficients _ 4 he.1 (he.2 ▸ hfirst)

end
end PierceLengthBound.FixedDividend
