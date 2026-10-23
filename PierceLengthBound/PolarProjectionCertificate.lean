/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionNewton

/-! Exact rational certificate for the quartic initial forms at the polar base point.
This module certifies the polynomial computations; it does not assume a theorem
identifying a local initial form with the degree of a divisor on the normalization. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Polynomial Matrix
noncomputable section

/-- The current Newton quartic at the rational certificate's polar base point. -/
def polarCertificateQuartic : ℚ[X] :=
  monicQuartic ![2, -669 / 112, 757 / 112, -20 / 7]

/-- The first-order remainder along the tangent vector `((9s-5t)/4,s,t)`. -/
def polarCertificateRemainder (s t : ℚ) : ℚ[X] :=
  C ((77 * s + 7 * t) / 14) + C ((-56 * s - 124 * t) / 14) * X +
    C ((-45 * s + 157 * t) / 14) * X ^ 2 + C ((28 * s - 28 * t) / 14) * X ^ 3

/-- The linear part of the cubic norm on the certificate's tangent plane. -/
def polarCertificateNormLinear (s t : ℚ) : ℚ := (3 * s + 85 * t) / 28

/-- The quartic resultant of the specialized quartic and first-order remainder. -/
def polarCertificateInitialResultant (s t : ℚ) : ℚ :=
  resultant polarCertificateQuartic (polarCertificateRemainder s t) 4 4

lemma polarCertificateQuartic_eq_newton :
    polarCertificateQuartic =
      firstNewtonQuartic (fun j : Fin 4 => coeffs (2 : ℚ) 5 (-3) j.castSucc)
        (polarBaseNodes (2 : ℚ) 5 (-3) 3 6 (-5)) := by
  rw [polarCertificateQuartic, firstNewtonQuartic_eq]
  congr 1
  ext j
  fin_cases j <;> norm_num [firstNewtonCoeffs, polarBaseNodes, coeffs]

/-- Exact expansion of the quartic resultant in the two tangent parameters. -/
theorem polarCertificateInitialResultant_formula (s t : ℚ) :
    polarCertificateInitialResultant s t =
      (32233977 * s ^ 4 - 95047956 * s ^ 3 * t + 147873750 * s ^ 2 * t ^ 2 -
        111199572 * s * t ^ 3 + 31702169 * t ^ 4) / 6272 := by
  let a : Fin 4 → ℚ := ![2, -669 / 112, 757 / 112, -20 / 7]
  let b : Fin 4 → ℚ :=
    ![2 + (77 * s + 7 * t) / 14, -669 / 112 + (-56 * s - 124 * t) / 14,
      757 / 112 + (-45 * s + 157 * t) / 14, -20 / 7 + (28 * s - 28 * t) / 14]
  have hb : monicQuartic b = polarCertificateRemainder s t + monicQuartic a * 1 := by
    simp [monicQuartic, a, b, polarCertificateRemainder]
    ring
  have he : polarCertificateInitialResultant s t = (quarticBezout a b).det := by
    unfold polarCertificateInitialResultant polarCertificateQuartic
    change resultant (monicQuartic a) (polarCertificateRemainder s t) 4 4 = _
    rw [← resultant_add_mul_right (monicQuartic a) (polarCertificateRemainder s t) 1 4 4
      (by simp) (by rw [monicQuartic_natDegree]), ← hb, resultant_monicQuartic]
  rw [he]
  norm_num [a, b, quarticBezout, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix_apply, Fin.succAbove]
  ring

/-- The displayed rational minor is nonzero, so the two quartics are independent. -/
theorem polarCertificate_initial_minor :
    polarCertificateInitialResultant 1 0 * polarCertificateNormLinear 0 1 ^ 4 -
      polarCertificateInitialResultant 0 1 * polarCertificateNormLinear 1 0 ^ 4 =
        26291112152499 / 60236288 := by
  rw [polarCertificateInitialResultant_formula, polarCertificateInitialResultant_formula]
  norm_num [polarCertificateNormLinear]

/-- A nonzero two-axis minor supplies one of two coordinate hyperplane
sections for every dividend. No general hyperplane coordinate change is needed. -/
theorem polar_initial_axes_nonzero {K : Type*} [CommRing K] [IsDomain K]
    (N₀ N₁ D₀ D₁ A b : K) (hA : A ≠ 0)
    (hminor : N₀ * D₁ ^ 4 - N₁ * D₀ ^ 4 ≠ 0) :
    A * N₀ - b * D₀ ^ 4 ≠ 0 ∨ A * N₁ - b * D₁ ^ 4 ≠ 0 := by
  by_contra! h
  apply mul_ne_zero hA hminor
  linear_combination D₁ ^ 4 * h.1 - D₀ ^ 4 * h.2

end
end PierceLengthBound.FixedDividend
