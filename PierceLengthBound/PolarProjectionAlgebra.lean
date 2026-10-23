/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendLines
public import PierceLengthBound.JointLiftAlgebra

/-! The exact affine polar map of the fixed-dividend quadric, in gap coordinates.
The polynomial identities are valid over every commutative ring. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Matrix Finset

/-- Matrix of the quadratic part in the first three gap coordinates. -/
def polarMatrix {R : Type*} [CommRing R] (ρ u v : R) : Matrix (Fin 3) (Fin 3) R :=
  !![ρ * (ρ + 1), -ρ * (u - 1), -ρ * (v - 1);
     -ρ * (u - 1), u * (u - 1), u * (v - 1);
     -ρ * (v - 1), u * (v - 1), v * (v - 1)]

/-- Linear part of the fixed-dividend quadric in gap coordinates. -/
def polarLinear {R : Type*} [CommRing R] (ρ u v ρ' u' v' : R) : Fin 3 → R :=
  ![ρ * (v - v'), ρ' - ρ - u * (v - v'), u - u' - v * (v - v')]

/-- The affine-linear polar direction `G x + ℓ`. -/
def polarVector {R : Type*} [CommRing R] (ρ u v ρ' u' v' : R) (x : Fin 3 → R) : Fin 3 → R :=
  polarMatrix ρ u v *ᵥ x + polarLinear ρ u v ρ' u' v'

/-- The quadric is exactly `x · (G x + ℓ)`; `lineQuadratic` uses cumulative nodes. -/
theorem polarVector_dot_gaps {R : Type*} [CommRing R] (ρ u v ρ' u' v' : R)
    (x : Fin 3 → R) :
    ∑ j, x j * polarVector ρ u v ρ' u' v' x j =
      lineQuadratic ρ u v ρ' u' v' (x 0) (x 0 + x 1) (x 0 + x 1 + x 2) := by
  simp [polarVector, polarMatrix, polarLinear, dotProduct,
    Fin.sum_univ_succ, lineQuadratic, lineNodes, lineGaps, fourthNode, coeffs]
  ring

/-- Exact Taylor expansion of the quadric in an arbitrary gap direction. The
linear term identifies its gradient as `2 G x + ℓ`. -/
theorem polarQuadric_translate {R : Type*} [CommRing R] (ρ u v ρ' u' v' t : R)
    (x y : Fin 3 → R) :
    (∑ j, (x j + t * y j) * polarVector ρ u v ρ' u' v' (x + t • y) j) =
      (∑ j, x j * polarVector ρ u v ρ' u' v' x j) +
        t * (∑ j, y j *
          (2 * (polarMatrix ρ u v *ᵥ x) j + polarLinear ρ u v ρ' u' v' j)) +
        t ^ 2 * (∑ j, y j * (polarMatrix ρ u v *ᵥ y) j) := by
  simp [polarVector, polarMatrix, polarLinear, dotProduct, Fin.sum_univ_succ]
  ring

/-- The quadratic part is nonsingular whenever the four displayed factors are nonzero. -/
theorem polarMatrix_det {R : Type*} [CommRing R] (ρ u v : R) :
    (polarMatrix ρ u v).det = ρ * (ρ + u) * (u - v) * (v - 1) := by
  simp [polarMatrix, Matrix.det_fin_three]
  ring

/-- The actual pattern signs force an invertible polar matrix. -/
theorem polarMatrix_det_ne_zero {ρ u v : ℝ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0) :
    (polarMatrix ρ u v).det ≠ 0 := by
  rw [polarMatrix_det]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by linarith) (by linarith))
    (by linarith)) (by linarith)

/-- Pairing the polar direction with the quadratic moment row gives the cubic norm,
modulo the defining quadric. This is an identity before imposing any curve equation. -/
theorem polarVector_dot_moment_sub_norm {R : Type*} [CommRing R]
    (ρ u v ρ' u' v' : R) (x : Fin 3 → R) :
    let k := lineGaps ρ u v ρ' u' v' (x 0) (x 0 + x 1) (x 0 + x 1 + x 2)
    let s := lineNodes ρ u v ρ' u' v' (x 0) (x 0 + x 1) (x 0 + x 1 + x 2)
    (∑ j : Fin 3, polarVector ρ u v ρ' u' v' x j *
      (k j.castSucc.castSucc * (s j.castSucc.castSucc.castSucc + s j.succ.castSucc.castSucc) +
        k j.succ.castSucc)) -
      lineNorm ρ u v ρ' u' v' (x 0) (x 0 + x 1) (x 0 + x 1 + x 2) =
      -(s 4 + 1 + v - v') *
        lineQuadratic ρ u v ρ' u' v' (x 0) (x 0 + x 1) (x 0 + x 1 + x 2) := by
  simp [polarVector, polarMatrix, polarLinear, dotProduct,
    Fin.sum_univ_succ, lineNorm, lineQuadratic, lineNodes, extendedLineGaps,
    lineGaps, fourthNode, coeffs]
  ring

/-- The mixed moment is the polarization of the quadric, with its full linear term. -/
theorem polarVector_dot_row {R : Type*} [CommRing R]
    (ρ u v ρ' u' v' : R) (x d : Fin 3 → R) :
    ∑ j, d j * polarVector ρ u v ρ' u' v' x j =
      ∑ j : Fin 5, coeffs ρ u v j *
        (lineNodes ρ u v ρ' u' v' (x 0) (x 0 + x 1) (x 0 + x 1 + x 2) j.castSucc *
          lineNodes ρ u v ρ' u' v' (d 0) (d 0 + d 1) (d 0 + d 1 + d 2) j.castSucc +
          lineGaps ρ u v ρ' u' v' (d 0) (d 0 + d 1) (d 0 + d 1 + d 2) j) := by
  simp [polarVector, polarMatrix, polarLinear, dotProduct,
    Fin.sum_univ_succ, lineNodes, lineGaps, fourthNode, coeffs]
  ring

/-- A vector annihilating the first two rows is recovered from its pairing with
an independent third row. This is the denominator-free scalar determination. -/
theorem polar_curvature_scalar_identity {R : Type*} [CommRing R]
    (d k r V : Fin 3 → R)
    (hd : ∑ j, d j * V j = 0) (hk : ∑ j, k j * V j = 0) :
    ∀ j, (∑ l, V l * r l) * curvatureVector d k j =
      (Matrix.of ![d, k, r]).det * V j := by
  simp only [Fin.sum_univ_three] at hd hk
  intro j
  fin_cases j <;> simp [Fin.sum_univ_three, curvatureVector, Matrix.det_fin_three]
  · linear_combination (k 2 * r 1 - k 1 * r 2) * hd + (d 1 * r 2 - d 2 * r 1) * hk
  · linear_combination (k 0 * r 2 - k 2 * r 0) * hd + (d 2 * r 0 - d 0 * r 2) * hk
  · linear_combination (k 1 * r 0 - k 0 * r 1) * hd + (d 0 * r 1 - d 1 * r 0) * hk

end PierceLengthBound.FixedDividend
