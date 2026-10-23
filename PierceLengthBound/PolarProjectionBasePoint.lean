/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionAlgebra
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The unique affine base point of the exact polar map. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Matrix Finset
noncomputable section

/-- The unique base point of the three affine polar coordinates when `G` is invertible. -/
def polarBasePoint {K : Type*} [Field K] (ρ u v ρ' u' v' : K) : Fin 3 → K :=
  -((polarMatrix ρ u v)⁻¹ *ᵥ polarLinear ρ u v ρ' u' v')

lemma polarBasePoint_polarVector {K : Type*} [Field K] (ρ u v ρ' u' v' : K)
    (hG : (polarMatrix ρ u v).det ≠ 0) :
    polarVector ρ u v ρ' u' v' (polarBasePoint ρ u v ρ' u' v') = 0 := by
  simp [polarVector, polarBasePoint, mulVec_neg, mulVec_mulVec,
    mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG)]

/-- The common zero of the polar coordinates is unique. -/
theorem polarVector_eq_zero_iff {K : Type*} [Field K] (ρ u v ρ' u' v' : K)
    (hG : (polarMatrix ρ u v).det ≠ 0) (x : Fin 3 → K) :
    polarVector ρ u v ρ' u' v' x = 0 ↔ x = polarBasePoint ρ u v ρ' u' v' := by
  constructor
  · intro hx
    apply Matrix.mulVec_injective_of_det_ne_zero hG
    apply add_right_cancel (b := polarLinear ρ u v ρ' u' v')
    exact hx.trans (polarBasePoint_polarVector ρ u v ρ' u' v' hG).symm
  · rintro rfl
    exact polarBasePoint_polarVector ρ u v ρ' u' v' hG

/-- The common zero of the homogenized polar coordinates is the line through
the affine base point. In particular no projective base point lies at infinity. -/
theorem polarHomogeneousVector_eq_zero_iff {K : Type*} [Field K]
    (ρ u v ρ' u' v' : K) (hG : (polarMatrix ρ u v).det ≠ 0)
    (x : Fin 3 → K) (w : K) :
    polarMatrix ρ u v *ᵥ x + w • polarLinear ρ u v ρ' u' v' = 0 ↔
      x = w • polarBasePoint ρ u v ρ' u' v' := by
  have hbase : polarMatrix ρ u v *ᵥ (w • polarBasePoint ρ u v ρ' u' v') +
      w • polarLinear ρ u v ρ' u' v' = 0 := by
    rw [mulVec_smul, ← smul_add]
    change w • polarVector ρ u v ρ' u' v'
      (polarBasePoint ρ u v ρ' u' v') = 0
    rw [polarBasePoint_polarVector ρ u v ρ' u' v' hG, smul_zero]
  constructor
  · intro hx
    apply Matrix.mulVec_injective_of_det_ne_zero hG
    exact add_right_cancel (hx.trans hbase.symm)
  · rintro rfl
    exact hbase

/-- At infinity the only zero of the three homogeneous coordinates is the
zero vector, which represents no projective point. -/
theorem polarHomogeneousVector_at_infinity {K : Type*} [Field K]
    (ρ u v ρ' u' v' : K) (hG : (polarMatrix ρ u v).det ≠ 0)
    (x : Fin 3 → K) :
    polarMatrix ρ u v *ᵥ x = 0 ↔ x = 0 := by
  simpa using polarHomogeneousVector_eq_zero_iff ρ u v ρ' u' v' hG x 0

/-- The quadric's gradient at the base point is minus its linear part. -/
theorem polarBasePoint_gradient {K : Type*} [Field K] (ρ u v ρ' u' v' : K)
    (hG : (polarMatrix ρ u v).det ≠ 0) :
    (2 : K) • (polarMatrix ρ u v *ᵥ polarBasePoint ρ u v ρ' u' v') +
      polarLinear ρ u v ρ' u' v' = -polarLinear ρ u v ρ' u' v' := by
  have h := polarBasePoint_polarVector ρ u v ρ' u' v' hG
  change polarMatrix ρ u v *ᵥ polarBasePoint ρ u v ρ' u' v' +
    polarLinear ρ u v ρ' u' v' = 0 at h
  rw [eq_neg_of_add_eq_zero_left h]
  module

/-- A nonzero linear part gives a nonzero gradient at the base point. -/
theorem polarBasePoint_gradient_ne_zero {K : Type*} [Field K]
    (ρ u v ρ' u' v' : K) (hG : (polarMatrix ρ u v).det ≠ 0)
    (hℓ : polarLinear ρ u v ρ' u' v' ≠ 0) :
    (2 : K) • (polarMatrix ρ u v *ᵥ polarBasePoint ρ u v ρ' u' v') +
      polarLinear ρ u v ρ' u' v' ≠ 0 := by
  rw [polarBasePoint_gradient ρ u v ρ' u' v' hG]
  exact neg_ne_zero.mpr hℓ

/-- The polar base point lies on the defining quadric. -/
theorem polarBasePoint_on_quadric {K : Type*} [Field K] (ρ u v ρ' u' v' : K)
    (hG : (polarMatrix ρ u v).det ≠ 0) :
    let x := polarBasePoint ρ u v ρ' u' v'
    lineQuadratic ρ u v ρ' u' v' (x 0) (x 0 + x 1) (x 0 + x 1 + x 2) = 0 := by
  dsimp only
  rw [← polarVector_dot_gaps, polarBasePoint_polarVector ρ u v ρ' u' v' hG]
  simp

/-- The cubic norm also vanishes at the polar base point. -/
theorem polarBasePoint_norm_zero {K : Type*} [Field K] (ρ u v ρ' u' v' : K)
    (hG : (polarMatrix ρ u v).det ≠ 0) :
    let x := polarBasePoint ρ u v ρ' u' v'
    lineNorm ρ u v ρ' u' v' (x 0) (x 0 + x 1) (x 0 + x 1 + x 2) = 0 := by
  have he := polarVector_dot_moment_sub_norm ρ u v ρ' u' v'
    (polarBasePoint ρ u v ρ' u' v')
  dsimp only at he ⊢
  rw [polarBasePoint_on_quadric ρ u v ρ' u' v' hG,
    polarBasePoint_polarVector ρ u v ρ' u' v' hG] at he
  simpa using he

/-- The rational coefficient certificate's base point, in the three gap coordinates. -/
theorem polarBasePoint_certificate :
    polarBasePoint (2 : ℚ) 5 (-3) 3 6 (-5) = ![-1 / 7, -3 / 28, -1 / 2] := by
  have hG : (polarMatrix (2 : ℚ) 5 (-3)).det ≠ 0 := by
    rw [polarMatrix_det]
    norm_num
  symm
  apply (polarVector_eq_zero_iff (2 : ℚ) 5 (-3) 3 6 (-5) hG _).mp
  ext j
  fin_cases j <;> norm_num [polarVector, polarMatrix, polarLinear, dotProduct, Fin.sum_univ_succ]

end
end PierceLengthBound.FixedDividend
