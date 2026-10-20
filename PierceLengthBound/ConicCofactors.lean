/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ConicReconstruction
public import PierceLengthBound.ConicResultantHeight
public import Mathlib.LinearAlgebra.Matrix.Rank

/-! Explicit cofactor reconstruction for a codimension-one moment system. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Matrix Finset

/-- Delete the zeroth column from a rectangular moment system. -/
def momentTail {K : Type*} {n : ℕ} (M : Matrix (Fin n) (Fin (n + 1)) K) :
    Matrix (Fin n) (Fin n) K := fun i j => M i j.succ

/-- The signed maximal-minor vector, normalized by its zeroth cofactor. -/
def momentCofactors {K : Type*} [CommRing K] {n : ℕ}
    (M : Matrix (Fin n) (Fin (n + 1)) K) : Fin (n + 1) → K :=
  Fin.cons (momentTail M).det (-(momentTail M).cramer (fun i => M i 0))

/-- The explicit cofactor vector solves the original rectangular system. -/
theorem momentCofactors_kernel {K : Type*} [CommRing K] {n : ℕ}
    (M : Matrix (Fin n) (Fin (n + 1)) K) : M *ᵥ momentCofactors M = 0 := by
  ext i
  have h := congrFun ((momentTail M).mulVec_cramer (fun i => M i 0)) i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, momentTail] at h
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, momentCofactors,
    Fin.cons_zero, Fin.cons_succ, Pi.neg_apply, Pi.zero_apply, mul_neg, Finset.sum_neg_distrib]
  linear_combination -h

/-- Independent rows and a kernel vector with nonzero zeroth coordinate force
that specific maximal minor to be nonzero. -/
theorem momentTail_det_ne_zero {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin (n + 1)) K) (hM : LinearIndependent K M.row)
    (v : Fin (n + 1) → K) (hv : M *ᵥ v = 0) (hv0 : v 0 ≠ 0) :
    (momentTail M).det ≠ 0 := by
  have htail : LinearIndependent K (momentTail M).row := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    apply Fintype.linearIndependent_iff.mp hM c ?_ i
    let r : Fin (n + 1) → K := ∑ i, c i • M.row i
    have hrs (j : Fin n) : r j.succ = 0 := by
      have h := congrFun hc j
      simpa only [r, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row,
        momentTail, Pi.zero_apply] using h
    have hr : dotProduct r v = 0 := by
      calc
        dotProduct r v = ∑ i, c i * (M *ᵥ v) i := by
          simp only [dotProduct, r, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
            Finset.sum_mul, Matrix.mulVec, Finset.mul_sum, Matrix.row]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = 0 := by simp [hv]
    have hr0 : r 0 = 0 := by
      rw [dotProduct, Fin.sum_univ_succ] at hr
      simp only [hrs, zero_mul, Finset.sum_const_zero, add_zero] at hr
      exact (mul_eq_zero.mp hr).resolve_right hv0
    change r = 0
    funext j
    induction j using Fin.cases with
    | zero => exact hr0
    | succ j => exact hrs j
  exact isUnit_iff_ne_zero.mp
    (((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_row_iff_isUnit.mp htail)))

/-- All kernel vectors have the same normalized coordinates as the cofactor
vector, when the zeroth cofactor is nonzero. -/
theorem momentCofactors_proportional {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin (n + 1)) K) (hd : (momentTail M).det ≠ 0)
    (v : Fin (n + 1) → K) (hv : M *ᵥ v = 0) :
    ∀ j, momentCofactors M 0 * v j = v 0 * momentCofactors M j := by
  have hm := momentCofactors_kernel M
  have htail : (momentTail M) *ᵥ (fun j => momentCofactors M 0 * v j.succ -
      v 0 * momentCofactors M j.succ) = 0 := by
    ext i
    have hi := congrFun hv i
    have hi' := congrFun hm i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Pi.zero_apply] at hi hi'
    simp only [Matrix.mulVec, dotProduct, momentTail, mul_sub, Finset.sum_sub_distrib,
      Pi.zero_apply]
    have he (a : K) (w : Fin n → K) :
        ∑ j, M i j.succ * (a * w j) = a * ∑ j, M i j.succ * w j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he, he]
    linear_combination momentCofactors M 0 * hi - v 0 * hi'
  have hz : (fun j : Fin n => momentCofactors M 0 * v j.succ -
      v 0 * momentCofactors M j.succ) = 0 := by
    apply (Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr hd)))
    simpa using htail
  intro j
  induction j using Fin.cases with
  | zero => exact mul_comm _ _
  | succ j => exact sub_eq_zero.mp (congrFun hz j)

/-- Every cofactor has the same factorial height bound as an ordinary square
minor. In the application this is `8! H^8`. -/
theorem momentCofactors_height {n H : ℕ} (M : Matrix (Fin n) (Fin (n + 1)) ℤ)
    (hM : ∀ i j, |M i j| ≤ H) :
    ∀ j, |momentCofactors M j| ≤ (n.factorial : ℤ) * H ^ n := by
  intro j
  induction j using Fin.cases with
  | zero => exact integer_det_height (momentTail M) (fun i j => hM i j.succ)
  | succ j =>
    simp only [momentCofactors, Fin.cons_succ, Pi.neg_apply, abs_neg, Matrix.cramer_apply]
    apply integer_det_height
    intro i k
    simp only [Matrix.updateCol_apply]
    split_ifs <;> first | exact hM i 0 | exact hM i k.succ

end
end PierceLengthBound.FixedDividend
