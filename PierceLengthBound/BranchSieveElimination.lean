/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveSextic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

/-! Exact elimination of the two moment equations for the infinity locations. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

variable {R : Type*} [CommRing R]

/-- The second-moment equation, after eliminating the fourth location. -/
def branchInfinityQuadratic (c1 c2 c3 t : R) : R[X] :=
  C (c3 * (c3 + 1)) * X ^ 2 + C (2 * c3 * (c1 + c2 * t)) * X +
    C (c1 + c2 * t ^ 2 + (c1 + c2 * t) ^ 2)

/-- The third-moment equation after the same elimination. -/
def branchInfinityCubic (c1 c2 c3 t : R) : R[X] :=
  C (c3 * (1 - c3 ^ 2)) * X ^ 3 - C (3 * c3 ^ 2 * (c1 + c2 * t)) * X ^ 2 -
    C (3 * c3 * (c1 + c2 * t) ^ 2) * X +
      C (c1 + c2 * t ^ 3 - (c1 + c2 * t) ^ 3)

lemma branchInfinityQuadratic_eval (c1 c2 c3 t y : R) :
    (branchInfinityQuadratic c1 c2 c3 t).eval y =
      c1 + c2 * t ^ 2 + c3 * y ^ 2 + (-c1 - c2 * t - c3 * y) ^ 2 := by
  simp only [branchInfinityQuadratic, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  ring

lemma branchInfinityCubic_eval (c1 c2 c3 t y : R) :
    (branchInfinityCubic c1 c2 c3 t).eval y =
      c1 + c2 * t ^ 3 + c3 * y ^ 3 + (-c1 - c2 * t - c3 * y) ^ 3 := by
  simp only [branchInfinityCubic, eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  ring

private theorem quadratic_cubic_resultant_formula (a0 a1 a2 b0 b1 b2 b3 : R) :
    resultant (C a2 * X ^ 2 + C a1 * X + C a0)
      (C b3 * X ^ 3 + C b2 * X ^ 2 + C b1 * X + C b0) 2 3 =
      a0 ^ 3 * b3 ^ 2 - a0 ^ 2 * a1 * b2 * b3 - 2 * a0 ^ 2 * a2 * b1 * b3 +
        a0 ^ 2 * a2 * b2 ^ 2 + a0 * a1 ^ 2 * b1 * b3 + 3 * a0 * a1 * a2 * b0 * b3 -
        a0 * a1 * a2 * b1 * b2 - 2 * a0 * a2 ^ 2 * b0 * b2 + a0 * a2 ^ 2 * b1 ^ 2 -
        a1 ^ 3 * b0 * b3 + a1 ^ 2 * a2 * b0 * b2 - a1 * a2 ^ 2 * b0 * b1 +
        a2 ^ 3 * b0 ^ 2 := by
  have hm : sylvester (C a2 * X ^ 2 + C a1 * X + C a0)
      (C b3 * X ^ 3 + C b2 * X ^ 2 + C b1 * X + C b0) 2 3 =
      !![b0, 0, a0, 0, 0; b1, b0, a1, a0, 0; b2, b1, a2, a1, a0;
        b3, b2, 0, a2, a1; 0, b3, 0, 0, a2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sylvester, Fin.addCases, coeff_add, coeff_X]
  rw [resultant, hm]
  norm_num [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix_apply, Fin.succAbove]
  ring

/-- The complete resultant identity, valid before imposing any nondegeneracy conditions. -/
theorem branchInfinity_resultant (c1 c2 c3 t : R) :
    resultant (branchInfinityQuadratic c1 c2 c3 t) (branchInfinityCubic c1 c2 c3 t) 2 3 =
      c3 ^ 2 * (c3 + 1) * (branchLocationSextic c1 c2 c3).eval t := by
  have hg : branchInfinityCubic c1 c2 c3 t =
      C (c3 * (1 - c3 ^ 2)) * X ^ 3 + C (-3 * c3 ^ 2 * (c1 + c2 * t)) * X ^ 2 +
        C (-3 * c3 * (c1 + c2 * t) ^ 2) * X +
          C (c1 + c2 * t ^ 3 - (c1 + c2 * t) ^ 3) := by
    simp only [branchInfinityCubic, neg_mul, map_neg]
    ring
  rw [branchInfinityQuadratic, hg, quadratic_cubic_resultant_formula]
  simp only [branchLocationSextic, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  ring

end
end PierceLengthBound.FixedDividend
