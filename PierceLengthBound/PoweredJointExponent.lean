/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftExponent

/-! Exponent arithmetic with an arbitrary powered-graph degree. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend

/-- The graph-degree parameter enters linearly in all window exponents. -/
theorem remainder_window_powered_box_exponent {T H X B A a C E D F K L u v : ℕ}
    (ha : 0 < a) (hA : 0 < A) (hcount : T ^ L ≤ K * X ^ (5 * L) * B)
    (hgap : H * (A * T) ≤ C * a) (hheight : X * a ^ 3 ≤ E * A ^ 4 * H ^ 6)
    (hbox : B * T ^ u ≤ F * a ^ v) (hdrop : T ^ 2 ≤ D * A) :
    T ^ (51 * L + u) ≤ K * E ^ (5 * L) * C ^ (30 * L) * F * D ^ (10 * L) *
      a ^ (15 * L + v) := by
  have hcount' : T ^ L ≤ (K * B) * (X ^ L) ^ 5 := by
    simpa only [← pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcount
  have hgap' : H ^ L * (A ^ L * T ^ L) ≤ C ^ L * a ^ L := by
    simpa only [mul_pow] using Nat.pow_le_pow_left hgap L
  have hheight' : X ^ L * (a ^ L) ^ 3 ≤ E ^ L * (A ^ L) ^ 4 * (H ^ L) ^ 6 := by
    simpa only [mul_pow, ← pow_mul, Nat.mul_comm] using Nat.pow_le_pow_left hheight L
  have hdrop' : (T ^ L) ^ 2 ≤ D ^ L * A ^ L := by
    simpa only [mul_pow, ← pow_mul, Nat.mul_comm] using Nat.pow_le_pow_left hdrop L
  have hc := remainder_window_arithmetic_conic_exponent (pow_pos ha L) (pow_pos hA L)
    hcount' hgap' hheight' hdrop'
  have hc' : T ^ (51 * L) ≤ K * E ^ (5 * L) * C ^ (30 * L) * D ^ (10 * L) *
      a ^ (15 * L) * B := by
    simpa only [← pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hc
  calc _ = T ^ (51 * L) * T ^ u := pow_add _ _ _
    _ ≤ (K * E ^ (5 * L) * C ^ (30 * L) * D ^ (10 * L) * a ^ (15 * L) * B) * T ^ u := by
      gcongr
    _ = K * E ^ (5 * L) * C ^ (30 * L) * D ^ (10 * L) * a ^ (15 * L) * (B * T ^ u) := by ring
    _ ≤ K * E ^ (5 * L) * C ^ (30 * L) * D ^ (10 * L) * a ^ (15 * L) * (F * a ^ v) := by
      gcongr
    _ = _ := by rw [pow_add]; ring

/-- The original node radius can be absorbed in the powered curvature box,
using the drop estimate and a positive curvature power. -/
lemma max_powered_curvature_height {a A T C S H D m : ℕ} (hm : 0 < m)
    (hA : 0 < A) (hD : 1 ≤ D) (hH : 1 ≤ H)
    (hgap : H * (A * T) ≤ C * a) (hS : S * T ^ 3 ≤ 4352 * C ^ 3 * a)
    (hdrop : T ^ 2 ≤ D * A) :
    max H (S ^ m) * T ^ (3 * m) ≤ ((4352 * C ^ 3 + C) * D) ^ m * a ^ m := by
  have hbox := max_curvature_height_times_cube hA hD hgap hS hdrop
  have hHm : H ≤ H ^ m := by
    simpa only [pow_one] using Nat.pow_le_pow_right hH (show 1 ≤ m by omega)
  have hmax : max H (S ^ m) ≤ (max H S) ^ m :=
    max_le (hHm.trans (Nat.pow_le_pow_left (le_max_left _ _) m))
      (Nat.pow_le_pow_left (le_max_right _ _) m)
  calc _ ≤ (max H S) ^ m * T ^ (3 * m) := by gcongr
    _ = (max H S * T ^ 3) ^ m := by rw [mul_pow, ← pow_mul]
    _ ≤ ((4352 * C ^ 3 + C) * D * a) ^ m := Nat.pow_le_pow_left hbox m
    _ = _ := mul_pow _ _ _

lemma powered_rank_five_height {a A T C Y H D J n : ℕ} (ha : 0 < a) (hA : 0 < A)
    (hgap : H * (A * T) ≤ C * a) (hY : Y * a ^ 4 ≤ J * A ^ 5 * H ^ 10)
    (hdrop : T ^ 2 ≤ D * A) :
    Y ^ n * T ^ (20 * n) ≤ (J * C ^ 10 * D ^ 5) ^ n * a ^ (6 * n) := by
  have h := Nat.pow_le_pow_left (rank_five_height_times_twenty ha hA hgap hY hdrop) n
  simpa only [mul_pow, ← pow_mul] using h

end PierceLengthBound.FixedDividend
