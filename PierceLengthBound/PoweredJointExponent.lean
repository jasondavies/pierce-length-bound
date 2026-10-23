/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftExponent
public import PierceLengthBound.WindowRealReduction

/-! Exponent arithmetic for the powered window branches, with an arbitrary powered-graph
degree `L`, and the box bounds `max(H, Sᵐ) T^{3m} ≪ a^m` and `Yⁿ T^{20n} ≪ a^{6n}`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend

/-- The graph-degree parameter enters linearly in all window exponents. -/
theorem remainder_window_powered_box_exponent {T H X B A a C E D F K L u v : ℕ}
    (ha : 0 < a) (hcount : T ^ L ≤ K * X ^ (5 * L) * B)
    (hgap : H * (A * T) ≤ C * a) (hheight : X * a ^ 3 ≤ E * A ^ 4 * H ^ 6)
    (hbox : B * T ^ u ≤ F * a ^ v) (hdrop : T ^ 2 ≤ D * A) :
    T ^ (51 * L + u) ≤ K * E ^ (5 * L) * C ^ (30 * L) * F * D ^ (10 * L) *
      a ^ (15 * L + v) := by
  have h := window_branch_exponent (q := 5 * L) ha hcount hgap hheight hbox hdrop
  calc T ^ (51 * L + u) = T ^ (L + 10 * (5 * L) + u) := by ring_nf
    _ ≤ _ := h
    _ = _ := by ring

/-- The node radius `H` can be absorbed in the powered curvature box,
using the drop estimate and a positive curvature power. -/
lemma max_powered_curvature_height {a A T C S H D K m : ℕ} (hm : 0 < m)
    (hA : 0 < A) (hD : 1 ≤ D) (hH : 1 ≤ H)
    (hgap : H * (A * T) ≤ C * a) (hS : S * T ^ 3 ≤ K * C ^ 3 * a)
    (hdrop : T ^ 2 ≤ D * A) :
    max H (S ^ m) * T ^ (3 * m) ≤ ((K * C ^ 3 + C) * D) ^ m * a ^ m := by
  have hbox := max_curvature_height_times_cube hA hD hgap hS hdrop
  have hHm : H ≤ H ^ m := by
    simpa only [pow_one] using Nat.pow_le_pow_right hH (show 1 ≤ m by omega)
  have hmax : max H (S ^ m) ≤ (max H S) ^ m :=
    max_le (hHm.trans (Nat.pow_le_pow_left (le_max_left _ _) m))
      (Nat.pow_le_pow_left (le_max_right _ _) m)
  calc _ ≤ (max H S) ^ m * T ^ (3 * m) := by gcongr
    _ = (max H S * T ^ 3) ^ m := by rw [mul_pow, ← pow_mul]
    _ ≤ ((K * C ^ 3 + C) * D * a) ^ m := Nat.pow_le_pow_left hbox m
    _ = _ := mul_pow _ _ _

/-- The powered rank-five box: `Yⁿ T^{20n} ≤ (J C¹⁰ D⁵)ⁿ a^{6n}`. -/
lemma powered_rank_five_height {a A T C Y H D J n : ℕ} (ha : 0 < a) (hA : 0 < A)
    (hgap : H * (A * T) ≤ C * a) (hY : Y * a ^ 4 ≤ J * A ^ 5 * H ^ 10)
    (hdrop : T ^ 2 ≤ D * A) :
    Y ^ n * T ^ (20 * n) ≤ (J * C ^ 10 * D ^ 5) ^ n * a ^ (6 * n) := by
  have h := Nat.pow_le_pow_left (rank_five_height_times_twenty ha hA hgap hY hdrop) n
  simpa only [mul_pow, ← pow_mul] using h

end PierceLengthBound.FixedDividend
