/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.Main
public import PierceLengthBound.SixStep

/-! Real window bounds from integer-power estimates: the large-mean-gap case and the generic
branch exponent arithmetic. -/

@[expose] public section
namespace PierceLengthBound
open Finset

/-- A window with a large mean gap, `A T > 28 a`, has `T ≤ B a^α` for every `α ≥ 5/17`
and `B ≥ 122449` (`window_large_mean_gap`). -/
lemma window_real_large_mean_gap {a A T B : ℕ} {α : ℝ} (ha : 1 ≤ a) (hB : 122449 ≤ B)
    (hα : (5 : ℝ) / 17 ≤ α) (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3) (hbig : 28 * a < A * T) :
    (T : ℝ) ≤ (B : ℝ) * (a : ℝ) ^ α :=
  window_real_bound_of_power (r := 1) ha (by omega) (by decide : 0 < 4)
    (by simpa using (window_large_mean_gap ha hsix hbig).trans (Nat.mul_le_mul_right a hB))
    ((by norm_num : ((1 : ℕ) : ℝ) / (4 : ℕ) ≤ 5 / 17).trans hα)

/-- **The generic window lemma.** A branch `T^L ≤ K X^q B` with a box bound `B T^u ≤ F a^v`,
the gap height `H ≤ C a/(A T)`, the minor height `X ≤ E A⁴ H⁶/a³` and the drop bound
`T² ≤ D A` give `T^{L+10q+u} ≪ a^{3q+v}`. -/
theorem window_branch_exponent {T X B A a H K C E D F L q u v : ℕ} (ha : 0 < a)
    (hcount : T ^ L ≤ K * X ^ q * B) (hgap : H * (A * T) ≤ C * a)
    (hheight : X * a ^ 3 ≤ E * A ^ 4 * H ^ 6) (hbox : B * T ^ u ≤ F * a ^ v)
    (hdrop : T ^ 2 ≤ D * A) :
    T ^ (L + 10 * q + u) ≤ K * (E * C ^ 6 * D ^ 2) ^ q * F * a ^ (3 * q + v) := by
  have h6 : X * T ^ 6 * A ^ 2 ≤ E * C ^ 6 * a ^ 3 := by
    apply Nat.le_of_mul_le_mul_right (c := a ^ 3) _ (by positivity)
    calc X * T ^ 6 * A ^ 2 * a ^ 3 = (X * a ^ 3) * A ^ 2 * T ^ 6 := by ring
      _ ≤ (E * A ^ 4 * H ^ 6) * A ^ 2 * T ^ 6 := by gcongr
      _ = E * (H * (A * T)) ^ 6 := by ring
      _ ≤ E * (C * a) ^ 6 := by gcongr
      _ = E * C ^ 6 * a ^ 3 * a ^ 3 := by ring
  have h10 : X * T ^ 10 ≤ E * C ^ 6 * D ^ 2 * a ^ 3 := by
    calc X * T ^ 10 = X * T ^ 6 * (T ^ 2) ^ 2 := by ring
      _ ≤ X * T ^ 6 * (D * A) ^ 2 := by gcongr
      _ = D ^ 2 * (X * T ^ 6 * A ^ 2) := by ring
      _ ≤ D ^ 2 * (E * C ^ 6 * a ^ 3) := by gcongr
      _ = _ := by ring
  calc T ^ (L + 10 * q + u) = T ^ L * (T ^ 10) ^ q * T ^ u := by
        rw [pow_add, pow_add, pow_mul]
    _ ≤ (K * X ^ q * B) * (T ^ 10) ^ q * T ^ u := by gcongr
    _ = K * (X * T ^ 10) ^ q * (B * T ^ u) := by rw [mul_pow]; ring
    _ ≤ K * (E * C ^ 6 * D ^ 2 * a ^ 3) ^ q * (F * a ^ v) := by gcongr
    _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring

/-- The gap height times `T³` is linear in `a`. -/
lemma gap_cube_box {H A T C D a : ℕ} (hgap : H * (A * T) ≤ C * a) (hdrop : T ^ 2 ≤ D * A) :
    H * T ^ 3 ≤ C * D * a := by
  calc H * T ^ 3 = H * T * T ^ 2 := by ring
    _ ≤ H * T * (D * A) := by gcongr
    _ = D * (H * (A * T)) := by ring
    _ ≤ D * (C * a) := by gcongr
    _ = _ := by ring

end PierceLengthBound
