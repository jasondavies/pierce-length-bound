/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendSelection

/-! # Height scales of the joint coordinates

The height bounds `S` for the curvature coordinates and `Y` for the rank-five coordinate
(Section 8.6), and the arithmetic eliminating the window scale `A` in the proof of
Corollary 8.14: with `H A T ≤ C a` and `T² ≤ D A`, `S T³ ≪ a`, `max(H, S) T³ ≪ a` and
`Y T²⁰ ≪ a⁶`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend

/-- The curvature height `S = ⌊4352 A³ H³ / a²⌋`, from the minor bound with constant `68` and
`q ≥ a/(4A)` (`4352 = 68 · 4³`). -/
def selectedCurvatureHeight (a A T : ℕ) : ℕ :=
  4352 * A ^ 3 * selectedGapHeight a A T ^ 3 / a ^ 2

/-- The rank-five height `Y = ⌊1259991040 A⁵ H¹⁰ / a⁴⌋`, from the Newton Gram bound for `J`
(Lemma 8.7). -/
def selectedRankFiveHeight (a A T : ℕ) : ℕ :=
  1259991040 * A ^ 5 * selectedGapHeight a A T ^ 10 / a ^ 4

/-- A curvature height `S ≤ K A³ H³/a²` times `T³` is linear in `a`. The joint lift takes
`K = 4352` and the exterior lattice coordinates `K = 9472`. -/
lemma curvature_height_times_cube {a A T C S H K : ℕ} (ha : 0 < a) (hA : 0 < A)
    (hgap : H * (A * T) ≤ C * a) (hS : S * a ^ 2 ≤ K * A ^ 3 * H ^ 3) :
    S * T ^ 3 ≤ K * C ^ 3 * a := by
  apply Nat.le_of_mul_le_mul_right (c := A ^ 3 * a ^ 2) ?_ (by positivity)
  calc _ = (S * a ^ 2) * A ^ 3 * T ^ 3 := by ring
    _ ≤ (K * A ^ 3 * H ^ 3) * A ^ 3 * T ^ 3 := by gcongr
    _ = K * A ^ 3 * (H * (A * T)) ^ 3 := by ring
    _ ≤ K * A ^ 3 * (C * a) ^ 3 := by gcongr
    _ = _ := by ring

/-- The larger of the gap and curvature heights times `T³` is linear in `a`. -/
lemma max_curvature_height_times_cube {a A T C S H D K : ℕ} (hA : 0 < A) (hD : 1 ≤ D)
    (hgap : H * (A * T) ≤ C * a) (hS : S * T ^ 3 ≤ K * C ^ 3 * a)
    (hdrop : T ^ 2 ≤ D * A) :
    max H S * T ^ 3 ≤ (K * C ^ 3 + C) * D * a := by
  have hH : H * T ^ 3 ≤ C * D * a := by
    apply Nat.le_of_mul_le_mul_right (c := A) ?_ hA
    calc H * T ^ 3 * A = (H * (A * T)) * T ^ 2 := by ring
      _ ≤ (C * a) * (D * A) := by gcongr
      _ = _ := by ring
  rcases le_total H S with h | h
  · rw [max_eq_right h]
    calc S * T ^ 3 ≤ K * C ^ 3 * a := hS
      _ = K * C ^ 3 * 1 * a := by ring
      _ ≤ (K * C ^ 3 + C) * D * a := by gcongr; omega
  · rw [max_eq_left h]
    exact hH.trans (by gcongr; omega)

/-- If `Y a⁴ ≤ J A⁵ H¹⁰`, `H A T ≤ C a` and `T² ≤ D A`, then `Y T²⁰ ≤ J C¹⁰ D⁵ a⁶`. -/
lemma rank_five_height_times_twenty {a A T C Y H D J : ℕ} (ha : 0 < a) (hA : 0 < A)
    (hgap : H * (A * T) ≤ C * a) (hY : Y * a ^ 4 ≤ J * A ^ 5 * H ^ 10)
    (hdrop : T ^ 2 ≤ D * A) :
    Y * T ^ 20 ≤ J * C ^ 10 * D ^ 5 * a ^ 6 := by
  have h1 : (Y * A ^ 5 * T ^ 10) * (a ^ 4 * A ^ 5) ≤
      (J * C ^ 10 * a ^ 6) * (a ^ 4 * A ^ 5) := by
    calc _ = (Y * a ^ 4) * (A * T) ^ 10 := by ring
      _ ≤ (J * A ^ 5 * H ^ 10) * (A * T) ^ 10 := by gcongr
      _ = J * A ^ 5 * (H * (A * T)) ^ 10 := by ring
      _ ≤ J * A ^ 5 * (C * a) ^ 10 := by gcongr
      _ = _ := by ring
  have h2 := Nat.le_of_mul_le_mul_right h1 (by positivity : 0 < a ^ 4 * A ^ 5)
  calc Y * T ^ 20 = Y * T ^ 10 * (T ^ 2) ^ 5 := by ring
    _ ≤ Y * T ^ 10 * (D * A) ^ 5 := by gcongr
    _ = (Y * A ^ 5 * T ^ 10) * D ^ 5 := by ring
    _ ≤ (J * C ^ 10 * a ^ 6) * D ^ 5 := by gcongr
    _ = _ := by ring

end PierceLengthBound.FixedDividend
