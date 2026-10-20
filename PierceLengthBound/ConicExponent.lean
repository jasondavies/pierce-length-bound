/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendWindow

/-! Exact exponent implications for the three terms in the 135/458 candidate.
The local conic counts are hypotheses here, not assumed global axioms. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend

/-- Arithmetic conics: the `X^5` term gives exponent `15/51 = 5/17`. -/
theorem arithmetic_conic_exponent {T X Q a C D K : ℕ}
    (hcount : T ≤ K * X ^ 5)
    (hheight : X * T ^ 6 ≤ C * a * Q ^ 2) (hdrop : Q * T ^ 2 ≤ D * a) :
    T ^ 51 ≤ K * C ^ 5 * D ^ 10 * a ^ 15 := by
  have h31 : T ^ 31 ≤ K * C ^ 5 * a ^ 5 * Q ^ 10 := by
    calc T ^ 31 = T * T ^ 30 := by ring
      _ ≤ K * X ^ 5 * T ^ 30 := by gcongr
      _ = K * (X * T ^ 6) ^ 5 := by ring
      _ ≤ K * (C * a * Q ^ 2) ^ 5 := by gcongr
      _ = _ := by ring
  calc T ^ 51 = T ^ 31 * (T ^ 2) ^ 10 := by ring
    _ ≤ (K * C ^ 5 * a ^ 5 * Q ^ 10) * (T ^ 2) ^ 10 := by gcongr
    _ = K * C ^ 5 * a ^ 5 * (Q * T ^ 2) ^ 10 := by ring
    _ ≤ K * C ^ 5 * a ^ 5 * (D * a) ^ 10 := by gcongr
    _ = _ := by ring

/-- Exceptional parabolas: the `X^4 H^(1/2)` term also gives `5/17`. -/
theorem exceptional_parabola_exponent {T H X Q a C D K : ℕ}
    (hcount : T ^ 2 ≤ K * H * X ^ 8)
    (hgap : H * T ≤ C * Q) (hheight : X * T ^ 6 ≤ C * a * Q ^ 2)
    (hdrop : Q * T ^ 2 ≤ D * a) :
    T ^ 85 ≤ K * C ^ 9 * D ^ 17 * a ^ 25 := by
  have h51 : T ^ 51 ≤ K * C ^ 9 * a ^ 8 * Q ^ 17 := by
    calc T ^ 51 = T ^ 2 * T ^ 49 := by ring
      _ ≤ (K * H * X ^ 8) * T ^ 49 := by gcongr
      _ = K * (H * T) * (X * T ^ 6) ^ 8 := by ring
      _ ≤ K * (C * Q) * (C * a * Q ^ 2) ^ 8 := by gcongr
      _ = _ := by ring
  calc T ^ 85 = T ^ 51 * (T ^ 2) ^ 17 := by ring
    _ ≤ (K * C ^ 9 * a ^ 8 * Q ^ 17) * (T ^ 2) ^ 17 := by gcongr
    _ = K * C ^ 9 * a ^ 8 * (Q * T ^ 2) ^ 17 := by ring
    _ ≤ K * C ^ 9 * a ^ 8 * (D * a) ^ 17 := by gcongr
    _ = _ := by ring

/-- Degree at least three: the cube-root weighted count gives `135/458`. -/
theorem higher_curve_exponent {T H X Q a C D K : ℕ}
    (hcount : T ^ 9 ≤ K * H ^ 3 * X ^ 44)
    (hgap : H * T ≤ C * Q) (hheight : X * T ^ 6 ≤ C * a * Q ^ 2)
    (hdrop : Q * T ^ 2 ≤ D * a) :
    T ^ 458 ≤ K * C ^ 47 * D ^ 91 * a ^ 135 := by
  have h276 : T ^ 276 ≤ K * C ^ 47 * a ^ 44 * Q ^ 91 := by
    calc T ^ 276 = T ^ 9 * T ^ 267 := by ring
      _ ≤ (K * H ^ 3 * X ^ 44) * T ^ 267 := by gcongr
      _ = K * (H * T) ^ 3 * (X * T ^ 6) ^ 44 := by ring
      _ ≤ K * (C * Q) ^ 3 * (C * a * Q ^ 2) ^ 44 := by gcongr
      _ = _ := by ring
  calc T ^ 458 = T ^ 276 * (T ^ 2) ^ 91 := by ring
    _ ≤ (K * C ^ 47 * a ^ 44 * Q ^ 91) * (T ^ 2) ^ 91 := by gcongr
    _ = K * C ^ 47 * a ^ 44 * (Q * T ^ 2) ^ 91 := by ring
    _ ≤ K * C ^ 47 * a ^ 44 * (D * a) ^ 91 := by gcongr
    _ = _ := by ring

/-- The higher-degree branch in the repository's actual remainder-window coordinates. -/
theorem remainder_window_higher_curve_exponent {T H X A a C E D K : ℕ}
    (ha : 0 < a) (hA : 0 < A) (hcount : T ^ 9 ≤ K * H ^ 3 * X ^ 44)
    (hgap : H * (A * T) ≤ C * a) (hheight : X * a ^ 3 ≤ E * A ^ 4 * H ^ 6)
    (hdrop : T ^ 2 ≤ D * A) :
    T ^ 458 ≤ K * E ^ 44 * C ^ 267 * D ^ 91 * a ^ 135 := by
  have h1 : T ^ 9 * a ^ 132 ≤ K * E ^ 44 * A ^ 176 * H ^ 267 := by
    calc T ^ 9 * a ^ 132 ≤ (K * H ^ 3 * X ^ 44) * a ^ 132 := by gcongr
      _ = K * H ^ 3 * (X * a ^ 3) ^ 44 := by ring
      _ ≤ K * H ^ 3 * (E * A ^ 4 * H ^ 6) ^ 44 := by gcongr
      _ = _ := by ring
  have h2 : (T ^ 276 * A ^ 91) * (A ^ 176 * a ^ 132) ≤
      (K * E ^ 44 * C ^ 267 * a ^ 135) * (A ^ 176 * a ^ 132) := by
    calc _ = (T ^ 9 * a ^ 132) * (A * T) ^ 267 := by ring
      _ ≤ (K * E ^ 44 * A ^ 176 * H ^ 267) * (A * T) ^ 267 := by gcongr
      _ = K * E ^ 44 * A ^ 176 * (H * (A * T)) ^ 267 := by ring
      _ ≤ K * E ^ 44 * A ^ 176 * (C * a) ^ 267 := by gcongr
      _ = _ := by ring
  have h3 := Nat.le_of_mul_le_mul_right h2 (by positivity : 0 < A ^ 176 * a ^ 132)
  calc T ^ 458 = T ^ 276 * (T ^ 2) ^ 91 := by ring
    _ ≤ T ^ 276 * (D * A) ^ 91 := by gcongr
    _ = (T ^ 276 * A ^ 91) * D ^ 91 := by ring
    _ ≤ (K * E ^ 44 * C ^ 267 * a ^ 135) * D ^ 91 := by gcongr
    _ = _ := by ring

lemma conic_exponent_comparison :
    (18 : ℚ) / 61 - 135 / 458 = 9 / 27938 ∧
    (135 : ℚ) / 458 - 5 / 17 = 5 / 7786 ∧
    (15 : ℚ) / 51 = 5 / 17 ∧ (25 : ℚ) / 85 = 5 / 17 := by norm_num

lemma conic_critical_balance :
    (188 : ℚ) / 458 - 135 / 458 = 53 / 458 ∧
    1 + 2 * ((188 : ℚ) / 458) - 6 * (135 / 458) = 24 / 458 ∧
    5 * ((135 : ℚ) / 458) - 1 - 188 / 458 = 29 / 458 ∧
    (44 / 9 : ℚ) * (24 / 458) + (1 / 3) * (53 / 458) = 135 / 458 := by norm_num

end PierceLengthBound.FixedDividend
