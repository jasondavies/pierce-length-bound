/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Tactic

/-!
# Exponent arithmetic for the fixed-dividend candidate

These implications verify the exponent calculation given the local count, height bound,
gap selection, and drop estimate. They do not assert those hypotheses for Pierce orbits.
-/

@[expose] public section

namespace PierceLengthBound.FixedDividend

/-- The nonlinear-curve contribution gives exponent `31/105`. -/
theorem nonlinear_exponent {T H X Q a C D K : ℕ}
    (hcount : T ^ 2 ≤ K * H * X ^ 10)
    (hgap : H * T ≤ C * Q) (hheight : X * T ^ 6 ≤ C * a * Q ^ 2)
    (hdrop : Q * T ^ 2 ≤ D * a) :
    T ^ 105 ≤ K * C ^ 11 * D ^ 21 * a ^ 31 := by
  have h63 : T ^ 63 ≤ K * C ^ 11 * a ^ 10 * Q ^ 21 := by
    calc T ^ 63 = T ^ 2 * T ^ 61 := by ring
      _ ≤ (K * H * X ^ 10) * T ^ 61 := Nat.mul_le_mul_right _ hcount
      _ = K * (H * T) * (X * T ^ 6) ^ 10 := by ring
      _ ≤ K * (C * Q) * (C * a * Q ^ 2) ^ 10 := by gcongr
      _ = K * C ^ 11 * a ^ 10 * Q ^ 21 := by ring
  calc T ^ 105 = T ^ 63 * (T ^ 2) ^ 21 := by ring
    _ ≤ (K * C ^ 11 * a ^ 10 * Q ^ 21) * (T ^ 2) ^ 21 :=
      Nat.mul_le_mul_right _ h63
    _ = K * C ^ 11 * a ^ 10 * (Q * T ^ 2) ^ 21 := by ring
    _ ≤ K * C ^ 11 * a ^ 10 * (D * a) ^ 21 := by gcongr
    _ = K * C ^ 11 * D ^ 21 * a ^ 31 := by ring

/-- The squared line contribution gives exponent `26/88 = 13/44`. -/
theorem line_exponent_sq {T H X Q a C D K : ℕ}
    (hcount : T ^ 2 ≤ K * H ^ 2 * X ^ 8)
    (hgap : H * T ≤ C * Q) (hheight : X * T ^ 6 ≤ C * a * Q ^ 2)
    (hdrop : Q * T ^ 2 ≤ D * a) :
    T ^ 88 ≤ K * C ^ 10 * D ^ 18 * a ^ 26 := by
  have h52 : T ^ 52 ≤ K * C ^ 10 * a ^ 8 * Q ^ 18 := by
    calc T ^ 52 = T ^ 2 * T ^ 50 := by ring
      _ ≤ (K * H ^ 2 * X ^ 8) * T ^ 50 := Nat.mul_le_mul_right _ hcount
      _ = K * (H * T) ^ 2 * (X * T ^ 6) ^ 8 := by ring
      _ ≤ K * (C * Q) ^ 2 * (C * a * Q ^ 2) ^ 8 := by gcongr
      _ = K * C ^ 10 * a ^ 8 * Q ^ 18 := by ring
  calc T ^ 88 = T ^ 52 * (T ^ 2) ^ 18 := by ring
    _ ≤ (K * C ^ 10 * a ^ 8 * Q ^ 18) * (T ^ 2) ^ 18 :=
      Nat.mul_le_mul_right _ h52
    _ = K * C ^ 10 * a ^ 8 * (Q * T ^ 2) ^ 18 := by ring
    _ ≤ K * C ^ 10 * a ^ 8 * (D * a) ^ 18 := by gcongr
    _ = K * C ^ 10 * D ^ 18 * a ^ 26 := by ring

/-- Taking the square root with a harmless enlargement of the constant. -/
theorem line_exponent {T H X Q a C D K : ℕ}
    (hcount : T ^ 2 ≤ K * H ^ 2 * X ^ 8)
    (hgap : H * T ≤ C * Q) (hheight : X * T ^ 6 ≤ C * a * Q ^ 2)
    (hdrop : Q * T ^ 2 ≤ D * a) :
    T ^ 44 ≤ K * C ^ 5 * D ^ 9 * a ^ 13 := by
  have h := line_exponent_sq hcount hgap hheight hdrop
  have hK : K ≤ K ^ 2 := Nat.le_self_pow (by norm_num) K
  have hs : (T ^ 44) ^ 2 ≤ (K * C ^ 5 * D ^ 9 * a ^ 13) ^ 2 := by
    calc (T ^ 44) ^ 2 = T ^ 88 := by ring
      _ ≤ K * C ^ 10 * D ^ 18 * a ^ 26 := h
      _ ≤ K ^ 2 * C ^ 10 * D ^ 18 * a ^ 26 := by gcongr
      _ = (K * C ^ 5 * D ^ 9 * a ^ 13) ^ 2 := by ring
  exact (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp hs

/-- Either term in the squared local count gives its stated exponent. -/
theorem local_count_dichotomy {T H X Q a C D K : ℕ}
    (hcount : T ^ 2 ≤ K * (H * X ^ 10 + H ^ 2 * X ^ 8))
    (hgap : H * T ≤ C * Q) (hheight : X * T ^ 6 ≤ C * a * Q ^ 2)
    (hdrop : Q * T ^ 2 ≤ D * a) :
    T ^ 105 ≤ 2 * K * C ^ 11 * D ^ 21 * a ^ 31 ∨
      T ^ 44 ≤ 2 * K * C ^ 5 * D ^ 9 * a ^ 13 := by
  by_cases h : T ^ 2 ≤ (2 * K) * H * X ^ 10
  · exact Or.inl (nonlinear_exponent h hgap hheight hdrop)
  · have hl : T ^ 2 ≤ (2 * K) * H ^ 2 * X ^ 8 := by nlinarith
    exact Or.inr (line_exponent hl hgap hheight hdrop)

/-- Sixth powers remove the half-integral exponents in the weighted local count.
This is an arithmetic implication, not an assertion of that count for an orbit. -/
theorem weighted_exponent {T H X Q a C D K : ℕ}
    (hcount : T ^ 6 ≤ K * H ^ 3 * X ^ 29)
    (hgap : H * T ≤ C * Q) (hheight : X * T ^ 6 ≤ C * a * Q ^ 2)
    (hdrop : Q * T ^ 2 ≤ D * a) :
    T ^ 305 ≤ K * C ^ 32 * D ^ 61 * a ^ 90 := by
  have h183 : T ^ 183 ≤ K * C ^ 32 * a ^ 29 * Q ^ 61 := by
    calc T ^ 183 = T ^ 6 * T ^ 177 := by ring
      _ ≤ (K * H ^ 3 * X ^ 29) * T ^ 177 := Nat.mul_le_mul_right _ hcount
      _ = K * (H * T) ^ 3 * (X * T ^ 6) ^ 29 := by ring
      _ ≤ K * (C * Q) ^ 3 * (C * a * Q ^ 2) ^ 29 := by gcongr
      _ = K * C ^ 32 * a ^ 29 * Q ^ 61 := by ring
  calc T ^ 305 = T ^ 183 * (T ^ 2) ^ 61 := by ring
    _ ≤ (K * C ^ 32 * a ^ 29 * Q ^ 61) * (T ^ 2) ^ 61 :=
      Nat.mul_le_mul_right _ h183
    _ = K * C ^ 32 * a ^ 29 * (Q * T ^ 2) ^ 61 := by ring
    _ ≤ K * C ^ 32 * a ^ 29 * (D * a) ^ 61 := by gcongr
    _ = K * C ^ 32 * D ^ 61 * a ^ 90 := by ring

/-- The complementary scale gives the strictly smaller exponent `5/17`. -/
theorem small_scale_exponent {T Q a C D : ℕ}
    (hscale : T ^ 11 ≤ C * a ^ 2 * Q ^ 3)
    (hdrop : Q * T ^ 2 ≤ D * a) :
    T ^ 17 ≤ C * D ^ 3 * a ^ 5 := by
  calc T ^ 17 = T ^ 11 * (T ^ 2) ^ 3 := by ring
    _ ≤ (C * a ^ 2 * Q ^ 3) * (T ^ 2) ^ 3 := Nat.mul_le_mul_right _ hscale
    _ = C * a ^ 2 * (Q * T ^ 2) ^ 3 := by ring
    _ ≤ C * a ^ 2 * (D * a) ^ 3 := by gcongr
    _ = C * D ^ 3 * a ^ 5 := by ring

/-- Exact exponent savings, including the complementary range. -/
lemma weighted_exponent_comparison :
    (90 : ℚ) / 305 = 18 / 61 ∧
    (13 : ℚ) / 44 - 31 / 105 = 1 / 4620 ∧
    (31 : ℚ) / 105 - 18 / 61 = 1 / 6405 ∧
    (13 : ℚ) / 44 - 18 / 61 = 1 / 2684 ∧
    (18 : ℚ) / 61 - 5 / 17 = 1 / 1037 := by norm_num

/-- The five scales claimed at the critical balance satisfy all exponent relations. -/
lemma weighted_critical_balance :
    (25 : ℚ) / 61 - 18 / 61 = 7 / 61 ∧
    1 + 2 * ((25 : ℚ) / 61) - 6 * (18 / 61) = 3 / 61 ∧
    5 * ((18 : ℚ) / 61) - 1 - 25 / 61 = 4 / 61 ∧
    ((7 : ℚ) / 61) / 2 + (29 / 6) * (3 / 61) = 18 / 61 := by norm_num

end PierceLengthBound.FixedDividend
