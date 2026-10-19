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

end PierceLengthBound.FixedDividend
