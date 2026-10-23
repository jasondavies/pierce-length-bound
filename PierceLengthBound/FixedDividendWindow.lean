/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.Defs

/-!
# Window scales for the fixed-dividend bound

These estimates express the line-exclusion condition in the remainder-window
coordinates used by the existing dyadic decomposition.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend

/-- Quotients have the required lower bound throughout a remainder window. -/
lemma window_quotient_lower {a b i A : ℕ} (hba : b < a) (hi : i < P a b)
    (hA : orb a b i < 2 * A) : a ≤ 4 * A * qq a b i := by
  have he := orb_div (a := a) (b := b) hi
  have hq := qq_pos hba hi
  have hn : orb a b (i + 1) < orb a b i := by
    rw [orb_succ_of_ne (orb_ne_zero_of_lt hi)]
    exact Nat.mod_lt _ (orb_pos_of_lt hi)
  have hnq : orb a b i ≤ orb a b i * qq a b i := Nat.le_mul_of_pos_right _ hq
  nlinarith

/-- One explicit window-scale inequality guarantees the orbit's line-exclusion scale. -/
lemma window_line_scale {a b i A H X : ℕ} (hba : b < a) (hi : i < P a b)
    (hA : orb a b i < 2 * A) (hX : 1 ≤ X)
    (hscale : 124928 * A ^ 4 * H ^ 5 * X < a ^ 3) :
    (a : ℤ) * (H : ℤ) ^ 5 * (24 * (X : ℤ) + 464) < (qq a b i : ℤ) ^ 4 := by
  have hq := Nat.pow_le_pow_left (window_quotient_lower hba hi hA) 4
  have ha : 0 < a := by omega
  have hApos : 0 < A := by omega
  have hs : a * H ^ 5 * (24 * X + 464) < qq a b i ^ 4 := by
    suffices h : 256 * A ^ 4 * (a * H ^ 5 * (24 * X + 464)) <
        256 * A ^ 4 * qq a b i ^ 4 from Nat.lt_of_mul_lt_mul_left h
    calc 256 * A ^ 4 * (a * H ^ 5 * (24 * X + 464))
        ≤ a * (124928 * A ^ 4 * H ^ 5 * X) := by
          have : 24 * X + 464 ≤ 488 * X := by omega
          calc _ ≤ 256 * A ^ 4 * (a * H ^ 5 * (488 * X)) := by gcongr
            _ = _ := by ring
      _ < a * a ^ 3 := Nat.mul_lt_mul_of_pos_left hscale ha
      _ ≤ 256 * A ^ 4 * qq a b i ^ 4 := by nlinarith [hq]
  exact_mod_cast hs

/-- Failure of the line-exclusion scale gives the stronger exponent `5/17`. -/
theorem remainder_window_small_exponent {T H X A a C E D F : ℕ}
    (ha : 0 < a) (hA : 0 < A)
    (hscale : a ^ 3 ≤ F * A ^ 4 * H ^ 5 * X)
    (hgap : H * (A * T) ≤ C * a) (hheight : X * a ^ 3 ≤ E * A ^ 4 * H ^ 6)
    (hdrop : T ^ 2 ≤ D * A) : T ^ 17 ≤ F * E * C ^ 11 * D ^ 3 * a ^ 5 := by
  have h1 : a ^ 6 ≤ F * E * A ^ 8 * H ^ 11 := by
    calc a ^ 6 = a ^ 3 * a ^ 3 := by ring
      _ ≤ (F * A ^ 4 * H ^ 5 * X) * a ^ 3 := by gcongr
      _ = F * A ^ 4 * H ^ 5 * (X * a ^ 3) := by ring
      _ ≤ F * A ^ 4 * H ^ 5 * (E * A ^ 4 * H ^ 6) := by gcongr
      _ = _ := by ring
  have h2 : (T ^ 11 * A ^ 3) * (a ^ 6 * A ^ 8) ≤
      (F * E * C ^ 11 * a ^ 5) * (a ^ 6 * A ^ 8) := by
    calc _ = a ^ 6 * (A * T) ^ 11 := by ring
      _ ≤ (F * E * A ^ 8 * H ^ 11) * (A * T) ^ 11 := by gcongr
      _ = F * E * A ^ 8 * (H * (A * T)) ^ 11 := by ring
      _ ≤ F * E * A ^ 8 * (C * a) ^ 11 := by gcongr
      _ = _ := by ring
  have h3 := Nat.le_of_mul_le_mul_right h2 (by positivity : 0 < a ^ 6 * A ^ 8)
  calc T ^ 17 = T ^ 11 * (T ^ 2) ^ 3 := by ring
    _ ≤ T ^ 11 * (D * A) ^ 3 := by gcongr
    _ = (T ^ 11 * A ^ 3) * D ^ 3 := by ring
    _ ≤ (F * E * C ^ 11 * a ^ 5) * D ^ 3 := by gcongr
    _ = _ := by ring

end PierceLengthBound.FixedDividend
