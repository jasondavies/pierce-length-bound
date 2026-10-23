/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendWindow

/-!
# An elementary bound for windows with a large mean gap

A window with a large mean quotient gap has an elementary quarter-power bound.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend

/-- A window with a large mean quotient gap has an elementary quarter-power bound. -/
lemma window_large_mean_gap {a A T : ℕ} (ha : 1 ≤ a)
    (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3) (hbig : 28 * a < A * T) :
    T ^ 4 ≤ 122449 * a := by
  have h1 : (28 * a) ^ 2 * T ^ 4 ≤ 96000000 * a ^ 3 := by
    calc (28 * a) ^ 2 * T ^ 4 ≤ (A * T) ^ 2 * T ^ 4 := by gcongr
      _ = T ^ 6 * A ^ 2 := by ring
      _ ≤ _ := hsix
  have h2 : (784 * T ^ 4) * a ^ 2 ≤ (784 * (122449 * a)) * a ^ 2 := by
    calc (784 * T ^ 4) * a ^ 2 = (28 * a) ^ 2 * T ^ 4 := by ring
      _ ≤ 96000000 * a ^ 3 := h1
      _ ≤ (784 * (122449 * a)) * a ^ 2 := by ring_nf; omega
  have := Nat.le_of_mul_le_mul_right h2 (by positivity)
  omega

end PierceLengthBound.FixedDividend
