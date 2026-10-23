/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib

/-!
# Cube roots and a reciprocal telescope

Two elementary facts used by the partial-summation estimates: every `X ≥ 1` lies within a factor
`8` below a cube (`exists_cube_root`), and `1/r` telescopes as
`1/L + ∑_{r ≤ j < L} 1/(j(j+1))` (`inv_telescope`).
-/

@[expose] public section

namespace PierceLengthBound

open Finset

/-- `1/r = 1/L + ∑_{r ≤ j < L} 1/(j(j+1))`. -/
lemma inv_telescope {r L : ℕ} (hr : 1 ≤ r) (hrL : r ≤ L) :
    (1 : ℝ) / r = 1 / L + ∑ j ∈ Ico r L, (1 : ℝ) / (j * (j + 1)) := by
  induction L, hrL using Nat.le_induction with
  | base => simp
  | succ L hL ih =>
    rw [sum_Ico_succ_top hL, ih]
    have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    push_cast
    field_simp
    ring

/-- A cube root: `X ≤ L³ ≤ 8X`. -/
lemma exists_cube_root {X : ℕ} (hX : 1 ≤ X) : ∃ L : ℕ, 1 ≤ L ∧ X ≤ L ^ 3 ∧ L ^ 3 ≤ 8 * X := by
  classical
  have hex : ∃ L, X ≤ L ^ 3 := ⟨X, by nlinarith [Nat.le_self_pow (n := 3) (by norm_num) X]⟩
  set L := Nat.find hex
  have hL : X ≤ L ^ 3 := Nat.find_spec hex
  have hL1 : 1 ≤ L := by
    by_contra h; push Not at h
    have : L = 0 := by omega
    rw [this] at hL; simp at hL; omega
  refine ⟨L, hL1, hL, ?_⟩
  rcases Nat.lt_or_ge L 2 with h | h
  · have : L = 1 := by omega
    rw [this]; omega
  · have hmin : ¬ X ≤ (L - 1) ^ 3 := Nat.find_min hex (by omega)
    push Not at hmin
    have : L ≤ 2 * (L - 1) := by omega
    calc L ^ 3 ≤ (2 * (L - 1)) ^ 3 := Nat.pow_le_pow_left this 3
      _ = 8 * (L - 1) ^ 3 := by ring
      _ ≤ 8 * X := by omega

end PierceLengthBound
