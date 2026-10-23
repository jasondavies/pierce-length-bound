/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveDilation
public import PierceLengthBound.BranchSieveHilbertSlack
import Mathlib.Tactic

/-! The coefficient-height and zero-scale terms in the actual arithmetic
vertex sieve. Both estimates are uniform in the common divisor of a vertex. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

theorem branch_dilated_height_polynomial (C d K a g : ℕ) (ha : 0 < a)
    (hg : g ≤ K * a ^ 7) :
    C * (a + 1) ^ d * g ^ d + 1 ≤ (C * (2 * K) ^ d + 1) * a ^ (8 * d) := by
  have hmain : C * (a + 1) ^ d * g ^ d ≤ C * (2 * K) ^ d * a ^ (8 * d) := by
    calc
      _ ≤ C * (2 * a) ^ d * (K * a ^ 7) ^ d := by gcongr; omega
      _ = _ := by
        rw [mul_pow, mul_pow, ← pow_mul, show 8 * d = d + 7 * d by omega,
          pow_add, mul_pow]
        ring
  have hpow : 1 ≤ a ^ (8 * d) := Nat.one_le_pow _ _ (by omega)
  nlinarith

theorem branch_zero_axis_card_le (B : ℕ) (hB : 0 < B)
    (S : Finset (Fin 4 → ℤ))
    (hS : ∀ x ∈ S, (∀ j, |x j| ≤ (B : ℤ)) ∧ x 0 = 0) :
    (S.card : ℝ) ≤ 27 * (B : ℝ) ^ (7 / 2 : ℝ) := by
  classical
  have hcard : S.card ≤ (2 * B + 1) ^ 3 := by
    calc
      S.card = (branchTailFiber S 0).card := by
        rw [branchTailFiber_card]
        congr 1
        symm
        exact filter_eq_self.mpr fun x hx => (hS x hx).2
      _ ≤ _ := branch_integer_box_card _ (fun x hx j =>
        (hS (Fin.cons 0 x) ((mem_branchTailFiber S 0 x).mp hx)).1 j.succ)
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hpow : (B : ℝ) ^ 3 ≤ (B : ℝ) ^ (7 / 2 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hBR (by norm_num)
  calc
    (S.card : ℝ) ≤ ((2 * B + 1 : ℕ) : ℝ) ^ 3 := by exact_mod_cast hcard
    _ ≤ (3 * B : ℝ) ^ 3 := by push_cast; gcongr; linarith
    _ = 27 * (B : ℝ) ^ 3 := by ring
    _ ≤ _ := by gcongr

end
end PierceLengthBound.FixedDividend
