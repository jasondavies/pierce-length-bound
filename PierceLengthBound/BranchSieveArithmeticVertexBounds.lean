/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveParameterInduction
public import PierceLengthBound.JointLiftCountingSlack
import Mathlib.Tactic

/-! The coefficient-height and zero-scale terms in the actual arithmetic
vertex sieve. Both estimates are uniform in the common divisor of a vertex.

Absorbing the logarithmic height cost of four-parameter Hilbert
irreducibility into a natural-valued subpolynomial coefficient. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

theorem branch_hilbert_four_size_eq (H B : ℕ) (hB : 0 < B) :
    branchHilbertSize 4 H B = (1 + Real.log (H + 1 : ℕ)) ^ 4 *
      (B : ℝ) ^ (7 / 2 : ℝ) * (1 + Real.log B) ^ 17 := by
  unfold branchHilbertSize
  norm_num only
  congr 2
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_sub (by positivity)]
  norm_num

theorem branch_four_parameter_hilbert_slack (C : ℝ) (hC : 0 ≤ C)
    (c e k f : ℕ) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ ∀ a H B : ℕ, 0 < a → 0 < B →
      H + 1 ≤ c * a ^ e → B ≤ k * a ^ f →
      C * branchHilbertSize 4 H B ≤ (R a : ℝ) * (B : ℝ) ^ (7 / 2 : ℝ) := by
  let M : ℕ := ⌈C * 2 ^ 21⌉₊ + 1
  let L₁ (a : ℕ) := Nat.log 2 (c * a ^ e) + 1
  let L₂ (a : ℕ) := Nat.log 2 (k * a ^ f) + 1
  refine ⟨fun a => M * L₁ a ^ 4 * L₂ a ^ 17,
    ((slowGrowth_const M).mul ((polynomial_log_slow c e).pow 4)).mul
      ((polynomial_log_slow k f).pow 17), ?_⟩
  intro a H B _ha hB hHpoly hBpoly
  have h₁ : 1 + Real.log (H + 1 : ℕ) ≤ 2 * (L₁ a : ℝ) := by
    simpa only [L₁, add_comm] using
      box_log_le_polynomial_log (by omega : 1 ≤ H + 1) hHpoly
  have h₂ : 1 + Real.log (B : ℝ) ≤ 2 * (L₂ a : ℝ) := by
    simpa only [L₂, add_comm] using box_log_le_polynomial_log hB hBpoly
  have hM : C * 2 ^ 21 ≤ (M : ℝ) := (Nat.le_ceil _).trans (by
    dsimp only [M]
    push_cast
    linarith)
  rw [branch_hilbert_four_size_eq H B hB]
  calc
    _ ≤ C * ((2 * (L₁ a : ℝ)) ^ 4 * (B : ℝ) ^ (7 / 2 : ℝ) *
        (2 * (L₂ a : ℝ)) ^ 17) := by gcongr
    _ = (C * 2 ^ 21) * (L₁ a : ℝ) ^ 4 * (L₂ a : ℝ) ^ 17 *
        (B : ℝ) ^ (7 / 2 : ℝ) := by ring
    _ ≤ (M : ℝ) * (L₁ a : ℝ) ^ 4 * (L₂ a : ℝ) ^ 17 *
        (B : ℝ) ^ (7 / 2 : ℝ) := by gcongr
    _ = _ := by push_cast; ring

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
