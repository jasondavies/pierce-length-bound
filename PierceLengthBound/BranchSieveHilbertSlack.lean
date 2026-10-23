/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveParameterInduction
public import PierceLengthBound.JointLiftCountingSlack
import Mathlib.Tactic

/-! Absorbing the logarithmic height cost of four-parameter Hilbert
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

end
end PierceLengthBound.FixedDividend
