/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.Main

/-! Extract real window bounds from integer-power estimates, then sum windows
with a uniform slowly growing coefficient. -/

@[expose] public section
namespace PierceLengthBound
open Finset

lemma window_real_bound_of_power {T a B N r : ℕ} {α : ℝ}
    (ha : 1 ≤ a) (hB : 1 ≤ B) (hN : 0 < N)
    (h : T ^ N ≤ B * a ^ r) (hexp : (r : ℝ) / N ≤ α) :
    (T : ℝ) ≤ (B : ℝ) * (a : ℝ) ^ α := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : (T : ℝ) ^ N ≤ (B : ℝ) * (a : ℝ) ^ r := by exact_mod_cast h
  have hr := Real.rpow_le_rpow (by positivity) hh (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹)
  rw [Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) (by omega : N ≠ 0),
    Real.mul_rpow (Nat.cast_nonneg _) (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg _)] at hr
  have hcoef : (B : ℝ) ^ ((N : ℝ)⁻¹) ≤ B := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hinv : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
    calc
      _ ≤ (B : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hB) hinv
      _ = B := Real.rpow_one _
  exact hr.trans (mul_le_mul hcoef
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast ha) (by simpa [div_eq_mul_inv] using hexp))
    (by positivity) (Nat.cast_nonneg _))

/-- A real-exponent window bound loses only an arbitrarily small power in
absorbing its coefficient and the number of dyadic windows. -/
theorem P_le_of_real_visits {S : ℕ → ℕ} {α : ℝ} (hS : SlowGrowth S) (hα : 0 ≤ α)
    (hvis : ∀ a b k : ℕ, 0 < b → b < a →
      (visits a b k).card ≤ 35 ∨ ((visits a b k).card : ℝ) ≤ (S a : ℝ) * (a : ℝ) ^ α) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ (α + ε) := by
  intro ε hε
  obtain ⟨Cs, hCs, hs⟩ := hS (ε / 2) (by positivity)
  obtain ⟨CL, hCL, hlog⟩ := log_add_one_le_rpow (ε / 2) (by positivity)
  refine ⟨CL * (35 + Cs), by positivity, fun a b hb hba => ?_⟩
  have ha : 1 ≤ a := by omega
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := by positivity
  have hwin (k) : ((visits a b k).card : ℝ) ≤ (35 + Cs) * (a : ℝ) ^ (α + ε / 2) := by
    rcases hvis a b k hb hba with h | h
    · have ht : ((visits a b k).card : ℝ) ≤ 35 := by exact_mod_cast h
      have hp := Real.one_le_rpow haR (by positivity : 0 ≤ α + ε / 2)
      nlinarith
    · calc _ ≤ (S a : ℝ) * (a : ℝ) ^ α := h
        _ ≤ (Cs * (a : ℝ) ^ (ε / 2)) * (a : ℝ) ^ α := by gcongr; exact hs a ha
        _ ≤ (35 + Cs) * (a : ℝ) ^ (α + ε / 2) := by
          rw [Real.rpow_add ha0]
          nlinarith [Real.rpow_nonneg (Nat.cast_nonneg a) α,
            Real.rpow_nonneg (Nat.cast_nonneg a) (ε / 2)]
  have hP : (P a b : ℝ) ≤ ((Nat.log 2 a + 1 : ℕ) : ℝ) *
      ((35 + Cs) * (a : ℝ) ^ (α + ε / 2)) := by
    rw [P_eq_sum_visits hba.le]
    push_cast
    calc ∑ k ∈ range (Nat.log 2 a + 1), ((visits a b k).card : ℝ)
        ≤ ∑ _k ∈ range (Nat.log 2 a + 1), (35 + Cs) * (a : ℝ) ^ (α + ε / 2) :=
          sum_le_sum fun k _ => hwin k
      _ = _ := by simp
  calc _ ≤ ((Nat.log 2 a + 1 : ℕ) : ℝ) * ((35 + Cs) * (a : ℝ) ^ (α + ε / 2)) := hP
    _ ≤ (CL * (a : ℝ) ^ (ε / 2)) * ((35 + Cs) * (a : ℝ) ^ (α + ε / 2)) :=
      mul_le_mul_of_nonneg_right (hlog a ha) (by positivity)
    _ = CL * (35 + Cs) * (a : ℝ) ^ (α + ε) := by
      rw [mul_mul_mul_comm, ← Real.rpow_add ha0]
      congr 2
      ring

end PierceLengthBound
