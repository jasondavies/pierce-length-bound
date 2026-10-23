/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FortyFiveMain

/-!
# Reciprocal weights

The real-valued form of the existing partial-summation estimate for reciprocal weights.
-/

@[expose] public section

namespace PierceLengthBound.FixedDividend

open Finset

/-- The real-valued form of the existing partial-summation estimate. -/
theorem reciprocal_sum_bound {ι : Type*} (S : Finset ι) (R : ι → ℕ) {L C : ℕ}
    (hR : ∀ p ∈ S, 1 ≤ R p ∧ R p ≤ L)
    (hc : ∀ r, 1 ≤ r → (S.filter fun p => R p ≤ r).card ≤ C * r ^ 3) :
    (L : ℝ) * ∑ p ∈ S, (1 : ℝ) / R p ≤ S.card + C * (L : ℝ) ^ 3 := by
  classical
  rcases S.eq_empty_or_nonempty with hS | ⟨p0, hp0⟩
  · subst hS; simp only [sum_empty, mul_zero, card_empty, Nat.cast_zero, zero_add]; positivity
  have hL : 1 ≤ L := ((hR p0 hp0).1).trans (hR p0 hp0).2
  have hLr : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  set g : ℕ → ℝ := fun j => (1 : ℝ) / (j * (j + 1))
  have key : ∑ p ∈ S, (1 : ℝ) / R p =
      S.card / L + ∑ j ∈ Ico 1 L, ((S.filter fun p => R p ≤ j).card : ℝ) * g j := by
    have h1 : ∀ p ∈ S, (1 : ℝ) / R p = 1 / L + ∑ j ∈ Ico 1 L, if R p ≤ j then g j else 0 := by
      intro p hp
      rw [inv_telescope (hR p hp).1 (hR p hp).2, ← sum_filter]
      congr 1
      refine sum_congr ?_ fun _ _ => rfl
      ext j; simp only [mem_Ico, mem_filter]; have := (hR p hp).1; omega
    rw [sum_congr rfl h1, sum_add_distrib, sum_comm]
    congr 1
    · rw [sum_const, nsmul_eq_mul]; ring
    · refine sum_congr rfl fun j _ => ?_
      rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hbound : ∑ j ∈ Ico 1 L, ((S.filter fun p => R p ≤ j).card : ℝ) * g j ≤ C * L ^ 2 := by
    calc ∑ j ∈ Ico 1 L, ((S.filter fun p => R p ≤ j).card : ℝ) * g j
        ≤ ∑ _j ∈ Ico 1 L, (C : ℝ) * L := by
          refine sum_le_sum fun j hj => ?_
          have hj1 : 1 ≤ j := (mem_Ico.mp hj).1
          have hjL : j < L := (mem_Ico.mp hj).2
          have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
          have hc' : ((S.filter fun p => R p ≤ j).card : ℝ) ≤ C * (j : ℝ) ^ 3 := by
            exact_mod_cast hc j hj1
          have hg : g j ≤ 1 / (j : ℝ) ^ 2 := by
            simp only [g]
            apply one_div_le_one_div_of_le (by positivity)
            nlinarith
          have hgp : 0 ≤ g j := by simp only [g]; positivity
          calc ((S.filter fun p => R p ≤ j).card : ℝ) * g j ≤ (C * (j : ℝ) ^ 3)
                 * (1 / (j : ℝ) ^ 2) :=
                mul_le_mul hc' hg hgp (by positivity)
            _ = C * j := by field_simp
            _ ≤ C * L := by gcongr
      _ = ((L - 1 : ℕ) : ℝ) * (C * L) := by rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ C * L ^ 2 := by
          have : ((L - 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast Nat.sub_le L 1
          calc ((L - 1 : ℕ) : ℝ) * (C * L) ≤ (L : ℝ) * (C * L) :=
                mul_le_mul_of_nonneg_right this (by positivity)
            _ = C * L ^ 2 := by ring
  calc (L : ℝ) * ∑ p ∈ S, (1 : ℝ) / R p
      = L * (S.card / L + ∑ j ∈ Ico 1 L,
          ((S.filter fun p => R p ≤ j).card : ℝ) * g j) := by rw [key]
    _ ≤ L * (S.card / L + C * L ^ 2) := by gcongr
    _ = S.card + C * (L : ℝ) ^ 3 := by field_simp

end PierceLengthBound.FixedDividend
