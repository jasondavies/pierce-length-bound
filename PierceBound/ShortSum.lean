/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceBound.SixStep

/-!
# Divisors in a dyadic range, counted over a short interval

`dcount A n` is the number of divisors of `n` in `[A, 2A)`. The drop argument of
`drop_bound` actually shows that a window run of length `T` satisfies
`T ≤ 2 ∑_{1 ≤ h ≤ 2A/(T-1)} dcount A (a + h)` (`drop_count_bound`). Any bound for
`∑_{x < n ≤ x + y} dcount A n` on short intervals therefore bounds `T`.
-/

@[expose] public section

namespace PierceBound

open Finset

/-- The number of divisors of `n` in `[A, 2A)`. -/
def dcount (A n : ℕ) : ℕ := (n.divisors.filter fun d => A ≤ d ∧ d < 2 * A).card

/-- **The drop bound, before applying any divisor estimate.** -/
theorem drop_count_bound {a A T : ℕ} {g : ℕ → ℕ} (W : Window a A T g) (hT : 2 ≤ T) :
    T ≤ 2 * ∑ h ∈ Icc 1 (2 * A / (T - 1)), dcount A (a + h) := by
  classical
  set J := range (T - 1)
  set h : ℕ → ℕ := fun j => g j - g (j + 1) with hh
  have hsum : ∑ j ∈ J, h j ≤ A - 1 := by
    have := W.sum_drops (T - 1) (by omega)
    have h0 := W.mem 0 (by omega)
    have h1 := W.mem (T - 1) (by omega)
    simp only [J, hh]
    omega
  set Sel := J.filter fun j => h j * (T - 1) ≤ 2 * A
  set Bad := J.filter fun j => ¬ (h j * (T - 1) ≤ 2 * A)
  have hsplit : Sel.card + Bad.card = T - 1 := by
    rw [card_filter_add_card_filter_not, card_range]
  have hbad : 2 * Bad.card < T - 1 := by
    have h1 : Bad.card * (2 * A + 1) ≤ ∑ j ∈ Bad, h j * (T - 1) := by
      rw [← smul_eq_mul]
      exact card_nsmul_le_sum _ _ _ fun j hj => by
        have := (mem_filter.mp hj).2; omega
    have h2 : ∑ j ∈ Bad, h j * (T - 1) ≤ ∑ j ∈ J, h j * (T - 1) :=
      sum_le_sum_of_subset (filter_subset _ _)
    have h3 : ∑ j ∈ J, h j * (T - 1) ≤ (A - 1) * (T - 1) := by
      rw [← sum_mul]; exact Nat.mul_le_mul_right _ hsum
    have h4 := h1.trans (h2.trans h3)
    have hA := W.one_le
    by_contra hcon
    push Not at hcon
    have : (T - 1) * (2 * A + 1) ≤ 2 * Bad.card * (2 * A + 1) := Nat.mul_le_mul_right _ hcon
    have : 2 * (A - 1) * (T - 1) < (T - 1) * (2 * A + 1) := by
      have : 2 * (A - 1) < 2 * A + 1 := by omega
      calc 2 * (A - 1) * (T - 1) < (2 * A + 1) * (T - 1) :=
            Nat.mul_lt_mul_of_pos_right this (by omega)
        _ = _ := by ring
    nlinarith
  have hsel : T ≤ 2 * Sel.card := by omega
  set H := 2 * A / (T - 1)
  have himg : ∀ j ∈ Sel, h j ∈ Icc 1 H := by
    intro j hj
    obtain ⟨hjJ, hjs⟩ := mem_filter.mp hj
    have hjT := mem_range.mp hjJ
    have := W.succ_lt (j := j) (by omega)
    exact mem_Icc.mpr ⟨by simp only [hh]; omega, (Nat.le_div_iff_mul_le (by omega)).mpr hjs⟩
  have hfib : ∀ b ∈ Icc 1 H, (Sel.filter fun j => h j = b).card ≤ dcount A (a + b) := by
    intro b hb
    have hb1 := (mem_Icc.mp hb).1
    apply card_le_card_of_injOn g
    · intro j hj
      obtain ⟨hjS, hjb⟩ := mem_filter.mp (Finset.mem_coe.mp hj)
      have hjT := mem_range.mp (mem_filter.mp hjS).1
      have hstep := W.step j (by omega)
      have hlt := W.succ_lt (j := j) (by omega)
      have hmem := W.mem j (by omega)
      have hdecomp := Nat.div_add_mod a (g j)
      rw [Finset.mem_coe, mem_filter, Nat.mem_divisors]
      refine ⟨⟨⟨a / g j + 1, ?_⟩, by omega⟩, hmem.1, hmem.2⟩
      simp only [hh] at hjb
      rw [← hstep] at hdecomp
      rw [← hjb]
      have : g (j + 1) ≤ g j := hlt.le
      zify [this] at hdecomp ⊢
      linarith
    · intro i hi j hj hij
      have hi' := mem_range.mp (mem_filter.mp (mem_filter.mp (Finset.mem_coe.mp hi)).1).1
      have hj' := mem_range.mp (mem_filter.mp (mem_filter.mp (Finset.mem_coe.mp hj)).1).1
      exact W.injOn (by simp; omega) (by simp; omega) hij
  have hcard : Sel.card ≤ ∑ b ∈ Icc 1 H, dcount A (a + b) := by
    rw [card_eq_sum_card_fiberwise himg]
    exact sum_le_sum hfib
  omega

/-- Reindexing `∑_{1 ≤ h ≤ Y} f(a + h) = ∑_{a < n ≤ a + Y} f(n)`. -/
lemma sum_Icc_shift (f : ℕ → ℕ) (a Y : ℕ) :
    ∑ h ∈ Icc 1 Y, f (a + h) = ∑ n ∈ Ioc a (a + Y), f n := by
  apply sum_nbij' (fun h => a + h) (fun n => n - a)
  · intro h hh; simp only [mem_Icc, mem_Ioc] at hh ⊢
    omega
  · intro n hn; simp only [mem_Icc, mem_Ioc] at hn ⊢
    omega
  · intro h _; simp
  · intro n hn; simp only [mem_Ioc] at hn; omega
  · intro h _; rfl

/-- The drop bound with the range padded to any `Y ≥ 2A/(T-1)`. -/
theorem drop_count_bound' {a A T Y : ℕ} {g : ℕ → ℕ} (W : Window a A T g) (hT : 2 ≤ T)
    (hY : 2 * A / (T - 1) ≤ Y) :
    T ≤ 2 * ∑ n ∈ Ioc a (a + Y), dcount A n := by
  have := drop_count_bound W hT
  rw [← sum_Icc_shift]
  calc T ≤ 2 * ∑ h ∈ Icc 1 (2 * A / (T - 1)), dcount A (a + h) := this
    _ ≤ 2 * ∑ h ∈ Icc 1 Y, dcount A (a + h) :=
        Nat.mul_le_mul_left _ (sum_le_sum_of_subset (Icc_subset_Icc_right hY))

end PierceBound
