/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendMainReduction
public import PierceLengthBound.FixedDividendSelection

/-!
# Global reduction for the proposed 18/61 bound

The conclusion in this file is conditional on a local window count. The divisor
estimate, integer rounding, complementary scales, root extraction, and dyadic
summation are discharged. The local count is not asserted as a theorem.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Finset

/-- The local estimate still to be supplied by coefficient-uniform curve counting. -/
def LocalWindowCount (K : ℕ → ℕ) : Prop :=
  ∀ a b s T A : ℕ, b < a →
    (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
    s + T ≤ P a b → 36 ≤ T →
    124928 * A ^ 4 * selectedGapHeight a A T ^ 5 * selectedMinorHeight a A T < a ^ 3 →
    T ^ 6 ≤ K a * selectedGapHeight a A T ^ 3 * selectedMinorHeight a A T ^ 29

lemma slowGrowth_add_one {K : ℕ → ℕ} (hK : SlowGrowth K) :
    SlowGrowth (fun a => K a + 1) := by
  intro η hη
  obtain ⟨C, hC, h⟩ := hK η hη
  refine ⟨C + 1, by positivity, fun a ha => ?_⟩
  have hpow : 1 ≤ (a : ℝ) ^ η := Real.one_le_rpow (by exact_mod_cast ha) hη.le
  have := h a ha
  push_cast
  nlinarith

/-- Every remainder window has the desired 305th-power bound, provided the local
count is available with the indicated slack. -/
theorem visits_305_of_local_count {K : ℕ → ℕ} (hlocal : LocalWindowCount K)
    {a b k Δ : ℕ} (hba : b < a) (hΔ : DivBound a Δ) :
    (visits a b k).card ≤ 35 ∨
      (visits a b k).card ^ 305 ≤ windowConstant305 * (K a + 1) * Δ ^ 61 * a ^ 90 := by
  by_cases hT : (visits a b k).card ≤ 35
  · exact Or.inl hT
  right
  set T := (visits a b k).card
  have hne : (visits a b k).Nonempty := by rw [← card_pos]; omega
  have W := visits_window hba.le hne
  set s := (visits a b k).min' hne
  have hmem : ∀ j < T, 2 ^ k ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * 2 ^ k := W.mem
  have hsT : s + T ≤ P a b := by
    have h := (hmem (T - 1) (by omega)).1
    have := lt_P_of_orb_pos (a := a) (b := b) (i := s + (T - 1))
      (lt_of_lt_of_le (Nat.two_pow_pos k) h)
    omega
  exact window_305_of_local_count (by omega)
    (six_step_bound W (by omega)) (drop_bound W hΔ (by omega))
    (hlocal a b s T (2 ^ k) hba hmem hsT (by omega))

/-- Conditional final reduction. The local curve count remains an explicit premise. -/
theorem P_le_18_61_of_local_count {K : ℕ → ℕ} (hK : SlowGrowth K)
    (hlocal : LocalWindowCount K) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((18 : ℝ) / 61 + ε) := by
  have h := P_le_of_visits (N := 305) (r := 90) (K := windowConstant305) (by norm_num)
    ((slowGrowth_add_one hK).mul ((tauMax_slow 32 7).pow 61)) fun a b k _ hba =>
      (visits_305_of_local_count (k := k) hlocal hba (tauMax_divBound a)).imp id
        fun h => h.trans_eq (by ring)
  intro ε hε
  obtain ⟨C, hC, hP⟩ := h ε hε
  refine ⟨C, hC, fun a b hb hba => ?_⟩
  have := hP a b hb hba
  norm_num at this ⊢
  exact this

end PierceLengthBound.FixedDividend
