/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftWindow
public import PierceLengthBound.FixedDividendGlobalReduction

/-! Conditional global reduction for the proposed 151/513 exponent.
This file does not assert the conic or higher-degree counting estimates. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend

/-- The remaining local estimate, required only in the line-exclusion range. -/
def IntegralLiftLocalWindowCount (K : ℕ → ℕ) : Prop :=
  ∀ a b s T A : ℕ, b < a →
    (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
    s + T ≤ P a b → 36 ≤ T →
    124928 * A ^ 4 * selectedGapHeight a A T ^ 5 * selectedMinorHeight a A T < a ^ 3 →
    IntegralLiftCountBranches (K a) T (selectedGapHeight a A T) (selectedMinorHeight a A T) (selectedLiftHeight a A T)

/-- Apply the full integral-coordinate window reduction to actual dyadic visits. -/
theorem visits_26163_of_integral_lift_count {K : ℕ → ℕ} (hlocal : IntegralLiftLocalWindowCount K)
    {a b k Δ : ℕ} (hba : b < a) (hΔ : DivBound a Δ) :
    (visits a b k).card ≤ 35 ∨
      (visits a b k).card ^ 26163 ≤
        (integralLiftWindowBase * (K a + 1) * Δ ^ 101) ^ 6541 * a ^ 7701 := by
  by_cases hT : (visits a b k).card ≤ 35
  · exact Or.inl hT
  right
  set T := (visits a b k).card
  have hne : (visits a b k).Nonempty := by rw [← Finset.card_pos]; omega
  have W := visits_window hba.le hne
  set s := (visits a b k).min' hne
  have hmem : ∀ j < T, 2 ^ k ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * 2 ^ k := W.mem
  have hsT : s + T ≤ P a b := by
    have h := (hmem (T - 1) (by omega)).1
    have := lt_P_of_orb_pos (a := a) (b := b) (i := s + (T - 1))
      (lt_of_lt_of_le (Nat.two_pow_pos k) h)
    omega
  exact window_26163_of_integral_lift_count (by omega)
    (six_step_bound W (by omega)) (drop_bound W hΔ (by omega))
    (hlocal a b s T (2 ^ k) hba hmem hsT (by omega))

/-- Conditional final theorem. The integral-coordinate local counting estimate is an
explicit premise, not an axiom or a proved unconditional result. -/
theorem P_le_151_513_of_integral_lift_count {K : ℕ → ℕ} (hK : SlowGrowth K)
    (hlocal : IntegralLiftLocalWindowCount K) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((151 : ℝ) / 513 + ε) := by
  have h := P_le_of_visits (N := 26163) (r := 7701) (K := integralLiftWindowBase ^ 6541)
    (by norm_num)
    (((slowGrowth_add_one hK).pow 6541).mul ((tauMax_slow 32 7).pow 660641))
    fun a b k _ hba =>
      (visits_26163_of_integral_lift_count (k := k) hlocal hba (tauMax_divBound a)).imp id
        fun h => h.trans_eq (by simp only [mul_pow, ← pow_mul, mul_assoc])
  intro ε hε
  obtain ⟨C, hC, hP⟩ := h ε hε
  refine ⟨C, hC, fun a b hb hba => ?_⟩
  have := hP a b hb hba
  norm_num at this ⊢
  exact this

end PierceLengthBound.FixedDividend
