/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ConicWindow
public import PierceLengthBound.FixedDividendGlobalReduction

/-! Conditional global reduction for the proposed 135/458 exponent.
This file does not assert the conic or higher-degree counting estimates. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend

/-- The remaining local estimate, required only in the line-exclusion range. -/
def ConicLocalWindowCount (K : ℕ → ℕ) : Prop :=
  ∀ a b s T A : ℕ, b < a →
    (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
    s + T ≤ P a b → 36 ≤ T →
    124928 * A ^ 4 * selectedGapHeight a A T ^ 5 * selectedMinorHeight a A T < a ^ 3 →
    ConicCountBranches (K a) T (selectedGapHeight a A T) (selectedMinorHeight a A T)

/-- Apply the full conic window reduction to actual dyadic visits. -/
theorem visits_4580_of_conic_count {K : ℕ → ℕ} (hlocal : ConicLocalWindowCount K)
    {a b k Δ : ℕ} (hba : b < a) (hΔ : DivBound a Δ) :
    (visits a b k).card ≤ 35 ∨
      (visits a b k).card ^ 4580 ≤
        (conicWindowBase * (K a + 1) * Δ ^ 91) ^ 1145 * a ^ 1350 := by
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
  exact window_4580_of_conic_count (by omega)
    (six_step_bound W (by omega)) (drop_bound W hΔ (by omega))
    (hlocal a b s T (2 ^ k) hba hmem hsT (by omega))

/-- Conditional final theorem. The coefficient-uniform local conic count is an
explicit premise, not an axiom or a proved unconditional result. -/
theorem P_le_135_458_of_conic_count {K : ℕ → ℕ} (hK : SlowGrowth K)
    (hlocal : ConicLocalWindowCount K) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((135 : ℝ) / 458 + ε) := by
  have h := P_le_of_visits (N := 4580) (r := 1350) (K := conicWindowBase ^ 1145)
    (by norm_num)
    (((slowGrowth_add_one hK).pow 1145).mul ((tauMax_slow 32 7).pow 104195))
    fun a b k _ hba =>
      (visits_4580_of_conic_count (k := k) hlocal hba (tauMax_divBound a)).imp id
        fun h => h.trans_eq (by simp only [mul_pow, ← pow_mul, mul_assoc])
  intro ε hε
  obtain ⟨C, hC, hP⟩ := h ε hε
  refine ⟨C, hC, fun a b hb hba => ?_⟩
  have := hP a b hb hba
  norm_num at this ⊢
  exact this

end PierceLengthBound.FixedDividend
