/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftWindow
public import PierceLengthBound.FixedDividendGlobalReduction

/-! Conditional global reduction for the proposed 128/435 exponent.
This file does not assert the conic or higher-degree counting estimates. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend

/-- The remaining local estimate, required only in the line-exclusion range. -/
def JointLiftLocalWindowCount (K : ℕ → ℕ) : Prop :=
  ∀ a b s T A : ℕ, b < a →
    (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
    s + T ≤ P a b → 36 ≤ T →
    124928 * A ^ 4 * selectedGapHeight a A T ^ 5 * selectedMinorHeight a A T < a ^ 3 →
    JointLiftCountBranches (K a) T (selectedGapHeight a A T) (selectedMinorHeight a A T)
      (selectedCurvatureHeight a A T) (selectedRankFiveHeight a A T)

/-- Apply the full integral-coordinate window reduction to actual dyadic visits. -/
theorem visits_227070_of_joint_lift_count {K : ℕ → ℕ} (hlocal : JointLiftLocalWindowCount K)
    {a b k Δ : ℕ} (hba : b < a) (hΔ : DivBound a Δ) :
    (visits a b k).card ≤ 35 ∨
      (visits a b k).card ^ 227070 ≤
        (jointLiftWindowBase * (K a + 1) * Δ ^ 175) ^ 56768 * a ^ 66816 := by
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
  exact window_227070_of_joint_lift_count (by omega)
    (six_step_bound W (by omega)) (drop_bound W hΔ (by omega))
    (hlocal a b s T (2 ^ k) hba hmem hsT (by omega))

/-- Conditional final theorem. The integral-coordinate local counting estimate is an
explicit premise, not an axiom or a proved unconditional result. -/
theorem P_le_128_435_of_joint_lift_count {K : ℕ → ℕ} (hK : SlowGrowth K)
    (hlocal : JointLiftLocalWindowCount K) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((128 : ℝ) / 435 + ε) := by
  have h := P_le_of_visits (N := 227070) (r := 66816) (K := jointLiftWindowBase ^ 56768)
    (by norm_num)
    (((slowGrowth_add_one hK).pow 56768).mul ((tauMax_slow 32 7).pow 9934400))
    fun a b k _ hba =>
      (visits_227070_of_joint_lift_count (k := k) hlocal hba (tauMax_divBound a)).imp id
        fun h => h.trans_eq (by simp only [mul_pow, ← pow_mul, mul_assoc])
  intro ε hε
  obtain ⟨C, hC, hP⟩ := h ε hε
  refine ⟨C, hC, fun a b hb hba => ?_⟩
  have := hP a b hb hba
  norm_num at this ⊢
  exact this

end PierceLengthBound.FixedDividend
