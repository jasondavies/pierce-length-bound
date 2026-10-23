/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ExceptionalSlack

/-! # Counting the patterns of a window

The selected starts of a window have at most `ordinaryPatternSlack a · X⁵` distinct full
patterns (Proposition 7.9), with a slowly growing divisor-count factor. Shared by the powered
joint, exterior lattice and polar local estimates; `patternSlack` is the combined slack of the
powered joint local estimate. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Finset

/-- Minor vectors of height at most `X` satisfying the Plücker relations number at most
`14581 τ X⁵`, where `τ` bounds the divisor counts of `1, …, X`. -/
theorem ordinary_minor_count {S : Finset (Fin 10 → ℤ)} {X τ : ℕ}
    (hX : 1 ≤ X) (hτ : 1 ≤ τ)
    (hS : ∀ p ∈ S, (∀ t, |p t| ≤ X) ∧ PluckerRel p)
    (hdiv : ∀ m ∈ Icc 1 X, m.divisors.card ≤ τ) : S.card ≤ 14581 * τ * X ^ 5 := by
  have hc := minor_vector_count hS
  have hs : ∑ m ∈ Icc 1 X, 729 * m ^ 4 * m.divisors.card ≤ 729 * X ^ 5 * τ := by
    calc
      _ ≤ ∑ _m ∈ Icc 1 X, 729 * X ^ 4 * τ := by
        apply sum_le_sum
        intro m hm
        have hmX := (mem_Icc.mp hm).2
        gcongr
        exact hdiv m hm
      _ = _ := by rw [sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]; ring
  have hp : 1 ≤ X ^ 5 * τ := Nat.mul_pos (by positivity) (by omega)
  nlinarith

/-- The slowly growing factor `14581 τ_max(10¹⁶ a⁷)` of the pattern count. -/
def ordinaryPatternSlack (a : ℕ) : ℕ := 14581 * tauMax (10 ^ 16 * a ^ 7)

lemma ordinaryPatternSlack_slow : SlowGrowth ordinaryPatternSlack := by
  have hc : SlowGrowth (fun _ : ℕ => 14581) := slowGrowth_const _
  exact hc.mul (tauMax_slow (10 ^ 16) 7)

/-- The selected starts of a window have at most `ordinaryPatternSlack a · X⁵` distinct full
patterns, where `X` is the minor height. -/
theorem selected_ordinary_pattern_count {a b s T A : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hT : 36 ≤ T) :
    ((selectedStarts a b s T A).image (fun i => plk (Mi a b i))).card ≤
      ordinaryPatternSlack a * selectedMinorHeight a A T ^ 5 := by
  have hX := selectedMinorHeight_pos hba hmem hsT hT
  have hXb := selectedMinorHeight_le hba hmem hT
  have hτ : 1 ≤ tauMax (10 ^ 16 * a ^ 7) := by
    simpa using (tau_le_tauMax (hX.trans hXb) : (1 : ℕ).divisors.card ≤ _)
  apply ordinary_minor_count hX hτ
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    exact ⟨selectedStart_minor_height hba hmem hsT hi, plucker _⟩
  · intro m hm
    exact tau_le_tauMax ((mem_Icc.mp hm).2.trans hXb)

/-- The combined slack `8 R(a) (ordinaryPatternSlack a + exceptionalPatternSlack a)`. -/
def patternSlack (R : ℕ → ℕ) (a : ℕ) : ℕ :=
  8 * R a * (ordinaryPatternSlack a + exceptionalPatternSlack a)

lemma patternSlack_slow {R : ℕ → ℕ} (hR : SlowGrowth R) :
    SlowGrowth (patternSlack R) := by
  have hc : SlowGrowth (fun _ : ℕ => 8) := slowGrowth_const _
  exact (hc.mul hR).mul (slowGrowth_add ordinaryPatternSlack_slow exceptionalPatternSlack_slow)

end PierceLengthBound.FixedDividend
