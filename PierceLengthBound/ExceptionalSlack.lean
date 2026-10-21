/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ExceptionalOrbitCount
public import PierceLengthBound.FixedDividendCountAssembly

/-! Absorbing the proved exceptional-pattern logarithm on actual orbit windows. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Finset

/-- The base-two logarithm of any fixed polynomial range is subpolynomial. -/
theorem polynomial_log_slow (c e : ℕ) :
    SlowGrowth (fun a => Nat.log 2 (c * a ^ e) + 1) := by
  intro η hη
  obtain ⟨C, hC, hbound⟩ := log_add_one_le_rpow η hη
  let D := Nat.log 2 c + e + 2
  refine ⟨D * C, by dsimp [D]; positivity, fun a ha => ?_⟩
  have hpoly : c * a ^ e ≤ 2 ^ ((Nat.log 2 c + 1) + e * (Nat.log 2 a + 1)) := by
    calc c * a ^ e ≤ 2 ^ (Nat.log 2 c + 1) * (2 ^ (Nat.log 2 a + 1)) ^ e :=
        Nat.mul_le_mul (Nat.lt_pow_succ_log_self (by decide) c).le
          (Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self (by decide) a).le _)
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; ring
  have hl := Nat.log_mono_right (b := 2) hpoly
  rw [Nat.log_pow (by decide : 1 < 2)] at hl
  have hd : Nat.log 2 (c * a ^ e) + 1 ≤ D * (Nat.log 2 a + 1) := by
    dsimp [D]
    nlinarith
  have hdR : ((Nat.log 2 (c * a ^ e) + 1 : ℕ) : ℝ) ≤ D * ((Nat.log 2 a + 1 : ℕ) : ℝ) :=
    by exact_mod_cast hd
  calc ((Nat.log 2 (c * a ^ e) + 1 : ℕ) : ℝ) ≤ D * ((Nat.log 2 a + 1 : ℕ) : ℝ) := hdR
    _ ≤ D * (C * (a : ℝ) ^ η) := by gcongr; exact hbound a ha
    _ = _ := by ring

/-- A convenient simplified version of the exact exceptional-pattern constant. -/
lemma exceptional_count_bound_simplify {X : ℕ} (hX : 1 ≤ X) :
    4 * ((6 * X + 1) ^ 3 + (Nat.log 2 (3 * X) + 1) * (273375 * (3 * X) ^ 4)) ≤
      88574872 * (Nat.log 2 (3 * X) + 1) * X ^ 4 := by
  have hs : (6 * X + 1) ^ 3 ≤ 343 * X ^ 4 := by
    calc (6 * X + 1) ^ 3 ≤ (7 * X) ^ 3 := Nat.pow_le_pow_left (by omega) _
      _ = 343 * X ^ 3 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (by decide))
  have hs' : (6 * X + 1) ^ 3 ≤ 343 * (Nat.log 2 (3 * X) + 1) * X ^ 4 := by
    calc (6 * X + 1) ^ 3 ≤ 343 * X ^ 4 := hs
      _ = 343 * 1 * X ^ 4 := by ring
      _ ≤ _ := by gcongr; omega
  calc _ ≤ 4 * (343 * (Nat.log 2 (3 * X) + 1) * X ^ 4 +
      (Nat.log 2 (3 * X) + 1) * (273375 * (3 * X) ^ 4)) := by gcongr
    _ = _ := by ring

/-- A proved subpolynomial coefficient for exceptional patterns. -/
def exceptionalPatternSlack (a : ℕ) : ℕ :=
  88574872 * (Nat.log 2 (3 * 10 ^ 16 * a ^ 7) + 1)

theorem exceptionalPatternSlack_slow : SlowGrowth exceptionalPatternSlack := by
  have hc : SlowGrowth (fun _ : ℕ => 88574872) := slowGrowth_const _
  exact hc.mul (polynomial_log_slow (3 * 10 ^ 16) 7)

/-- The exceptional-pattern contribution now has a proved `X⁴` coefficient
with subpolynomial dependence on the dividend. -/
theorem selected_exceptional_pattern_count_slack {a b s T A : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hT : 36 ≤ T) :
    (((selectedStarts a b s T A).image (fun i => plk (Mi a b i))).filter
      fun p => ∃ d, ExceptionalMinorRelation p d).card ≤
      exceptionalPatternSlack a * selectedMinorHeight a A T ^ 4 := by
  have hX := selectedMinorHeight_pos hba hmem hsT hT
  have hXb := selectedMinorHeight_le hba hmem hT
  have hlog : Nat.log 2 (3 * selectedMinorHeight a A T) ≤
      Nat.log 2 (3 * 10 ^ 16 * a ^ 7) :=
    Nat.log_mono_right (by nlinarith)
  exact ((selected_exceptional_pattern_count hba hmem hsT hT).trans
    (exceptional_count_bound_simplify hX)).trans (by unfold exceptionalPatternSlack; gcongr)

end PierceLengthBound.FixedDividend
