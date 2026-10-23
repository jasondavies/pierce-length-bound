/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointPatternCount

/-!
# Summing per-pattern estimates

The length `T` of a window is at most eight times the number of pairs of a pattern and a gap
vector among its selected starts (`le_eight_mul_pair_image`). Summing a `JointPatternEstimate`
over the patterns, the `O(X⁴)` exceptional patterns contribute `R H^{1/2}` each, and every pattern
contributes at most its nonexceptional bound `R (1 + B^e)`. This first step is shared by the
powered, lattice and polar local estimates; each then bounds the remaining sum over the
patterns for its own box.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

/-- The window length is bounded by the per-pattern estimate summed over the selected patterns:
`T ≤ 8 (R ∑_p (1 + B_p^e) + R H^{1/2} · Ex X⁴)`. -/
theorem selected_count_le_pattern_sum {B : (Fin 10 → ℤ) → ℕ → ℕ → ℕ → ℝ} {e : ℝ}
    {R : ℕ → ℕ} (hcurve : JointPatternEstimate B e R) {a b s T A : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hT : 36 ≤ T)
    (hscale : 124928 * A ^ 4 * selectedGapHeight a A T ^ 5 * selectedMinorHeight a A T < a ^ 3)
    (hB : ∀ p a A T, 0 ≤ B p a A T := by intros; positivity) :
    (T : ℝ) ≤ 8 * ((R a : ℝ) *
      ∑ p ∈ (selectedStarts a b s T A).image (fun i => plk (Mi a b i)), (1 + B p a A T ^ e) +
      (R a : ℝ) * (selectedGapHeight a A T : ℝ) ^ (1 / 2 : ℝ) *
        (exceptionalPatternSlack a * (selectedMinorHeight a A T : ℝ) ^ 4)) := by
  classical
  set G := selectedStarts a b s T A
  set pm := fun i => plk (Mi a b i)
  set Pset := G.image pm
  let E := fun p : Fin 10 → ℤ => ∃ d, ExceptionalMinorRelation p d
  set V := (R a : ℝ) * (selectedGapHeight a A T : ℝ) ^ (1 / 2 : ℝ)
  let F := fun p => (R a : ℝ) * (1 + B p a A T ^ e)
  have hF (p) : 0 ≤ F p :=
    mul_nonneg (Nat.cast_nonneg _) (add_nonneg zero_le_one (Real.rpow_nonneg (hB _ _ _ _) _))
  have hs : ((G.image fun i => (pm i, kap a b i)).card : ℝ) ≤
      ∑ p ∈ Pset, (((G.filter fun i => pm i = p).image (kap a b)).card : ℝ) := by
    exact_mod_cast pair_image_card_le_sum G pm (kap a b)
  have hsum : ∑ p ∈ Pset, (((G.filter fun i => pm i = p).image (kap a b)).card : ℝ) ≤
      ∑ p ∈ Pset, F p + V * ((Pset.filter E).card : ℝ) := by
    calc _ ≤ ∑ p ∈ Pset, (F p + if E p then V else 0) := by
          refine sum_le_sum fun p hp => ?_
          have hc := hcurve a b s T A hba hmem hsT hT hscale p hp
          have := hF p
          split_ifs at hc ⊢ <;> linarith
      _ = _ := by
          rw [sum_add_distrib, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
          ring
  have hPE : ((Pset.filter E).card : ℝ) ≤
      exceptionalPatternSlack a * (selectedMinorHeight a A T : ℝ) ^ 4 := by
    exact_mod_cast selected_exceptional_pattern_count_slack hba hmem hsT hT
  have hTc : (T : ℝ) ≤ 8 * ((G.image fun i => (pm i, kap a b i)).card : ℝ) := by
    exact_mod_cast le_eight_mul_pair_image hba hmem hsT hT
  have hV : 0 ≤ V := by positivity
  refine hTc.trans (mul_le_mul_of_nonneg_left (hs.trans (hsum.trans ?_)) (by norm_num))
  rw [mul_sum]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hPE hV)

end
end PierceLengthBound.FixedDividend
