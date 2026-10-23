/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.HypersurfacePatternCountNonzero
public import PierceLengthBound.HypersurfacePatternCountZero

/-! Every zero on a maximal-minor chart lies in a zero or a nonzero fiber. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Finset

lemma chart_zero_count_le_fiber_counts (B : HypersurfaceChartPolynomial) (m : ℕ) :
    (((crossSet m).filter fun uv => eval
      (Sum.elim (fun i => (uv.2 i : ℚ)) (chartFirstVertex m uv.1)) B = 0).card : ℝ) ≤
      (zeroChartFibers B m).card + (nonzeroChartFibers B m).card := by
  classical
  have hs : ((crossSet m).filter fun uv => eval
      (Sum.elim (fun i => (uv.2 i : ℚ)) (chartFirstVertex m uv.1)) B = 0) ⊆
      zeroChartFibers B m ∪ nonzeroChartFibers B m := by
    intro uv huv
    obtain ⟨huv, hzero⟩ := mem_filter.mp huv
    by_cases hf : chartPolynomialFiber B (chartFirstVertex m uv.1) = 0
    · exact mem_union_left _ (mem_filter.mpr ⟨huv, hf⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨huv, hf, by
        rw [chartPolynomialFiber_eval]
        exact hzero⟩)
  exact_mod_cast (card_le_card hs).trans (card_union_le _ _)

end
end PierceLengthBound.FixedDividend
