/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveArithmeticVertexCount
public import PierceLengthBound.BranchSievePatternCountSlow
public import PierceLengthBound.PolarProjectionGeometryGoodPattern
public import PierceLengthBound.PolarProjectionBound

/-! The polar-projection length bounds (Theorems 1.1 and 10.8). The scaled-vertex
sieve and its completion to full patterns (Lemma 10.5) bound the branch-bad
patterns; together with the retained-component geometry this gives the six-term
window estimate (Proposition 10.7) for all positive powers `m`, `n`. -/

@[expose] public section
namespace PierceLengthBound
noncomputable section
open Finset

namespace FixedDividend

/-- Branch-bad full patterns in a selected window number at most a slowly
growing factor times `X^{14/3}`, from the scaled-vertex sieve and Lemma 10.5. -/
theorem polar_branch_bad_pattern_count_slow :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ PolarBadPatternCount PolarBranchGood R := by
  classical
  obtain ⟨R, hR, hvertex⟩ := branch_vertex_good_scaled_box_count_slow
  obtain ⟨Rbad, hRbad, hbad⟩ := selected_branch_pattern_count_slow branchVertexGood hR hvertex
  refine ⟨Rbad, hRbad, ?_⟩
  intro a b s T A hba hmem hsT hT
  have hcount := hbad hba hmem hsT hT
  convert hcount using 1
  apply congrArg (fun S : Finset (Fin 10 → ℤ) => (S.card : ℝ))
  apply filter_congr
  intro p hp
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
  have hp0 := orbit_pattern_first (l := i) hba
    (by have := (selectedStart_spec hmem hsT hi).1; omega)
  exact not_congr (polarBranchGood_iff_vertex hp0)

/-- The six-term polar window estimate (Proposition 10.7) for positive powers `m`, `n`. -/
theorem polar_projection_six_term_estimates (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ PolarProjectionSixTermEstimate m n R := by
  obtain ⟨R, hR, hbad⟩ := polar_branch_bad_pattern_count_slow
  exact polar_six_term_of_branch_bad_pattern_count m n hm hn hR hbad

end FixedDividend

/-- The rational polar-projection bound `P(a,b) ≪ a^{4317/14677+ε}`, with
curvature power three and rank-five-invariant power two (Theorem 10.8 at
`(m, n) = (3, 2)`). -/
theorem P_le_4317_14677 :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((4317 : ℝ) / 14677 + ε) := by
  obtain ⟨R, hR, hcount⟩ := FixedDividend.polar_projection_six_term_estimates 3 2
    (by decide) (by decide)
  exact FixedDividend.P_le_4317_14677_of_six_term_count hR hcount

/-- The optimized polar-projection bound `P(a,b) ≪ a^{β_*+ε}` with
`β_* = (41301 - 3√82849)/137480` (Theorem 1.1). -/
theorem P_le_polar_optimal :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ (((41301 : ℝ) - 3 * Real.sqrt 82849) / 137480 + ε) := by
  exact FixedDividend.P_le_polar_optimal_of_six_term_estimates
    FixedDividend.polar_projection_six_term_estimates

end
end PierceLengthBound
