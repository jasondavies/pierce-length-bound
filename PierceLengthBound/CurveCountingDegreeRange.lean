/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.CurveCounting

/-! The curve count uniformly over a finite degree range `lo ≤ d ≤ hi`: the factors `d³` and
`log B + d` are absorbed into a constant depending on `hi`, and `B^{1/d} ≤ B^{1/lo}`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- For `n ≥ 2` and `0 < lo ≤ hi` there is a constant `C` such that every prime curve in `n`
coordinates of degree `d ∈ [lo, hi]` has at most `C B^{1/lo} (log B + 1)` integer points in the
box `[-B, B]ⁿ`. The constant depends only on `n` and `hi`. -/
theorem affine_curve_points_degree_range (n lo hi : ℕ) (hn : 2 ≤ n)
    (hlo : 0 < lo) (hhi : lo ≤ hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal (MvPolynomial (Fin n) ℚ), I.IsPrime →
      ∀ d : ℕ, lo ≤ d → d ≤ hi →
        (∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
          (Module.finrank ℚ (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c) →
      ∀ B : ℝ, 1 ≤ B → ∀ S : Finset (Fin n → ℤ),
        (∀ z ∈ S, ∀ j, |(z j : ℝ)| ≤ B) →
        (∀ z ∈ S, (fun j => (z j : ℚ)) ∈ coordinateZeroLocus I) →
        (S.card : ℝ) ≤ C * B ^ (1 / (lo : ℝ)) * (Real.log B + 1) := by
  obtain ⟨C, hC, hcount⟩ := affine_curve_finite_points n hn
  have hhi0 : (0 : ℝ) < hi := by exact_mod_cast (hlo.trans_le hhi)
  refine ⟨C * (hi : ℝ) ^ 4, by positivity, ?_⟩
  intro I hI d hdlo hdhi hdegree B hB S hbox hpoints
  have hd : 0 < d := hlo.trans_le hdlo
  have hh := hcount I hI d hd hdegree B hB S hbox hpoints
  have hdloR : (lo : ℝ) ≤ d := by exact_mod_cast hdlo
  have hdhiR : (d : ℝ) ≤ hi := by exact_mod_cast hdhi
  have hloR : (0 : ℝ) < lo := by exact_mod_cast hlo
  have hhi1 : (1 : ℝ) ≤ hi := by exact_mod_cast (hlo.trans_le hhi)
  have hlog := Real.log_nonneg hB
  have hp : B ^ (1 / (d : ℝ)) ≤ B ^ (1 / (lo : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hB (one_div_le_one_div_of_le hloR hdloR)
  have hloghi : Real.log B + d ≤ hi * (Real.log B + 1) := by
    nlinarith [mul_le_mul_of_nonneg_right hhi1 hlog]
  apply hh.trans
  calc
    _ ≤ C * (hi : ℝ) ^ 3 * B ^ (1 / (lo : ℝ)) * (hi * (Real.log B + 1)) := by gcongr
    _ = _ := by ring

end
end PierceLengthBound.FixedDividend
