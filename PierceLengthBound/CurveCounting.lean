/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AffineCurveBound
public import PierceLengthBound.FixedDividendFilteredIntersection
public import PierceLengthBound.FixedDividendComponents

/-! The CCDN affine curve bound `CCDN.affineCurveBound`, stated for the coordinate ideals and
filtered Hilbert functions of this development: a prime curve over `ℚ` in `n ≥ 2` coordinates,
of degree `d`, has at most `C d³ B^{1/d} (log B + d)` integer points in the box `[-B, B]ⁿ`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

lemma coordinateZeroLocus_eq_external {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ)) :
    coordinateZeroLocus I = CCDN.idealZeroLocus I := rfl

/-- For each `n ≥ 2` there is a constant `C` such that, for every prime
`I ⊆ ℚ[x₁, …, xₙ]` whose Hilbert function is eventually `d m + c` with `0 < d` and every
`B ≥ 1`, the zero locus of `I` has at most `C d³ B^{1/d} (log B + d)` integer points in the box
`[-B, B]ⁿ`. The constant depends only on `n`. -/
theorem affine_curve_counting (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal (MvPolynomial (Fin n) ℚ), I.IsPrime →
      ∀ d : ℕ, 0 < d →
        (∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
          (Module.finrank ℚ (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c) →
      ∀ B : ℝ, 1 ≤ B →
        (CCDN.count (coordinateZeroLocus I) B : ℝ) ≤
          C * (d : ℝ) ^ 3 * B ^ (1 / (d : ℝ)) * (Real.log B + d) := by
  obtain ⟨C, hC, hcount⟩ := CCDN.affineCurveBound n hn
  refine ⟨C, hC, ?_⟩
  intro I hI d hd hdegree B hB
  have hh := hcount I hI d hd hdegree B hB
  simpa only [coordinateZeroLocus_eq_external, CCDN.curveBound, mul_assoc] using hh

/-- The same bound for any finite set of integer points of the zero locus in the box
`[-B, B]ⁿ`. -/
theorem affine_curve_finite_points (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal (MvPolynomial (Fin n) ℚ), I.IsPrime →
      ∀ d : ℕ, 0 < d →
        (∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
          (Module.finrank ℚ (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c) →
      ∀ B : ℝ, 1 ≤ B → ∀ S : Finset (Fin n → ℤ),
        (∀ z ∈ S, ∀ j, |(z j : ℝ)| ≤ B) →
        (∀ z ∈ S, (fun j => (z j : ℚ)) ∈ coordinateZeroLocus I) →
        (S.card : ℝ) ≤ C * (d : ℝ) ^ 3 * B ^ (1 / (d : ℝ)) * (Real.log B + d) := by
  obtain ⟨C, hC, hcount⟩ := affine_curve_counting n hn
  refine ⟨C, hC, ?_⟩
  intro I hI d hd hdegree B hB S hbox hpoints
  have hS : S ⊆ CCDN.integralPoints (coordinateZeroLocus I) B := by
    intro z hz
    exact CCDN.mem_integralPoints.mpr ⟨hbox z hz, hpoints z hz⟩
  have hh : (S.card : ℝ) ≤ CCDN.count (coordinateZeroLocus I) B := by
    exact_mod_cast Finset.card_le_card hS
  exact hh.trans (hcount I hI d hd hdegree B hB)

end
end PierceLengthBound.FixedDividend
