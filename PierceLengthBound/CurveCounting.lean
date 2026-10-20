/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import AffineCurveCounting.AffineCurveBound
public import PierceLengthBound.FixedDividendFilteredIntersection
public import PierceLengthBound.FixedDividendComponents

/-! Apply the proved external curve-counting theorem to the coordinate ideals
and filtered Hilbert degrees used throughout the Pierce development. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

lemma coordinateSpace_eq_external {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ)) (N : ℕ) :
    filteredCoordinateSpace I N = AffineCurveCounting.coordinateSpace I N := rfl

lemma coordinateZeroLocus_eq_external {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ)) :
    coordinateZeroLocus I = AffineCurveCounting.idealZeroLocus I := rfl

/-- One coefficient-uniform constant works for all prime curves in each fixed
ambient dimension. This is a theorem, not a counting hypothesis. -/
theorem affine_curve_counting (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal (MvPolynomial (Fin n) ℚ), I.IsPrime →
      ∀ d : ℕ, 0 < d →
        (∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
          (Module.finrank ℚ (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c) →
      ∀ B : ℝ, 1 ≤ B →
        (AffineCurveCounting.count (coordinateZeroLocus I) B : ℝ) ≤
          C * (d : ℝ) ^ 3 * B ^ (1 / (d : ℝ)) * (Real.log B + d) := by
  obtain ⟨C, hC, hcount⟩ := AffineCurveCounting.affineCurveBound n hn
  refine ⟨C, hC, ?_⟩
  intro I hI d hd hdegree B hB
  have hh := hcount I hI d hd hdegree B hB
  simpa only [coordinateZeroLocus_eq_external, AffineCurveCounting.curveBound, mul_assoc] using hh

/-- The same bound applies directly to a finite family of distinct integer
points satisfying the source ideal, in the form used by the orbit arguments. -/
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
  have hS : S ⊆ AffineCurveCounting.integralPoints (coordinateZeroLocus I) B := by
    intro z hz
    exact AffineCurveCounting.mem_integralPoints.mpr ⟨hbox z hz, hpoints z hz⟩
  have hh : (S.card : ℝ) ≤ AffineCurveCounting.count (coordinateZeroLocus I) B := by
    exact_mod_cast Finset.card_le_card hS
  exact hh.trans (hcount I hI d hd hdegree B hB)

end
end PierceLengthBound.FixedDividend
