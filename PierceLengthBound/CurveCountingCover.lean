/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.CurveCountingCoordinates

/-! Sum the proved curve count over actual finite prime-component covers.
No disjointness of components and no extra counting hypothesis are required. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- A finite cover by bounded-degree prime curves costs only its number of
components. The degree and membership premises match the existing covers. -/
theorem affine_curve_cover_points (σ : Type*) [Fintype σ]
    (lo hi : ℕ) (hn : 2 ≤ Fintype.card σ) (hlo : 0 < lo) (hhi : lo ≤ hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : Finset (Ideal (MvPolynomial σ ℚ)),
      (∀ I ∈ T, I.IsPrime ∧ ∃ d : ℕ, lo ≤ d ∧ d ≤ hi ∧
        ∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
          (Module.finrank ℚ (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c) →
      ∀ B : ℝ, 1 ≤ B → ∀ S : Finset (σ → ℤ),
        (∀ z ∈ S, ∀ j, |(z j : ℝ)| ≤ B) →
        (∀ z ∈ S, ∃ I ∈ T, (fun j => (z j : ℚ)) ∈ coordinateZeroLocus I) →
        (S.card : ℝ) ≤ C * T.card * B ^ (1 / (lo : ℝ)) * (Real.log B + 1) := by
  classical
  obtain ⟨C, hC, hcount⟩ := affine_curve_points_finite_coordinates σ lo hi hn hlo hhi
  refine ⟨C, hC, ?_⟩
  intro T hT B hB S hbox hcover
  let U (I : Ideal (MvPolynomial σ ℚ)) := S.filter
    (fun z => (fun j => (z j : ℚ)) ∈ coordinateZeroLocus I)
  have hSU : S ⊆ T.biUnion U := by
    intro z hz
    obtain ⟨I, hI, hzI⟩ := hcover z hz
    exact Finset.mem_biUnion.mpr ⟨I, hI, Finset.mem_filter.mpr ⟨hz, hzI⟩⟩
  have hcard : S.card ≤ ∑ I ∈ T, (U I).card :=
    (Finset.card_le_card hSU).trans (Finset.card_biUnion_le)
  have hU (I : Ideal (MvPolynomial σ ℚ)) (hI : I ∈ T) :
      ((U I).card : ℝ) ≤ C * B ^ (1 / (lo : ℝ)) * (Real.log B + 1) := by
    obtain ⟨hprime, d, hdlo, hdhi, hd⟩ := hT I hI
    apply hcount I hprime d hdlo hdhi hd B hB (U I)
    · intro z hz
      exact hbox z (Finset.mem_filter.mp hz).1
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
  calc
    _ ≤ ∑ I ∈ T, ((U I).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _I ∈ T, C * B ^ (1 / (lo : ℝ)) * (Real.log B + 1) := Finset.sum_le_sum hU
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end
end PierceLengthBound.FixedDividend
