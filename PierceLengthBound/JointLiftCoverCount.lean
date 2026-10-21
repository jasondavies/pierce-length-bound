/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftCountingSlack

/-! Count actual gap vectors covered by at most twenty-four joint graphs.
Components may overlap, and the reference pattern need not occur on each one. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

/-- The full finite-cover count, with all arithmetic inputs proved. For the
candidate exponent take `lo = 17`; its graph-degree premise remains geometric. -/
theorem selected_jointGraph_cover_gap_count_slow (lo : ℕ) (hlo : 0 < lo)
    (hlohi : lo ≤ 5928) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ ∀ {a b s T A i : ℕ}, b < a →
      (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
      s + T ≤ P a b → 0 < T →
      ∀ S : Finset (Ideal (MvPolynomial (Fin 3) ℚ)), S.card ≤ 24 →
        (∀ I ∈ S, I.IsPrime ∧ ∃ δ : ℕ, lo ≤ δ ∧ δ ≤ 5928 ∧
          ∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
            (Module.finrank ℚ
              (filteredCoordinateSpace (orbitJointGraphIdeal a b i I) m) : ℤ) =
                (δ : ℤ) * m + c) →
        ∀ G : Finset ℕ, G ⊆ selectedStarts a b s T A →
          (∀ l ∈ G, theta a b i = theta a b l) →
          (∀ l ∈ G, ∃ I ∈ S, orbitFreeNodesQ a b l ∈ coordinateZeroLocus I) →
          ((G.image (kap a b)).card : ℝ) ≤ (R a : ℝ) *
            (max (max (selectedGapHeight a A T) (selectedCurvatureHeight a A T))
              (selectedRankFiveHeight a A T) : ℝ) ^ (1 / (lo : ℝ)) := by
  classical
  obtain ⟨R, hR, hcount⟩ := selected_jointGraph_gap_count_slow lo hlo hlohi
  have h24 : SlowGrowth (fun _ : ℕ => 24) := slowGrowth_const _
  refine ⟨fun a => 24 * R a, h24.mul hR, ?_⟩
  intro a b s T A i hba hmem hsT hT S hS hdegree G hG hθ hcover
  let U (I : Ideal (MvPolynomial (Fin 3) ℚ)) :=
    G.filter (fun l => orbitFreeNodesQ a b l ∈ coordinateZeroLocus I)
  let B := max (max (selectedGapHeight a A T) (selectedCurvatureHeight a A T))
    (selectedRankFiveHeight a A T)
  have hsub : G.image (kap a b) ⊆ S.biUnion (fun I => (U I).image (kap a b)) := by
    intro k hk
    obtain ⟨l, hl, rfl⟩ := mem_image.mp hk
    obtain ⟨I, hI, hz⟩ := hcover l hl
    exact mem_biUnion.mpr ⟨I, hI, mem_image.mpr ⟨l, mem_filter.mpr ⟨hl, hz⟩, rfl⟩⟩
  have hcard : (G.image (kap a b)).card ≤ ∑ I ∈ S, ((U I).image (kap a b)).card :=
    (card_le_card hsub).trans card_biUnion_le
  have hU (I : Ideal (MvPolynomial (Fin 3) ℚ)) (hI : I ∈ S) :
      (((U I).image (kap a b)).card : ℝ) ≤ (R a : ℝ) * (B : ℝ) ^ (1 / (lo : ℝ)) := by
    obtain ⟨hprime, hd⟩ := hdegree I hI
    simp only [B, Nat.cast_max]
    apply hcount hba hmem hsT hT I hprime hd (U I)
    · intro l hl
      exact hG (mem_filter.mp hl).1
    · intro l hl
      exact hθ l (mem_filter.mp hl).1
    · intro l hl
      exact (mem_filter.mp hl).2
  calc ((G.image (kap a b)).card : ℝ) ≤
        ∑ I ∈ S, (((U I).image (kap a b)).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _I ∈ S, (R a : ℝ) * (B : ℝ) ^ (1 / (lo : ℝ)) := sum_le_sum hU
    _ = (S.card : ℝ) * ((R a : ℝ) * (B : ℝ) ^ (1 / (lo : ℝ))) := by
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ (24 : ℝ) * ((R a : ℝ) * (B : ℝ) ^ (1 / (lo : ℝ))) := by
      gcongr
      exact_mod_cast hS
    _ = _ := by simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_max, B]; ring

end
end PierceLengthBound.FixedDividend
