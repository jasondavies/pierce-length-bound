/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PoweredJointPointCount
public import PierceLengthBound.JointLiftCountingSlack

/-! The actual joint box has polynomial height in the dividend. Consequently
the logarithm in the proved curve theorem costs a proved subpolynomial factor. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- For fixed powers the powered box remains polynomial in the dividend. -/
lemma poweredJointPointBoxHeight_polynomial {a A T : ℕ} (ha : 1 ≤ a) (hA : A ≤ a)
    (m n : ℕ) : poweredJointPointBoxHeight a A T m n ≤
      (10 ^ 25) ^ (m + n + 1) * a ^ (15 * (m + n + 1)) := by
  let B := jointPointBoxHeight a A T
  have hB : 1 ≤ B := jointPointBoxHeight_pos a A T
  have hH : 3 * selectedGapHeight a A T ≤ B := le_max_left _ _
  have hS : selectedCurvatureHeight a A T ≤ B :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hY : selectedRankFiveHeight a A T ≤ B :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hbox : poweredJointPointBoxHeight a A T m n ≤ B ^ (m + n + 1) := by
    apply max_le
    · exact hH.trans (by
        simpa only [pow_one] using Nat.pow_le_pow_right hB (by omega : 1 ≤ m + n + 1))
    · exact max_le ((Nat.pow_le_pow_left hS m).trans
        (Nat.pow_le_pow_right hB (by omega)))
        ((Nat.pow_le_pow_left hY n).trans (Nat.pow_le_pow_right hB (by omega)))
  calc _ ≤ B ^ (m + n + 1) := hbox
    _ ≤ (10 ^ 25 * a ^ 15) ^ (m + n + 1) := by
      exact Nat.pow_le_pow_left (jointPointBoxHeight_polynomial ha hA) _
    _ = _ := by simp only [mul_pow, ← pow_mul]

lemma poweredJointPointBoxHeight_le (a A T m n : ℕ) :
    poweredJointPointBoxHeight a A T m n ≤
      3 * max (max (selectedGapHeight a A T) (selectedCurvatureHeight a A T ^ m))
        (selectedRankFiveHeight a A T ^ n) := by
  unfold poweredJointPointBoxHeight
  apply max_le
  · exact Nat.mul_le_mul_left 3 ((le_max_left _ _).trans (le_max_left _ _))
  · apply max_le
    · have h := (le_max_right (selectedGapHeight a A T) (selectedCurvatureHeight a A T ^ m)).trans
        (le_max_left (max (selectedGapHeight a A T) (selectedCurvatureHeight a A T ^ m))
          (selectedRankFiveHeight a A T ^ n))
      omega
    · have h := le_max_right
        (max (selectedGapHeight a A T) (selectedCurvatureHeight a A T ^ m))
        (selectedRankFiveHeight a A T ^ n)
      omega

/-- For actual windows and fixed degree range, the curve theorem supplies the
subpolynomial coefficient needed by the per-pattern counting argument. -/
theorem selected_poweredJointGraph_gap_count_slow (m n lo hi : ℕ)
    (hlo : 0 < lo) (hlohi : lo ≤ hi) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ ∀ {a b s T A i : ℕ}, b < a →
      (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
      s + T ≤ P a b → 0 < T →
      ∀ I : Ideal (MvPolynomial (Fin 3) ℚ), I.IsPrime →
        (∃ δ : ℕ, lo ≤ δ ∧ δ ≤ hi ∧ ∃ N : ℕ, ∃ c : ℤ, ∀ k ≥ N,
          (Module.finrank ℚ
            (filteredCoordinateSpace (orbitPoweredJointGraphIdeal a b i m n I) k) : ℤ) =
              (δ : ℤ) * k + c) →
        ∀ G : Finset ℕ, G ⊆ selectedStarts a b s T A →
          (∀ l ∈ G, theta a b i = theta a b l) →
          (∀ l ∈ G, orbitFreeNodesQ a b l ∈ coordinateZeroLocus I) →
          ((G.image (kap a b)).card : ℝ) ≤ (R a : ℝ) *
            (max (max (selectedGapHeight a A T) (selectedCurvatureHeight a A T ^ m))
              (selectedRankFiveHeight a A T ^ n) : ℝ) ^ (1 / (lo : ℝ)) := by
  obtain ⟨C, hC, hcount⟩ := selected_poweredJointGraph_gap_count m n lo hi hlo hlohi
  let M := ⌈C * (3 : ℝ) ^ (1 / (lo : ℝ)) * 2⌉₊ + 1
  have hM : C * (3 : ℝ) ^ (1 / (lo : ℝ)) * 2 ≤ (M : ℝ) := by
    exact (Nat.le_ceil _).trans (by simp only [M, Nat.cast_add, Nat.cast_one]; linarith)
  have hMs : SlowGrowth (fun _ : ℕ => M) := by
    intro η hη
    refine ⟨M, by dsimp [M]; positivity, fun a ha => ?_⟩
    have hp := Real.one_le_rpow (by exact_mod_cast ha : (1 : ℝ) ≤ a) hη.le
    exact le_mul_of_one_le_right (Nat.cast_nonneg M) hp
  refine ⟨fun a => M * (Nat.log 2 ((10 ^ 25) ^ (m + n + 1) * a ^ (15 * (m + n + 1))) + 1),
    hMs.mul (polynomial_log_slow ((10 ^ 25) ^ (m + n + 1)) (15 * (m + n + 1))), ?_⟩
  intro a b s T A i hba hmem hsT hT I hI hd G hG hθ hz
  have ha : 1 ≤ a := by omega
  have hA : A ≤ a := by
    have := (hmem 0 hT).1
    have := (orb_le a b (s + 0)).trans hba.le
    omega
  let B := max (max (selectedGapHeight a A T) (selectedCurvatureHeight a A T ^ m))
    (selectedRankFiveHeight a A T ^ n)
  let L := Nat.log 2 ((10 ^ 25) ^ (m + n + 1) * a ^ (15 * (m + n + 1))) + 1
  have hlog : Real.log (poweredJointPointBoxHeight a A T m n) + 1 ≤ 2 * (L : ℝ) :=
    box_log_le_polynomial_log (poweredJointPointBoxHeight_pos a A T m n)
      (poweredJointPointBoxHeight_polynomial ha hA m n)
  have hbox : (poweredJointPointBoxHeight a A T m n : ℝ) ≤ 3 * (B : ℝ) := by
    exact_mod_cast poweredJointPointBoxHeight_le a A T m n
  have hp : (poweredJointPointBoxHeight a A T m n : ℝ) ^ (1 / (lo : ℝ)) ≤
      (3 : ℝ) ^ (1 / (lo : ℝ)) * (B : ℝ) ^ (1 / (lo : ℝ)) := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (Nat.cast_nonneg B)]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hbox (by positivity)
  calc ((G.image (kap a b)).card : ℝ) ≤
        C * (poweredJointPointBoxHeight a A T m n : ℝ) ^ (1 / (lo : ℝ)) *
          (Real.log (poweredJointPointBoxHeight a A T m n) + 1) :=
      hcount hba hmem hsT I hI hd G hG hθ hz
    _ ≤ C * ((3 : ℝ) ^ (1 / (lo : ℝ)) * (B : ℝ) ^ (1 / (lo : ℝ))) * (2 * L) := by
      gcongr
    _ = (C * (3 : ℝ) ^ (1 / (lo : ℝ)) * 2) * L * (B : ℝ) ^ (1 / (lo : ℝ)) := by ring
    _ ≤ (M : ℝ) * L * (B : ℝ) ^ (1 / (lo : ℝ)) := by gcongr
    _ = _ := by simp only [Nat.cast_mul, Nat.cast_max, Nat.cast_pow, B, L]

end
end PierceLengthBound.FixedDividend
