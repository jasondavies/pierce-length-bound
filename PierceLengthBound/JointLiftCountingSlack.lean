/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftPointCount
public import PierceLengthBound.ExceptionalSlack

/-! # Slowly growing coefficient for the joint graph count

The joint-lift point box has height at most `10²⁵ a¹⁵`, so the logarithm in the curve-counting
bound costs only a slowly growing factor. This turns the per-pattern graph count
`selected_jointGraph_gap_count` into a bound `R(a) B^(1/lo)` with `R` slowly growing. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- The joint-lift point box has height at most `10²⁵ a¹⁵`; only the logarithm of this bound
is used. -/
lemma jointPointBoxHeight_polynomial {a A T : ℕ} (ha : 1 ≤ a) (hA : A ≤ a) :
    jointPointBoxHeight a A T ≤ 10 ^ 25 * a ^ 15 := by
  have hH : selectedGapHeight a A T ≤ 29 * a := by
    have := Nat.div_le_self (28 * a) (A * T)
    unfold selectedGapHeight
    omega
  have hpow (k : ℕ) (hk : k ≤ 15) : a ^ k ≤ a ^ 15 := Nat.pow_le_pow_right ha hk
  apply max_le
  · calc 3 * selectedGapHeight a A T ≤ 87 * a := by omega
      _ ≤ 10 ^ 25 * a ^ 15 := by
        have := hpow 1 (by decide)
        norm_num only [pow_one] at this
        gcongr; norm_num
  · apply max_le
    · calc selectedCurvatureHeight a A T ≤
            4352 * A ^ 3 * selectedGapHeight a A T ^ 3 := Nat.div_le_self _ _
        _ ≤ 4352 * a ^ 3 * (29 * a) ^ 3 := by gcongr
        _ = (4352 * 29 ^ 3) * a ^ 6 := by ring
        _ ≤ 10 ^ 25 * a ^ 15 := by gcongr <;> norm_num
    · calc selectedRankFiveHeight a A T ≤
            1259991040 * A ^ 5 * selectedGapHeight a A T ^ 10 := Nat.div_le_self _ _
        _ ≤ 1259991040 * a ^ 5 * (29 * a) ^ 10 := by gcongr
        _ = (1259991040 * 29 ^ 10) * a ^ 15 := by ring
        _ ≤ 10 ^ 25 * a ^ 15 := by gcongr; norm_num

/-- If `1 ≤ B ≤ c aᵉ`, then `log B + 1` is at most twice the binary logarithm of `c aᵉ` (plus
one), a slowly growing function of `a` (`polynomial_log_slow`). -/
lemma box_log_le_polynomial_log {B c e a : ℕ} (hB : 1 ≤ B) (hpoly : B ≤ c * a ^ e) :
    Real.log (B : ℝ) + 1 ≤ 2 * ((Nat.log 2 (c * a ^ e) + 1 : ℕ) : ℝ) := by
  have hpow : (B : ℝ) ≤ (2 : ℝ) ^ (Nat.log 2 (c * a ^ e) + 1) := by
    exact_mod_cast hpoly.trans (Nat.lt_pow_succ_log_self (by decide) (c * a ^ e)).le
  have hlog := Real.log_le_log (by exact_mod_cast (show 0 < B by omega)) hpow
  rw [Real.log_pow] at hlog
  have htwo : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hN : (0 : ℝ) ≤ Nat.log 2 (c * a ^ e) := Nat.cast_nonneg _
  push_cast at hlog ⊢
  nlinarith

/-- If the joint graph over a prime component `I` has degree `δ ∈ [lo, 5928]`, then any set of
selected starts of one pattern with free nodes on `I` has at most `R(a) B^(1/lo)` distinct gap
vectors, where `B = max(H, S, Y)` and `R` grows slowly. -/
theorem selected_jointGraph_gap_count_slow (lo : ℕ) (hlo : 0 < lo) (hlohi : lo ≤ 5928) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ ∀ {a b s T A i : ℕ}, b < a →
      (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
      s + T ≤ P a b → 0 < T →
      ∀ I : Ideal (MvPolynomial (Fin 3) ℚ), I.IsPrime →
        (∃ δ : ℕ, lo ≤ δ ∧ δ ≤ 5928 ∧ ∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
          (Module.finrank ℚ
            (filteredCoordinateSpace (orbitJointGraphIdeal a b i I) m) : ℤ) =
              (δ : ℤ) * m + c) →
        ∀ G : Finset ℕ, G ⊆ selectedStarts a b s T A →
          (∀ l ∈ G, theta a b i = theta a b l) →
          (∀ l ∈ G, orbitFreeNodesQ a b l ∈ coordinateZeroLocus I) →
          ((G.image (kap a b)).card : ℝ) ≤ (R a : ℝ) *
            (max (max (selectedGapHeight a A T) (selectedCurvatureHeight a A T))
              (selectedRankFiveHeight a A T) : ℝ) ^ (1 / (lo : ℝ)) := by
  obtain ⟨C, hC, hcount⟩ := selected_jointGraph_gap_count lo hlo hlohi
  let M := ⌈C * (3 : ℝ) ^ (1 / (lo : ℝ)) * 2⌉₊ + 1
  have hM : C * (3 : ℝ) ^ (1 / (lo : ℝ)) * 2 ≤ (M : ℝ) := by
    exact (Nat.le_ceil _).trans (by simp only [M, Nat.cast_add, Nat.cast_one]; linarith)
  have hMs : SlowGrowth (fun _ : ℕ => M) := slowGrowth_const _
  refine ⟨fun a => M * (Nat.log 2 (10 ^ 25 * a ^ 15) + 1),
    hMs.mul (polynomial_log_slow (10 ^ 25) 15), ?_⟩
  intro a b s T A i hba hmem hsT hT I hI hd G hG hθ hz
  have ha : 1 ≤ a := by omega
  have hA : A ≤ a := by
    have := (hmem 0 hT).1
    have := (orb_le a b (s + 0)).trans hba.le
    omega
  let B := max (max (selectedGapHeight a A T) (selectedCurvatureHeight a A T))
    (selectedRankFiveHeight a A T)
  let L := Nat.log 2 (10 ^ 25 * a ^ 15) + 1
  have hlog : Real.log (jointPointBoxHeight a A T) + 1 ≤ 2 * (L : ℝ) :=
    box_log_le_polynomial_log (jointPointBoxHeight_pos a A T)
      (jointPointBoxHeight_polynomial ha hA)
  have hbox : (jointPointBoxHeight a A T : ℝ) ≤ 3 * (B : ℝ) := by
    exact_mod_cast jointPointBoxHeight_le a A T
  have hp : (jointPointBoxHeight a A T : ℝ) ^ (1 / (lo : ℝ)) ≤
      (3 : ℝ) ^ (1 / (lo : ℝ)) * (B : ℝ) ^ (1 / (lo : ℝ)) := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (Nat.cast_nonneg B)]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hbox (by positivity)
  calc ((G.image (kap a b)).card : ℝ) ≤
        C * (jointPointBoxHeight a A T : ℝ) ^ (1 / (lo : ℝ)) *
          (Real.log (jointPointBoxHeight a A T) + 1) :=
      hcount hba hmem hsT I hI hd G hG hθ hz
    _ ≤ C * ((3 : ℝ) ^ (1 / (lo : ℝ)) * (B : ℝ) ^ (1 / (lo : ℝ))) * (2 * L) := by
      gcongr
    _ = (C * (3 : ℝ) ^ (1 / (lo : ℝ)) * 2) * L * (B : ℝ) ^ (1 / (lo : ℝ)) := by ring
    _ ≤ (M : ℝ) * L * (B : ℝ) ^ (1 / (lo : ℝ)) := by gcongr
    _ = _ := by simp only [Nat.cast_mul, Nat.cast_max, B, L]

end
end PierceLengthBound.FixedDividend
