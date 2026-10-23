/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftCountingSlack
public import PierceLengthBound.IntegralLiftOrbitConicProperness

/-! Affine-curve counting in the three node coordinates, in the node box `3H`,
`H = selectedGapHeight a A T`: a component of affine Hilbert degree between `2` and `24`
carries `≪ a^ε H^{1/2}` gap vectors. This gives the square-root bound used for exceptional
patterns (`selected_pattern_curve_gap_count_slow`). -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

/-- A component of affine Hilbert degree between `2` and `24` (so not a line) has at most
`C (3H)^{1/2} (log 3H + 1)` gap vectors in the node box. -/
theorem selected_curve_gap_count :
    ∃ C : ℝ, 0 < C ∧ ∀ {a b s T A i : ℕ}, b < a →
      (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
      s + T ≤ P a b →
      ∀ I : Ideal (MvPolynomial (Fin 3) ℚ), I.IsPrime →
        (∃ d : ℕ, 2 ≤ d ∧ d ≤ 24 ∧ ∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
          (Module.finrank ℚ (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c) →
        ∀ G : Finset ℕ, G ⊆ selectedStarts a b s T A →
          (∀ l ∈ G, theta a b i = theta a b l) →
          (∀ l ∈ G, orbitFreeNodesQ a b l ∈ coordinateZeroLocus I) →
          ((G.image (kap a b)).card : ℝ) ≤
            C * (3 * (selectedGapHeight a A T : ℝ)) ^ (1 / (2 : ℝ)) *
              (Real.log (3 * (selectedGapHeight a A T : ℝ)) + 1) := by
  classical
  obtain ⟨C, hC, hcount⟩ := affine_curve_points_finite_coordinates (Fin 3) 2 24
    (by simp) (by decide) (by decide)
  refine ⟨C, hC, ?_⟩
  intro a b s T A i hba hmem hsT I hI hd G hG hθ hz
  obtain ⟨d, hd2, hd24, hdegree⟩ := hd
  obtain ⟨l, hl, _hk, hinj⟩ := gap_image_representatives hba G
    (fun l hl => by have := (selectedStart_spec hmem hsT (hG hl)).1; omega) hθ
  let z (j : G.image (kap a b)) := orbitFreeNodesZ a b (l j)
  have hz_inj : Function.Injective z := by
    intro j k he
    apply hinj
    dsimp only
    rw [← orbitFreeNodesZ_cast a b (l j), ← orbitFreeNodesZ_cast a b (l k)]
    change (fun t => (z j t : ℚ)) = (fun t => (z k t : ℚ))
    rw [he]
  let S := Finset.univ.image z
  have hScard : S.card = (G.image (kap a b)).card := by
    dsimp only [S]
    rw [card_image_of_injective _ hz_inj, card_univ, Fintype.card_coe]
  have hH : 1 ≤ selectedGapHeight a A T := Nat.le_add_left 1 _
  have hB : (1 : ℝ) ≤ 3 * (selectedGapHeight a A T : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ 3 * selectedGapHeight a A T)
  have hc := hcount I hI d hd2 hd24 hdegree (3 * (selectedGapHeight a A T : ℝ)) hB S (by
    intro w hw t
    obtain ⟨j, _, rfl⟩ := mem_image.mp hw
    have hb := selected_node_height hmem hsT (hG (hl j)) t
    change |(z j t : ℝ)| ≤ _
    exact_mod_cast hb) (by
    intro w hw
    obtain ⟨j, _, rfl⟩ := mem_image.mp hw
    change (fun t => (orbitFreeNodesZ a b (l j) t : ℚ)) ∈ coordinateZeroLocus I
    rw [orbitFreeNodesZ_cast]
    exact hz _ (hl j))
  rwa [hScard] at hc

/-- `selected_curve_gap_count` with the logarithm absorbed into a subpolynomial
coefficient, uniformly in all selected windows. -/
theorem selected_curve_gap_count_slow :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ ∀ {a b s T A i : ℕ}, b < a →
      (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
      s + T ≤ P a b →
      ∀ I : Ideal (MvPolynomial (Fin 3) ℚ), I.IsPrime →
        (∃ d : ℕ, 2 ≤ d ∧ d ≤ 24 ∧ ∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
          (Module.finrank ℚ (filteredCoordinateSpace I m) : ℤ) = (d : ℤ) * m + c) →
        ∀ G : Finset ℕ, G ⊆ selectedStarts a b s T A →
          (∀ l ∈ G, theta a b i = theta a b l) →
          (∀ l ∈ G, orbitFreeNodesQ a b l ∈ coordinateZeroLocus I) →
          ((G.image (kap a b)).card : ℝ) ≤ (R a : ℝ) *
            (selectedGapHeight a A T : ℝ) ^ (1 / (2 : ℝ)) := by
  obtain ⟨C, hC, hcount⟩ := selected_curve_gap_count
  let M := ⌈C * (3 : ℝ) ^ (1 / (2 : ℝ)) * 2⌉₊ + 1
  have hM : C * (3 : ℝ) ^ (1 / (2 : ℝ)) * 2 ≤ (M : ℝ) := by
    exact (Nat.le_ceil _).trans (by simp only [M, Nat.cast_add, Nat.cast_one]; linarith)
  have hMs : SlowGrowth (fun _ : ℕ => M) := slowGrowth_const _
  refine ⟨fun a => M * (Nat.log 2 (87 * a ^ 1) + 1),
    hMs.mul (polynomial_log_slow 87 1), ?_⟩
  intro a b s T A i hba hmem hsT I hI hd G hG hθ hz
  have hH : 1 ≤ selectedGapHeight a A T := Nat.le_add_left 1 _
  have hpoly : 3 * selectedGapHeight a A T ≤ 87 * a ^ 1 := by
    have := Nat.div_le_self (28 * a) (A * T)
    dsimp only [selectedGapHeight]
    simp only [pow_one]
    omega
  let L := Nat.log 2 (87 * a ^ 1) + 1
  have hlog : Real.log (3 * (selectedGapHeight a A T : ℝ)) + 1 ≤ 2 * (L : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      box_log_le_polynomial_log (by omega : 1 ≤ 3 * selectedGapHeight a A T) hpoly
  have hc := hcount hba hmem hsT I hI hd G hG hθ hz
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (Nat.cast_nonneg _)] at hc
  calc _ ≤ C * ((3 : ℝ) ^ (1 / (2 : ℝ)) *
        (selectedGapHeight a A T : ℝ) ^ (1 / (2 : ℝ))) *
        (Real.log (3 * (selectedGapHeight a A T : ℝ)) + 1) := hc
    _ ≤ C * ((3 : ℝ) ^ (1 / (2 : ℝ)) *
        (selectedGapHeight a A T : ℝ) ^ (1 / (2 : ℝ))) * (2 * L) := by gcongr
    _ = (C * (3 : ℝ) ^ (1 / (2 : ℝ)) * 2) * L *
        (selectedGapHeight a A T : ℝ) ^ (1 / (2 : ℝ)) := by ring
    _ ≤ (M : ℝ) * L * (selectedGapHeight a A T : ℝ) ^ (1 / (2 : ℝ)) := by gcongr
    _ = _ := by simp only [Nat.cast_mul, L]

end
end PierceLengthBound.FixedDividend
