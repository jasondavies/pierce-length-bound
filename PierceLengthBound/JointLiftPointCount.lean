/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.CurveCountingCoordinates
public import PierceLengthBound.JointLiftPointBox
public import PierceLengthBound.OrbitGapCoordinates

/-! # Counting points on the joint graph

The coefficient-uniform affine-curve bound of Castryck–Cluckers–Dittmann–Nguyen (quoted in
Section 8.9), applied to the integer points of the joint graph: for a graph of degree
`δ ∈ [lo, 5928]`, the selected starts of one pattern on a component have at most
`C B^(1/lo) (log B + 1)` distinct gap vectors, where `B` is the joint point box. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

lemma jointPointBoxHeight_pos (a A T : ℕ) : 1 ≤ jointPointBoxHeight a A T := by
  have h := le_max_left (3 * selectedGapHeight a A T)
    (max (selectedCurvatureHeight a A T) (selectedRankFiveHeight a A T))
  have hH : 1 ≤ selectedGapHeight a A T := Nat.le_add_left 1 _
  change 1 ≤ max (3 * selectedGapHeight a A T)
    (max (selectedCurvatureHeight a A T) (selectedRankFiveHeight a A T))
  omega

/-- Two joint points with the same coordinates have the same free nodes, whatever their
rank-five values. -/
lemma orbitFreeNodesQ_eq_of_jointPoint_eq {a b i l J K : ℕ}
    (h : orbitJointPoint a b i J = orbitJointPoint a b l K) :
    orbitFreeNodesQ a b i = orbitFreeNodesQ a b l := by
  funext j
  have he := congrFun h (Sum.inl j)
  change sq a b i (j.val + 1) = sq a b l (j.val + 1) at he
  dsimp only [sq] at he
  dsimp only [orbitFreeNodesQ]
  exact_mod_cast he

/-- If the joint graph over the prime component `I` has degree `δ ∈ [lo, 5928]`, then any set
of selected starts with the pattern of `i` and free nodes on `I` has at most
`C B^(1/lo) (log B + 1)` distinct gap vectors, where `B = jointPointBoxHeight a A T` and `C`
depends only on `lo`. -/
theorem selected_jointGraph_gap_count (lo : ℕ) (hlo : 0 < lo) (hlohi : lo ≤ 5928) :
    ∃ C : ℝ, 0 < C ∧ ∀ {a b s T A i : ℕ}, b < a →
      (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
      s + T ≤ P a b →
      ∀ I : Ideal (MvPolynomial (Fin 3) ℚ), I.IsPrime →
        (∃ δ : ℕ, lo ≤ δ ∧ δ ≤ 5928 ∧ ∃ N : ℕ, ∃ c : ℤ, ∀ m ≥ N,
          (Module.finrank ℚ
            (filteredCoordinateSpace (orbitJointGraphIdeal a b i I) m) : ℤ) =
              (δ : ℤ) * m + c) →
        ∀ G : Finset ℕ, G ⊆ selectedStarts a b s T A →
          (∀ l ∈ G, theta a b i = theta a b l) →
          (∀ l ∈ G, orbitFreeNodesQ a b l ∈ coordinateZeroLocus I) →
          ((G.image (kap a b)).card : ℝ) ≤
            C * (jointPointBoxHeight a A T : ℝ) ^ (1 / (lo : ℝ)) *
              (Real.log (jointPointBoxHeight a A T) + 1) := by
  classical
  obtain ⟨C, hC, hcount⟩ := affine_curve_points_finite_coordinates
    (Fin 3 ⊕ Fin 4) lo 5928 (by simp) hlo hlohi
  refine ⟨C, hC, ?_⟩
  intro a b s T A i hba hmem hsT I hI hdegree G hG hθ hz
  obtain ⟨δ, hdlo, hdhi, hd⟩ := hdegree
  let : I.IsPrime := hI
  have hB : (1 : ℝ) ≤ jointPointBoxHeight a A T := by
    exact_mod_cast jointPointBoxHeight_pos a A T
  have hlog : 0 ≤ Real.log (jointPointBoxHeight a A T) := Real.log_nonneg hB
  by_cases hne : G.Nonempty
  · obtain ⟨j, hj⟩ := hne
    have hjP := (selectedStart_spec hmem hsT (hG hj)).1
    have hprime : (orbitJointGraphIdeal a b i I).IsPrime := by
      rw [orbitJointGraph_congr (hθ j hj)]
      exact orbitJointGraphIdeal_isPrime hba (by omega : j + 7 < P a b) I (hz j hj)
    obtain ⟨l, hl, _hk, hinj⟩ := gap_image_representatives hba G
      (fun l hl => by have := (selectedStart_spec hmem hsT (hG hl)).1; omega) hθ
    choose J _hpos hpoint hbox using fun j =>
      selected_jointGraph_integerPoint hba hmem hsT (hG (hl j)) (hθ _ (hl j)) I (hz _ (hl j))
    let z (j : G.image (kap a b)) := orbitJointPoint a b (l j) (J j)
    have hz_inj : Function.Injective z := by
      intro j k he
      exact hinj (orbitFreeNodesQ_eq_of_jointPoint_eq he)
    let S := Finset.univ.image z
    have hScard : S.card = (G.image (kap a b)).card := by
      dsimp only [S]
      rw [card_image_of_injective _ hz_inj, card_univ, Fintype.card_coe]
    have hc := hcount (orbitJointGraphIdeal a b i I) hprime δ hdlo hdhi hd
      (jointPointBoxHeight a A T) hB S (by
        intro w hw k
        obtain ⟨j, _, rfl⟩ := mem_image.mp hw
        exact_mod_cast hbox j k) (by
        intro w hw
        obtain ⟨j, _, rfl⟩ := mem_image.mp hw
        exact hpoint j)
    rwa [hScard] at hc
  · have he : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he, image_empty, card_empty, Nat.cast_zero]
    positivity

end
end PierceLengthBound.FixedDividend
