/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.CurveCountingCoordinates
public import PierceLengthBound.PoweredJointPointBox
public import PierceLengthBound.OrbitGapCoordinates

/-! Apply the proved affine-curve theorem to actual powered joint-lift points and
count distinct gap vectors, the objects used in the pattern estimate. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

lemma poweredJointPointBoxHeight_pos (a A T m n : ℕ) :
    1 ≤ poweredJointPointBoxHeight a A T m n := by
  have h := le_max_left (3 * selectedGapHeight a A T)
    (max (selectedCurvatureHeight a A T ^ m) (selectedRankFiveHeight a A T ^ n))
  have hH : 1 ≤ selectedGapHeight a A T := Nat.le_add_left 1 _
  change 1 ≤ max (3 * selectedGapHeight a A T)
    (max (selectedCurvatureHeight a A T ^ m) (selectedRankFiveHeight a A T ^ n))
  omega

/-- Uniform counting on the actual powered joint graph, for any specified
bounded Hilbert-degree range. All box and orbit-membership inputs are proved. -/
theorem selected_poweredJointGraph_gap_count (m n lo hi : ℕ) (hlo : 0 < lo) (hlohi : lo ≤ hi) :
    ∃ C : ℝ, 0 < C ∧ ∀ {a b s T A i : ℕ}, b < a →
      (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
      s + T ≤ P a b →
      ∀ I : Ideal (MvPolynomial (Fin 3) ℚ), I.IsPrime →
        (∃ δ : ℕ, lo ≤ δ ∧ δ ≤ hi ∧ ∃ N : ℕ, ∃ c : ℤ, ∀ k ≥ N,
          (Module.finrank ℚ
            (filteredCoordinateSpace (orbitPoweredJointGraphIdeal a b i m n I) k) : ℤ) =
              (δ : ℤ) * k + c) →
        ∀ G : Finset ℕ, G ⊆ selectedStarts a b s T A →
          (∀ l ∈ G, theta a b i = theta a b l) →
          (∀ l ∈ G, orbitFreeNodesQ a b l ∈ coordinateZeroLocus I) →
          ((G.image (kap a b)).card : ℝ) ≤
            C * (poweredJointPointBoxHeight a A T m n : ℝ) ^ (1 / (lo : ℝ)) *
              (Real.log (poweredJointPointBoxHeight a A T m n) + 1) := by
  classical
  obtain ⟨C, hC, hcount⟩ := affine_curve_points_finite_coordinates
    (Fin 3 ⊕ Fin 4) lo hi (by simp) hlo hlohi
  refine ⟨C, hC, ?_⟩
  intro a b s T A i hba hmem hsT I hI hdegree G hG hθ hz
  obtain ⟨δ, hdlo, hdhi, hd⟩ := hdegree
  let : I.IsPrime := hI
  have hB : (1 : ℝ) ≤ poweredJointPointBoxHeight a A T m n := by
    exact_mod_cast poweredJointPointBoxHeight_pos a A T m n
  have hlog : 0 ≤ Real.log (poweredJointPointBoxHeight a A T m n) := Real.log_nonneg hB
  by_cases hne : G.Nonempty
  · obtain ⟨j, hj⟩ := hne
    have hjP := (selectedStart_spec hmem hsT (hG hj)).1
    have hprime : (orbitPoweredJointGraphIdeal a b i m n I).IsPrime := by
      rw [orbitPoweredJointGraph_congr (hθ j hj)]
      apply jointGraphIdeal_isPrime I _ _
      intro hmemD
      have hev := hz j hj _ hmemD
      rw [map_pow] at hev
      exact pow_ne_zero (m + n)
        (orbitJointDenominator_eval_ne_zero hba (by omega : j + 7 < P a b)) hev
    obtain ⟨l, hl, _hk, hinj⟩ := gap_image_representatives hba G
      (fun l hl => by have := (selectedStart_spec hmem hsT (hG hl)).1; omega) hθ
    choose J _hpos hpoint hbox using fun j =>
      selected_poweredJointGraph_integerPoint hba hmem hsT (hG (hl j))
        (hθ _ (hl j)) m n I (hz _ (hl j))
    let z (j : G.image (kap a b)) := orbitPoweredJointPoint a b (l j) (J j) m n
    have hz_inj : Function.Injective z := by
      intro j k he
      exact hinj (orbitFreeNodesQ_eq_of_poweredJointPoint_eq he)
    let S := Finset.univ.image z
    have hScard : S.card = (G.image (kap a b)).card := by
      dsimp only [S]
      rw [card_image_of_injective _ hz_inj, card_univ, Fintype.card_coe]
    have hc := hcount (orbitPoweredJointGraphIdeal a b i m n I) hprime δ hdlo hdhi hd
      (poweredJointPointBoxHeight a A T m n) hB S (by
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
