/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftComponentCount
public import PierceLengthBound.FixedDividendRationalParityCover

/-! The actual rational component cover supplies the full nonexceptional
pattern estimate. No graph-degree or retained-identity hypothesis remains. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

/-- The nonexceptional branch of the joint-lift pattern count, with all
geometric and arithmetic inputs discharged on the actual orbit. -/
theorem selected_nonexceptional_joint_gap_count_slow :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ ∀ {a b s T A i : ℕ}, b < a →
      (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
      s + T ≤ P a b → 36 ≤ T → i + 7 < P a b →
      NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i) →
      ∀ G : Finset ℕ, G ⊆ selectedStarts a b s T A →
        (∀ l ∈ G, theta a b i = theta a b l) →
        ((G.image (kap a b)).card : ℝ) ≤ (R a : ℝ) *
          (1 + (max (max (selectedGapHeight a A T) (selectedCurvatureHeight a A T))
            (selectedRankFiveHeight a A T) : ℝ) ^ (1 / (17 : ℝ))) := by
  classical
  obtain ⟨R, hR, hcount⟩ := selected_joint_component_gap_count_slow
  have h24 : SlowGrowth (fun _ : ℕ => 24) := by
    intro η hη
    refine ⟨24, by norm_num, fun a ha => ?_⟩
    have := Real.one_le_rpow (by exact_mod_cast ha : (1 : ℝ) ≤ a) hη.le
    norm_num
    linarith
  refine ⟨fun a => 24 * R a, h24.mul hR, ?_⟩
  intro a b s T A i hba hmem hsT hT hi hne G hG hθ
  obtain ⟨hρ, hu, hv⟩ := orbit_rational_pattern_signs hba (by omega : i + 6 < P a b)
  have hL : (Lz a b i : ℚ) ≠ 0 := by
    have := Lz_pos hba (by omega : i + 5 < P a b)
    exact_mod_cast (show Lz a b i ≠ 0 by omega)
  have hneQ : NonexceptionalPattern (patternRhoQ a b i : ℝ)
      (patternUQ a b i : ℝ) (patternVQ a b i : ℝ) := by simpa using hne
  obtain ⟨S, hS, hcomp, hcover⟩ := rational_nonexceptional_curve_decomposition hρ hu hv hneQ
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i) a hL (by exact_mod_cast (show a ≠ 0 by omega))
  have hpoints (l) (hl : l ∈ G) : ∃ I ∈ S, orbitFreeNodesQ a b l ∈ coordinateZeroLocus I := by
    apply (hcover _).mp
    change MvPolynomial.eval (orbitFreeNodesQ a b l) (orbitCurveQuadraticQ a b i) = 0 ∧
      MvPolynomial.eval (orbitFreeNodesQ a b l) (orbitCurveEquationQ a b i) = 0
    rw [(orbitCurve_polynomials_congr (hθ l hl)).1, (orbitCurve_polynomials_congr (hθ l hl)).2]
    apply orbit_rational_curve_zeros hba
    have := (selectedStart_spec hmem hsT (hG hl)).1
    omega
  let U (I : Ideal (MvPolynomial (Fin 3) ℚ)) :=
    G.filter (fun l => orbitFreeNodesQ a b l ∈ coordinateZeroLocus I)
  let B : ℝ := max (max (selectedGapHeight a A T : ℝ) (selectedCurvatureHeight a A T))
    (selectedRankFiveHeight a A T)
  have hsub : G.image (kap a b) ⊆ S.biUnion (fun I => (U I).image (kap a b)) := by
    intro k hk
    obtain ⟨l, hl, rfl⟩ := mem_image.mp hk
    obtain ⟨I, hI, hz⟩ := hpoints l hl
    exact mem_biUnion.mpr ⟨I, hI, mem_image.mpr ⟨l, mem_filter.mpr ⟨hl, hz⟩, rfl⟩⟩
  have hcard : (G.image (kap a b)).card ≤ ∑ I ∈ S, ((U I).image (kap a b)).card :=
    (card_le_card hsub).trans card_biUnion_le
  have hU (I : Ideal (MvPolynomial (Fin 3) ℚ)) (hI : I ∈ S) :
      (((U I).image (kap a b)).card : ℝ) ≤ (R a : ℝ) * (1 + B ^ (1 / (17 : ℝ))) := by
    obtain ⟨hprime, _, hf, hg, d, _, hd24, _, hsplit, hd⟩ := hcomp I hI
    apply hcount hba hmem hsT hT hne I hprime hf hg ⟨d, hd24, hsplit, hd⟩ (U I)
    · intro l hl
      exact hG (mem_filter.mp hl).1
    · intro l hl
      exact hθ l (mem_filter.mp hl).1
    · intro l hl
      exact (mem_filter.mp hl).2
  calc ((G.image (kap a b)).card : ℝ) ≤
        ∑ I ∈ S, (((U I).image (kap a b)).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _I ∈ S, (R a : ℝ) * (1 + B ^ (1 / (17 : ℝ))) := sum_le_sum hU
    _ = (S.card : ℝ) * ((R a : ℝ) * (1 + B ^ (1 / (17 : ℝ)))) := by
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ (24 : ℝ) * ((R a : ℝ) * (1 + B ^ (1 / (17 : ℝ)))) := by
      gcongr
      exact_mod_cast hS
    _ = _ := by simp only [Nat.cast_mul, Nat.cast_ofNat, B]; ring

end
end PierceLengthBound.FixedDividend
