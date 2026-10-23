/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.OrbitCurveGapCount
public import PierceLengthBound.OrbitPatternGeometry

/-! The original curve cover and actual-window line exclusion give the
square-root count for every pattern in the large-scale range. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

/-- Square-root counting for any complete pattern in the large-scale range.
In particular, this proves the exceptional branch of the joint-lift estimate. -/
theorem selected_pattern_curve_gap_count_slow :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ ∀ {a b s T A i : ℕ}, b < a →
      (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
      s + T ≤ P a b → 36 ≤ T → i + 7 < P a b →
      124928 * A ^ 4 * selectedGapHeight a A T ^ 5 * selectedMinorHeight a A T < a ^ 3 →
      ∀ G : Finset ℕ, G ⊆ selectedStarts a b s T A →
        (∀ l ∈ G, theta a b i = theta a b l) →
        ((G.image (kap a b)).card : ℝ) ≤ (R a : ℝ) *
          (selectedGapHeight a A T : ℝ) ^ (1 / (2 : ℝ)) := by
  classical
  obtain ⟨R, hR, hcount⟩ := selected_curve_gap_count_slow
  have h24 : SlowGrowth (fun _ : ℕ => 24) := slowGrowth_const _
  refine ⟨fun a => 24 * R a, h24.mul hR, ?_⟩
  intro a b s T A i hba hmem hsT hT hi hscale G hG hθ
  obtain ⟨hρ, hu, hv⟩ := orbit_rational_pattern_signs hba (by omega : i + 6 < P a b)
  obtain ⟨S, hS, hcomp, hcover⟩ := rational_curve_decomposition_with_degrees hρ hu hv
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i) a (by exact_mod_cast (show a ≠ 0 by omega))
  have hX := selectedMinorHeight_pos hba hmem hsT hT
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
  let B : ℝ := selectedGapHeight a A T
  have hsub : G.image (kap a b) ⊆ S.biUnion (fun I => (U I).image (kap a b)) := by
    intro k hk
    obtain ⟨l, hl, rfl⟩ := mem_image.mp hk
    obtain ⟨I, hI, hz⟩ := hpoints l hl
    exact mem_biUnion.mpr ⟨I, hI, mem_image.mpr ⟨l, mem_filter.mpr ⟨hl, hz⟩, rfl⟩⟩
  have hcard : (G.image (kap a b)).card ≤ ∑ I ∈ S, ((U I).image (kap a b)).card :=
    (card_le_card hsub).trans card_biUnion_le
  have hU (I : Ideal (MvPolynomial (Fin 3) ℚ)) (hI : I ∈ S) :
      (((U I).image (kap a b)).card : ℝ) ≤ (R a : ℝ) * (B ^ (1 / (2 : ℝ))) := by
    obtain ⟨hprime, hheight, hf, hg, _⟩ := hcomp I hI
    by_cases hn : (U I).Nonempty
    · obtain ⟨j, hj⟩ := hn
      have hjG := (mem_filter.mp hj).1
      have hjI := (mem_filter.mp hj).2
      have hjselected := hG hjG
      obtain ⟨hjP, hgap, horb⟩ := selectedStart_spec hmem hsT hjselected
      have hf' : orbitCurveQuadraticQ a b j ∈ I := by
        rw [← (orbitCurve_polynomials_congr (hθ j hjG)).1]; exact hf
      have hg' : orbitCurveEquationQ a b j ∈ I := by
        rw [← (orbitCurve_polynomials_congr (hθ j hjG)).2]; exact hg
      have hU : |U1z a b j| ≤ (selectedMinorHeight a A T : ℤ) :=
        selectedStart_theta_height hba hmem hsT hjselected 3
      have hV : |U2z a b j| ≤ (selectedMinorHeight a A T : ℤ) :=
        selectedStart_theta_height hba hmem hsT hjselected 4
      let : I.IsPrime := hprime
      have hd := orbit_rational_component_degree_range hba (by omega : j + 7 < P a b)
        (by exact_mod_cast hX : (1 : ℤ) ≤ selectedMinorHeight a A T)
        (fun m hm => (hgap m (by omega)).2) hU hV
        (window_line_scale hba (by omega : j < P a b) horb hX hscale)
        I hheight hf' hg' hjI
      apply hcount hba hmem hsT I hprime hd (U I)
      · intro l hl
        exact hG (mem_filter.mp hl).1
      · intro l hl
        exact hθ l (mem_filter.mp hl).1
      · intro l hl
        exact (mem_filter.mp hl).2
    · rw [not_nonempty_iff_eq_empty.mp hn, image_empty, card_empty, Nat.cast_zero]
      positivity
  calc ((G.image (kap a b)).card : ℝ) ≤
        ∑ I ∈ S, (((U I).image (kap a b)).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _I ∈ S, (R a : ℝ) * (B ^ (1 / (2 : ℝ))) := sum_le_sum hU
    _ = (S.card : ℝ) * ((R a : ℝ) * (B ^ (1 / (2 : ℝ)))) := by
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ (24 : ℝ) * ((R a : ℝ) * (B ^ (1 / (2 : ℝ)))) := by
      gcongr
      exact_mod_cast hS
    _ = _ := by simp only [Nat.cast_mul, Nat.cast_ofNat, B]; ring

end
end PierceLengthBound.FixedDividend
