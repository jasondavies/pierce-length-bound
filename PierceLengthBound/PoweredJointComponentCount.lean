/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.OrbitPatternGeometry
public import PierceLengthBound.OrbitConicGapCount
public import PierceLengthBound.PoweredJointCountingSlack
public import PierceLengthBound.PoweredJointGraphLowerDegree
public import PierceLengthBound.FixedDividendCountAssembly
public import PierceLengthBound.JointPatternCount

/-! Combine conic counting, bounded polynomial cuts, and the proved degree
range of the retained joint graph on each actual nonexceptional component; the nonexceptional
powered count is then `JointPatternCount` applied in the box `poweredJointBox`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

/-- The box of the powered joint graph; it does not depend on the pattern. -/
abbrev poweredJointBox (m n : ℕ) (_p : Fin 10 → ℤ) (a A T : ℕ) : ℝ :=
  (max (max (selectedGapHeight a A T) (selectedCurvatureHeight a A T ^ m))
    (selectedRankFiveHeight a A T ^ n) : ℝ)

/-- Every supported nonexceptional component has the required powered-graph
count, including components on which either retained identity fails: then one of the cuts
bounds its starts by `404 d ≤ 404 · 24 = 9696` (`jointResolventPolynomial_identity_or_card_bound`;
the normalization cut gives `166 d`). -/
theorem selected_powered_joint_component_gap_count_slow (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ ∀ {a b s T A i : ℕ}, b < a →
      (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
      s + T ≤ P a b → 36 ≤ T →
      NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i) →
      ∀ I : Ideal (MvPolynomial (Fin 3) ℚ), I.IsPrime →
        orbitCurveQuadraticQ a b i ∈ I → orbitCurveEquationQ a b i ∈ I →
        (∃ d : ℕ, d ≤ 24 ∧ (d = 2 ∨ 4 ≤ d) ∧ ∃ N : ℕ, ∃ c : ℤ, ∀ k ≥ N,
          (Module.finrank ℚ (filteredCoordinateSpace I k) : ℤ) = (d : ℤ) * k + c) →
        ∀ G : Finset ℕ, G ⊆ selectedStarts a b s T A →
          (∀ l ∈ G, theta a b i = theta a b l) →
          (∀ l ∈ G, orbitFreeNodesQ a b l ∈ coordinateZeroLocus I) →
          ((G.image (kap a b)).card : ℝ) ≤ (R a : ℝ) *
            (1 + (max (max (selectedGapHeight a A T) (selectedCurvatureHeight a A T ^ m))
              (selectedRankFiveHeight a A T ^ n) : ℝ) ^ (1 / ((10 * n + 7 * m : ℕ) : ℝ))) := by
  classical
  obtain ⟨Rc, hRc, hc⟩ := orbit_conic_gap_count_slow
  obtain ⟨Rg, hRg, hg⟩ := selected_poweredJointGraph_gap_count_slow m n
    (10 * n + 7 * m) (((m + n) * 247 + 1) * 24) (by omega) (by omega)
  have hR : SlowGrowth (fun a => Rc a + Rg a + 9696) :=
    slowGrowth_add (slowGrowth_add hRc hRg) (slowGrowth_const 9696)
  refine ⟨fun a => Rc a + Rg a + 9696, hR, ?_⟩
  intro a b s T A i hba hmem hsT hT hne I hI hf he hd G hG hθ hz
  let B : ℝ := max (max (selectedGapHeight a A T : ℝ) (selectedCurvatureHeight a A T ^ m))
    (selectedRankFiveHeight a A T ^ n)
  have hpow : 0 ≤ B ^ (1 / ((10 * n + 7 * m : ℕ) : ℝ)) := by positivity
  push_cast at hpow
  have hsmall (h : ((G.image (kap a b)).card : ℝ) ≤ 9696) :
      ((G.image (kap a b)).card : ℝ) ≤
        ((Rc a + Rg a + 9696 : ℕ) : ℝ) * (1 + B ^ (1 / ((10 * n + 7 * m : ℕ) : ℝ))) := by
    push_cast
    nlinarith [(show (0 : ℝ) ≤ Rc a by positivity), (show (0 : ℝ) ≤ Rg a by positivity)]
  by_cases hnonempty : G.Nonempty
  · obtain ⟨j, hj⟩ := hnonempty
    have hj7 : j + 7 < P a b := by
      have := (selectedStart_spec hmem hsT (hG hj)).1
      omega
    have hmargin (l) (hl : l ∈ G) : l + 7 < P a b := by
      have := (selectedStart_spec hmem hsT (hG hl)).1
      omega
    have hθj (l) (hl : l ∈ G) : theta a b j = theta a b l := (hθ j hj).symm.trans (hθ l hl)
    have hnej := (orbit_nonexceptional_congr (hθ j hj)).mp hne
    have hf' : orbitCurveQuadraticQ a b j ∈ I := by
      rw [← (orbitCurve_polynomials_congr (hθ j hj)).1]; exact hf
    have he' : orbitCurveEquationQ a b j ∈ I := by
      rw [← (orbitCurve_polynomials_congr (hθ j hj)).2]; exact he
    let : I.IsPrime := hI
    obtain ⟨d, hd24, hsplit, hdegree⟩ := hd
    rcases hsplit with rfl | hd4
    · have hcount := hc hba hj7 (selectedMinorHeight_pos hba hmem hsT hT)
        (selectedStart_theta_height hba hmem hsT (hG hj))
        (selectedMinorHeight_le hba hmem hT) hnej I hI hf' he' hdegree
        (hz j hj) G hmargin hθj hz
      have hcountR : ((G.image (kap a b)).card : ℝ) ≤ Rc a := by exact_mod_cast hcount
      change _ ≤ ((Rc a + Rg a + 9696 : ℕ) : ℝ) * (1 + B ^ (1 / ((10 * n + 7 * m : ℕ) : ℝ)))
      push_cast
      nlinarith [(show (0 : ℝ) ≤ Rc a by positivity), (show (0 : ℝ) ≤ Rg a by positivity)]
    · have hnorm := jointNormalizationPolynomial_identity_or_card_bound hba I hdegree
        (fun l : G => l.val) Subtype.val_injective
        (fun l => hmargin l.val l.property) (fun l => hθj l.val l.property)
        (fun l => hz l.val l.property)
      have hres := jointResolventPolynomial_identity_or_card_bound hba I hdegree
        (fun l : G => l.val) Subtype.val_injective
        (fun l => hmargin l.val l.property) (fun l => hθj l.val l.property)
        (fun l => hz l.val l.property)
      rcases hnorm with hnorm | hnorm
      · rcases hres with hres | hres
        · obtain ⟨hQ, hQdeg⟩ := orbitCurveQuadraticQ_prime_degree hba hj7
          obtain ⟨δ, hδ, hδupper, hgraph⟩ :=
            orbitPoweredJointGraph_retained_degree_range hm hn hba hj7
              hnej I hf' he' (hz j hj) hnorm hres _ hQ hQdeg hf' hd4 hdegree
          have hcount := hg hba hmem hsT (by omega : 0 < T) I hI
            ⟨δ, hδ, hδupper.trans (Nat.mul_le_mul_left _ hd24), hgraph⟩ G hG hθj hz
          change ((G.image (kap a b)).card : ℝ) ≤
            (Rg a : ℝ) * B ^ (1 / ((10 * n + 7 * m : ℕ) : ℝ)) at hcount
          change _ ≤ ((Rc a + Rg a + 9696 : ℕ) : ℝ) * (1 + B ^ (1 / ((10 * n + 7 * m : ℕ) : ℝ)))
          push_cast at hcount ⊢
          nlinarith [(show (0 : ℝ) ≤ Rc a by positivity), (show (0 : ℝ) ≤ Rg a by positivity)]
        · apply hsmall
          simp only [Fintype.card_coe] at hres
          have : (G.image (kap a b)).card ≤ 9696 := (card_image_le).trans (by omega)
          exact_mod_cast this
      · apply hsmall
        simp only [Fintype.card_coe] at hnorm
        have : (G.image (kap a b)).card ≤ 9696 := (card_image_le).trans (by omega)
        exact_mod_cast this
  · apply hsmall
    simp [not_nonempty_iff_eq_empty.mp hnonempty]

/-- The nonexceptional branch of the powered pattern count, with all
geometric and arithmetic inputs discharged on the actual orbit. -/
theorem selected_nonexceptional_powered_joint_gap_count_slow (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧
      JointNonexceptionalCount (poweredJointBox m n) (1 / ((10 * n + 7 * m : ℕ) : ℝ)) R := by
  obtain ⟨R, hR, hcount⟩ := selected_powered_joint_component_gap_count_slow m n hm hn
  exact jointNonexceptionalCount_of_components hR
    fun hba hmem hsT hT hne I hI hf hg hd G hG hpat hz =>
      hcount hba hmem hsT hT hne I hI hf hg hd G hG (theta_eq_of_plk_eq hpat) hz

end
end PierceLengthBound.FixedDividend
