/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.LatticeJointPointCount
public import PierceLengthBound.OrbitConicGapCount
public import PierceLengthBound.JointPatternCount

/-! The per-pattern count in exterior lattice coordinates: conics, bounded cuts and the
retained linearly changed graph on each component. The steps from components to patterns are
those of `JointPatternCount`, with the box `latticeJointBox`, which depends on the pattern
through its shortest lattice vector. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

/-- The lattice box `latticeJointBoxHeight`, as a real function of the pattern. -/
abbrev latticeJointBox (m n : ℕ) (p : Fin 10 → ℤ) (a A T : ℕ) : ℝ :=
  (latticeJointBoxHeight p a A T m n : ℝ)

/-- Every supported nonexceptional component has the lattice-box count. A component either
satisfies both retained identities, and then the graph count applies, or one of the cuts bounds
its starts by `404 d ≤ 404 · 24 = 9696` (`jointResolventPolynomial_identity_or_card_bound`;
the normalization cut gives `166 d`). -/
theorem selected_lattice_joint_component_gap_count_slow (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧
      JointComponentCount (latticeJointBox m n) (1 / ((10 * n + 7 * m : ℕ) : ℝ)) R := by
  classical
  obtain ⟨Rc, hRc, hc⟩ := orbit_conic_gap_count_slow
  obtain ⟨Rg, hRg, hg⟩ := selected_latticeJointGraph_gap_count_slow m n
    (10 * n + 7 * m) (((m + n) * 247 + 1) * 24) (by omega) (by omega)
  have hR : SlowGrowth (fun a => Rc a + Rg a + 9696) :=
    slowGrowth_add (slowGrowth_add hRc hRg) (slowGrowth_const 9696)
  refine ⟨fun a => Rc a + Rg a + 9696, hR, ?_⟩
  intro a b s T A i hba hmem hsT hT hne I hI hf he hd G hG hpat hz
  let B : ℝ := latticeJointBoxHeight (plk (Mi a b i)) a A T m n
  have hpow : 0 ≤ B ^ (1 / ((10 * n + 7 * m : ℕ) : ℝ)) := by positivity
  push_cast at hpow
  have hθ := theta_eq_of_plk_eq hpat
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
    have hpatj (l) (hl : l ∈ G) : plk (Mi a b l) = plk (Mi a b j) :=
      (hpat l hl).trans (hpat j hj).symm
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
          have hp0 : plk (Mi a b j) 0 ≠ 0 := orbit_pattern_first hba (by omega)
          have hGdet := (patternCurvature_spec hp0 ⟨Mi a b j, rfl⟩).1
          obtain ⟨δ, hδ, hδupper, hgraph⟩ := orbitLinearJointGraph_retained_degree_range
            (patternCurvatureMatrix (plk (Mi a b j))) (isUnit_iff_ne_zero.mpr hGdet) hm hn hba
            hj7 hnej I hf' he' (hz j hj) hnorm hres _ hQ hQdeg hf' hd4 hdegree
          have hcount := hg hba hmem hsT (by omega : 0 < T) I hI
            ⟨δ, hδ, hδupper.trans (Nat.mul_le_mul_left _ hd24), hgraph⟩ G hG hpatj hz
          rw [hpat j hj] at hcount
          change ((G.image (kap a b)).card : ℝ) ≤ (Rg a : ℝ) *
            B ^ (1 / ((10 * n + 7 * m : ℕ) : ℝ)) at hcount
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

/-- Per-pattern estimates in the lattice box: square-root counting for exceptional patterns, and
a constant plus the lattice graph count otherwise. -/
def LatticeJointPatternEstimate (m n : ℕ) (R : ℕ → ℕ) : Prop :=
  JointPatternEstimate (latticeJointBox m n) (1 / ((10 * n + 7 * m : ℕ) : ℝ)) R

/-- The lattice-box pattern estimate holds with a proved subpolynomial coefficient. -/
theorem latticeJointPatternEstimate_exists (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ LatticeJointPatternEstimate m n R := by
  obtain ⟨Rc, hRc, hcount⟩ := selected_lattice_joint_component_gap_count_slow m n hm hn
  obtain ⟨Rn, hRn, hcountn⟩ := jointNonexceptionalCount_of_components hRc hcount
  exact jointPatternEstimate_of_nonexceptional hRn hcountn

end
end PierceLengthBound.FixedDividend
