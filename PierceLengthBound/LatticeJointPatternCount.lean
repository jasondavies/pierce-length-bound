/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.LatticeJointPointCount
public import PierceLengthBound.PoweredJointPatternCount

/-! The per-pattern count in exterior lattice coordinates: conics, bounded cuts and the
retained powered graph on each component, then the twenty-four components of a nonexceptional
pattern. The box now depends on the pattern through its shortest lattice vector. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

/-- Every supported nonexceptional component has the lattice-box count. -/
theorem selected_lattice_joint_component_gap_count_slow (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ ∀ {a b s T A i : ℕ}, b < a →
      (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
      s + T ≤ P a b → 36 ≤ T →
      NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i) →
      ∀ I : Ideal (MvPolynomial (Fin 3) ℚ), I.IsPrime →
        orbitCurveQuadraticQ a b i ∈ I → orbitCurveEquationQ a b i ∈ I →
        (∃ d : ℕ, d ≤ 24 ∧ (d = 2 ∨ 4 ≤ d) ∧ ∃ N : ℕ, ∃ c : ℤ, ∀ k ≥ N,
          (Module.finrank ℚ (filteredCoordinateSpace I k) : ℤ) = (d : ℤ) * k + c) →
        ∀ G : Finset ℕ, G ⊆ selectedStarts a b s T A →
          (∀ l ∈ G, plk (Mi a b l) = plk (Mi a b i)) →
          (∀ l ∈ G, orbitFreeNodesQ a b l ∈ coordinateZeroLocus I) →
          ((G.image (kap a b)).card : ℝ) ≤ (R a : ℝ) *
            (1 + (latticeJointBoxHeight (plk (Mi a b i)) a A T m n : ℝ) ^
              (1 / ((10 * n + 7 * m : ℕ) : ℝ))) := by
  classical
  obtain ⟨Rc, hRc, hc⟩ := orbit_conic_gap_count_slow
  obtain ⟨Rg, hRg, hg⟩ := selected_latticeJointGraph_gap_count_slow m n
    (10 * n + 7 * m) (((m + n) * 247 + 1) * 24) (by omega) (by omega)
  have hR : SlowGrowth (fun a => Rc a + Rg a + 9696) := by
    intro η hη
    obtain ⟨Cc, hCc, hbc⟩ := hRc η hη
    obtain ⟨Cg, hCg, hbg⟩ := hRg η hη
    refine ⟨Cc + Cg + 9696, by positivity, fun a ha => ?_⟩
    have hp := Real.one_le_rpow (by exact_mod_cast ha : (1 : ℝ) ≤ a) hη.le
    have := hbc a ha
    have := hbg a ha
    push_cast
    nlinarith
  refine ⟨fun a => Rc a + Rg a + 9696, hR, ?_⟩
  intro a b s T A i hba hmem hsT hT hne I hI hf he hd G hG hpat hz
  let B : ℝ := latticeJointBoxHeight (plk (Mi a b i)) a A T m n
  have hpow : 0 ≤ B ^ (1 / ((10 * n + 7 * m : ℕ) : ℝ)) := by positivity
  push_cast at hpow
  have hθ (l) (hl : l ∈ G) : theta a b i = theta a b l := by
    rw [theta_eq, theta_eq, hpat l hl]
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

/-- The nonexceptional branch of the lattice-box pattern count. -/
theorem selected_nonexceptional_lattice_joint_gap_count_slow (m n : ℕ) (hm : 0 < m)
    (hn : 0 < n) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ ∀ {a b s T A i : ℕ}, b < a →
      (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
      s + T ≤ P a b → 36 ≤ T → i + 7 < P a b →
      NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i) →
      ∀ G : Finset ℕ, G ⊆ selectedStarts a b s T A →
        (∀ l ∈ G, plk (Mi a b l) = plk (Mi a b i)) →
        ((G.image (kap a b)).card : ℝ) ≤ (R a : ℝ) *
          (1 + (latticeJointBoxHeight (plk (Mi a b i)) a A T m n : ℝ) ^
            (1 / ((10 * n + 7 * m : ℕ) : ℝ))) := by
  classical
  obtain ⟨R, hR, hcount⟩ := selected_lattice_joint_component_gap_count_slow m n hm hn
  have h24 : SlowGrowth (fun _ : ℕ => 24) := by
    intro η hη
    refine ⟨24, by norm_num, fun a ha => ?_⟩
    have := Real.one_le_rpow (by exact_mod_cast ha : (1 : ℝ) ≤ a) hη.le
    norm_num
    linarith
  refine ⟨fun a => 24 * R a, h24.mul hR, ?_⟩
  intro a b s T A i hba hmem hsT hT hi hne G hG hpat
  have hθ (l) (hl : l ∈ G) : theta a b i = theta a b l := by
    rw [theta_eq, theta_eq, hpat l hl]
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
  let B : ℝ := latticeJointBoxHeight (plk (Mi a b i)) a A T m n
  have hsub : G.image (kap a b) ⊆ S.biUnion (fun I => (U I).image (kap a b)) := by
    intro k hk
    obtain ⟨l, hl, rfl⟩ := mem_image.mp hk
    obtain ⟨I, hI, hz⟩ := hpoints l hl
    exact mem_biUnion.mpr ⟨I, hI, mem_image.mpr ⟨l, mem_filter.mpr ⟨hl, hz⟩, rfl⟩⟩
  have hcard : (G.image (kap a b)).card ≤ ∑ I ∈ S, ((U I).image (kap a b)).card :=
    (card_le_card hsub).trans card_biUnion_le
  have hU (I : Ideal (MvPolynomial (Fin 3) ℚ)) (hI : I ∈ S) :
      (((U I).image (kap a b)).card : ℝ) ≤
        (R a : ℝ) * (1 + B ^ (1 / ((10 * n + 7 * m : ℕ) : ℝ))) := by
    obtain ⟨hprime, _, hf, hg, d, _, hd24, _, hsplit, hd⟩ := hcomp I hI
    apply hcount hba hmem hsT hT hne I hprime hf hg ⟨d, hd24, hsplit, hd⟩ (U I)
    · intro l hl
      exact hG (mem_filter.mp hl).1
    · intro l hl
      exact hpat l (mem_filter.mp hl).1
    · intro l hl
      exact (mem_filter.mp hl).2
  calc ((G.image (kap a b)).card : ℝ) ≤
        ∑ I ∈ S, (((U I).image (kap a b)).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ _I ∈ S, (R a : ℝ) * (1 + B ^ (1 / ((10 * n + 7 * m : ℕ) : ℝ))) := sum_le_sum hU
    _ = (S.card : ℝ) * ((R a : ℝ) * (1 + B ^ (1 / ((10 * n + 7 * m : ℕ) : ℝ)))) := by
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ (24 : ℝ) * ((R a : ℝ) * (1 + B ^ (1 / ((10 * n + 7 * m : ℕ) : ℝ)))) := by
      gcongr
      exact_mod_cast hS
    _ = _ := by simp only [Nat.cast_mul, Nat.cast_ofNat, B]; ring

/-- Per-pattern estimates in the lattice box: square-root counting for exceptional patterns, and
a constant plus the powered-graph count otherwise. -/
def LatticeJointPatternEstimate (m n : ℕ) (R : ℕ → ℕ) : Prop :=
  ∀ a b s T A : ℕ, b < a →
    (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
    s + T ≤ P a b → 36 ≤ T →
    124928 * A ^ 4 * selectedGapHeight a A T ^ 5 * selectedMinorHeight a A T < a ^ 3 →
    ∀ p ∈ (selectedStarts a b s T A).image (fun i => plk (Mi a b i)),
      ((((selectedStarts a b s T A).filter fun i => plk (Mi a b i) = p).image
        (kap a b)).card : ℝ) ≤
      if ∃ d, ExceptionalMinorRelation p d then
        (R a : ℝ) * (selectedGapHeight a A T : ℝ) ^ (1 / 2 : ℝ)
      else (R a : ℝ) * (1 + (latticeJointBoxHeight p a A T m n : ℝ) ^
        (1 / ((10 * n + 7 * m : ℕ) : ℝ)))

/-- The lattice-box pattern estimate holds with a proved subpolynomial coefficient. -/
theorem latticeJointPatternEstimate_exists (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ LatticeJointPatternEstimate m n R := by
  classical
  obtain ⟨Re, hRe, he⟩ := selected_pattern_curve_gap_count_slow
  obtain ⟨Rn, hRn, hcountn⟩ := selected_nonexceptional_lattice_joint_gap_count_slow m n hm hn
  have hR : SlowGrowth (fun a => Re a + Rn a) := by
    intro η hη
    obtain ⟨Ce, hCe, hbe⟩ := hRe η hη
    obtain ⟨Cn, hCn, hbn⟩ := hRn η hη
    refine ⟨Ce + Cn, by positivity, fun a ha => ?_⟩
    have := hbe a ha
    have := hbn a ha
    push_cast
    nlinarith
  refine ⟨fun a => Re a + Rn a, hR, ?_⟩
  intro a b s T A hba hmem hsT hT hscale p hp
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
  have hi7 : i + 7 < P a b := by
    have := (selectedStart_spec hmem hsT hi).1
    omega
  let G := (selectedStarts a b s T A).filter (fun l => plk (Mi a b l) = plk (Mi a b i))
  have hG : G ⊆ selectedStarts a b s T A := filter_subset _ _
  have hpat (l) (hl : l ∈ G) : plk (Mi a b l) = plk (Mi a b i) := (mem_filter.mp hl).2
  have hθ (l) (hl : l ∈ G) : theta a b i = theta a b l := by
    rw [theta_eq, theta_eq, hpat l hl]
  change ((G.image (kap a b)).card : ℝ) ≤ _
  split_ifs with hex
  · calc ((G.image (kap a b)).card : ℝ) ≤
          (Re a : ℝ) * (selectedGapHeight a A T : ℝ) ^ (1 / (2 : ℝ)) :=
        he hba hmem hsT hT hi7 hscale G hG hθ
      _ ≤ _ := by
        push_cast
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Nat.cast_nonneg _))
          (by positivity)
  · have hne : NonexceptionalPattern (patternRho a b i) (patternU a b i)
        (patternV a b i) := by
      by_contra hnot
      exact hex (orbit_exceptional_minor_relation hba (by omega : i + 6 < P a b) hnot)
    calc ((G.image (kap a b)).card : ℝ) ≤ (Rn a : ℝ) *
          (1 + (latticeJointBoxHeight (plk (Mi a b i)) a A T m n : ℝ) ^
            (1 / ((10 * n + 7 * m : ℕ) : ℝ))) :=
        hcountn hba hmem hsT hT hi7 hne G hG hpat
      _ ≤ _ := by
        push_cast
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (Nat.cast_nonneg _))
          (by positivity)

end
end PierceLengthBound.FixedDividend
