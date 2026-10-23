/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionCuts
public import PierceLengthBound.PolarProjectionExponent
public import PierceLengthBound.LatticeJointPatternCount
public import PierceLengthBound.JointLiftComponentCount

/-! Point counts on components of the pattern curve. `PolarRetainedDegree`
is the powered graph degree bound on retained components of good patterns
(proved in `PolarProjectionGeometryGoodPattern`). From it, conics, the bounded
cuts and the finite component cover give the component count and the
per-pattern estimate with the mixed box `polarPatternBox`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Finset

/-- On good full patterns, every prime component of degree `4 ≤ d ≤ 24` that
satisfies the normalization, resolvent and polar cuts has powered graph degree
at least `60n + 56m`. The predicate `good` may depend on the dividend. -/
def PolarRetainedDegree (m n : ℕ) (good : ℕ → (Fin 10 → ℤ) → Prop) : Prop :=
  ∀ {a b i d δ : ℕ}, b < a → i + 7 < P a b →
    NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i) →
    good a (plk (Mi a b i)) →
    ∀ I : Ideal (MvPolynomial (Fin 3) ℚ), I.IsPrime →
      orbitCurveQuadraticQ a b i ∈ I → orbitCurveEquationQ a b i ∈ I →
      orbitFreeNodesQ a b i ∈ coordinateZeroLocus I →
      jointNormalizationPolynomial a b i ∈ I → jointResolventPolynomial a b i ∈ I →
      (∀ j, orbitPolarIdentityPolynomial a b i j ∈ I) →
      4 ≤ d → d ≤ 24 →
      (∃ N : ℕ, ∃ c : ℤ, ∀ k ≥ N,
        (Module.finrank ℚ (filteredCoordinateSpace I k) : ℤ) = (d : ℤ) * k + c) →
      (∃ N : ℕ, ∃ c : ℤ, ∀ k ≥ N,
        (Module.finrank ℚ (filteredCoordinateSpace
          (orbitLinearJointGraphIdeal (patternCurvatureMatrix (plk (Mi a b i)))
            a b i m n I) k) : ℤ) = (δ : ℤ) * k + c) →
      polarProjectionGraphDegree m n ≤ δ

/-- On a good pattern, the selected starts on one prime component of the
pattern curve give at most `R(a) (1 + B^{1/(60n+56m)})` values of `κ`, with `B`
the lattice-joint box. Conics and components on which a normalization,
resolvent or polar cut is proper contribute `O(R(a))`. -/
theorem selected_polar_good_component_gap_count_slow (m n : ℕ) (hm : 0 < m)
    (hn : 0 < n) (good : ℕ → (Fin 10 → ℤ) → Prop)
    (hdegreeGood : PolarRetainedDegree m n good) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧
      ∀ {a b s T A i : ℕ}, b < a →
        (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
        s + T ≤ P a b → 36 ≤ T →
        NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i) →
        good a (plk (Mi a b i)) →
        ∀ I : Ideal (MvPolynomial (Fin 3) ℚ), I.IsPrime →
          orbitCurveQuadraticQ a b i ∈ I → orbitCurveEquationQ a b i ∈ I →
          (∃ d : ℕ, d ≤ 24 ∧ (d = 2 ∨ 4 ≤ d) ∧ ∃ N : ℕ, ∃ c : ℤ, ∀ k ≥ N,
            (Module.finrank ℚ (filteredCoordinateSpace I k) : ℤ) = (d : ℤ) * k + c) →
          ∀ G : Finset ℕ, G ⊆ selectedStarts a b s T A →
            (∀ l ∈ G, plk (Mi a b l) = plk (Mi a b i)) →
            (∀ l ∈ G, orbitFreeNodesQ a b l ∈ coordinateZeroLocus I) →
            ((G.image (kap a b)).card : ℝ) ≤ (R a : ℝ) *
              (1 + latticeJointBox m n (plk (Mi a b i)) a A T ^
                (1 / (polarProjectionGraphDegree m n : ℝ))) := by
  classical
  obtain ⟨Rc, hRc, hc⟩ := orbit_conic_gap_count_slow
  obtain ⟨Rg, hRg, hg⟩ := selected_latticeJointGraph_gap_count_slow m n
    (polarProjectionGraphDegree m n) (((m + n) * 247 + 1) * 24)
    (by simp [polarProjectionGraphDegree]; omega)
    (by simp [polarProjectionGraphDegree]; omega)
  have hR : SlowGrowth (fun a => Rc a + Rg a + 9696) :=
    slowGrowth_add (slowGrowth_add hRc hRg) (slowGrowth_const 9696)
  refine ⟨fun a => Rc a + Rg a + 9696, hR, ?_⟩
  intro a b s T A i hba hmem hsT hT hne hgood I hI hf he hd G hG hpat hz
  let B : ℝ := latticeJointBox m n (plk (Mi a b i)) a A T
  let e : ℝ := 1 / (polarProjectionGraphDegree m n : ℝ)
  have hpow : 0 ≤ B ^ e := by positivity
  have hθ := theta_eq_of_plk_eq hpat
  have hsmall (h : ((G.image (kap a b)).card : ℝ) ≤ 9696) :
      ((G.image (kap a b)).card : ℝ) ≤
        ((Rc a + Rg a + 9696 : ℕ) : ℝ) * (1 + B ^ e) := by
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
    have hθj (l) (hl : l ∈ G) : theta a b j = theta a b l :=
      (hθ j hj).symm.trans (hθ l hl)
    have hpatj (l) (hl : l ∈ G) : plk (Mi a b l) = plk (Mi a b j) :=
      (hpat l hl).trans (hpat j hj).symm
    have hnej := (orbit_nonexceptional_congr (hθ j hj)).mp hne
    have hgoodj : good a (plk (Mi a b j)) := by rw [hpat j hj]; exact hgood
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
      change _ ≤ ((Rc a + Rg a + 9696 : ℕ) : ℝ) * (1 + B ^ e)
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
      have hpolar := orbitPolarIdentityPolynomial_identity_or_card_bound hba I hdegree
        (fun l : G => l.val) Subtype.val_injective
        (fun l => hmargin l.val l.property) (fun l => hθj l.val l.property)
        (fun l => hz l.val l.property)
      rcases hnorm with hnorm | hnorm
      · rcases hres with hres | hres
        · rcases hpolar with hpolar | hpolar
          · obtain ⟨_, δ, _, hδupper, hgraph⟩ := orbitLinearJointGraph_degree_bounds
              (patternCurvatureMatrix (plk (Mi a b j))) hba hj7 m n I (hz j hj) hdegree
            have hδ := hdegreeGood hba hj7 hnej hgoodj I hI hf' he' (hz j hj)
              hnorm hres hpolar hd4 hd24 hdegree hgraph
            have hcount := hg hba hmem hsT (by omega : 0 < T) I hI
              ⟨δ, hδ, hδupper.trans (Nat.mul_le_mul_left _ hd24), hgraph⟩ G hG hpatj hz
            rw [hpat j hj] at hcount
            change ((G.image (kap a b)).card : ℝ) ≤ (Rg a : ℝ) * B ^ e at hcount
            change _ ≤ ((Rc a + Rg a + 9696 : ℕ) : ℝ) * (1 + B ^ e)
            push_cast at hcount ⊢
            nlinarith [(show (0 : ℝ) ≤ Rc a by positivity),
              (show (0 : ℝ) ≤ Rg a by positivity)]
          · apply hsmall
            simp only [Fintype.card_coe] at hpolar
            have : (G.image (kap a b)).card ≤ 9696 := card_image_le.trans (by omega)
            exact_mod_cast this
        · apply hsmall
          simp only [Fintype.card_coe] at hres
          have : (G.image (kap a b)).card ≤ 9696 := card_image_le.trans (by omega)
          exact_mod_cast this
      · apply hsmall
        simp only [Fintype.card_coe] at hnorm
        have : (G.image (kap a b)).card ≤ 9696 := card_image_le.trans (by omega)
        exact_mod_cast this
  · apply hsmall
    simp [not_nonempty_iff_eq_empty.mp hnonempty]

/-- The lattice-joint box to the power `1/(60n+56m)` on good patterns, and the
joint-lift box to the power `1/17` on the others. -/
def polarPatternBox (good : ℕ → (Fin 10 → ℤ) → Prop) (m n : ℕ)
    (p : Fin 10 → ℤ) (a A T : ℕ) : ℝ := by
  classical
  exact if good a p then
    latticeJointBox m n p a A T ^ (1 / (polarProjectionGraphDegree m n : ℝ))
  else jointLiftBox p a A T ^ (1 / 17 : ℝ)

lemma polarPatternBox_nonneg (good : ℕ → (Fin 10 → ℤ) → Prop) (m n : ℕ)
    (p : Fin 10 → ℤ) (a A T : ℕ) : 0 ≤ polarPatternBox good m n p a A T := by
  classical
  unfold polarPatternBox
  split_ifs <;> positivity

/-- The component count with the mixed box `polarPatternBox`, given
`PolarRetainedDegree`. -/
theorem polar_component_count_of_retained_degree (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (good : ℕ → (Fin 10 → ℤ) → Prop) (hdegree : PolarRetainedDegree m n good) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ JointComponentCount (polarPatternBox good m n) 1 R := by
  classical
  obtain ⟨Rg, hRg, hg⟩ := selected_polar_good_component_gap_count_slow m n hm hn good hdegree
  obtain ⟨Rb, hRb, hb⟩ := selected_joint_component_gap_count_slow
  refine ⟨fun a => Rg a + Rb a, slowGrowth_add hRg hRb, ?_⟩
  intro a b s T A i hba hmem hsT hT hne I hI hf he hd G hG hpat hz
  rw [Real.rpow_one]
  by_cases hgood : good a (plk (Mi a b i))
  · rw [polarPatternBox, ite_eq_left hgood]
    have hc := hg hba hmem hsT hT hne hgood I hI hf he hd G hG hpat hz
    exact hc.trans (mul_le_mul_of_nonneg_right
      (by simp only [Nat.cast_add]; exact le_add_of_nonneg_right (Nat.cast_nonneg _))
      (by positivity))
  · rw [polarPatternBox, ite_eq_right hgood]
    have hc := hb hba hmem hsT hT hne I hI hf he hd G hG (theta_eq_of_plk_eq hpat) hz
    exact hc.trans (mul_le_mul_of_nonneg_right
      (by simp only [Nat.cast_add]; exact le_add_of_nonneg_left (Nat.cast_nonneg _))
      (by positivity))

/-- The per-pattern estimate with the mixed box, given `PolarRetainedDegree`:
exceptional patterns have the square-root bound, good patterns the polar
graph-degree bound and the remaining patterns the seventeenth-root bound. -/
theorem polar_pattern_count_of_retained_degree (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (good : ℕ → (Fin 10 → ℤ) → Prop) (hdegree : PolarRetainedDegree m n good) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ JointPatternEstimate (polarPatternBox good m n) 1 R := by
  obtain ⟨Rc, hRc, hc⟩ := polar_component_count_of_retained_degree m n hm hn good hdegree
  obtain ⟨Rn, hRn, hncount⟩ := jointNonexceptionalCount_of_components hRc hc
    (polarPatternBox_nonneg good m n)
  exact jointPatternEstimate_of_nonexceptional hRn hncount (polarPatternBox_nonneg good m n)

end
end PierceLengthBound.FixedDividend
