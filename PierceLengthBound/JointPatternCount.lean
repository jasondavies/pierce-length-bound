/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendRationalParityCover
public import PierceLengthBound.OrbitPatternCurveCount

/-!
# Pattern counts from component counts

The steps from a count on one component of a nonexceptional pattern to the per-pattern estimate
do not depend on the box of the graph count. They are stated here for a box `B p a A T` of the
pattern `p` and an exponent `e`, and used by the powered joint graph (`PoweredJointLocalEstimate`)
and the exterior lattice coordinates (`LatticeJointPatternCount`), each with `e = 1/h`. The box
is inferred from the count, and its nonnegativity is discharged by `positivity`.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

variable (B : (Fin 10 → ℤ) → ℕ → ℕ → ℕ → ℝ) (e : ℝ)

/-- A count on every supported nonexceptional component, with coefficient `R` and graph count
`B ^ e` in the box `B p a A T` of the pattern `p`. -/
def JointComponentCount (R : ℕ → ℕ) : Prop :=
  ∀ {a b s T A i : ℕ}, b < a →
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
          (1 + B (plk (Mi a b i)) a A T ^ e)

/-- The same count for all the starts of one nonexceptional pattern. -/
def JointNonexceptionalCount (R : ℕ → ℕ) : Prop :=
  ∀ {a b s T A i : ℕ}, b < a →
    (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
    s + T ≤ P a b → 36 ≤ T → i + 7 < P a b →
    NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i) →
    ∀ G : Finset ℕ, G ⊆ selectedStarts a b s T A →
      (∀ l ∈ G, plk (Mi a b l) = plk (Mi a b i)) →
      ((G.image (kap a b)).card : ℝ) ≤ (R a : ℝ) *
        (1 + B (plk (Mi a b i)) a A T ^ e)

/-- Per-pattern estimates: square-root counting for exceptional patterns, and a constant plus
the graph count `B ^ e` otherwise. -/
def JointPatternEstimate (R : ℕ → ℕ) : Prop :=
  ∀ a b s T A : ℕ, b < a →
    (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
    s + T ≤ P a b → 36 ≤ T →
    124928 * A ^ 4 * selectedGapHeight a A T ^ 5 * selectedMinorHeight a A T < a ^ 3 →
    ∀ p ∈ (selectedStarts a b s T A).image (fun i => plk (Mi a b i)),
      ((((selectedStarts a b s T A).filter fun i => plk (Mi a b i) = p).image
        (kap a b)).card : ℝ) ≤
      if ∃ d, ExceptionalMinorRelation p d then
        (R a : ℝ) * (selectedGapHeight a A T : ℝ) ^ (1 / 2 : ℝ)
      else (R a : ℝ) * (1 + B p a A T ^ e)

/-- A nonexceptional pattern has at most twenty-four components, so a component count gives
the pattern count with `24` times the coefficient. -/
theorem jointNonexceptionalCount_of_components {B e} {R : ℕ → ℕ} (hR : SlowGrowth R)
    (hcount : JointComponentCount B e R)
    (hB : ∀ p a A T, 0 ≤ B p a A T := by intros; positivity) :
    ∃ R' : ℕ → ℕ, SlowGrowth R' ∧ JointNonexceptionalCount B e R' := by
  classical
  refine ⟨fun a => 24 * R a, (slowGrowth_const 24).mul hR, ?_⟩
  intro a b s T A i hba hmem hsT hT hi hne G hG hpat
  have hθ := theta_eq_of_plk_eq hpat
  obtain ⟨hρ, hu, hv, hneQ, ha, hL⟩ := orbit_rational_nonexceptional_data hba hi hne
  obtain ⟨S, hS, hcomp, hcover⟩ := rational_nonexceptional_curve_decomposition hρ hu hv hneQ
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i) a hL ha
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
  set E : ℝ := (R a : ℝ) * (1 + B (plk (Mi a b i)) a A T ^ e)
  have hE : 0 ≤ E :=
    mul_nonneg (Nat.cast_nonneg _) (add_nonneg zero_le_one (Real.rpow_nonneg (hB _ _ _ _) _))
  have hsub : G.image (kap a b) ⊆ S.biUnion (fun I => (U I).image (kap a b)) := by
    intro k hk
    obtain ⟨l, hl, rfl⟩ := mem_image.mp hk
    obtain ⟨I, hI, hz⟩ := hpoints l hl
    exact mem_biUnion.mpr ⟨I, hI, mem_image.mpr ⟨l, mem_filter.mpr ⟨hl, hz⟩, rfl⟩⟩
  have hcard : (G.image (kap a b)).card ≤ ∑ I ∈ S, ((U I).image (kap a b)).card :=
    (card_le_card hsub).trans card_biUnion_le
  have hU (I : Ideal (MvPolynomial (Fin 3) ℚ)) (hI : I ∈ S) :
      (((U I).image (kap a b)).card : ℝ) ≤ E := by
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
    _ ≤ ∑ _I ∈ S, E := sum_le_sum hU
    _ = (S.card : ℝ) * E := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ 24 * E := mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hE
    _ = _ := by simp only [E, Nat.cast_mul, Nat.cast_ofNat]; ring

/-- Square-root counting for exceptional patterns and the nonexceptional count otherwise give
the per-pattern estimate. -/
theorem jointPatternEstimate_of_nonexceptional {B e} {Rn : ℕ → ℕ} (hRn : SlowGrowth Rn)
    (hcountn : JointNonexceptionalCount B e Rn)
    (hB : ∀ p a A T, 0 ≤ B p a A T := by intros; positivity) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ JointPatternEstimate B e R := by
  classical
  obtain ⟨Re, hRe, he⟩ := selected_pattern_curve_gap_count_slow
  refine ⟨fun a => Re a + Rn a, slowGrowth_add hRe hRn, ?_⟩
  intro a b s T A hba hmem hsT hT hscale p hp
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
  have hi7 : i + 7 < P a b := by
    have := (selectedStart_spec hmem hsT hi).1
    omega
  let G := (selectedStarts a b s T A).filter (fun l => plk (Mi a b l) = plk (Mi a b i))
  have hG : G ⊆ selectedStarts a b s T A := filter_subset _ _
  have hpat (l) (hl : l ∈ G) : plk (Mi a b l) = plk (Mi a b i) := (mem_filter.mp hl).2
  have hθ := theta_eq_of_plk_eq hpat
  have hpow : 0 ≤ B (plk (Mi a b i)) a A T ^ e := Real.rpow_nonneg (hB _ _ _ _) _
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
          (1 + B (plk (Mi a b i)) a A T ^ e) :=
        hcountn hba hmem hsT hT hi7 hne G hG hpat
      _ ≤ _ := by
        push_cast
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (Nat.cast_nonneg _))
          (add_nonneg zero_le_one hpow)

end
end PierceLengthBound.FixedDividend
