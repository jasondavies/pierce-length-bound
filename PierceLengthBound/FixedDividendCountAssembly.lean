/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendCount
public import PierceLengthBound.FixedDividendGlobalReduction

/-!
# From distinct gap counts to the final exponent

This connects the actual selected orbit sets, quartic multiplicity, minor heights,
and half-power lattice weights. Its single geometric counting premise is explicit.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Finset

/-- Per-pattern count required from the curve theorem and lattice coordinates.
`R` absorbs the logarithm and any absolute constant. -/
def SelectedPatternCount (R : ℕ → ℕ) : Prop :=
  ∀ a b s T A : ℕ, b < a →
    (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
    s + T ≤ P a b → 36 ≤ T →
    124928 * A ^ 4 * selectedGapHeight a A T ^ 5 * selectedMinorHeight a A T < a ^ 3 →
    ∀ p ∈ (selectedStarts a b s T A).image (fun i => plk (Mi a b i)),
      ((((selectedStarts a b s T A).filter fun i => plk (Mi a b i) = p).image
        (kap a b)).card : ℝ) ≤
      R a * Real.sqrt (selectedGapHeight a A T) * Real.sqrt ((1 : ℝ) / shortR p)

/-- The selected exact minor height lies in a fixed polynomial range. -/
lemma selectedMinorHeight_le {a b s T A : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hT : 36 ≤ T) : selectedMinorHeight a A T ≤ 10 ^ 16 * a ^ 7 := by
  have ha : 0 < a := by omega
  have hH : selectedGapHeight a A T ≤ 29 * a := by
    unfold selectedGapHeight
    have := Nat.div_le_self (28 * a) (A * T)
    omega
  have hA : A ≤ a := by
    have := (hmem 0 (by omega)).1
    have := (orb_le a b (s + 0)).trans hba.le
    omega
  apply Nat.le_of_mul_le_mul_right (c := a ^ 3) ?_ (by positivity)
  calc selectedMinorHeight a A T * a ^ 3 ≤
      3609600 * A ^ 4 * selectedGapHeight a A T ^ 6 := Nat.div_mul_le_self _ _
    _ ≤ 3609600 * a ^ 4 * (29 * a) ^ 6 := by gcongr
    _ = 2147074259481600 * a ^ 7 * a ^ 3 := by ring
    _ ≤ (10 ^ 16 * a ^ 7) * a ^ 3 := by gcongr; norm_num

/-- Explicit natural slack after the sixth-power weighted count. -/
def curveCountSlack (R : ℕ → ℕ) (a : ℕ) : ℕ :=
  (8 ^ 6 * (14581 * (14581 + 8 * 393660)) ^ 3) * R a ^ 6 *
    tauMax (10 ^ 16 * a ^ 7) ^ 9

/-- Each pair of a pattern and a gap vector comes from at most four selected starts. -/
theorem selectedStarts_card_le_pair_image {a b s T A : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) (hsT : s + T ≤ P a b) :
    (selectedStarts a b s T A).card ≤
      4 * ((selectedStarts a b s T A).image fun i => (plk (Mi a b i), kap a b i)).card := by
  have facts := fun i hi => selectedStart_spec hmem hsT (i := i) hi
  apply pattern_gap_multiplicity (θ := theta a b) (Q := fun i => (qq a b i : ℤ))
    (a := (a : ℤ)) (fun i _ => theta_eq i)
  · intro i hi i' hi' h
    have hP := (facts i hi).1
    have hP' := (facts i' hi').1
    simp only [Nat.cast_inj] at h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (qq_strictMono (a := a) (b := b) hlt (by omega)).ne h
    · exact (qq_strictMono (a := a) (b := b) hlt (by omega)).ne h.symm
  · intro i hi
    simpa [theta] using Lz_pos hba (i := i) (by have := (facts i hi).1; omega)
  · intro i hi
    simpa [theta, kap] using mult_at (a := a) (b := b) (i := i)
      (by have := (facts i hi).1; omega)

/-- At least `T/8` pairs of a pattern and a gap vector occur among the selected starts. -/
theorem le_eight_mul_pair_image {a b s T A : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) (hsT : s + T ≤ P a b)
    (hT : 36 ≤ T) :
    T ≤ 8 * ((selectedStarts a b s T A).image fun i => (plk (Mi a b i), kap a b i)).card := by
  have h1 := selectedStarts_card hba hmem hsT hT
  have h2 := selectedStarts_card_le_pair_image hba hmem hsT
  omega

/-- The required per-pattern estimate implies the local window estimate. -/
theorem localWindowCount_of_selectedPatternCount {R : ℕ → ℕ}
    (hcurve : SelectedPatternCount R) : LocalWindowCount (curveCountSlack R) := by
  intro a b s T A hba hmem hsT hT hscale
  classical
  let G := selectedStarts a b s T A
  let pm := fun i => plk (Mi a b i)
  let S := G.image pm
  let H := selectedGapHeight a A T
  let M := selectedMinorHeight a A T
  let τ := tauMax (10 ^ 16 * a ^ 7)
  have hc := selectedStarts_card hba hmem hsT hT
  have facts := fun i hi => selectedStart_spec hmem hsT (i := i) hi
  have hmult : G.card ≤ 4 * (G.image fun i => (pm i, kap a b i)).card :=
    selectedStarts_card_le_pair_image hba hmem hsT
  have hcount := pattern_curve_count_sum (H := (H : ℝ)) (K := (R a : ℝ)) hmult
    (hcurve a b s T A hba hmem hsT hT hscale)
  have hM : 1 ≤ M := selectedMinorHeight_pos hba hmem hsT hT
  have hMb : M ≤ 10 ^ 16 * a ^ 7 := selectedMinorHeight_le hba hmem hT
  have hτ : 1 ≤ τ := by
    have h := tau_le_tauMax (hM.trans hMb)
    change 1 ≤ tauMax (10 ^ 16 * a ^ 7)
    simpa using h
  have hS : ∀ p ∈ S, (∀ t, |p t| ≤ M) ∧ PluckerRel p ∧ p (piv p) ≠ 0 := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    refine ⟨fun t => selectedStart_minor_height hba hmem hsT hi t, plucker _, ?_⟩
    have h6 : 1 ≤ pm i 6 := by
      have := Lz_pos hba (i := i + 1) (by have := (facts i hi).1; omega)
      have e := congrFun (theta_eq (a := a) (b := b) i) 1
      simp only [theta, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, projθ] at e
      simp only [pm]
      rw [← e]
      exact_mod_cast this
    exact piv_ne_zero (by omega : pm i 6 ≠ 0)
  have hTc : (T : ℝ) ≤ 8 * R a * Real.sqrt H *
      ∑ p ∈ S, Real.sqrt ((1 : ℝ) / shortR p) := by
    have hc' : (T : ℝ) ≤ 2 * G.card := by exact_mod_cast hc
    calc (T : ℝ) ≤ 2 * G.card := hc'
      _ ≤ 2 * (4 * R a * Real.sqrt H *
          ∑ p ∈ S, Real.sqrt ((1 : ℝ) / shortR p)) := by gcongr
      _ = _ := by ring
  have hw := weighted_count_sixth hM hτ hS
    (fun m hm => tau_le_tauMax ((mem_Icc.mp hm).2.trans hMb))
    (Nat.cast_nonneg T) (Nat.cast_nonneg H) hTc
  have he : (T : ℝ) ^ 6 ≤ (curveCountSlack R a : ℝ) * H ^ 3 * M ^ 29 := by
    convert hw using 1
    simp only [curveCountSlack, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_add, τ]
    ring
  exact_mod_cast he

/-- The weighted-count slack is subpolynomial whenever the per-pattern slack is. -/
lemma curveCountSlack_slow {R : ℕ → ℕ} (hR : SlowGrowth R) :
    SlowGrowth (curveCountSlack R) := by
  have hc : SlowGrowth (fun _ : ℕ => 8 ^ 6 * (14581 * (14581 + 8 * 393660)) ^ 3) :=
    slowGrowth_const _
  exact (hc.mul (hR.pow 6)).mul ((tauMax_slow (10 ^ 16) 7).pow 9)

/-- Conditional conclusion with only the per-pattern geometric count left open. -/
theorem P_le_18_61_of_selectedPatternCount {R : ℕ → ℕ} (hR : SlowGrowth R)
    (hcurve : SelectedPatternCount R) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((18 : ℝ) / 61 + ε) :=
  P_le_18_61_of_local_count (curveCountSlack_slow hR)
    (localWindowCount_of_selectedPatternCount hcurve)

end PierceLengthBound.FixedDividend
