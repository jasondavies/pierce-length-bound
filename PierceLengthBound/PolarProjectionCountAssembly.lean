/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionPointCount
public import PierceLengthBound.PolarProjectionLocalEstimate
public import PierceLengthBound.LatticeJointLocalEstimate

/-! Sum the actual polar pattern estimates, including every exceptional and
bad pattern, into the six-term local inequality. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

open scoped Classical in
/-- Cardinality of the bad full patterns in an actual selected orbit window. -/
def PolarBadPatternCount (good : ℕ → (Fin 10 → ℤ) → Prop) (Rbad : ℕ → ℕ) : Prop :=
  ∀ {a b s T A : ℕ}, b < a →
    (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
    s + T ≤ P a b → 36 ≤ T →
    ((((selectedStarts a b s T A).image (fun i => plk (Mi a b i))).filter
      (fun p => ¬ good a p)).card : ℝ) ≤
      Rbad a * (selectedMinorHeight a A T : ℝ) ^ (14 / 3 : ℝ)

/-- A single coefficient for the five ordinary terms and the bad-pattern term. -/
def polarPatternSlack (R Rbad : ℕ → ℕ) (a : ℕ) : ℕ :=
  8 * R a * (2 * ordinaryPatternSlack a + exceptionalPatternSlack a +
    8 * latticeWeightSlack a + Rbad a)

lemma polarPatternSlack_slow {R Rbad : ℕ → ℕ} (hR : SlowGrowth R)
    (hbad : SlowGrowth Rbad) : SlowGrowth (polarPatternSlack R Rbad) := by
  exact ((slowGrowth_const 8).mul hR).mul
    (slowGrowth_add (slowGrowth_add
      (slowGrowth_add ((slowGrowth_const 2).mul ordinaryPatternSlack_slow)
        exceptionalPatternSlack_slow) ((slowGrowth_const 8).mul latticeWeightSlack_slow)) hbad)

/-- The six-term inequality follows by summing actual point counts with the
proved fractional lattice weights and the cardinality of the bad patterns. -/
theorem polar_six_term_of_pattern_estimate {m n : ℕ} (hm : 0 < m)
    {good : ℕ → (Fin 10 → ℤ) → Prop} {R Rbad : ℕ → ℕ}
    (hcurve : JointPatternEstimate (polarPatternBox good m n) 1 R)
    (hbad : PolarBadPatternCount good Rbad) :
    PolarProjectionSixTermEstimate m n (polarPatternSlack R Rbad) := by
  intro a b s T A hba hmem hsT hT hscale
  classical
  let G := selectedStarts a b s T A
  let pm := fun i => plk (Mi a b i)
  let Pset := G.image pm
  set hN : ℕ := polarProjectionGraphDegree m n
  set h : ℝ := (hN : ℝ)
  set H := selectedGapHeight a A T
  set X := selectedMinorHeight a A T
  set S := selectedAllMinorHeight a A T
  set Y := selectedRankFiveHeight a A T
  have facts := fun i hi => selectedStart_spec hmem hsT (i := i) hi
  have hh1 : (1 : ℝ) ≤ h := by
    simp only [h, hN, polarProjectionGraphDegree]; push_cast
    nlinarith [show (1 : ℝ) ≤ m by exact_mod_cast hm,
      show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  have hh : 0 < h := by linarith
  have hm2 : (2 * m : ℝ) ≤ h := by
    simp only [h, hN, polarProjectionGraphDegree]
    push_cast
    nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n,
      show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
  have hs : ((G.image fun i => (pm i, kap a b i)).card : ℝ) ≤
      ∑ p ∈ Pset, (((G.filter fun i => pm i = p).image (kap a b)).card : ℝ) := by
    exact_mod_cast pair_image_card_le_sum G pm (kap a b)
  -- the per-pattern bound
  let E := fun p : Fin 10 → ℤ => ∃ d, ExceptionalMinorRelation p d
  let f := fun p : Fin 10 → ℤ => (R a : ℝ) * (2 + 3 * (H : ℝ) ^ (1 / h) *
    ((shortR p : ℝ)⁻¹) ^ (1 / h) + 8 * (S : ℝ) ^ ((m : ℝ) / h) *
      ((shortR p : ℝ)⁻¹) ^ (2 * (m : ℝ) / h) + (Y : ℝ) ^ ((n : ℝ) / h))
  let B : ℕ := max H (max S Y)
  let Bad := fun p => ¬ good a p
  have hper (p) (hp : p ∈ Pset) :
      (((G.filter fun i => pm i = p).image (kap a b)).card : ℝ) ≤
        f p + (if E p then (R a : ℝ) * (H : ℝ) ^ (1 / 2 : ℝ) else 0) +
          (if Bad p then (R a : ℝ) * (B : ℝ) ^ (1 / 17 : ℝ) else 0) := by
    have hc := hcurve a b s T A hba hmem hsT hT hscale p hp
    change _ ≤ if E p then (R a : ℝ) * (H : ℝ) ^ (1 / 2 : ℝ)
      else (R a : ℝ) * (1 + polarPatternBox good m n p a A T ^ (1 : ℝ)) at hc
    have hf0 : 0 ≤ f p := by positivity
    have hbad0 : 0 ≤ if Bad p then (R a : ℝ) * (B : ℝ) ^ (1 / 17 : ℝ) else 0 := by
      split_ifs <;> positivity
    by_cases hE : E p
    · rw [ite_eq_left hE]
      have hc' : (((G.filter fun i => pm i = p).image (kap a b)).card : ℝ) ≤
          (R a : ℝ) * (H : ℝ) ^ (1 / 2 : ℝ) := by
        simpa only [JointPatternEstimate, ite_eq_left hE] using hc
      linarith
    · have hc' : (((G.filter fun i => pm i = p).image (kap a b)).card : ℝ) ≤
          (R a : ℝ) * (1 + polarPatternBox good m n p a A T) := by
        simpa only [ite_eq_right hE, Real.rpow_one] using hc
      rw [ite_eq_right hE, add_zero]
      by_cases hgood : good a p
      · rw [ite_eq_right (show ¬ Bad p from not_not.mpr hgood), add_zero]
        rw [polarPatternBox, ite_eq_left hgood] at hc'
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
        have hP := (facts i hi).1
        have hl := shortR_pos (orbit_pattern_first hba (l := i) (by omega))
        have hbox := lattice_box_rpow_le (H := H) (S := S) (Y := Y)
          (m := m) (n := n) hl hh1 hm2
        refine hc'.trans ?_
        calc (R a : ℝ) * (1 + latticeJointBox m n (plk (Mi a b i)) a A T ^
              (1 / (polarProjectionGraphDegree m n : ℝ))) ≤
            (R a : ℝ) * (1 + (1 + 3 * (H : ℝ) ^ (1 / h) *
              ((shortR (plk (Mi a b i)) : ℝ)⁻¹) ^ (1 / h) +
              8 * (S : ℝ) ^ ((m : ℝ) / h) *
              ((shortR (plk (Mi a b i)) : ℝ)⁻¹) ^ (2 * (m : ℝ) / h) +
              (Y : ℝ) ^ ((n : ℝ) / h))) := by gcongr; exact hbox
          _ = f (plk (Mi a b i)) := by simp only [f]; ring
      · rw [ite_eq_left (show Bad p from hgood)]
        rw [polarPatternBox, ite_eq_right hgood] at hc'
        have hB : jointLiftBox p a A T ≤ (B : ℝ) := by
          have hS : selectedCurvatureHeight a A T ≤ S := by
            dsimp [S, selectedCurvatureHeight, selectedAllMinorHeight]
            apply Nat.div_le_div_right
            gcongr; norm_num
          dsimp only [jointLiftBox, B, H, Y]
          push_cast
          exact max_le (max_le (le_max_left _ _)
            ((by exact_mod_cast hS : (selectedCurvatureHeight a A T : ℝ) ≤ S).trans
              ((le_max_left _ _).trans (le_max_right _ _))))
            ((le_max_right _ _).trans (le_max_right _ _))
        have hpower := Real.rpow_le_rpow (by positivity : 0 ≤ jointLiftBox p a A T)
          hB (by norm_num : (0 : ℝ) ≤ 1 / 17)
        have hfR : (R a : ℝ) ≤ f p := by
          dsimp [f]
          nlinarith [show 0 ≤ 3 * (H : ℝ) ^ (1 / h) *
              ((shortR p : ℝ)⁻¹) ^ (1 / h) by positivity,
            show 0 ≤ 8 * (S : ℝ) ^ ((m : ℝ) / h) *
              ((shortR p : ℝ)⁻¹) ^ (2 * (m : ℝ) / h) by positivity,
            show 0 ≤ (Y : ℝ) ^ ((n : ℝ) / h) by positivity,
            show (0 : ℝ) ≤ R a by positivity]
        have hhB := mul_le_mul_of_nonneg_left hpower (Nat.cast_nonneg (R a))
        nlinarith
  have hsum : ∑ p ∈ Pset, (((G.filter fun i => pm i = p).image (kap a b)).card : ℝ) ≤
      ∑ p ∈ Pset, f p + (R a : ℝ) * (H : ℝ) ^ (1 / 2 : ℝ) * ((Pset.filter E).card : ℝ) +
        (R a : ℝ) * (B : ℝ) ^ (1 / 17 : ℝ) * ((Pset.filter Bad).card : ℝ) := by
    calc _ ≤ ∑ p ∈ Pset, (f p +
          (if E p then (R a : ℝ) * (H : ℝ) ^ (1 / 2 : ℝ) else 0) +
          (if Bad p then (R a : ℝ) * (B : ℝ) ^ (1 / 17 : ℝ) else 0)) := sum_le_sum hper
      _ = _ := by
          rw [sum_add_distrib, sum_add_distrib, sum_ite, sum_ite]
          simp only [sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
          ring
  -- the weights and counts
  have hW1 := selected_pattern_weight_sum hba hmem hsT hT (t := 1 / h) (by positivity)
    (by rw [div_le_one hh]; exact hh1)
  have hW2 := selected_pattern_weight_sum hba hmem hsT hT (t := 2 * (m : ℝ) / h) (by positivity)
    (by rw [div_le_one hh]; exact hm2)
  have hP : (Pset.card : ℝ) ≤ ordinaryPatternSlack a * (X : ℝ) ^ 5 := by
    exact_mod_cast selected_ordinary_pattern_count hba hmem hsT hT
  have hPE : ((Pset.filter E).card : ℝ) ≤ exceptionalPatternSlack a * (X : ℝ) ^ 4 := by
    exact_mod_cast selected_exceptional_pattern_count_slack hba hmem hsT hT
  have hPB : ((Pset.filter Bad).card : ℝ) ≤ Rbad a * (X : ℝ) ^ (14 / 3 : ℝ) :=
    hbad hba hmem hsT hT
  have hfsum : ∑ p ∈ Pset, f p = (R a : ℝ) * ((Pset.card : ℝ) * (2 + (Y : ℝ) ^ ((n : ℝ) / h)) +
      3 * (H : ℝ) ^ (1 / h) * ∑ p ∈ Pset, ((shortR p : ℝ)⁻¹) ^ (1 / h) +
      8 * (S : ℝ) ^ ((m : ℝ) / h) * ∑ p ∈ Pset, ((shortR p : ℝ)⁻¹) ^ (2 * (m : ℝ) / h)) := by
    simp only [f, ← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul]
    ring
  have hTc : (T : ℝ) ≤ 8 * ((G.image fun i => (pm i, kap a b i)).card : ℝ) := by
    exact_mod_cast le_eight_mul_pair_image hba hmem hsT hT
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast selectedMinorHeight_pos hba hmem hsT hT
  set W := (latticeWeightSlack a : ℝ)
  set O := (ordinaryPatternSlack a : ℝ)
  set Ex := (exceptionalPatternSlack a : ℝ)
  set Ra := (R a : ℝ)
  set Rb := (Rbad a : ℝ)
  have hO : 0 ≤ O := Nat.cast_nonneg _
  have hEx : 0 ≤ Ex := Nat.cast_nonneg _
  have hW : 0 ≤ W := Nat.cast_nonneg _
  have hRa : 0 ≤ Ra := Nat.cast_nonneg _
  have hRb : 0 ≤ Rb := Nat.cast_nonneg _
  have t1 : 0 ≤ (H : ℝ) ^ (1 / h) := by positivity
  have t2 : 0 ≤ (S : ℝ) ^ ((m : ℝ) / h) := by positivity
  have t3 : 0 ≤ (Y : ℝ) ^ ((n : ℝ) / h) := by positivity
  have t4 : 0 ≤ (H : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have tbad : 0 ≤ (B : ℝ) ^ (1 / 17 : ℝ) := by positivity
  have hxbad : 0 ≤ (X : ℝ) ^ (14 / 3 : ℝ) := by positivity
  have hx5 : 0 ≤ (X : ℝ) ^ 5 := by positivity
  have hx4 : 0 ≤ (X : ℝ) ^ 4 := by positivity
  have hxa : 0 ≤ (X : ℝ) ^ (5 - (1 / h) / 3) := by positivity
  have hxb : 0 ≤ (X : ℝ) ^ (5 - (2 * (m : ℝ) / h) / 3) := by positivity
  have hW1' : ∑ p ∈ Pset, ((shortR p : ℝ)⁻¹) ^ (1 / h) ≤ W * (X : ℝ) ^ (5 - (1 / h) / 3) := hW1
  have hW2' : ∑ p ∈ Pset, ((shortR p : ℝ)⁻¹) ^ (2 * (m : ℝ) / h) ≤
      W * (X : ℝ) ^ (5 - (2 * (m : ℝ) / h) / 3) := hW2
  have hbound : (T : ℝ) ≤ 8 * (Ra * ((O * (X : ℝ) ^ 5) * (2 + (Y : ℝ) ^ ((n : ℝ) / h)) +
      3 * (H : ℝ) ^ (1 / h) * (W * (X : ℝ) ^ (5 - (1 / h) / 3)) +
      8 * (S : ℝ) ^ ((m : ℝ) / h) * (W * (X : ℝ) ^ (5 - (2 * (m : ℝ) / h) / 3))) +
      Ra * (H : ℝ) ^ (1 / 2 : ℝ) * (Ex * (X : ℝ) ^ 4) +
      Ra * (B : ℝ) ^ (1 / 17 : ℝ) * (Rb * (X : ℝ) ^ (14 / 3 : ℝ))) := by
    refine hTc.trans ?_
    gcongr
    refine hs.trans (hsum.trans ?_)
    rw [hfsum]
    gcongr
  change (T : ℝ) ≤ (polarPatternSlack R Rbad a : ℝ) * _
  have hgoal : (polarPatternSlack R Rbad a : ℝ) = 8 * Ra * (2 * O + Ex + 8 * W + Rb) := by
    simp only [polarPatternSlack, Ra, Rb, O, Ex, W]; push_cast; ring
  rw [hgoal]
  -- each term of `hbound` is at most `8 Ra Σ` times the matching term of the goal
  set Csum := 2 * O + Ex + 8 * W + Rb
  have e1 := mul_le_mul_of_nonneg_right (show 2 * O ≤ Csum by linarith) hx5
  have e2 := mul_le_mul_of_nonneg_right (show O ≤ Csum by linarith) (mul_nonneg hx5 t3)
  have e3 := mul_le_mul_of_nonneg_right (show 3 * W ≤ Csum by linarith) (mul_nonneg hxa t1)
  have e4 := mul_le_mul_of_nonneg_right (show 8 * W ≤ Csum by linarith) (mul_nonneg hxb t2)
  have e5 := mul_le_mul_of_nonneg_right (show Ex ≤ Csum by linarith) (mul_nonneg hx4 t4)
  have e6 := mul_le_mul_of_nonneg_right (show Rb ≤ Csum by linarith)
    (mul_nonneg hxbad tbad)
  have hterms : (O * (X : ℝ) ^ 5) * (2 + (Y : ℝ) ^ ((n : ℝ) / h)) +
      3 * (H : ℝ) ^ (1 / h) * (W * (X : ℝ) ^ (5 - (1 / h) / 3)) +
      8 * (S : ℝ) ^ ((m : ℝ) / h) * (W * (X : ℝ) ^ (5 - (2 * (m : ℝ) / h) / 3)) +
      (H : ℝ) ^ (1 / 2 : ℝ) * (Ex * (X : ℝ) ^ 4) +
      (B : ℝ) ^ (1 / 17 : ℝ) * (Rb * (X : ℝ) ^ (14 / 3 : ℝ)) ≤
      Csum * ((X : ℝ) ^ 5 + (X : ℝ) ^ 4 * (H : ℝ) ^ (1 / 2 : ℝ) +
        (X : ℝ) ^ (5 - (1 / h) / 3) * (H : ℝ) ^ (1 / h) +
        (X : ℝ) ^ (5 - (2 * (m : ℝ) / h) / 3) * (S : ℝ) ^ ((m : ℝ) / h) +
        (X : ℝ) ^ 5 * (Y : ℝ) ^ ((n : ℝ) / h) +
        (X : ℝ) ^ (14 / 3 : ℝ) * (B : ℝ) ^ (1 / 17 : ℝ)) := by
    linarith
  have := mul_le_mul_of_nonneg_left hterms (by positivity : (0 : ℝ) ≤ 8 * Ra)
  refine hbound.trans ((le_of_eq ?_).trans (this.trans (le_of_eq ?_)))
  · ring
  · dsimp [polarGoodTerms, polarBadTerm, Csum, h, hN, H, X, S, Y, B]
    ring

/-- The arithmetic counting assembly needs only a degree theorem on retained
prime components and a count of the patterns where it is unavailable. -/
theorem polar_six_term_of_retained_degree (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (good : ℕ → (Fin 10 → ℤ) → Prop) (hdegree : PolarRetainedDegree m n good)
    {Rbad : ℕ → ℕ} (hRbad : SlowGrowth Rbad) (hbad : PolarBadPatternCount good Rbad) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ PolarProjectionSixTermEstimate m n R := by
  obtain ⟨R, hR, hcount⟩ := polar_pattern_count_of_retained_degree m n hm hn good hdegree
  exact ⟨polarPatternSlack R Rbad, polarPatternSlack_slow hR hRbad,
    polar_six_term_of_pattern_estimate hm hcount hbad⟩

end
end PierceLengthBound.FixedDividend
