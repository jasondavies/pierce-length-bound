/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ExceptionalSlack
public import PierceLengthBound.IntegralLiftLocalEstimate

/-! Ordinary pattern counting for the integral-coordinate lift. No weighted
lattice incidence estimate occurs in the count or in its proof. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Finset

/-- The ordinary minor count, keeping a harmless divisor slack explicitly. -/
theorem ordinary_minor_count {S : Finset (Fin 10 → ℤ)} {X τ : ℕ}
    (hX : 1 ≤ X) (hτ : 1 ≤ τ)
    (hS : ∀ p ∈ S, (∀ t, |p t| ≤ X) ∧ PluckerRel p)
    (hdiv : ∀ m ∈ Icc 1 X, m.divisors.card ≤ τ) : S.card ≤ 14581 * τ * X ^ 5 := by
  have hc := minor_vector_count hS
  have hs : ∑ m ∈ Icc 1 X, 729 * m ^ 4 * m.divisors.card ≤ 729 * X ^ 5 * τ := by
    calc
      _ ≤ ∑ _m ∈ Icc 1 X, 729 * X ^ 4 * τ := by
        apply sum_le_sum
        intro m hm
        have hmX := (mem_Icc.mp hm).2
        gcongr
        exact hdiv m hm
      _ = _ := by rw [sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]; ring
  have hp : 1 ≤ X ^ 5 * τ := Nat.mul_pos (by positivity) (by omega)
  nlinarith

def ordinaryPatternSlack (a : ℕ) : ℕ := 14581 * tauMax (10 ^ 16 * a ^ 7)

lemma ordinaryPatternSlack_slow : SlowGrowth ordinaryPatternSlack := by
  have hc : SlowGrowth (fun _ : ℕ => 14581) := by
    intro η hη
    refine ⟨14581, by norm_num, fun a ha => ?_⟩
    have hp := Real.one_le_rpow (by exact_mod_cast ha : (1 : ℝ) ≤ a) hη.le
    norm_num
    linarith
  exact hc.mul (tauMax_slow (10 ^ 16) 7)

/-- The selected full patterns have an `X^5` count with proved subpolynomial slack. -/
theorem selected_ordinary_pattern_count {a b s T A : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hT : 36 ≤ T) :
    ((selectedStarts a b s T A).image (fun i => plk (Mi a b i))).card ≤
      ordinaryPatternSlack a * selectedMinorHeight a A T ^ 5 := by
  have hX := selectedMinorHeight_pos hba hmem hsT hT
  have hXb := selectedMinorHeight_le hba hmem hT
  have hτ : 1 ≤ tauMax (10 ^ 16 * a ^ 7) := by
    simpa using (tau_le_tauMax (hX.trans hXb) : (1 : ℕ).divisors.card ≤ _)
  apply ordinary_minor_count hX hτ
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    exact ⟨selectedStart_minor_height hba hmem hsT hi, plucker _⟩
  · intro m hm
    exact tau_le_tauMax ((mem_Icc.mp hm).2.trans hXb)

/-- The ordinary sum over patterns splits into two uniformly bounded classes. -/
theorem pattern_sum_two_classes {ι α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : Finset ι) (p : ι → α) (k : ι → β) (E : α → Prop) [DecidablePred E]
    {M N U V : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hM : ((G.image p).card : ℝ) ≤ M)
    (hN : (((G.image p).filter E).card : ℝ) ≤ N)
    (hc : ∀ v ∈ G.image p, (((G.filter fun i => p i = v).image k).card : ℝ) ≤
      if E v then V else U) :
    ((G.image fun i => (p i, k i)).card : ℝ) ≤ M * U + N * V := by
  have hs : ((G.image fun i => (p i, k i)).card : ℝ) ≤
      ∑ v ∈ G.image p, (((G.filter fun i => p i = v).image k).card : ℝ) := by
    exact_mod_cast pair_image_card_le_sum G p k
  calc _ ≤ ∑ v ∈ G.image p, if E v then V else U := hs.trans (sum_le_sum hc)
    _ = (((G.image p).filter E).card : ℝ) * V +
        (((G.image p).filter fun v => ¬ E v).card : ℝ) * U := by
      rw [sum_ite]
      simp
    _ ≤ N * V + ((G.image p).card : ℝ) * U := by
      gcongr
      exact filter_subset _ _
    _ ≤ N * V + M * U := by gcongr
    _ = _ := by ring

/-- Geometric estimates remaining per full pattern: square-root counting for
exceptional patterns, and a constant plus tenth-root graph count otherwise. -/
def IntegralLiftPatternEstimate (R : ℕ → ℕ) : Prop :=
  ∀ a b s T A : ℕ, b < a →
    (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
    s + T ≤ P a b → 36 ≤ T →
    124928 * A ^ 4 * selectedGapHeight a A T ^ 5 * selectedMinorHeight a A T < a ^ 3 →
    ∀ p ∈ (selectedStarts a b s T A).image (fun i => plk (Mi a b i)),
      ((((selectedStarts a b s T A).filter fun i => plk (Mi a b i) = p).image
        (kap a b)).card : ℝ) ≤
      if ∃ d, ExceptionalMinorRelation p d then
        (R a : ℝ) * (selectedGapHeight a A T : ℝ) ^ (1 / 2 : ℝ)
      else (R a : ℝ) * (1 + (max (selectedGapHeight a A T) (selectedLiftHeight a A T) : ℝ) ^
        (1 / 10 : ℝ))

/-- No lattice weights occur in the slack for the new embedding argument. -/
def integralLiftPatternSlack (R : ℕ → ℕ) (a : ℕ) : ℕ :=
  8 * R a * (ordinaryPatternSlack a + exceptionalPatternSlack a)

/-- Assemble the ordinary full-pattern count, exceptional-pattern count, and
quartic multiplicity into the displayed local estimate. -/
theorem integralLift_three_term_of_pattern_estimate {R : ℕ → ℕ}
    (hcurve : IntegralLiftPatternEstimate R) :
    IntegralLiftThreeTermEstimate (integralLiftPatternSlack R) := by
  intro a b s T A hba hmem hsT hT hscale
  classical
  let G := selectedStarts a b s T A
  let pm := fun i => plk (Mi a b i)
  let H := selectedGapHeight a A T
  let X := selectedMinorHeight a A T
  let B := max H (selectedLiftHeight a A T)
  have facts := fun i hi => selectedStart_spec hmem hsT (i := i) hi
  have hmult : G.card ≤ 4 * (G.image fun i => (pm i, kap a b i)).card :=
    selectedStarts_card_le_pair_image hba hmem hsT
  have hp := pattern_sum_two_classes G pm (kap a b) (fun p => ∃ d, ExceptionalMinorRelation p d)
    (show (0 : ℝ) ≤ R a * (1 + (B : ℝ) ^ (1 / 10 : ℝ)) by positivity)
    (show (0 : ℝ) ≤ R a * (H : ℝ) ^ (1 / 2 : ℝ) by positivity)
    (show ((G.image pm).card : ℝ) ≤ ordinaryPatternSlack a * (X : ℝ) ^ 5 by
      exact_mod_cast selected_ordinary_pattern_count hba hmem hsT hT)
    (show (((G.image pm).filter fun p => ∃ d, ExceptionalMinorRelation p d).card : ℝ) ≤
        exceptionalPatternSlack a * (X : ℝ) ^ 4 by
      exact_mod_cast selected_exceptional_pattern_count_slack hba hmem hsT hT)
    (by simpa only [G, pm, H, B, Nat.cast_max] using hcurve a b s T A hba hmem hsT hT hscale)
  have hTcard := selectedStarts_card hba hmem hsT hT
  change T ≤ 2 * G.card at hTcard
  have hTc : (T : ℝ) ≤ 8 * ((G.image fun i => (pm i, kap a b i)).card : ℝ) := by
    exact_mod_cast (show T ≤ 8 * (G.image fun i => (pm i, kap a b i)).card by omega)
  dsimp only
  have hO : (ordinaryPatternSlack a : ℝ) ≤ ordinaryPatternSlack a + exceptionalPatternSlack a :=
    le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hE : (exceptionalPatternSlack a : ℝ) ≤ ordinaryPatternSlack a + exceptionalPatternSlack a :=
    le_add_of_nonneg_left (Nat.cast_nonneg _)
  calc (T : ℝ) ≤ 8 * ((ordinaryPatternSlack a : ℝ) * (X : ℝ) ^ 5 *
        ((R a : ℝ) * (1 + (B : ℝ) ^ (1 / 10 : ℝ))) +
        (exceptionalPatternSlack a : ℝ) * (X : ℝ) ^ 4 * ((R a : ℝ) * (H : ℝ) ^ (1 / 2 : ℝ))) :=
      hTc.trans (mul_le_mul_of_nonneg_left hp (by norm_num))
    _ ≤ 8 * (((ordinaryPatternSlack a : ℝ) + exceptionalPatternSlack a) * (X : ℝ) ^ 5 *
        ((R a : ℝ) * (1 + (B : ℝ) ^ (1 / 10 : ℝ))) +
        ((ordinaryPatternSlack a : ℝ) + exceptionalPatternSlack a) * (X : ℝ) ^ 4 *
          ((R a : ℝ) * (H : ℝ) ^ (1 / 2 : ℝ))) := by gcongr
    _ = _ := by simp only [integralLiftPatternSlack, Nat.cast_mul, Nat.cast_add,
        Nat.cast_ofNat, Nat.cast_max, B, H, X]; ring

lemma slowGrowth_add {F G : ℕ → ℕ} (hF : SlowGrowth F) (hG : SlowGrowth G) :
    SlowGrowth (fun a => F a + G a) := by
  intro η hη
  obtain ⟨C, hC, hc⟩ := hF η hη
  obtain ⟨D, hD, hd⟩ := hG η hη
  refine ⟨C + D, by positivity, fun a ha => ?_⟩
  have h1 := hc a ha
  have h2 := hd a ha
  push_cast
  nlinarith

lemma integralLiftPatternSlack_slow {R : ℕ → ℕ} (hR : SlowGrowth R) :
    SlowGrowth (integralLiftPatternSlack R) := by
  have hc : SlowGrowth (fun _ : ℕ => 8) := by
    intro η hη
    refine ⟨8, by norm_num, fun a ha => ?_⟩
    have hp := Real.one_le_rpow (by exact_mod_cast ha : (1 : ℝ) ≤ a) hη.le
    norm_num
    linarith
  exact (hc.mul hR).mul (slowGrowth_add ordinaryPatternSlack_slow exceptionalPatternSlack_slow)

/-- The final exponent now depends only on the two unweighted per-pattern
arithmetic estimates, with all combinatorial and analytic assembly proved. -/
theorem P_le_151_513_of_pattern_estimate {R : ℕ → ℕ} (hR : SlowGrowth R)
    (hcurve : IntegralLiftPatternEstimate R) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((151 : ℝ) / 513 + ε) :=
  P_le_151_513_of_three_term_estimate (integralLiftPatternSlack_slow hR)
    (integralLift_three_term_of_pattern_estimate hcurve)

end PierceLengthBound.FixedDividend
