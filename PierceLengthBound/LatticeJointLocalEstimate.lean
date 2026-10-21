/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.LatticeJointPatternCount
public import PierceLengthBound.LatticeJointWeights
public import PierceLengthBound.RealPowerBounds

/-!
# The five-term local estimate

Summing the lattice-box pattern counts over patterns, the box of a pattern with shortest lattice
vector `λ` contributes `(H/λ)^{1/h} + (S/λ²)^{m/h} + Y^{n/h}`, and the fractional weights
`∑ λ^{-t} ≪ X^{5-t/3}` turn this into
`T ≪ X⁵ + X⁴H^{1/2} + X^{5-1/(3h)}H^{1/h} + X^{5-2m/(3h)}S^{m/h} + X⁵Y^{n/h}`
with `h = 10n + 7m`.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

/-- The `1/h`-th power of the lattice box splits into the three coordinate terms (paper,
`prop:latticewindow`). -/
theorem lattice_box_rpow_le {H S Y lam m n : ℕ} (hlam : 1 ≤ lam) {h : ℝ} (h1 : 1 ≤ h)
    (hm : (2 * m : ℝ) ≤ h) :
    ((max 1 (max (3 * H / lam) (max ((8 * S / (3 * lam ^ 2)) ^ m) (Y ^ n))) : ℕ) : ℝ) ^
        (1 / h) ≤
      1 + 3 * (H : ℝ) ^ (1 / h) * ((lam : ℝ)⁻¹) ^ (1 / h) +
        8 * (S : ℝ) ^ ((m : ℝ) / h) * ((lam : ℝ)⁻¹) ^ (2 * (m : ℝ) / h) +
        (Y : ℝ) ^ ((n : ℝ) / h) := by
  have hh : 0 < h := by linarith
  have hr : (0 : ℝ) ≤ 1 / h := by positivity
  have hlr : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hl0 : (0 : ℝ) < lam := by linarith
  have hli : (0 : ℝ) ≤ (lam : ℝ)⁻¹ := by positivity
  have hmh0 : (0 : ℝ) ≤ (m : ℝ) / h := by positivity
  have hmh : (m : ℝ) / h ≤ 1 := by
    rw [div_le_one hh]; linarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
  simp only [Nat.cast_max, Nat.cast_one]
  have m1 := max_rpow_le_add (r := 1 / h) (u := 1)
    (v := max ((3 * H / lam : ℕ) : ℝ) (max (((8 * S / (3 * lam ^ 2)) ^ m : ℕ) : ℝ)
      ((Y ^ n : ℕ) : ℝ))) (by norm_num) (by positivity)
  have m2 := max_rpow_le_add (r := 1 / h) (u := ((3 * H / lam : ℕ) : ℝ))
    (v := max (((8 * S / (3 * lam ^ 2)) ^ m : ℕ) : ℝ) ((Y ^ n : ℕ) : ℝ))
    (by positivity) (by positivity)
  have m3 := max_rpow_le_add (r := 1 / h) (u := (((8 * S / (3 * lam ^ 2)) ^ m : ℕ) : ℝ))
    (v := ((Y ^ n : ℕ) : ℝ)) (by positivity) (by positivity)
  rw [Real.one_rpow] at m1
  -- node term
  have hx : ((3 * H / lam : ℕ) : ℝ) ^ (1 / h) ≤
      3 * (H : ℝ) ^ (1 / h) * ((lam : ℝ)⁻¹) ^ (1 / h) := by
    have hle : ((3 * H / lam : ℕ) : ℝ) ≤ 3 * (H : ℝ) * (lam : ℝ)⁻¹ := by
      have := Nat.cast_div_le (α := ℝ) (m := 3 * H) (n := lam)
      push_cast at this
      simpa [div_eq_mul_inv] using this
    calc ((3 * H / lam : ℕ) : ℝ) ^ (1 / h) ≤ (3 * (H : ℝ) * (lam : ℝ)⁻¹) ^ (1 / h) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hle hr
      _ = (3 : ℝ) ^ (1 / h) * (H : ℝ) ^ (1 / h) * ((lam : ℝ)⁻¹) ^ (1 / h) := by
          rw [Real.mul_rpow (by positivity) hli, Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)]
      _ ≤ 3 * (H : ℝ) ^ (1 / h) * ((lam : ℝ)⁻¹) ^ (1 / h) := by
          gcongr
          exact rpow_le_self_of_le_one (by norm_num)
            (by rw [div_le_one hh]; exact h1)
  -- curvature term
  have hy : ((((8 * S / (3 * lam ^ 2)) ^ m : ℕ)) : ℝ) ^ (1 / h) ≤
      8 * (S : ℝ) ^ ((m : ℝ) / h) * ((lam : ℝ)⁻¹) ^ (2 * (m : ℝ) / h) := by
    rw [natCast_pow_rpow]
    have hle : ((8 * S / (3 * lam ^ 2) : ℕ) : ℝ) ≤ 8 * (S : ℝ) * ((lam : ℝ)⁻¹) ^ 2 := by
      have h3 := Nat.cast_div_le (α := ℝ) (m := 8 * S) (n := 3 * lam ^ 2)
      push_cast at h3
      refine h3.trans ?_
      rw [inv_pow, ← div_eq_mul_inv]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [pow_pos hl0 2]
    calc ((8 * S / (3 * lam ^ 2) : ℕ) : ℝ) ^ ((m : ℝ) / h) ≤
          (8 * (S : ℝ) * ((lam : ℝ)⁻¹) ^ 2) ^ ((m : ℝ) / h) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hle hmh0
      _ = (8 : ℝ) ^ ((m : ℝ) / h) * (S : ℝ) ^ ((m : ℝ) / h) *
            ((lam : ℝ)⁻¹) ^ (2 * (m : ℝ) / h) := by
          rw [Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by norm_num) (Nat.cast_nonneg _), ← Real.rpow_natCast,
            ← Real.rpow_mul hli]
          congr 2; push_cast; ring
      _ ≤ 8 * (S : ℝ) ^ ((m : ℝ) / h) * ((lam : ℝ)⁻¹) ^ (2 * (m : ℝ) / h) := by
          gcongr
          exact rpow_le_self_of_le_one (by norm_num) hmh
  have hY : (((Y ^ n : ℕ)) : ℝ) ^ (1 / h) = (Y : ℝ) ^ ((n : ℝ) / h) := natCast_pow_rpow Y n
  linarith

/-- The five-term local estimate on actual remainder windows. -/
def LatticeJointFiveTermEstimate (m n : ℕ) (R : ℕ → ℕ) : Prop :=
  ∀ a b s T A : ℕ, b < a →
    (∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) →
    s + T ≤ P a b → 36 ≤ T →
    124928 * A ^ 4 * selectedGapHeight a A T ^ 5 * selectedMinorHeight a A T < a ^ 3 →
    let h : ℝ := ((10 * n + 7 * m : ℕ) : ℝ)
    let H : ℝ := selectedGapHeight a A T
    let X : ℝ := selectedMinorHeight a A T
    let S : ℝ := selectedAllMinorHeight a A T
    let Y : ℝ := selectedRankFiveHeight a A T
    (T : ℝ) ≤ R a * (X ^ 5 + X ^ 4 * H ^ (1 / 2 : ℝ) +
      X ^ (5 - (1 / h) / 3) * H ^ (1 / h) + X ^ (5 - (2 * m / h) / 3) * S ^ (m / h) +
      X ^ 5 * Y ^ (n / h))

/-- The slack of the five-term estimate: `8 = 4 · 2` from the pattern multiplicity and the
selected starts, and `2 O + Ex + 8 W` dominates the coefficients of the five terms (the `2` from
`1 + (1 + …)` in the pattern count and the `8` from the curvature coefficient). -/
def latticeJointSlack (R : ℕ → ℕ) (a : ℕ) : ℕ :=
  8 * R a * (2 * ordinaryPatternSlack a + exceptionalPatternSlack a + 8 * latticeWeightSlack a)

lemma latticeJointSlack_slow {R : ℕ → ℕ} (hR : SlowGrowth R) :
    SlowGrowth (latticeJointSlack R) := by
  have hsum : SlowGrowth (fun a => 2 * ordinaryPatternSlack a + exceptionalPatternSlack a +
      8 * latticeWeightSlack a) :=
    slowGrowth_add (slowGrowth_add ((slowGrowth_const 2).mul ordinaryPatternSlack_slow)
      exceptionalPatternSlack_slow) ((slowGrowth_const 8).mul latticeWeightSlack_slow)
  exact ((slowGrowth_const 8).mul hR).mul hsum

/-- Summing the pattern estimate with the fractional lattice weights. -/
theorem lattice_joint_five_term_of_pattern_estimate {m n : ℕ} (hm : 0 < m) {R : ℕ → ℕ}
    (hcurve : LatticeJointPatternEstimate m n R) :
    LatticeJointFiveTermEstimate m n (latticeJointSlack R) := by
  intro a b s T A hba hmem hsT hT hscale
  classical
  let G := selectedStarts a b s T A
  let pm := fun i => plk (Mi a b i)
  let Pset := G.image pm
  set hN : ℕ := 10 * n + 7 * m
  set h : ℝ := (hN : ℝ)
  set H := selectedGapHeight a A T
  set X := selectedMinorHeight a A T
  set S := selectedAllMinorHeight a A T
  set Y := selectedRankFiveHeight a A T
  have facts := fun i hi => selectedStart_spec hmem hsT (i := i) hi
  have hh1 : (1 : ℝ) ≤ h := by
    simp only [h, hN]; push_cast
    nlinarith [show (1 : ℝ) ≤ m by exact_mod_cast hm, show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  have hh : 0 < h := by linarith
  have hm2 : (2 * m : ℝ) ≤ h := by
    simp only [h, hN]; push_cast; nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n,
      show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
  have hs : ((G.image fun i => (pm i, kap a b i)).card : ℝ) ≤
      ∑ p ∈ Pset, (((G.filter fun i => pm i = p).image (kap a b)).card : ℝ) := by
    exact_mod_cast pair_image_card_le_sum G pm (kap a b)
  -- the per-pattern bound
  let E := fun p : Fin 10 → ℤ => ∃ d, ExceptionalMinorRelation p d
  let f := fun p : Fin 10 → ℤ => (R a : ℝ) * (2 + 3 * (H : ℝ) ^ (1 / h) *
    ((shortR p : ℝ)⁻¹) ^ (1 / h) + 8 * (S : ℝ) ^ ((m : ℝ) / h) *
      ((shortR p : ℝ)⁻¹) ^ (2 * (m : ℝ) / h) + (Y : ℝ) ^ ((n : ℝ) / h))
  have hper (p) (hp : p ∈ Pset) :
      (((G.filter fun i => pm i = p).image (kap a b)).card : ℝ) ≤
        f p + if E p then (R a : ℝ) * (H : ℝ) ^ (1 / 2 : ℝ) else 0 := by
    have hc := hcurve a b s T A hba hmem hsT hT hscale p hp
    have hf0 : 0 ≤ f p := by positivity
    split_ifs at hc ⊢ with hE
    · linarith
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
      have hP := (facts i hi).1
      have hl := shortR_pos (orbit_pattern_first hba (l := i) (by omega))
      have hbox := lattice_box_rpow_le (H := H) (S := S) (Y := Y) (m := m) (n := n) hl hh1 hm2
      refine hc.trans ?_
      rw [add_zero]
      calc (R a : ℝ) * (1 + (latticeJointBoxHeight (plk (Mi a b i)) a A T m n : ℝ) ^
            (1 / ((10 * n + 7 * m : ℕ) : ℝ))) ≤ (R a : ℝ) * (1 + (1 + 3 * (H : ℝ) ^ (1 / h) *
            ((shortR (plk (Mi a b i)) : ℝ)⁻¹) ^ (1 / h) + 8 * (S : ℝ) ^ ((m : ℝ) / h) *
            ((shortR (plk (Mi a b i)) : ℝ)⁻¹) ^ (2 * (m : ℝ) / h) +
            (Y : ℝ) ^ ((n : ℝ) / h))) := by
            gcongr
            exact hbox
        _ = f (plk (Mi a b i)) := by simp only [f]; ring
  have hsum : ∑ p ∈ Pset, (((G.filter fun i => pm i = p).image (kap a b)).card : ℝ) ≤
      ∑ p ∈ Pset, f p + (R a : ℝ) * (H : ℝ) ^ (1 / 2 : ℝ) * ((Pset.filter E).card : ℝ) := by
    calc _ ≤ ∑ p ∈ Pset, (f p + if E p then (R a : ℝ) * (H : ℝ) ^ (1 / 2 : ℝ) else 0) :=
          sum_le_sum hper
      _ = _ := by
          rw [sum_add_distrib, sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
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
  have hO : 0 ≤ O := Nat.cast_nonneg _
  have hEx : 0 ≤ Ex := Nat.cast_nonneg _
  have hW : 0 ≤ W := Nat.cast_nonneg _
  have hRa : 0 ≤ Ra := Nat.cast_nonneg _
  have t1 : 0 ≤ (H : ℝ) ^ (1 / h) := by positivity
  have t2 : 0 ≤ (S : ℝ) ^ ((m : ℝ) / h) := by positivity
  have t3 : 0 ≤ (Y : ℝ) ^ ((n : ℝ) / h) := by positivity
  have t4 : 0 ≤ (H : ℝ) ^ (1 / 2 : ℝ) := by positivity
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
      Ra * (H : ℝ) ^ (1 / 2 : ℝ) * (Ex * (X : ℝ) ^ 4)) := by
    refine hTc.trans ?_
    gcongr
    refine hs.trans (hsum.trans ?_)
    rw [hfsum]
    gcongr
  dsimp only
  have hgoal : (latticeJointSlack R a : ℝ) = 8 * Ra * (2 * O + Ex + 8 * W) := by
    simp only [latticeJointSlack, Ra, O, Ex, W]; push_cast; ring
  rw [hgoal]
  -- each term of `hbound` is at most `8 Ra Σ` times the matching term of the goal
  set Csum := 2 * O + Ex + 8 * W
  have e1 := mul_le_mul_of_nonneg_right (show 2 * O ≤ Csum by linarith) hx5
  have e2 := mul_le_mul_of_nonneg_right (show O ≤ Csum by linarith) (mul_nonneg hx5 t3)
  have e3 := mul_le_mul_of_nonneg_right (show 3 * W ≤ Csum by linarith) (mul_nonneg hxa t1)
  have e4 := mul_le_mul_of_nonneg_right (show 8 * W ≤ Csum by linarith) (mul_nonneg hxb t2)
  have e5 := mul_le_mul_of_nonneg_right (show Ex ≤ Csum by linarith) (mul_nonneg hx4 t4)
  have hterms : (O * (X : ℝ) ^ 5) * (2 + (Y : ℝ) ^ ((n : ℝ) / h)) +
      3 * (H : ℝ) ^ (1 / h) * (W * (X : ℝ) ^ (5 - (1 / h) / 3)) +
      8 * (S : ℝ) ^ ((m : ℝ) / h) * (W * (X : ℝ) ^ (5 - (2 * (m : ℝ) / h) / 3)) +
      (H : ℝ) ^ (1 / 2 : ℝ) * (Ex * (X : ℝ) ^ 4) ≤
      Csum * ((X : ℝ) ^ 5 + (X : ℝ) ^ 4 * (H : ℝ) ^ (1 / 2 : ℝ) +
        (X : ℝ) ^ (5 - (1 / h) / 3) * (H : ℝ) ^ (1 / h) +
        (X : ℝ) ^ (5 - (2 * (m : ℝ) / h) / 3) * (S : ℝ) ^ ((m : ℝ) / h) +
        (X : ℝ) ^ 5 * (Y : ℝ) ^ ((n : ℝ) / h)) := by
    linarith
  have := mul_le_mul_of_nonneg_left hterms (by positivity : (0 : ℝ) ≤ 8 * Ra)
  refine hbound.trans ((le_of_eq ?_).trans (this.trans (le_of_eq ?_))) <;> ring

/-- Every fixed pair of positive powers has the five-term local bound. -/
theorem latticeJointFiveTermEstimate_exists (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ LatticeJointFiveTermEstimate m n R := by
  obtain ⟨R, hR, hcount⟩ := latticeJointPatternEstimate_exists m n hm hn
  exact ⟨latticeJointSlack R, latticeJointSlack_slow hR,
    lattice_joint_five_term_of_pattern_estimate hm hcount⟩

end
end PierceLengthBound.FixedDividend
