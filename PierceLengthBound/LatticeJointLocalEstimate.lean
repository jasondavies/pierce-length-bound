/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.LatticeJointPatternCount
public import PierceLengthBound.JointPatternAssembly
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

/-- The lattice box of a selected pattern, split by `lattice_box_rpow_le` at its shortest
lattice vector. -/
theorem selected_lattice_box_rpow_le {m n hN : ℕ} (hh1 : (1 : ℝ) ≤ hN) (hm2 : (2 * m : ℝ) ≤ hN)
    {a b s T A : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) (hsT : s + T ≤ P a b)
    {p : Fin 10 → ℤ} (hp : p ∈ (selectedStarts a b s T A).image (fun i => plk (Mi a b i))) :
    latticeJointBox m n p a A T ^ (1 / (hN : ℝ)) ≤
      1 + 3 * (selectedGapHeight a A T : ℝ) ^ (1 / (hN : ℝ)) *
          ((shortR p : ℝ)⁻¹) ^ (1 / (hN : ℝ)) +
        8 * (selectedAllMinorHeight a A T : ℝ) ^ ((m : ℝ) / hN) *
          ((shortR p : ℝ)⁻¹) ^ (2 * (m : ℝ) / hN) +
        (selectedRankFiveHeight a A T : ℝ) ^ ((n : ℝ) / hN) := by
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
  have hP := (selectedStart_spec hmem hsT hi).1
  exact lattice_box_rpow_le (shortR_pos (orbit_pattern_first hba (l := i) (by omega))) hh1 hm2

/-- Summing the lattice boxes with the fractional lattice weights, shared by the five- and
six-term estimates. The window bound `hT8` is `selected_count_le_pattern_sum`, and each box
`Box p` is at most the split lattice box plus an extra term, whose sum is at most `Rb Q`. Each
term is then at most `8 R (2 O + Ex + 8 W + Rb)` times the matching displayed term. -/
theorem lattice_terms_of_pattern_sum {m n hN : ℕ} (hh1 : (1 : ℝ) ≤ hN)
    (hm2 : (2 * m : ℝ) ≤ hN) {R : ℕ → ℕ} {a b s T A : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hT : 36 ≤ T) {Box extra : (Fin 10 → ℤ) → ℝ} {Rb Q : ℝ}
    (hRb : 0 ≤ Rb) (hQ : 0 ≤ Q)
    (hT8 : (T : ℝ) ≤ 8 * ((R a : ℝ) *
      ∑ p ∈ (selectedStarts a b s T A).image (fun i => plk (Mi a b i)), (1 + Box p) +
      (R a : ℝ) * (selectedGapHeight a A T : ℝ) ^ (1 / 2 : ℝ) *
        (exceptionalPatternSlack a * (selectedMinorHeight a A T : ℝ) ^ 4)))
    (hbox : ∀ p ∈ (selectedStarts a b s T A).image (fun i => plk (Mi a b i)),
      Box p ≤ 1 + 3 * (selectedGapHeight a A T : ℝ) ^ (1 / (hN : ℝ)) *
          ((shortR p : ℝ)⁻¹) ^ (1 / (hN : ℝ)) +
        8 * (selectedAllMinorHeight a A T : ℝ) ^ ((m : ℝ) / hN) *
          ((shortR p : ℝ)⁻¹) ^ (2 * (m : ℝ) / hN) +
        (selectedRankFiveHeight a A T : ℝ) ^ ((n : ℝ) / hN) + extra p)
    (hextra : ∑ p ∈ (selectedStarts a b s T A).image (fun i => plk (Mi a b i)), extra p ≤
      Rb * Q) :
    let h : ℝ := hN
    let H : ℝ := selectedGapHeight a A T
    let X : ℝ := selectedMinorHeight a A T
    let S : ℝ := selectedAllMinorHeight a A T
    let Y : ℝ := selectedRankFiveHeight a A T
    (T : ℝ) ≤ 8 * R a * (2 * ordinaryPatternSlack a + exceptionalPatternSlack a +
        8 * latticeWeightSlack a + Rb) *
      (X ^ 5 + X ^ 4 * H ^ (1 / 2 : ℝ) +
        X ^ (5 - (1 / h) / 3) * H ^ (1 / h) + X ^ (5 - (2 * m / h) / 3) * S ^ (m / h) +
        X ^ 5 * Y ^ (n / h) + Q) := by
  classical
  set Pset := (selectedStarts a b s T A).image fun i => plk (Mi a b i)
  set h : ℝ := (hN : ℝ)
  set H := selectedGapHeight a A T
  set X := selectedMinorHeight a A T
  set S := selectedAllMinorHeight a A T
  set Y := selectedRankFiveHeight a A T
  have hh : 0 < h := by linarith
  let f := fun p : Fin 10 → ℤ => 2 + 3 * (H : ℝ) ^ (1 / h) *
    ((shortR p : ℝ)⁻¹) ^ (1 / h) + 8 * (S : ℝ) ^ ((m : ℝ) / h) *
      ((shortR p : ℝ)⁻¹) ^ (2 * (m : ℝ) / h) + (Y : ℝ) ^ ((n : ℝ) / h)
  have hsum : ∑ p ∈ Pset, (1 + Box p) ≤ ∑ p ∈ Pset, f p + Rb * Q := by
    calc _ ≤ ∑ p ∈ Pset, (f p + extra p) := sum_le_sum fun p hp => by
          have := hbox p hp
          simp only [f]
          linarith
      _ ≤ _ := by rw [sum_add_distrib]; linarith
  -- the weights and counts
  have hW1 := selected_pattern_weight_sum hba hmem hsT hT (t := 1 / h) (by positivity)
    (by rw [div_le_one hh]; exact hh1)
  have hW2 := selected_pattern_weight_sum hba hmem hsT hT (t := 2 * (m : ℝ) / h) (by positivity)
    (by rw [div_le_one hh]; exact hm2)
  have hP : (Pset.card : ℝ) ≤ ordinaryPatternSlack a * (X : ℝ) ^ 5 := by
    exact_mod_cast selected_ordinary_pattern_count hba hmem hsT hT
  have hfsum : ∑ p ∈ Pset, f p = (Pset.card : ℝ) * (2 + (Y : ℝ) ^ ((n : ℝ) / h)) +
      3 * (H : ℝ) ^ (1 / h) * ∑ p ∈ Pset, ((shortR p : ℝ)⁻¹) ^ (1 / h) +
      8 * (S : ℝ) ^ ((m : ℝ) / h) * ∑ p ∈ Pset, ((shortR p : ℝ)⁻¹) ^ (2 * (m : ℝ) / h) := by
    simp only [f, ← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul]
    ring
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
      8 * (S : ℝ) ^ ((m : ℝ) / h) * (W * (X : ℝ) ^ (5 - (2 * (m : ℝ) / h) / 3)) + Rb * Q) +
      Ra * (H : ℝ) ^ (1 / 2 : ℝ) * (Ex * (X : ℝ) ^ 4)) := by
    refine hT8.trans ?_
    gcongr
    refine hsum.trans ?_
    rw [hfsum]
    gcongr
  dsimp only
  -- each term of `hbound` is at most `8 Ra Σ` times the matching term of the goal
  set Csum := 2 * O + Ex + 8 * W + Rb
  have e1 := mul_le_mul_of_nonneg_right (show 2 * O ≤ Csum by linarith) hx5
  have e2 := mul_le_mul_of_nonneg_right (show O ≤ Csum by linarith) (mul_nonneg hx5 t3)
  have e3 := mul_le_mul_of_nonneg_right (show 3 * W ≤ Csum by linarith) (mul_nonneg hxa t1)
  have e4 := mul_le_mul_of_nonneg_right (show 8 * W ≤ Csum by linarith) (mul_nonneg hxb t2)
  have e5 := mul_le_mul_of_nonneg_right (show Ex ≤ Csum by linarith) (mul_nonneg hx4 t4)
  have e6 := mul_le_mul_of_nonneg_right (show Rb ≤ Csum by linarith) hQ
  have hterms : (O * (X : ℝ) ^ 5) * (2 + (Y : ℝ) ^ ((n : ℝ) / h)) +
      3 * (H : ℝ) ^ (1 / h) * (W * (X : ℝ) ^ (5 - (1 / h) / 3)) +
      8 * (S : ℝ) ^ ((m : ℝ) / h) * (W * (X : ℝ) ^ (5 - (2 * (m : ℝ) / h) / 3)) + Rb * Q +
      (H : ℝ) ^ (1 / 2 : ℝ) * (Ex * (X : ℝ) ^ 4) ≤
      Csum * ((X : ℝ) ^ 5 + (X : ℝ) ^ 4 * (H : ℝ) ^ (1 / 2 : ℝ) +
        (X : ℝ) ^ (5 - (1 / h) / 3) * (H : ℝ) ^ (1 / h) +
        (X : ℝ) ^ (5 - (2 * (m : ℝ) / h) / 3) * (S : ℝ) ^ ((m : ℝ) / h) +
        (X : ℝ) ^ 5 * (Y : ℝ) ^ ((n : ℝ) / h) + Q) := by
    linarith
  have := mul_le_mul_of_nonneg_left hterms (by positivity : (0 : ℝ) ≤ 8 * Ra)
  refine hbound.trans ((le_of_eq ?_).trans (this.trans (le_of_eq ?_))) <;> ring

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
  have hh1 : (1 : ℝ) ≤ ((10 * n + 7 * m : ℕ) : ℝ) := by
    push_cast
    nlinarith [show (1 : ℝ) ≤ m by exact_mod_cast hm, show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  have hm2 : (2 * m : ℝ) ≤ ((10 * n + 7 * m : ℕ) : ℝ) := by
    push_cast; nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n,
      show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
  have h := lattice_terms_of_pattern_sum hh1 hm2 hba hmem hsT hT le_rfl le_rfl
    (selected_count_le_pattern_sum hcurve hba hmem hsT hT hscale)
    (fun p hp => (selected_lattice_box_rpow_le hh1 hm2 hba hmem hsT hp).trans_eq
      (add_zero _).symm) (sum_const_zero.trans_le (mul_zero 0).ge)
  refine h.trans (le_of_eq ?_)
  simp only [latticeJointSlack, add_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]

/-- Every fixed pair of positive powers has the five-term local bound. -/
theorem latticeJointFiveTermEstimate_exists (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ R : ℕ → ℕ, SlowGrowth R ∧ LatticeJointFiveTermEstimate m n R := by
  obtain ⟨R, hR, hcount⟩ := latticeJointPatternEstimate_exists m n hm hn
  exact ⟨latticeJointSlack R, latticeJointSlack_slow hR,
    lattice_joint_five_term_of_pattern_estimate hm hcount⟩

end
end PierceLengthBound.FixedDividend
