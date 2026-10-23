/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.HypersurfacePatternCountNonzero
public import PierceLengthBound.HypersurfacePatternCountZero

/-! # The complete polynomial count on a maximal-minor chart -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Finset

lemma chart_zero_count_le_fiber_counts (B : HypersurfaceChartPolynomial) (m : ℕ) :
    (((crossSet m).filter fun uv => eval
      (Sum.elim (fun i => (uv.2 i : ℚ)) (chartFirstVertex m uv.1)) B = 0).card : ℝ) ≤
      (zeroChartFibers B m).card + (nonzeroChartFibers B m).card := by
  classical
  have hs : ((crossSet m).filter fun uv => eval
      (Sum.elim (fun i => (uv.2 i : ℚ)) (chartFirstVertex m uv.1)) B = 0) ⊆
      zeroChartFibers B m ∪ nonzeroChartFibers B m := by
    intro uv huv
    obtain ⟨huv, hzero⟩ := mem_filter.mp huv
    by_cases hf : chartPolynomialFiber B (chartFirstVertex m uv.1) = 0
    · exact mem_union_left _ (mem_filter.mpr ⟨huv, hf⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨huv, hf, by
        rw [chartPolynomialFiber_eval]
        exact hzero⟩)
  exact_mod_cast (card_le_card hs).trans (card_union_le _ _)

/-- A fixed nonzero chart polynomial removes one-third of a power from the ordinary
five-dimensional pattern count. All common divisors and all identically-zero fibers are
included. The epsilon absorbs only the two divisor-maximum factors. -/
theorem chart_polynomial_count {B : HypersurfaceChartPolynomial} (hB : B ≠ 0) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ X : ℕ, 1 ≤ X →
      (∑ m ∈ Icc 1 X, (((crossSet m).filter fun uv => eval
        (Sum.elim (fun i => (uv.2 i : ℚ)) (chartFirstVertex m uv.1)) B = 0).card : ℝ)) ≤
        C * (X : ℝ) ^ (14 / 3 + ε) := by
  obtain ⟨q, hq, hqzero⟩ := chartPolynomialFiber_zero_certificate hB
  have hslow : SlowGrowth (fun X => tauMax X ^ 2) := by
    simpa only [pow_one, one_mul] using (tauMax_slow 1 1).pow 2
  intro ε hε
  obtain ⟨C, hC, hτ⟩ := hslow ε hε
  let K : ℝ := 2187 * q.totalDegree + 1423737 * (chartPolynomialFamily B).totalDegree * C + 1
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro X hX
  have hXR : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hτX : (tauMax X : ℝ) ^ 2 ≤ C * (X : ℝ) ^ ε := by
    simpa only [Nat.cast_pow] using hτ X hX
  have hpow := Real.one_le_rpow (show (1 : ℝ) ≤ X by exact_mod_cast hX) hε.le
  have hcoeff : 2187 * q.totalDegree +
      1423737 * (chartPolynomialFamily B).totalDegree * (tauMax X : ℝ) ^ 2 ≤
      K * (X : ℝ) ^ ε := by
    have ht := mul_le_mul_of_nonneg_left hτX
      (show (0 : ℝ) ≤ 1423737 * (chartPolynomialFamily B).totalDegree by positivity)
    have hz := mul_le_mul_of_nonneg_left hpow
      (show (0 : ℝ) ≤ 2187 * q.totalDegree by positivity)
    dsimp [K]
    nlinarith [Real.rpow_nonneg hXR.le ε]
  have hz := zeroChartFibers_sum B hq hqzero hX
  have hn := nonzeroChartFibers_sum B hX
  calc _ ≤ ∑ m ∈ Icc 1 X,
        ((zeroChartFibers B m).card + (nonzeroChartFibers B m).card : ℝ) :=
          sum_le_sum fun m _ => chart_zero_count_le_fiber_counts B m
    _ ≤ (2187 * q.totalDegree +
        1423737 * (chartPolynomialFamily B).totalDegree * (tauMax X : ℝ) ^ 2) *
        (X : ℝ) ^ (14 / 3 : ℝ) := by rw [sum_add_distrib]; nlinarith
    _ ≤ (K * (X : ℝ) ^ ε) * (X : ℝ) ^ (14 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hXR.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hXR, add_comm ε]

end
end PierceLengthBound.FixedDividend
