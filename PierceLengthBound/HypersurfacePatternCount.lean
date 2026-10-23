/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.HypersurfacePatternCover
public import PierceLengthBound.HypersurfacePatternCountChartBound

/-! Assemble the twenty signed charts into a count of integral Plücker vectors,
first with an explicit divisor-maximum coefficient at the exponent 14/3 and
then in the `X^(14/3+ε)` form. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open MvPolynomial Finset
noncomputable section

/-- A fixed nonzero chart polynomial has at most `K (1 + τ_max(X)²) X^(14/3)` zeros
over the pivots `1 ≤ m ≤ X`. -/
theorem chart_polynomial_count_tau {B : HypersurfaceChartPolynomial} (hB : B ≠ 0) :
    ∃ K : ℕ, ∀ X : ℕ, 1 ≤ X →
      (∑ m ∈ Icc 1 X, ((chartPolynomialZeros B m).card : ℝ)) ≤
        (K : ℝ) * (1 + (tauMax X : ℝ) ^ 2) * (X : ℝ) ^ (14 / 3 : ℝ) := by
  obtain ⟨q, hq, hqzero⟩ := chartPolynomialFiber_zero_certificate hB
  refine ⟨2187 * q.totalDegree + 1423737 * (chartPolynomialFamily B).totalDegree, ?_⟩
  intro X hX
  have hz := zeroChartFibers_sum B hq hqzero hX
  have hn := nonzeroChartFibers_sum B hX
  have hc : 2187 * (q.totalDegree : ℝ) +
      1423737 * (chartPolynomialFamily B).totalDegree * (tauMax X : ℝ) ^ 2 ≤
      (2187 * q.totalDegree + 1423737 * (chartPolynomialFamily B).totalDegree : ℕ) *
        (1 + (tauMax X : ℝ) ^ 2) := by
    push_cast
    nlinarith [sq_nonneg (tauMax X : ℝ)]
  calc _ ≤ ∑ m ∈ Icc 1 X,
        ((zeroChartFibers B m).card + (nonzeroChartFibers B m).card : ℝ) :=
          sum_le_sum fun m _ => chart_zero_count_le_fiber_counts B m
    _ ≤ (2187 * q.totalDegree +
        1423737 * (chartPolynomialFamily B).totalDegree * (tauMax X : ℝ) ^ 2) *
        (X : ℝ) ^ (14 / 3 : ℝ) := by rw [sum_add_distrib]; nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

/-- A proper polynomial condition `F = 0` holds on at most
`K (1 + τ_max(X)²) X^(14/3)` integral Plücker vectors of height at most `X`.
The count includes non-primitive vectors and the zero vector. -/
theorem hypersurface_pattern_count_tau {F : MvPolynomial (Fin 10) ℚ}
    (hF : ProperOnMinorCone F) :
    ∃ K : ℕ, ∀ X : ℕ, 1 ≤ X → ∀ S : Finset (Fin 10 → ℤ),
      (∀ p ∈ S, (∀ j, |p j| ≤ X) ∧ PluckerRel p ∧ eval (fun j => (p j : ℚ)) F = 0) →
      (S.card : ℝ) ≤ (K : ℝ) * (1 + (tauMax X : ℝ) ^ 2) *
        (X : ℝ) ^ (14 / 3 : ℝ) := by
  classical
  obtain ⟨B, hB0, hB⟩ := exists_minorChart_equations hF
  choose K hK using fun t b => chart_polynomial_count_tau (hB0 t b)
  let Ksum : ℕ := ∑ t : Fin 10, ∑ b : Bool, K t b
  refine ⟨1 + Ksum, ?_⟩
  intro X hX S hS
  let T := S.filter fun p => p ≠ 0
  have hT : ∀ p ∈ T, (∀ j, |p j| ≤ X) ∧ PluckerRel p ∧ p (piv p) ≠ 0 ∧
      (uVec p (piv p), vVec p (piv p)) ∈
        chartPolynomialZeros (B (piv p) (decide (0 < p (piv p)))) (p (piv p)).natAbs := by
    intro p hp
    obtain ⟨hpS, hp0⟩ := mem_filter.mp hp
    obtain ⟨hb, hpl, hzero⟩ := hS p hpS
    have ht : p (piv p) ≠ 0 := by
      intro hz
      apply hp0
      funext j
      have h := piv_max p j
      rw [hz, abs_zero] at h
      exact abs_nonpos_iff.mp h
    exact ⟨hb, hpl, ht, hB p hpl ht hzero⟩
  have hTcard : (T.card : ℝ) ≤ Ksum * (1 + (tauMax X : ℝ) ^ 2) *
      (X : ℝ) ^ (14 / 3 : ℝ) := by
    calc (T.card : ℝ)
        ≤ ∑ t : Fin 10, ∑ b : Bool, ∑ m ∈ Icc 1 X,
            ((chartPolynomialZeros (B t b) m).card : ℝ) :=
          minor_patterns_card_le_chart_sum B hT
      _ ≤ ∑ t : Fin 10, ∑ b : Bool,
          (K t b : ℝ) * (1 + (tauMax X : ℝ) ^ 2) * (X : ℝ) ^ (14 / 3 : ℝ) :=
          sum_le_sum fun t _ => sum_le_sum fun b _ => hK t b X hX
      _ = _ := by simp only [Ksum, Nat.cast_sum, sum_mul]
  have hScard : S.card ≤ 1 + T.card := by
    have hz : (S.filter fun p => p = 0).card ≤ 1 := by
      apply (card_le_card (s := S.filter fun p => p = 0) (t := {0}) ?_).trans
        (by simp)
      intro p hp
      rw [(mem_filter.mp hp).2]
      exact mem_singleton_self _
    have he := card_filter_add_card_filter_not (s := S) (p := fun p => p = 0)
    have hh := Nat.add_le_add_right hz (S.filter fun p => ¬ p = 0).card
    rw [he] at hh
    simpa only [T, ne_eq] using hh
  have hone : 1 ≤ (X : ℝ) ^ (14 / 3 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hX) (by norm_num)
  have hone' : 1 ≤ (1 + (tauMax X : ℝ) ^ 2) * (X : ℝ) ^ (14 / 3 : ℝ) := by
    nlinarith [sq_nonneg (tauMax X : ℝ)]
  have hScardR : (S.card : ℝ) ≤ 1 + (T.card : ℝ) := by exact_mod_cast hScard
  push_cast
  nlinarith

/-- The divisor-maximum coefficient is absorbed by an arbitrarily small power. -/
lemma tauMax_coeff_le_rpow : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ X : ℕ, 1 ≤ X →
    (1 + (tauMax X : ℝ) ^ 2) * (X : ℝ) ^ (14 / 3 : ℝ) ≤ C * (X : ℝ) ^ (14 / 3 + ε) := by
  intro ε hε
  have hslow : SlowGrowth (fun X => tauMax X ^ 2) := by
    simpa only [pow_one, one_mul] using (tauMax_slow 1 1).pow 2
  obtain ⟨C, hC, hτ⟩ := hslow ε hε
  refine ⟨1 + C, by positivity, fun X hX => ?_⟩
  have hXR : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hτX : (tauMax X : ℝ) ^ 2 ≤ C * (X : ℝ) ^ ε := by
    simpa only [Nat.cast_pow] using hτ X hX
  have hpow := Real.one_le_rpow (show (1 : ℝ) ≤ X by exact_mod_cast hX) hε.le
  have h1 : 1 + (tauMax X : ℝ) ^ 2 ≤ (1 + C) * (X : ℝ) ^ ε := by
    rw [add_mul, one_mul]
    linarith
  calc _ ≤ ((1 + C) * (X : ℝ) ^ ε) * (X : ℝ) ^ (14 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hXR.le _)
    _ = _ := by rw [Real.rpow_add hXR]; ring

/-- The `X^(14/3+ε)` form of `chart_polynomial_count_tau`: a fixed nonzero chart
polynomial has `O_ε(X^(14/3+ε))` zeros over the pivots `1 ≤ m ≤ X`, one-third of a
power below the `X^5` count of all patterns. -/
theorem chart_polynomial_count {B : HypersurfaceChartPolynomial} (hB : B ≠ 0) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ X : ℕ, 1 ≤ X →
      (∑ m ∈ Icc 1 X, ((chartPolynomialZeros B m).card : ℝ)) ≤
        C * (X : ℝ) ^ (14 / 3 + ε) := by
  obtain ⟨K, hK⟩ := chart_polynomial_count_tau hB
  intro ε hε
  obtain ⟨C, hC, hc⟩ := tauMax_coeff_le_rpow ε hε
  refine ⟨(K + 1) * C, by positivity, fun X hX => (hK X hX).trans ?_⟩
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul (by linarith) (hc X hX) (by positivity) (by positivity)

/-- The `X^(14/3+ε)` form of `hypersurface_pattern_count_tau`: a proper polynomial
condition `F = 0` holds on `O_{F,ε}(X^(14/3+ε))` integral Plücker vectors of height
at most `X`, counting non-primitive vectors and the zero vector. -/
theorem hypersurface_pattern_count {F : MvPolynomial (Fin 10) ℚ}
    (hF : ProperOnMinorCone F) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ X : ℕ, 1 ≤ X → ∀ S : Finset (Fin 10 → ℤ),
      (∀ p ∈ S, (∀ j, |p j| ≤ X) ∧ PluckerRel p ∧ eval (fun j => (p j : ℚ)) F = 0) →
      (S.card : ℝ) ≤ C * (X : ℝ) ^ (14 / 3 + ε) := by
  obtain ⟨K, hK⟩ := hypersurface_pattern_count_tau hF
  intro ε hε
  obtain ⟨C, hC, hc⟩ := tauMax_coeff_le_rpow ε hε
  refine ⟨(K + 1) * C, by positivity, fun X hX S hS => (hK X hX S hS).trans ?_⟩
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul (by linarith) (hc X hX) (by positivity) (by positivity)

end
end PierceLengthBound.FixedDividend
