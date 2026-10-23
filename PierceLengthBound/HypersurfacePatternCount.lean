/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.HypersurfacePatternCover
public import PierceLengthBound.HypersurfacePatternCountChartBound

/-! Assemble the twenty signed charts into a count of integral Plücker vectors. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open MvPolynomial Finset
noncomputable section

/-- The finite-chart assembly, including the zero vector and every common factor. -/
theorem hypersurface_pattern_count_of_chart_counts
    (hchart : ∀ B : HypersurfaceChartPolynomial, B ≠ 0 →
      ∀ ε > (0 : ℝ), ∃ C > 0, ∀ X : ℕ, 1 ≤ X →
        (∑ m ∈ Icc 1 X, ((chartPolynomialZeros B m).card : ℝ)) ≤
          C * (X : ℝ) ^ (14 / 3 + ε))
    {F : MvPolynomial (Fin 10) ℚ} (hF : ProperOnMinorCone F) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ X : ℕ, 1 ≤ X → ∀ S : Finset (Fin 10 → ℤ),
      (∀ p ∈ S, (∀ j, |p j| ≤ X) ∧ PluckerRel p ∧ eval (fun j => (p j : ℚ)) F = 0) →
      (S.card : ℝ) ≤ C * (X : ℝ) ^ (14 / 3 + ε) := by
  classical
  intro ε hε
  obtain ⟨B, hB0, hB⟩ := exists_minorChart_equations hF
  choose C hCpos hCbound using fun t b => hchart (B t b) (hB0 t b) ε hε
  let Csum : ℝ := ∑ t : Fin 10, ∑ b : Bool, C t b
  have hCsum : 0 ≤ Csum := sum_nonneg fun t _ => sum_nonneg fun b _ => (hCpos t b).le
  refine ⟨1 + Csum, by positivity, ?_⟩
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
  have hTcard : (T.card : ℝ) ≤ Csum * (X : ℝ) ^ (14 / 3 + ε) := by
    calc (T.card : ℝ)
        ≤ ∑ t : Fin 10, ∑ b : Bool, ∑ m ∈ Icc 1 X,
            ((chartPolynomialZeros (B t b) m).card : ℝ) :=
          minor_patterns_card_le_chart_sum B hT
      _ ≤ ∑ t : Fin 10, ∑ b : Bool, C t b * (X : ℝ) ^ (14 / 3 + ε) :=
          sum_le_sum fun t _ => sum_le_sum fun b _ => hCbound t b X hX
      _ = Csum * (X : ℝ) ^ (14 / 3 + ε) := by simp only [Csum, sum_mul]
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
  have hone : 1 ≤ (X : ℝ) ^ (14 / 3 + ε) :=
    Real.one_le_rpow (by exact_mod_cast hX) (by linarith)
  calc (S.card : ℝ) ≤ 1 + (T.card : ℝ) := by exact_mod_cast hScard
       _ ≤ (X : ℝ) ^ (14 / 3 + ε) + Csum * (X : ℝ) ^ (14 / 3 + ε) :=
         add_le_add hone hTcard
       _ = (1 + Csum) * (X : ℝ) ^ (14 / 3 + ε) := by ring

/-- A proper fixed polynomial condition cuts the height-X integral Plücker cone in
`O(F,ε)(X^(14/3+ε))` vectors. All signs and common factors, and the zero vector, are included. -/
theorem hypersurface_pattern_count {F : MvPolynomial (Fin 10) ℚ}
    (hF : ProperOnMinorCone F) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ X : ℕ, 1 ≤ X → ∀ S : Finset (Fin 10 → ℤ),
      (∀ p ∈ S, (∀ j, |p j| ≤ X) ∧ PluckerRel p ∧ eval (fun j => (p j : ℚ)) F = 0) →
      (S.card : ℝ) ≤ C * (X : ℝ) ^ (14 / 3 + ε) := by
  apply hypersurface_pattern_count_of_chart_counts ?_ hF
  intro B hB
  simpa only [chartPolynomialZeros] using chart_polynomial_count hB

end
end PierceLengthBound.FixedDividend
