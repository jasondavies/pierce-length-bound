module

public import AffineCurveCounting.HomogeneousLeadingCoefficient
public import AffineCurveCounting.HomogeneousEvaluationHeight

/-! The bounded leading-coefficient translation has a controlled height cost.
Its logarithmic coefficient-position loss is at most 14d². -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Real

def leadingPositionHeightFactor (d : ℕ) : ℝ :=
  ((d : ℝ) + 1) ^ (4 * (d + 1)) * ((d : ℝ) + 2) ^ 2 * (2 * (d : ℝ) + 1) ^ d

lemma leadingPositionHeightFactor_one_le (d : ℕ) : 1 ≤ leadingPositionHeightFactor d := by
  unfold leadingPositionHeightFactor
  apply one_le_mul_of_one_le_of_one_le
  · apply one_le_mul_of_one_le_of_one_le
    · exact one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
    · exact one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
  · exact one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith)

lemma leadingPositionHeightFactor_log_le {d : ℕ} (hd : 0 < d) :
    Real.log (leadingPositionHeightFactor d) ≤ 14 * (d : ℝ) ^ 2 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h₁ : Real.log ((d : ℝ) + 1) ≤ d := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < d + 1 by positivity)
    linarith
  have h₂ : Real.log ((d : ℝ) + 2) ≤ d + 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < d + 2 by positivity)
    linarith
  have h₃ : Real.log (2 * (d : ℝ) + 1) ≤ 2 * d := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * d + 1 by positivity)
    linarith
  unfold leadingPositionHeightFactor
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  calc
    _ ≤ 4 * ((d : ℝ) + 1) * d + 2 * ((d : ℝ) + 1) + d * (2 * d) := by gcongr
    _ ≤ _ := by nlinarith

/-- Control the transformed coefficients through interpolation of translated
grid values. No coefficient formula for the substitution is assumed. -/
theorem homogeneousTranslation_chart_coefficient_bound {d : ℕ}
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d)
    (a : Fin 2 → ℤ) (ha : ∀ j, 0 ≤ a j ∧ a j ≤ d)
    {L : ℝ} (hL : 0 ≤ L)
    (hcoeff : ∀ m, |(f.coeff m : ℝ)| ≤ ((d : ℝ) + 1) ^ (2 * (d + 1)) * L)
    (m : Fin 2 →₀ ℕ) :
    |((affineChart 2 (homogeneousTranslation ℤ a f)).coeff m : ℝ)| ≤
      leadingPositionHeightFactor d * L := by
  let K := ((d : ℝ) + 1) ^ (2 * (d + 1))
  let V := ((d : ℝ) + 2) ^ 2 * (K * L) * (2 * (d : ℝ) + 1) ^ d
  have heval (x y : ℕ) (hx : x ≤ d) (hy : y ≤ d) :
      |(eval ![(x : ℤ), (y : ℤ)] (affineChart 2 (homogeneousTranslation ℤ a f)) : ℝ)| ≤ V := by
    let z : Fin 2 → ℤ := ![(x : ℤ), (y : ℤ)]
    have hz : ∀ j, 0 ≤ z j ∧ z j ≤ d := by
      intro j
      fin_cases j
      · change 0 ≤ (x : ℤ) ∧ (x : ℤ) ≤ d
        exact ⟨by positivity, by exact_mod_cast hx⟩
      · change 0 ≤ (y : ℤ) ∧ (y : ℤ) ≤ d
        exact ⟨by positivity, by exact_mod_cast hy⟩
    have hbox : ∀ j, |((Fin.cons 1 (z + a) : Fin 3 → ℤ) j : ℝ)| ≤ 2 * d + 1 := by
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp only [Fin.cons_zero, Int.cast_one, abs_one]
        have := Nat.cast_nonneg (α := ℝ) d
        linarith
      · simp only [Fin.cons_succ, Pi.add_apply, Int.cast_add]
        have hz0 : (0 : ℝ) ≤ z k := by exact_mod_cast (hz k).1
        have ha0 : (0 : ℝ) ≤ a k := by exact_mod_cast (ha k).1
        have hzd : (z k : ℝ) ≤ d := by exact_mod_cast (hz k).2
        have had : (a k : ℝ) ≤ d := by exact_mod_cast (ha k).2
        rw [abs_of_nonneg (by linarith)]
        linarith
    rw [affineChart_eval, homogeneousTranslation_eval_chart]
    have h := homogeneous_integer_evaluation_bound f hf (show 0 ≤ K * L by dsimp [K]; positivity)
      (show (1 : ℝ) ≤ 2 * d + 1 by have := Nat.cast_nonneg (α := ℝ) d; linarith)
      hcoeff (Fin.cons 1 (z + a)) hbox
    apply h.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (ternary_homogeneous_dimension_le_square d) (by positivity))
      (by positivity)
  have h := integer_plane_coefficient_bound_of_grid (affineChart 2 (homogeneousTranslation ℤ a f))
    ((affineChart_totalDegree_le _).trans (homogeneousTranslation_homogeneous a hf).totalDegree_le)
    (show 0 ≤ V by dsimp [V, K]; positivity) heval m
  convert h using 1
  dsimp only [leadingPositionHeightFactor, V, K]
  rw [show 4 * (d + 1) = 2 * (d + 1) + 2 * (d + 1) by omega, pow_add]
  ring

/-- An actual bounded integer translation supplies the leading-position
hypothesis with absolute constant 14, and a coefficient height at least one. -/
theorem exists_translated_coefficient_position {d : ℕ} (hd : 0 < d)
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    ∃ (a : Fin 2 → ℤ) (H : ℝ), (∀ j, 0 ≤ a j ∧ a j ≤ d) ∧ 1 ≤ H ∧
      (∀ m, |((affineChart 2 (homogeneousTranslation ℤ a f)).coeff m : ℝ)| ≤ H) ∧
      Real.log |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)| ≤ Real.log H ∧
      Real.log H ≤ Real.log |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)| +
        14 * (d : ℝ) ^ 2 := by
  obtain ⟨a, ha, hne, hcoeff⟩ := exists_bounded_leading_coefficient_translation f hf hf0
  let L := |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a f) : ℤ) : ℝ)|
  have hL : 1 ≤ L := by
    dsimp only [L]
    exact_mod_cast Int.one_le_abs hne
  have hP := leadingPositionHeightFactor_one_le d
  have hpos : 0 < leadingPositionHeightFactor d := by linarith
  have hLpos : 0 < L := by linarith
  refine ⟨a, leadingPositionHeightFactor d * L, ha, one_le_mul_of_one_le_of_one_le hP hL,
    homogeneousTranslation_chart_coefficient_bound f hf a ha hLpos.le hcoeff, ?_, ?_⟩
  · apply Real.log_le_log hLpos
    nlinarith
  · rw [Real.log_mul hpos.ne' hLpos.ne']
    have h := leadingPositionHeightFactor_log_le hd
    linarith

end
end AffineCurveCounting
