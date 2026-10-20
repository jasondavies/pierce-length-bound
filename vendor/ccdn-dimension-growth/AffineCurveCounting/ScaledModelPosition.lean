module

public import AffineCurveCounting.LeadingPositionHeight
public import AffineCurveCounting.ScaledHomogenization
public import AffineCurveCounting.ScaledHeightElimination

/-! Positioning a scaled homogeneous model while retaining a coefficient bound
for the original affine equation and the full scaling gain in its height. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Real

lemma leadingPositionHeightFactor_interpolation_le (d : ℕ) :
    ((d : ℝ) + 1) ^ (2 * (d + 1)) ≤ leadingPositionHeightFactor d := by
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hb : (1 : ℝ) ≤ d + 1 := by linarith
  have h₁ : 1 ≤ ((d : ℝ) + 2) ^ 2 := one_le_pow₀ (by linarith)
  have h₂ : 1 ≤ (2 * (d : ℝ) + 1) ^ d := one_le_pow₀ (by linarith)
  have hp := pow_le_pow_right₀ hb (show 2 * (d + 1) ≤ 4 * (d + 1) by omega)
  unfold leadingPositionHeightFactor
  nlinarith [show 0 ≤ ((d : ℝ) + 1) ^ (4 * (d + 1)) by positivity,
    mul_le_mul_of_nonneg_left h₁ (show 0 ≤ ((d : ℝ) + 1) ^ (4 * (d + 1)) by positivity)]

/-- The chosen height bounds both the original homogeneous coefficients and
the translated chart coefficients, with the same absolute position loss. -/
theorem exists_translated_model_position {d : ℕ} (hd : 0 < d)
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    ∃ (a : Fin 2 → ℤ) (H : ℝ), (∀ j, 0 ≤ a j ∧ a j ≤ d) ∧ 1 ≤ H ∧
      (∀ m, |(f.coeff m : ℝ)| ≤ H) ∧
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
    ?_, homogeneousTranslation_chart_coefficient_bound f hf a ha hLpos.le hcoeff, ?_, ?_⟩
  · intro m
    exact (hcoeff m).trans (mul_le_mul_of_nonneg_right
      (leadingPositionHeightFactor_interpolation_le d) hLpos.le)
  · apply Real.log_le_log hLpos
    nlinarith
  · rw [Real.log_mul hpos.ne' hLpos.ne']
    have h := leadingPositionHeightFactor_log_le hd
    linarith

/-- The model height is at least h^d and also bounds every original affine
coefficient, even after leading-coefficient positioning of the scaled model. -/
theorem exists_scaled_model_position (f : MvPolynomial (Fin 2) ℤ)
    (hf0 : f ≠ 0) (hd : 0 < f.totalDegree) {h : ℤ} (hh : 1 ≤ h) :
    ∃ (a : Fin 2 → ℤ) (H : ℝ), (∀ j, 0 ≤ a j ∧ a j ≤ f.totalDegree) ∧
      1 ≤ H ∧ (h : ℝ) ^ f.totalDegree ≤ H ∧
      (∀ m, |(f.coeff m : ℝ)| ≤ H) ∧
      Real.log |((MonomialOrder.lex.leadingCoeff
        (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree h f)) : ℤ) : ℝ)| ≤ Real.log H ∧
      Real.log H ≤ Real.log |((MonomialOrder.lex.leadingCoeff
        (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree h f)) : ℤ) : ℝ)| +
        14 * (f.totalDegree : ℝ) ^ 2 := by
  have hh0 : h ≠ 0 := by omega
  obtain ⟨a, H, ha, hH, hc, _, hlo, hhi⟩ := exists_translated_model_position hd
    (scaledHomogenize f.totalDegree h f) (scaledHomogenize_homogeneous _ _ le_rfl)
    (scaledHomogenize_ne_zero _ hh0 hf0)
  obtain ⟨m, _, hm⟩ := exists_scaledHomogenize_top_coefficient f hf0 hh
  exact ⟨a, H, ha, hH, hm.trans (hc _),
    fun m => (scaledHomogenize_integer_coefficient_lower _ hh f m).trans (hc _), hlo, hhi⟩

/-- The exact height saving obtained from a scaling factor h. -/
theorem scaled_positioned_height_ratio_le {d : ℕ} (hd : 0 < d) {h H L : ℝ}
    (hh : 1 ≤ h) (hH : h ^ d ≤ H) (hL : 0 < L)
    (hposition : Real.log H ≤ Real.log L + 14 * (d : ℝ) ^ 2) :
    (1 + Real.log H / (d : ℝ) ^ 2) / L ^ (1 / (d : ℝ) ^ 2) ≤
      Real.exp 14 * ((1 + Real.log h / d) / h ^ (1 / (d : ℝ))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hh0 : 0 < h := by linarith
  have hp : (h ^ d) ^ (1 / (d : ℝ) ^ 2) = h ^ (1 / (d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh0.le]
    congr 1
    field_simp
  have he : Real.log (h ^ d) / (d : ℝ) ^ 2 = Real.log h / d := by
    rw [Real.log_pow]
    field_simp
  have ht := positioned_height_ratio_le hdR (one_le_pow₀ hh) hH hL hposition
  rw [hp, he] at ht
  exact ht

end
end AffineCurveCounting
