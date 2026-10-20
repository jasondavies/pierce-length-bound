/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendConicTernaryNumerators
public import PierceLengthBound.FixedDividendRationalOrbit

/-! Polynomial-height common denominators from the actual seven minor labels. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- Six common numerators and their common denominator for the two adjacent
rational patterns. -/
def conicPatternCommon (t : Fin 7 → ℤ) : Fin 7 → ℤ :=
  ![t 1 * t 1, t 3 * t 1, t 4 * t 1, t 2 * t 0,
    t 5 * t 0, t 6 * t 0, t 0 * t 1]

def conicPatternTernary (t : Fin 7 → ℤ) : Fin 6 → ℤ :=
  let w := conicPatternCommon t
  ternaryNumerators (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6)

lemma conicPatternCommon_height {t : Fin 7 → ℤ} {X : ℤ}
    (ht : ∀ j, |t j| ≤ X) : ∀ j, |conicPatternCommon t j| ≤ X ^ 2 := by
  have hmul (i j : Fin 7) : |t i * t j| ≤ X ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (ht i) (ht j) (abs_nonneg _) ((abs_nonneg _).trans (ht i))
  intro j
  fin_cases j <;> exact hmul _ _

/-- Actual pattern height `X` gives ternary numerator and common denominator
height at most `12X⁴`. -/
theorem conicPatternTernary_height {t : Fin 7 → ℤ} {X : ℤ}
    (hX : 1 ≤ X) (ht : ∀ j, |t j| ≤ X) :
    |conicPatternCommon t 6| ≤ 12 * X ^ 4 ∧
      ∀ j, |conicPatternTernary t j| ≤ 12 * X ^ 4 := by
  have hw := conicPatternCommon_height ht
  have hX2 : 1 ≤ X ^ 2 := by nlinarith
  have hp := ternaryNumerators_height hX2 (hw 0) (hw 1) (hw 2)
    (hw 3) (hw 4) (hw 5) (hw 6)
  constructor
  · have hh := hw 6
    nlinarith [sq_nonneg (X ^ 2 - 1)]
  · simpa only [conicPatternTernary, ← pow_mul, Nat.reduceMul] using hp

lemma conicPatternCommon_ratios (t : Fin 7 → ℤ) (h0 : t 0 ≠ 0) (h1 : t 1 ≠ 0) :
    let w := conicPatternCommon t
    ![(w 0 : ℚ) / w 6, (w 1 : ℚ) / w 6, (w 2 : ℚ) / w 6,
      (w 3 : ℚ) / w 6, (w 4 : ℚ) / w 6, (w 5 : ℚ) / w 6] =
    ![(t 1 : ℚ) / t 0, (t 3 : ℚ) / t 0, (t 4 : ℚ) / t 0,
      (t 2 : ℚ) / t 1, (t 5 : ℚ) / t 1, (t 6 : ℚ) / t 1] := by
  have h0' : (t 0 : ℚ) ≠ 0 := by exact_mod_cast h0
  have h1' : (t 1 : ℚ) ≠ 0 := by exact_mod_cast h1
  ext j
  fin_cases j <;> simp [conicPatternCommon] <;> field_simp

/-- The common rational coefficients are precisely the actual orbit patterns. -/
lemma conicPatternCommon_orbit {a b i : ℕ} (hba : b < a) (hi : i + 6 < P a b) :
    let w := conicPatternCommon (theta a b i)
    ![(w 0 : ℚ) / w 6, (w 1 : ℚ) / w 6, (w 2 : ℚ) / w 6,
      (w 3 : ℚ) / w 6, (w 4 : ℚ) / w 6, (w 5 : ℚ) / w 6] =
    ![patternRhoQ a b i, patternUQ a b i, patternVQ a b i,
      patternRhoQ a b (i + 1), patternUQ a b (i + 1), patternVQ a b (i + 1)] := by
  have h0 : theta a b i 0 ≠ 0 := by
    simpa only [theta, Matrix.cons_val_zero] using
      (ne_of_gt (Lz_pos hba (by omega : i + 5 < P a b)))
  have h1 : theta a b i 1 ≠ 0 := by
    simpa only [theta, Matrix.cons_val_one, Matrix.cons_val_zero] using
      (ne_of_gt (Lz_pos hba (by omega : i + 1 + 5 < P a b)))
  simpa [theta, patternRhoQ, patternUQ, patternVQ, Nat.add_assoc] using
    conicPatternCommon_ratios (theta a b i) h0 h1

end
end PierceLengthBound.FixedDividend
