/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftUniversalExpression
public import PierceLengthBound.FixedDividendConicPolynomialIdentities

/-! The actual minor ratios and bounded integer conic parameter have a common
integer denominator with polynomially bounded numerator coefficients. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

def liftInputDenominator (θ : Fin 7 → ℤ) (E : ℤ) : ℤ := θ 0 * θ 1 * E

def liftInputNumerators (θ : Fin 7 → ℤ) (a E : ℤ)
    (σ : Fin 3 ≃ Fin 3) (F : Fin 3 → Polynomial ℤ) : Fin 10 → Polynomial ℤ :=
  ![C (θ 1 * θ 1 * E), C (θ 3 * θ 1 * E), C (θ 4 * θ 1 * E),
    C (θ 2 * θ 0 * E), C (θ 5 * θ 0 * E), C (θ 6 * θ 0 * E),
    C (θ 0 * θ 1) * F (σ.symm 0), C (θ 0 * θ 1) * F (σ.symm 1),
    C (θ 0 * θ 1) * F (σ.symm 2), C (a * θ 0 * θ 1 * E)]

lemma liftInputNumerators_degree (θ : Fin 7 → ℤ) (a E : ℤ)
    (σ : Fin 3 ≃ Fin 3) (F : Fin 3 → Polynomial ℤ)
    (hF : ∀ j, (F j).natDegree ≤ 2) (j : Fin 10) :
    (liftInputNumerators θ a E σ F j).natDegree ≤ 2 := by
  fin_cases j <;> simp only [liftInputNumerators, Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals first
  | exact (natDegree_C_mul_le _ _).trans (hF _)
  | exact (natDegree_C _).le.trans (by omega)

lemma liftInputDenominator_height {θ : Fin 7 → ℤ} {E : ℤ} {M : ℕ}
    (hM : 1 ≤ M) (hθ : ∀ j, |θ j| ≤ M) (hE : |E| ≤ M) :
    |liftInputDenominator θ E| ≤ (M ^ 4 : ℕ) := by
  have hm : (1 : ℤ) ≤ M := by exact_mod_cast hM
  have h := mul_le_mul (mul_le_mul (hθ 0) (hθ 1) (abs_nonneg _) (Nat.cast_nonneg _))
    hE (abs_nonneg _) (by positivity : (0 : ℤ) ≤ (M : ℤ) * M)
  simp only [liftInputDenominator, abs_mul]
  have hp := pow_le_pow_right₀ hm (by decide : 3 ≤ 4)
  push_cast
  nlinarith only [h, hp]

lemma liftInputNumerators_height {θ : Fin 7 → ℤ} {a E : ℤ} {M : ℕ}
    (hM : 1 ≤ M) (hθ : ∀ j, |θ j| ≤ M) (ha : |a| ≤ M) (hE : |E| ≤ M)
    (σ : Fin 3 ≃ Fin 3) (F : Fin 3 → Polynomial ℤ)
    (hF : ∀ j k, |(F j).coeff k| ≤ M) :
    ∀ j k, |(liftInputNumerators θ a E σ F j).coeff k| ≤ (M ^ 4 : ℕ) := by
  have hm : (1 : ℤ) ≤ M := by exact_mod_cast hM
  have h3 {x y z : ℤ} (hx : |x| ≤ M) (hy : |y| ≤ M) (hz : |z| ≤ M) :
      |x * y * z| ≤ (M ^ 4 : ℕ) := by
    rw [abs_mul, abs_mul]
    have h := mul_le_mul (mul_le_mul hx hy (abs_nonneg _) (Nat.cast_nonneg _))
      hz (abs_nonneg _) (by positivity : (0 : ℤ) ≤ (M : ℤ) * M)
    have hp := pow_le_pow_right₀ hm (by decide : 3 ≤ 4)
    push_cast
    nlinarith only [h, hp]
  have h4 : |a * θ 0 * θ 1 * E| ≤ (M ^ 4 : ℕ) := by
    rw [abs_mul, abs_mul, abs_mul]
    have h := mul_le_mul
      (mul_le_mul (mul_le_mul ha (hθ 0) (abs_nonneg _) (Nat.cast_nonneg _))
        (hθ 1) (abs_nonneg _) (by positivity : (0 : ℤ) ≤ (M : ℤ) * M))
      hE (abs_nonneg _) (by positivity : (0 : ℤ) ≤ (M : ℤ) * M * M)
    push_cast
    nlinarith only [h]
  have hc (x : ℤ) (hx : |x| ≤ (M ^ 4 : ℕ)) (k : ℕ) :
      |(C x).coeff k| ≤ (M ^ 4 : ℕ) := by
    rw [coeff_C]
    split_ifs
    · exact hx
    · simp
  have hp (j : Fin 3) (k : ℕ) : |(C (θ 0 * θ 1) * F j).coeff k| ≤ (M ^ 4 : ℕ) := by
    rw [coeff_C_mul]
    exact h3 (hθ 0) (hθ 1) (hF j k)
  intro j k
  fin_cases j
  · exact hc _ (h3 (hθ 1) (hθ 1) hE) k
  · exact hc _ (h3 (hθ 3) (hθ 1) hE) k
  · exact hc _ (h3 (hθ 4) (hθ 1) hE) k
  · exact hc _ (h3 (hθ 2) (hθ 0) hE) k
  · exact hc _ (h3 (hθ 5) (hθ 0) hE) k
  · exact hc _ (h3 (hθ 6) (hθ 0) hE) k
  · exact hp (σ.symm 0) k
  · exact hp (σ.symm 1) k
  · exact hp (σ.symm 2) k
  · exact hc _ h4 k

/-- Exact denominator-cleared inputs for the actual bounded conic parameter. -/
theorem actualLiftInput_numerators_spec {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (σ : Fin 3 ≃ Fin 3) {E : ℤ} (hE : E ≠ 0) (F : Fin 3 → Polynomial ℤ) :
    liftInputDenominator (theta a b i) E ≠ 0 ∧
    (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ)
        ((liftInputNumerators (theta a b i) a E σ F j).map (Int.castRingHom ℚ)) /
      (liftInputDenominator (theta a b i) E : RatFunc ℚ)) =
        orbitLiftInputs a b i (normalizedParameter σ E F) := by
  have h0 : Lz a b i ≠ 0 := by have := Lz_pos hba (by omega : i + 5 < P a b); omega
  have h1 : Lz a b (i + 1) ≠ 0 := by
    have := Lz_pos hba (by omega : i + 1 + 5 < P a b); omega
  have h0' : (Lz a b i : RatFunc ℚ) ≠ 0 := by exact_mod_cast h0
  have h1' : (Lz a b (i + 1) : RatFunc ℚ) ≠ 0 := by exact_mod_cast h1
  have hE' : (E : RatFunc ℚ) ≠ 0 := by exact_mod_cast hE
  constructor
  · exact mul_ne_zero (mul_ne_zero h0 h1) hE
  · funext j
    fin_cases j <;>
      simp [liftInputNumerators, liftInputDenominator, orbitLiftInputs,
        Matrix.cons_val, theta,
        patternRhoQ, patternUQ, patternVQ, normalizedParameter,
        Polynomial.map_mul, map_mul, RatFunc.algebraMap_C,
        Int.cast_mul, map_div₀, map_inv₀,
        map_intCast, map_natCast, Nat.add_assoc, Nat.reduceAdd]
    all_goals field_simp

end
end PierceLengthBound.FixedDividend
