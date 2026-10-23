/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftIntegerInputs
public import PierceLengthBound.ConicCommonDenominator

/-! Uniform integer coefficient bounds for the actual cofactor lift after the
proved bounded quadratic parametrization. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

/-- The degree and height constants depend only on the fixed cofactor formula,
not on the dividend, minor pattern, plane, or conic. -/
theorem orbitLift_integer_representation_height :
    ∃ D C e : ℕ, 1 ≤ C ∧ ∀ {a b i M : ℕ}, b < a → i + 7 < P a b → 1 ≤ M →
      (∀ j, |theta a b i j| ≤ M) → a ≤ M →
      ∀ (σ : Fin 3 ≃ Fin 3) (E : ℤ) (F : Fin 3 → Polynomial ℤ),
      E ≠ 0 → |E| ≤ M → (∀ j, (F j).natDegree ≤ 2) →
      (∀ j n, |(F j).coeff n| ≤ M) →
      ∃ A B : Polynomial ℤ,
        A.natDegree ≤ D ∧ B.natDegree ≤ D ∧
        (∀ n, |A.coeff n| ≤ (C * M ^ e : ℕ)) ∧
        (∀ n, |B.coeff n| ≤ (C * M ^ e : ℕ)) ∧
        orbitLiftParameter a b i (normalizedParameter σ E F) =
          algebraMap (Polynomial ℚ) (RatFunc ℚ) (A.map (Int.castRingHom ℚ)) /
            algebraMap (Polynomial ℚ) (RatFunc ℚ) (B.map (Int.castRingHom ℚ)) := by
  obtain ⟨D, C, e, hC, hrep⟩ := fixed_rational_expression_integer_representation
    universalLiftNumerator universalLiftDenominator
  refine ⟨D, C, 4 * e, hC, ?_⟩
  intro a b i M hba hi hM hθ ha σ E F hE hEb hFd hFc
  obtain ⟨hB, heval⟩ := actualLiftInput_numerators_spec hba hi σ hE F
  have haZ : |(a : ℤ)| ≤ M := by simpa using (show (a : ℤ) ≤ M by exact_mod_cast ha)
  obtain ⟨A, B, hAd, hBd, hAc, hBc, hval⟩ := hrep (M ^ 4) (Nat.one_le_pow _ _ hM)
    (liftInputDenominator (theta a b i) E) (liftInputNumerators (theta a b i) a E σ F)
    hB (liftInputDenominator_height hM hθ hEb)
    (liftInputNumerators_degree _ _ _ σ F hFd)
    (liftInputNumerators_height hM hθ haZ hEb σ F hFc)
  rw [heval, universalLift_orbit] at hval
  refine ⟨A, B, hAd, hBd, ?_, ?_, hval⟩
  · simpa only [← pow_mul] using hAc
  · simpa only [← pow_mul] using hBc

/-- A single explicit polynomial bound contains every actual input height
provided by the bounded conic parameter theorem. -/
def conicInputHeight (a X L : ℕ) : ℕ :=
  1 + a + X + 33 * L * (10 * (12 * X ^ 4) ^ 2 * L ^ 2) ^ 3

/-- Specializing the universal bound needs only the coefficient bounds already
proved for the actual bounded integer parametrization. -/
theorem orbitLift_bounded_parameter_height :
    ∃ D C e : ℕ, 1 ≤ C ∧ ∀ {a b i X L : ℕ}, b < a → i + 7 < P a b →
      (∀ j, |theta a b i j| ≤ X) →
      ∀ (σ : Fin 3 ≃ Fin 3) (E : ℤ) (F : Fin 3 → Polynomial ℤ),
      E ≠ 0 → |E| ≤ 12 * (L : ℤ) * (10 * (12 * X ^ 4) ^ 2 * L ^ 2) ^ 3 →
      (∀ j, (F j).natDegree ≤ 2) →
      (∀ j n, |(F j).coeff n| ≤ 33 * (L : ℤ) * (10 * (12 * X ^ 4) ^ 2 * L ^ 2) ^ 3) →
      ∃ A B : Polynomial ℤ,
        A.natDegree ≤ D ∧ B.natDegree ≤ D ∧
        (∀ n, |A.coeff n| ≤ (C * conicInputHeight a X L ^ e : ℕ)) ∧
        (∀ n, |B.coeff n| ≤ (C * conicInputHeight a X L ^ e : ℕ)) ∧
        orbitLiftParameter a b i (normalizedParameter σ E F) =
          algebraMap (Polynomial ℚ) (RatFunc ℚ) (A.map (Int.castRingHom ℚ)) /
            algebraMap (Polynomial ℚ) (RatFunc ℚ) (B.map (Int.castRingHom ℚ)) := by
  obtain ⟨D, C, e, hC, hrep⟩ := orbitLift_integer_representation_height
  refine ⟨D, C, e, hC, ?_⟩
  intro a b i X L hba hi hθ σ E F hE hEb hFd hFc
  have hM : 1 ≤ conicInputHeight a X L := by unfold conicInputHeight; omega
  have hXM : X ≤ conicInputHeight a X L := by unfold conicInputHeight; omega
  have haM : a ≤ conicInputHeight a X L := by unfold conicInputHeight; omega
  have hcoef : (33 * L * (10 * (12 * X ^ 4) ^ 2 * L ^ 2) ^ 3 : ℕ) ≤
      conicInputHeight a X L := by unfold conicInputHeight; omega
  have hcoefZ : 33 * (L : ℤ) * (10 * (12 * X ^ 4) ^ 2 * L ^ 2) ^ 3 ≤
      conicInputHeight a X L := by exact_mod_cast hcoef
  have hEb' : |E| ≤ conicInputHeight a X L := by
    apply hEb.trans
    have hpos : (0 : ℤ) ≤ L * (10 * (12 * X ^ 4) ^ 2 * L ^ 2) ^ 3 := by positivity
    nlinarith only [hcoefZ, hpos]
  exact hrep hba hi hM (fun j => (hθ j).trans (by exact_mod_cast hXM)) haM σ E F hE hEb'
    hFd (fun j n => (hFc j n).trans hcoefZ)

end
end PierceLengthBound.FixedDividend
