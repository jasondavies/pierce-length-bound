/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftRetainedIdentities
public import PierceLengthBound.JointLiftCurvatureNonvanishing

/-! The polynomial graph coordinates agree with the rational curvature
formulas in every field where their common denominator is nonzero. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

theorem jointLift_field_coordinates {F : Type*} [Field F]
    (φ : MvPolynomial (Fin 3) ℚ →+* F)
    (P Q A J : MvPolynomial (Fin 3) ℚ) (k : Fin 5 → MvPolynomial (Fin 3) ℚ)
    (hD : φ (jointLiftDenominator Q k) ≠ 0) :
    let B0 := rawHankelThree (φ (k 0)) (φ (k 1)) (φ (k 2))
    let B1 := rawHankelThree (φ (k 1)) (φ (k 2)) (φ (k 3))
    let E0 := φ P / φ Q
    let E12 := (B1 * E0 - φ A * φ (k 1)) / B0
    (fun j => φ (jointLiftNumerators P Q A J k j) / φ (jointLiftDenominator Q k)) =
      ![E12, -((φ (k 0) * E12 + φ (k 2) * E0) / φ (k 1)), E0, φ J] := by
  simp only [jointLiftDenominator, map_mul, map_rawHankelThree] at hD
  obtain ⟨hQB, hk⟩ := mul_ne_zero_iff.mp hD
  obtain ⟨hQ, hB⟩ := mul_ne_zero_iff.mp hQB
  dsimp only
  ext j
  fin_cases j <;>
    simp only [jointLiftNumerators, jointLiftDenominator, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons,
      map_mul, map_add, map_sub, map_neg, map_rawHankelThree]
  all_goals field_simp

/-- The curvature identity survives the passage from common-denominator
polynomial coordinates to rational functions in the component field. -/
theorem jointLift_field_dot_row {F : Type*} [Field F]
    (φ : MvPolynomial (Fin 3) ℚ →+* F)
    (P Q A J : MvPolynomial (Fin 3) ℚ) (k : Fin 5 → MvPolynomial (Fin 3) ℚ)
    (hD : φ (jointLiftDenominator Q k) ≠ 0) :
    ∑ j : Fin 3, (φ (jointLiftNumerators P Q A J k j.castSucc) /
      φ (jointLiftDenominator Q k)) * φ (curvatureRow k j) = φ A := by
  have he := congrArg φ (jointLiftNumerators_dot_row P Q A J k)
  simp only [map_sum, map_mul] at he
  calc _ = (∑ j : Fin 3, φ (jointLiftNumerators P Q A J k j.castSucc) *
        φ (curvatureRow k j)) / φ (jointLiftDenominator Q k) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = φ A := by rw [he, mul_div_cancel_right₀ _ hD]

end
end PierceLengthBound.FixedDividend
