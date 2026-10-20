/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendPolynomialSubstitution

/-! Rational polynomial coordinates from the checked bounded integer parameters. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

/-- Restore the original node order and divide by the common denominator. -/
def normalizedParameter (σ : Fin 3 ≃ Fin 3) (E : ℤ) (F : Fin 3 → Polynomial ℤ) :
    Fin 3 → Polynomial ℚ := fun j =>
  C (E : ℚ)⁻¹ * (F (σ.symm j)).map (Int.castRingHom ℚ)

lemma normalizedParameter_degree (σ : Fin 3 ≃ Fin 3) (E : ℤ)
    (F : Fin 3 → Polynomial ℤ) (hF : ∀ j, (F j).natDegree ≤ 2) :
    ∀ j, (normalizedParameter σ E F j).natDegree ≤ 2 := by
  intro j
  exact (natDegree_C_mul_le _ _).trans ((natDegree_map_le).trans (hF _))

lemma normalizedParameter_first_coeff (σ : Fin 3 ≃ Fin 3) (hσ : σ 1 = 0)
    {E : ℤ} (hE : E ≠ 0) (F : Fin 3 → Polynomial ℤ) (hF : (F 1).coeff 2 ≠ 0) :
    (normalizedParameter σ E F 0).coeff 2 ≠ 0 := by
  have hs : σ.symm 0 = 1 := (σ.symm_apply_eq).mpr hσ.symm
  simp only [normalizedParameter, hs, coeff_C_mul, coeff_map]
  apply mul_ne_zero (inv_ne_zero (by exact_mod_cast hE))
  change ((F 1).coeff 2 : ℚ) ≠ 0
  exact_mod_cast hF

/-- The rational polynomial coordinates evaluate to the actual integer point. -/
lemma normalizedParameter_eval (σ : Fin 3 ≃ Fin 3) {E : ℤ} (hE : E ≠ 0)
    (F : Fin 3 → Polynomial ℤ) (z : Fin 3 → ℤ) (t : ℤ)
    (he : ∀ j, E * z (σ j) = (F j).eval t) :
    ∀ j, (normalizedParameter σ E F j).eval (t : ℚ) = (z j : ℚ) := by
  have hEq : (E : ℚ) ≠ 0 := by exact_mod_cast hE
  intro j
  have hh := congrArg (Int.castRingHom ℚ) (he (σ.symm j))
  simp only [map_mul, Equiv.apply_symm_apply] at hh
  rw [normalizedParameter, eval_mul, eval_C]
  change (E : ℚ)⁻¹ * ((F (σ.symm j)).map (Int.castRingHom ℚ)).eval
    ((Int.castRingHom ℚ) t) = _
  rw [eval_map_apply]
  rw [← hh]
  simp only [Int.coe_castRingHom]
  field_simp

end
end PierceLengthBound.FixedDividend
