/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ConicSubstitutionHeight
public import Mathlib.FieldTheory.RatFunc.Basic

/-! Uniform clearing of a common denominator in any fixed integer polynomial
expression. The cleared expression is itself a fixed integer polynomial. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- Clearing a common denominator does not depend on the parameter values.
The new variable `none` denotes that common denominator. -/
theorem fixed_polynomial_clear_denominator {σ K : Type*} [Field K]
    (f : MvPolynomial σ ℤ) :
    ∃ d : ℕ, ∃ F : MvPolynomial (Option σ) ℤ,
      ∀ (B : K), B ≠ 0 → ∀ v : σ → K,
        MvPolynomial.eval₂ (Int.castRingHom K) (fun j => v j / B) f * B ^ d =
          MvPolynomial.eval₂ (Int.castRingHom K) (fun j => j.elim B v) F := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, C a, ?_⟩
    intro B hB v
    simp only [eval₂_C, pow_zero, mul_one]
  | add f g ihf ihg =>
    obtain ⟨d, F, hF⟩ := ihf
    obtain ⟨e, G, hG⟩ := ihg
    refine ⟨d + e, F * X none ^ e + G * X none ^ d, ?_⟩
    intro B hB v
    simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, Option.elim_none]
    rw [← hF B hB v, ← hG B hB v, pow_add]
    ring
  | mul_X f j ih =>
    obtain ⟨d, F, hF⟩ := ih
    refine ⟨d + 1, F * X (some j), ?_⟩
    intro B hB v
    simp only [eval₂_mul, eval₂_X, Option.elim_some]
    rw [← hF B hB v, pow_succ]
    field_simp

/-- A fixed rational expression in common-denominator quadratic inputs admits
integer numerator polynomials of uniformly bounded degree and coefficient height. -/
theorem fixed_polynomial_integer_representation {σ : Type*} (f : MvPolynomial σ ℤ) :
    ∃ d D C e : ℕ, 1 ≤ C ∧ ∀ (H : ℕ), 1 ≤ H →
      ∀ (B : ℤ) (v : σ → Polynomial ℤ), B ≠ 0 → |B| ≤ H →
      (∀ j, (v j).natDegree ≤ 2) → (∀ j n, |(v j).coeff n| ≤ H) →
      ∃ F : Polynomial ℤ, F.natDegree ≤ D ∧
        (∀ n, |F.coeff n| ≤ (C * H ^ e : ℕ)) ∧
        MvPolynomial.eval₂ (Int.castRingHom (RatFunc ℚ))
          (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) ((v j).map (Int.castRingHom ℚ)) /
            (B : RatFunc ℚ)) f * (B : RatFunc ℚ) ^ d =
          algebraMap (Polynomial ℚ) (RatFunc ℚ) (F.map (Int.castRingHom ℚ)) := by
  obtain ⟨d, F, hF⟩ := fixed_polynomial_clear_denominator (K := RatFunc ℚ) f
  obtain ⟨D, C, e, hC, hheight⟩ := fixed_polynomial_substitution_height F
  refine ⟨d, D, C, e, hC, ?_⟩
  intro H hH B v hB hBH hvd hvc
  let w : Option σ → Polynomial ℤ := fun j => j.elim (Polynomial.C B) v
  have hwd : ∀ j, (w j).natDegree ≤ 2 := by
    intro j
    cases j with
    | none => simp [w]
    | some j => exact hvd j
  have hwc : ∀ j n, |(w j).coeff n| ≤ H := by
    intro j n
    cases j with
    | none =>
      change |(Polynomial.C B).coeff n| ≤ H
      rw [Polynomial.coeff_C]
      split_ifs
      · exact hBH
      · simp
    | some j => exact hvc j n
  let Fz := MvPolynomial.eval₂ Polynomial.C w F
  obtain ⟨hFd, hFc⟩ := hheight H hH w hwd hwc
  refine ⟨Fz, hFd, hFc, ?_⟩
  let φ : Polynomial ℤ →+* RatFunc ℚ :=
    (algebraMap (Polynomial ℚ) (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))
  have hφ : φ.comp Polynomial.C = Int.castRingHom (RatFunc ℚ) := by
    ext
    simp [φ]
  have hB' : (B : RatFunc ℚ) ≠ 0 := by exact_mod_cast hB
  have he := hF (B : RatFunc ℚ) hB'
    (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) ((v j).map (Int.castRingHom ℚ)))
  rw [he]
  change _ = φ Fz
  rw [show φ Fz = MvPolynomial.eval₂ (φ.comp Polynomial.C) (φ ∘ w) F from
    MvPolynomial.eval₂_comp_left φ _ _ F]
  rw [hφ]
  congr 1
  funext j
  cases j with
  | none => simp [φ, w]
  | some j => rfl

/-- A fixed pair of integer expressions has an integer rational-function
representation of uniformly bounded degree and polynomial coefficient height. -/
theorem fixed_rational_expression_integer_representation {σ : Type*}
    (f g : MvPolynomial σ ℤ) :
    ∃ D C e : ℕ, 1 ≤ C ∧ ∀ (H : ℕ), 1 ≤ H →
      ∀ (B : ℤ) (v : σ → Polynomial ℤ), B ≠ 0 → |B| ≤ H →
      (∀ j, (v j).natDegree ≤ 2) → (∀ j n, |(v j).coeff n| ≤ H) →
      ∃ F G : Polynomial ℤ,
        F.natDegree ≤ D ∧ G.natDegree ≤ D ∧
        (∀ n, |F.coeff n| ≤ (C * H ^ e : ℕ)) ∧
        (∀ n, |G.coeff n| ≤ (C * H ^ e : ℕ)) ∧
        (MvPolynomial.eval₂ (Int.castRingHom (RatFunc ℚ))
          (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) ((v j).map (Int.castRingHom ℚ)) /
            (B : RatFunc ℚ)) f /
         MvPolynomial.eval₂ (Int.castRingHom (RatFunc ℚ))
          (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) ((v j).map (Int.castRingHom ℚ)) /
            (B : RatFunc ℚ)) g) =
          algebraMap (Polynomial ℚ) (RatFunc ℚ) (F.map (Int.castRingHom ℚ)) /
            algebraMap (Polynomial ℚ) (RatFunc ℚ) (G.map (Int.castRingHom ℚ)) := by
  obtain ⟨d, D, C, e, hC, hf⟩ := fixed_polynomial_integer_representation f
  obtain ⟨d', D', C', e', hC', hg⟩ := fixed_polynomial_integer_representation g
  refine ⟨max D D', C + C', e + e' + d + d', by omega, ?_⟩
  intro H hH B v hB hBH hvd hvc
  obtain ⟨F, hFd, hFc, hFe⟩ := hf H hH B v hB hBH hvd hvc
  obtain ⟨G, hGd, hGc, hGe⟩ := hg H hH B v hB hBH hvd hvc
  refine ⟨Polynomial.C (B ^ d') * F, Polynomial.C (B ^ d) * G,
    (Polynomial.natDegree_C_mul_le _ _).trans (hFd.trans (le_max_left ..)),
    (Polynomial.natDegree_C_mul_le _ _).trans (hGd.trans (le_max_right ..)), ?_, ?_, ?_⟩
  · intro n
    rw [Polynomial.coeff_C_mul, abs_mul, abs_pow]
    have hbpow : |B| ^ d' ≤ (H : ℤ) ^ d' := pow_le_pow_left₀ (abs_nonneg B) hBH _
    calc |B| ^ d' * |F.coeff n| ≤ (H : ℤ) ^ d' * (C * H ^ e : ℕ) :=
        mul_le_mul hbpow (hFc n) (abs_nonneg _) (by positivity)
      _ = (C * H ^ (e + d') : ℕ) := by push_cast; ring
      _ ≤ ((C + C') * H ^ (e + e' + d + d') : ℕ) := by
        exact_mod_cast Nat.mul_le_mul (Nat.le_add_right C C')
          (Nat.pow_le_pow_right hH (by omega))
  · intro n
    rw [Polynomial.coeff_C_mul, abs_mul, abs_pow]
    have hbpow : |B| ^ d ≤ (H : ℤ) ^ d := pow_le_pow_left₀ (abs_nonneg B) hBH _
    calc |B| ^ d * |G.coeff n| ≤ (H : ℤ) ^ d * (C' * H ^ e' : ℕ) :=
        mul_le_mul hbpow (hGc n) (abs_nonneg _) (by positivity)
      _ = (C' * H ^ (e' + d) : ℕ) := by push_cast; ring
      _ ≤ ((C + C') * H ^ (e + e' + d + d') : ℕ) := by
        exact_mod_cast Nat.mul_le_mul (Nat.le_add_left C' C)
          (Nat.pow_le_pow_right hH (by omega))
  · have hB' : (B : RatFunc ℚ) ≠ 0 := by exact_mod_cast hB
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Int.coe_castRingHom,
      map_mul, map_pow, map_intCast]
    rw [← hFe, ← hGe]
    have hpow : (B : RatFunc ℚ) ^ (d + d') ≠ 0 := pow_ne_zero _ hB'
    convert (mul_div_mul_right
      (MvPolynomial.eval₂ (Int.castRingHom (RatFunc ℚ))
        (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) ((v j).map (Int.castRingHom ℚ)) /
          (B : RatFunc ℚ)) f)
      (MvPolynomial.eval₂ (Int.castRingHom (RatFunc ℚ))
        (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) ((v j).map (Int.castRingHom ℚ)) /
          (B : RatFunc ℚ)) g) hpow).symm using 1
    ring

end
end PierceLengthBound.FixedDividend
