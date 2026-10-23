/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ConicFactorHeight
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.FieldTheory.RatFunc.Degree

/-! Gcd cancellation over the integers preserves a rational representation and
supplies the rational coprimality required by the integer-value theorem. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial
open scoped nonZeroDivisors

lemma integer_relPrime_rat_coprime {F G : Polynomial ℤ} (hF : F ≠ 0)
    (hcop : IsRelPrime F G) :
    IsCoprime (F.map (Int.castRingHom ℚ)) (G.map (Int.castRingHom ℚ)) := by
  apply IsRelPrime.isCoprime
  intro q hqF hqG
  have hq : q ≠ 0 := ne_zero_of_dvd_ne_zero (by
    simpa only [Polynomial.map_zero] using
      (Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective).ne hF) hqF
  let Q := IsLocalization.integerNormalization (ℤ⁰) q
  have hp : Q.primPart.IsPrimitive := Q.isPrimitive_primPart
  have hpdvd : Q.primPart.map (Int.castRingHom ℚ) ∣ q := by
    have hmap := Polynomial.map_dvd (Int.castRingHom ℚ) Q.primPart_dvd
    obtain ⟨c, hc, he⟩ := IsLocalization.integerNormalization_spec (ℤ⁰) q
    have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
    have hcu : IsUnit (C (c : ℚ)) := isUnit_C.mpr (by exact_mod_cast hc0 : (c : ℚ) ≠ 0).isUnit
    change Q.map (Int.castRingHom ℚ) = c • q at he
    rw [he, Algebra.smul_def] at hmap
    exact (hcu.dvd_mul_left).mp hmap
  have hpF : Q.primPart ∣ F :=
    (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ hp).mpr (hpdvd.trans hqF)
  have hpG : Q.primPart ∣ G :=
    (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ hp).mpr (hpdvd.trans hqG)
  exact Polynomial.isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart hq (hcop hpF hpG)

/-- A rational representation by two nonzero integer polynomials admits common
integer-factor cancellation, rational coprimality, and no increase in degrees. -/
theorem integer_rational_reduction (F G : Polynomial ℤ) (hF : F ≠ 0) (hG : G ≠ 0) :
    ∃ F' G' : Polynomial ℤ,
      F' ∣ F ∧ G' ∣ G ∧ F' ≠ 0 ∧ G' ≠ 0 ∧
      IsCoprime (F'.map (Int.castRingHom ℚ)) (G'.map (Int.castRingHom ℚ)) ∧
      algebraMap (Polynomial ℚ) (RatFunc ℚ) (F.map (Int.castRingHom ℚ)) /
          algebraMap (Polynomial ℚ) (RatFunc ℚ) (G.map (Int.castRingHom ℚ)) =
        algebraMap (Polynomial ℚ) (RatFunc ℚ) (F'.map (Int.castRingHom ℚ)) /
          algebraMap (Polynomial ℚ) (RatFunc ℚ) (G'.map (Int.castRingHom ℚ)) := by
  obtain ⟨F', G', hFF, hGG, hunit⟩ := extract_gcd F G
  let J := gcd F G
  change F = J * F' at hFF
  change G = J * G' at hGG
  have hgcd : J ≠ 0 := by intro h; rw [h, zero_mul] at hFF; exact hF hFF
  have hF' : F' ≠ 0 := by intro h; rw [h, mul_zero] at hFF; exact hF hFF
  have hG' : G' ≠ 0 := by intro h; rw [h, mul_zero] at hGG; exact hG hGG
  refine ⟨F', G', ⟨J, by rw [hFF]; ring⟩, ⟨J, by rw [hGG]; ring⟩,
    hF', hG', integer_relPrime_rat_coprime hF' (gcd_isUnit_iff_isRelPrime.mp hunit), ?_⟩
  have hm : (J).map (Int.castRingHom ℚ) ≠ 0 := by
    simpa only [Polynomial.map_zero] using
      (Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective).ne hgcd
  have hc : algebraMap (Polynomial ℚ) (RatFunc ℚ)
      ((J).map (Int.castRingHom ℚ)) ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ)).ne hm
  rw [hFF, hGG, Polynomial.map_mul, Polynomial.map_mul, map_mul, map_mul,
    mul_div_mul_left _ _ hc]

end
end PierceLengthBound.FixedDividend
