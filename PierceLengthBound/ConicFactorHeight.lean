/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ConicResultantHeight
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Data.Nat.Choose.Bounds

/-! Polynomial height stays controlled when common integer factors are cancelled.
The bound follows from the checked Mahler-measure coefficient inequality. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial Finset

/-- A nonzero integer polynomial has Mahler measure at least one. -/
lemma integer_polynomial_mahler_ge_one {F : ℤ[X]} (hF : F ≠ 0) :
    1 ≤ (F.map (Int.castRingHom ℂ)).mahlerMeasure := by
  apply Polynomial.one_le_mahlerMeasure_of_one_le_norm_leadingCoeff
  rw [leadingCoeff_map_of_injective (f := Int.castRingHom ℂ) Int.cast_injective]
  have h : (1 : ℤ) ≤ |F.leadingCoeff| := Int.one_le_abs (leadingCoeff_ne_zero.mpr hF)
  simpa only [Int.coe_castRingHom, Complex.norm_intCast] using
    (show (1 : ℝ) ≤ |(F.leadingCoeff : ℝ)| by exact_mod_cast h)

/-- The Mahler measure is at most the coefficient height times `d+1`. -/
lemma integer_polynomial_mahler_le {F : ℤ[X]} {d H : ℕ}
    (hd : F.natDegree ≤ d) (hH : ∀ n, |F.coeff n| ≤ H) :
    (F.map (Int.castRingHom ℂ)).mahlerMeasure ≤ (d + 1 : ℕ) * (H : ℝ) := by
  let FC := F.map (Int.castRingHom ℂ)
  have hdeg : FC.natDegree ≤ d := by
    simpa only [FC, natDegree_map_eq_of_injective (f := Int.castRingHom ℂ) Int.cast_injective]
      using hd
  have hcoef (i : ℕ) : ‖FC.coeff i‖ ≤ (H : ℝ) := by
    have hi := hH i
    simpa only [FC, coeff_map, Int.coe_castRingHom, Complex.norm_intCast] using
      (show |(F.coeff i : ℝ)| ≤ (H : ℝ) by exact_mod_cast hi)
  calc FC.mahlerMeasure ≤ FC.sum (fun _ a => ‖a‖) := FC.mahlerMeasure_le_sum_norm_coeff
    _ ≤ ∑ _i ∈ FC.support, (H : ℝ) := by
      exact sum_le_sum fun i _ => hcoef i
    _ = (FC.support.card : ℝ) * H := by simp
    _ ≤ (d + 1 : ℕ) * (H : ℝ) := by
      gcongr
      exact_mod_cast (FC.card_supp_le_succ_natDegree.trans (by omega))

/-- Every integer polynomial factor has coefficients bounded by
`2^d (d+1) H`; this includes the numerators and denominators after gcd cancellation. -/
theorem integer_factor_height {F G : ℤ[X]} {d H : ℕ} (hF : F ≠ 0) (hGF : G ∣ F)
    (hd : F.natDegree ≤ d) (hH : ∀ n, |F.coeff n| ≤ H) :
    ∀ n, |G.coeff n| ≤ (2 ^ d * (d + 1) * H : ℕ) := by
  obtain ⟨Q, he⟩ := hGF
  have hG : G ≠ 0 := by intro hz; simp only [hz, zero_mul] at he; exact hF he
  have hQ : Q ≠ 0 := by intro hz; simp only [hz, mul_zero] at he; exact hF he
  have hgdeg : G.natDegree ≤ d := (natDegree_le_of_dvd ⟨Q, he⟩ hF).trans hd
  intro n
  have hc := norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure n
    (G.map (Int.castRingHom ℂ)) (Q.map (Int.castRingHom ℂ))
    (integer_polynomial_mahler_ge_one hQ)
  rw [← Polynomial.map_mul, ← he,
    natDegree_map_eq_of_injective (f := Int.castRingHom ℂ) Int.cast_injective] at hc
  have hchoose : (G.natDegree.choose n : ℝ) ≤ 2 ^ d := by
    exact_mod_cast (Nat.choose_le_two_pow G.natDegree n).trans
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hgdeg)
  have hmc := integer_polynomial_mahler_le hd hH
  have hbound : ‖(G.map (Int.castRingHom ℂ)).coeff n‖ ≤
      (2 : ℝ) ^ d * (d + 1 : ℕ) * H := by
    calc _ ≤ (G.natDegree.choose n : ℝ) * (F.map (Int.castRingHom ℂ)).mahlerMeasure := hc
      _ ≤ (2 : ℝ) ^ d * ((d + 1 : ℕ) * (H : ℝ)) :=
        mul_le_mul hchoose hmc (Polynomial.mahlerMeasure_nonneg _) (by positivity)
      _ = _ := by ring
  simp only [coeff_map, Int.coe_castRingHom, Complex.norm_intCast] at hbound
  exact_mod_cast hbound

/-- Cancelling any common integer factor preserves a polynomial bound on both
coefficient heights, so the proved divisor estimate applies to a coprime reduction. -/
theorem reduced_integer_values_card {F G F' G' : ℤ[X]} {d H : ℕ}
    (hF : F ≠ 0) (hG : G ≠ 0) (hF' : F' ∣ F) (hG' : G' ∣ G)
    (hFd : F.natDegree ≤ d) (hGd : G.natDegree ≤ d) (hH : 1 ≤ H)
    (hFH : ∀ n, |F.coeff n| ≤ H) (hGH : ∀ n, |G.coeff n| ≤ H)
    (hGpos : 0 < G'.natDegree)
    (hcop : IsCoprime (F'.map (Int.castRingHom ℚ)) (G'.map (Int.castRingHom ℚ)))
    (S : Finset ℤ) (hdiv : ∀ t ∈ S, G'.eval t ∣ F'.eval t) :
    S.card ≤ 2 * d * tauMax ((2 * d).factorial *
      (2 ^ d * (d + 1) * H) ^ (2 * d)) := by
  have hheight : 1 ≤ 2 ^ d * (d + 1) * H := by
    have : 0 < H := by omega
    exact Nat.succ_le_of_lt (by positivity)
  apply integer_values_card_of_height hheight
    ((natDegree_le_of_dvd hF' hF).trans hFd) ((natDegree_le_of_dvd hG' hG).trans hGd)
    hGpos (integer_factor_height hF hF' hFd hFH) (integer_factor_height hG hG' hGd hGH) hcop S hdiv

end
end PierceLengthBound.FixedDividend
