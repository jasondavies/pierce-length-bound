/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendWeights
public import Mathlib.Algebra.Order.Chebyshev

/-! Quarter-power lattice weights for the proposed 180/611 refinement.
The divisor slack is retained and can be absorbed into an arbitrary epsilon. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Finset

/-- Jensen transfers the reciprocal-length sum to quarter-power weights. -/
theorem quarter_weight_fourth {ι : Type*} (S : Finset ι) (R : ι → ℕ) :
    (∑ p ∈ S, ((1 : ℝ) / R p) ^ (1 / 4 : ℝ)) ^ 4 ≤
      (S.card : ℝ) ^ 3 * ∑ p ∈ S, (1 : ℝ) / R p := by
  have h := pow_sum_le_card_mul_sum_pow (s := S)
    (f := fun p => ((1 : ℝ) / R p) ^ (1 / 4 : ℝ))
    (fun _ _ => Real.rpow_nonneg (by positivity) _) 3
  have he (p : ι) : (((1 : ℝ) / R p) ^ (1 / 4 : ℝ)) ^ (3 + 1) = (1 : ℝ) / R p := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  simpa only [he] using h

/-- Twelfth-power form of the new lattice-weight estimate, with divisor slack. -/
theorem quarter_weight_minor_bound {S : Finset (Fin 10 → ℤ)} {X τ : ℕ}
    (hX : 1 ≤ X) (hτ1 : 1 ≤ τ)
    (hS : ∀ p ∈ S, (∀ t, |p t| ≤ X) ∧ PluckerRel p ∧ p (piv p) ≠ 0)
    (hτ : ∀ m ∈ Icc 1 X, m.divisors.card ≤ τ) :
    (∑ p ∈ S, ((1 : ℝ) / shortR p) ^ (1 / 4 : ℝ)) ^ 12 ≤
      (14581 ^ 3 * (14581 + 8 * 393660) : ℝ) ^ 3 * (X : ℝ) ^ 59 * (τ : ℝ) ^ 15 := by
  classical
  have hSc : S.card ≤ 14581 * X ^ 5 * τ := by
    have h1 : S.card ≤ 1 + 20 * ∑ m ∈ Icc 1 X, 729 * m ^ 4 * m.divisors.card :=
      minor_vector_count fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩
    have h2 : ∑ m ∈ Icc 1 X, 729 * m ^ 4 * m.divisors.card ≤ 729 * X ^ 5 * τ := by
      calc ∑ m ∈ Icc 1 X, 729 * m ^ 4 * m.divisors.card
          ≤ ∑ _m ∈ Icc 1 X, 729 * X ^ 4 * τ := by
            refine sum_le_sum fun m hm => ?_
            have := (mem_Icc.mp hm).2
            gcongr
            exact hτ m hm
        _ = 729 * X ^ 5 * τ := by
          rw [sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]; ring
    have : 1 ≤ X ^ 5 * τ := Nat.mul_pos (by positivity) (by omega)
    nlinarith
  obtain ⟨L, hL1, hLX, hLX8⟩ := exists_cube_root hX
  have hR : ∀ p ∈ S, 1 ≤ shortR p ∧ shortR p ≤ L := by
    intro p hp
    obtain ⟨hb, hpl, hm⟩ := hS p hp
    refine ⟨(shortR_spec hm).1, shortR_le (pivLat_short hpl hm ?_)⟩
    have hpX : (p (piv p)).natAbs ≤ X := by
      have h' : ((p (piv p)).natAbs : ℤ) ≤ X := by
        rw [Int.natCast_natAbs]; exact hb (piv p)
      exact_mod_cast h'
    calc (p (piv p)).natAbs ≤ L ^ 3 := hpX.trans hLX
      _ < (L + 1) ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have hab := reciprocal_sum_bound S shortR (C := 393660 * X ^ 4 * τ ^ 2) hR
    (fun r _ => (short_count (Y := X) (R := r) hS hτ).trans (by ring_nf; exact le_rfl))
  have hcs := quarter_weight_fourth S shortR
  let w := ∑ p ∈ S, ((1 : ℝ) / shortR p) ^ (1 / 4 : ℝ)
  have hpos : 0 ≤ w := sum_nonneg fun _ _ => Real.rpow_nonneg (by positivity) _
  have hSc' : (S.card : ℝ) ≤ 14581 * (X : ℝ) ^ 5 * τ := by exact_mod_cast hSc
  have hLX' : (X : ℝ) ≤ (L : ℝ) ^ 3 := by exact_mod_cast hLX
  have hLX8' : (L : ℝ) ^ 3 ≤ 8 * (X : ℝ) := by exact_mod_cast hLX8
  have ht : (1 : ℝ) ≤ τ := by exact_mod_cast hτ1
  have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
  have hbound : (L : ℝ) * w ^ 4 ≤
      (14581 ^ 3 * (14581 + 8 * 393660) : ℝ) * (X : ℝ) ^ 20 * (τ : ℝ) ^ 5 := by
    calc (L : ℝ) * w ^ 4 ≤ L * ((S.card : ℝ) ^ 3 * ∑ p ∈ S, (1 : ℝ) / shortR p) :=
          mul_le_mul_of_nonneg_left hcs hL
      _ = S.card ^ 3 * (L * ∑ p ∈ S, (1 : ℝ) / shortR p) := by ring
      _ ≤ S.card ^ 3 * (S.card + (393660 * X ^ 4 * τ ^ 2 : ℕ) * (L : ℝ) ^ 3) := by gcongr
      _ ≤ (14581 * (X : ℝ) ^ 5 * τ) ^ 3 *
          (14581 * (X : ℝ) ^ 5 * τ + 393660 * (X : ℝ) ^ 4 * (τ : ℝ) ^ 2 * (8 * X)) := by
            push_cast
            gcongr
      _ ≤ (14581 * (X : ℝ) ^ 5 * τ) ^ 3 *
          (14581 * (X : ℝ) ^ 5 * (τ : ℝ) ^ 2 +
            393660 * (X : ℝ) ^ 4 * (τ : ℝ) ^ 2 * (8 * X)) := by
            gcongr
            nlinarith
      _ = _ := by ring
  have hcub := pow_le_pow_left₀ (mul_nonneg hL (pow_nonneg hpos 4)) hbound 3
  have hx : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  apply (mul_le_mul_iff_right₀ hx).mp
  calc (X : ℝ) * w ^ 12 ≤ (L : ℝ) ^ 3 * w ^ 12 := by gcongr
    _ = ((L : ℝ) * w ^ 4) ^ 3 := by ring
    _ ≤ ((14581 ^ 3 * (14581 + 8 * 393660) : ℝ) * (X : ℝ) ^ 20 * (τ : ℝ) ^ 5) ^ 3 := hcub
    _ = _ := by ring


end PierceLengthBound.FixedDividend
