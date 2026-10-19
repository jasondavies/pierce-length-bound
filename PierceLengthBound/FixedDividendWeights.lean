/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FortyFiveMain

/-!
# Half-power weights from the existing minor-lattice count

Cauchy–Schwarz transfers the existing reciprocal-length estimate to the half-power
weight needed by the `18/61` candidate. The explicit divisor-factor loss is harmless
for the proposed epsilon bound. This avoids assuming the candidate's new primitive
rank-three lattice enumeration lemma.
-/

@[expose] public section

namespace PierceLengthBound.FixedDividend

open Finset

/-- The real-valued form of the existing partial-summation estimate. -/
theorem reciprocal_sum_bound {ι : Type*} (S : Finset ι) (R : ι → ℕ) {L C : ℕ}
    (hR : ∀ p ∈ S, 1 ≤ R p ∧ R p ≤ L)
    (hc : ∀ r, 1 ≤ r → (S.filter fun p => R p ≤ r).card ≤ C * r ^ 3) :
    (L : ℝ) * ∑ p ∈ S, (1 : ℝ) / R p ≤ S.card + C * (L : ℝ) ^ 3 := by
  classical
  rcases S.eq_empty_or_nonempty with hS | ⟨p0, hp0⟩
  · subst hS; simp only [sum_empty, mul_zero, card_empty, Nat.cast_zero, zero_add]; positivity
  have hL : 1 ≤ L := ((hR p0 hp0).1).trans (hR p0 hp0).2
  have hLr : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  set g : ℕ → ℝ := fun j => (1 : ℝ) / (j * (j + 1))
  have key : ∑ p ∈ S, (1 : ℝ) / R p =
      S.card / L + ∑ j ∈ Ico 1 L, ((S.filter fun p => R p ≤ j).card : ℝ) * g j := by
    have h1 : ∀ p ∈ S, (1 : ℝ) / R p = 1 / L + ∑ j ∈ Ico 1 L, if R p ≤ j then g j else 0 := by
      intro p hp
      rw [inv_telescope (hR p hp).1 (hR p hp).2, ← sum_filter]
      congr 1
      refine sum_congr ?_ fun _ _ => rfl
      ext j; simp only [mem_Ico, mem_filter]; have := (hR p hp).1; omega
    rw [sum_congr rfl h1, sum_add_distrib, sum_comm]
    congr 1
    · rw [sum_const, nsmul_eq_mul]; ring
    · refine sum_congr rfl fun j _ => ?_
      rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hbound : ∑ j ∈ Ico 1 L, ((S.filter fun p => R p ≤ j).card : ℝ) * g j ≤ C * L ^ 2 := by
    calc ∑ j ∈ Ico 1 L, ((S.filter fun p => R p ≤ j).card : ℝ) * g j
        ≤ ∑ _j ∈ Ico 1 L, (C : ℝ) * L := by
          refine sum_le_sum fun j hj => ?_
          have hj1 : 1 ≤ j := (mem_Ico.mp hj).1
          have hjL : j < L := (mem_Ico.mp hj).2
          have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
          have hc' : ((S.filter fun p => R p ≤ j).card : ℝ) ≤ C * (j : ℝ) ^ 3 := by
            exact_mod_cast hc j hj1
          have hg : g j ≤ 1 / (j : ℝ) ^ 2 := by
            simp only [g]
            apply one_div_le_one_div_of_le (by positivity)
            nlinarith
          have hgp : 0 ≤ g j := by simp only [g]; positivity
          calc ((S.filter fun p => R p ≤ j).card : ℝ) * g j ≤ (C * (j : ℝ) ^ 3)
                 * (1 / (j : ℝ) ^ 2) :=
                mul_le_mul hc' hg hgp (by positivity)
            _ = C * j := by field_simp
            _ ≤ C * L := by gcongr
      _ = ((L - 1 : ℕ) : ℝ) * (C * L) := by rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ C * L ^ 2 := by
          have : ((L - 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast Nat.sub_le L 1
          calc ((L - 1 : ℕ) : ℝ) * (C * L) ≤ (L : ℝ) * (C * L) :=
                mul_le_mul_of_nonneg_right this (by positivity)
            _ = C * L ^ 2 := by ring
  calc (L : ℝ) * ∑ p ∈ S, (1 : ℝ) / R p
      = L * (S.card / L + ∑ j ∈ Ico 1 L,
          ((S.filter fun p => R p ≤ j).card : ℝ) * g j) := by rw [key]
    _ ≤ L * (S.card / L + C * L ^ 2) := by gcongr
    _ = S.card + C * (L : ℝ) ^ 3 := by field_simp

/-- Cauchy–Schwarz transfers an inverse-length sum to the inverse-square-root sum. -/
theorem half_weight_sq {ι : Type*} (S : Finset ι) (R : ι → ℕ) :
    (∑ p ∈ S, Real.sqrt ((1 : ℝ) / R p)) ^ 2 ≤
      S.card * ∑ p ∈ S, (1 : ℝ) / R p := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ))
    (fun p => Real.sqrt ((1 : ℝ) / R p))
  simpa only [one_mul, one_pow, Real.sq_sqrt (div_nonneg zero_le_one (Nat.cast_nonneg _)),
    sum_const, nsmul_eq_mul, mul_one] using h

/-- Sixth-power form of the half-weight estimate, with explicit divisor slack.
`shortR` is the integral pivot-lattice minimum already used for basis coordinates. -/
theorem half_weight_minor_bound {S : Finset (Fin 10 → ℤ)} {X τ : ℕ}
    (hX : 1 ≤ X) (hτ1 : 1 ≤ τ)
    (hS : ∀ p ∈ S, (∀ t, |p t| ≤ X) ∧ PluckerRel p ∧ p (piv p) ≠ 0)
    (hτ : ∀ m ∈ Icc 1 X, m.divisors.card ≤ τ) :
    (∑ p ∈ S, Real.sqrt ((1 : ℝ) / shortR p)) ^ 6 ≤
      (14581 * (14581 + 8 * 393660) : ℝ) ^ 3 * (X : ℝ) ^ 29 * (τ : ℝ) ^ 9 := by
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
  have hcs := half_weight_sq S shortR
  let w := ∑ p ∈ S, Real.sqrt ((1 : ℝ) / shortR p)
  have hpos : 0 ≤ w := sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hSc' : (S.card : ℝ) ≤ 14581 * (X : ℝ) ^ 5 * τ := by exact_mod_cast hSc
  have hLX' : (X : ℝ) ≤ (L : ℝ) ^ 3 := by exact_mod_cast hLX
  have hLX8' : (L : ℝ) ^ 3 ≤ 8 * (X : ℝ) := by exact_mod_cast hLX8
  have ht : (1 : ℝ) ≤ τ := by exact_mod_cast hτ1
  have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
  have hbound : (L : ℝ) * w ^ 2 ≤
      (14581 * (14581 + 8 * 393660) : ℝ) * (X : ℝ) ^ 10 * (τ : ℝ) ^ 3 := by
    calc (L : ℝ) * w ^ 2 ≤ L * ((S.card : ℝ) * ∑ p ∈ S, (1 : ℝ) / shortR p) :=
          mul_le_mul_of_nonneg_left hcs hL
      _ = S.card * (L * ∑ p ∈ S, (1 : ℝ) / shortR p) := by ring
      _ ≤ S.card * (S.card + (393660 * X ^ 4 * τ ^ 2 : ℕ) * (L : ℝ) ^ 3) := by gcongr
      _ ≤ (14581 * (X : ℝ) ^ 5 * τ) *
          (14581 * (X : ℝ) ^ 5 * τ + 393660 * (X : ℝ) ^ 4 * (τ : ℝ) ^ 2 * (8 * X)) := by
            push_cast
            gcongr
      _ ≤ (14581 * (X : ℝ) ^ 5 * τ) *
          (14581 * (X : ℝ) ^ 5 * (τ : ℝ) ^ 2 +
            393660 * (X : ℝ) ^ 4 * (τ : ℝ) ^ 2 * (8 * X)) := by
            gcongr
            nlinarith
      _ = _ := by ring
  have hcub := pow_le_pow_left₀ (mul_nonneg hL (sq_nonneg w)) hbound 3
  have hx : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  apply (mul_le_mul_iff_right₀ hx).mp
  calc (X : ℝ) * w ^ 6 ≤ (L : ℝ) ^ 3 * w ^ 6 := by gcongr
    _ = ((L : ℝ) * w ^ 2) ^ 3 := by ring
    _ ≤ ((14581 * (14581 + 8 * 393660) : ℝ) * (X : ℝ) ^ 10 * (τ : ℝ) ^ 3) ^ 3 := hcub
    _ = _ := by ring

/-- Transfer a per-pattern square-root count to a sixth-power bound.
The local curve-count premise is explicit and is not established by this theorem. -/
theorem weighted_count_sixth {S : Finset (Fin 10 → ℤ)} {X τ : ℕ}
    (hX : 1 ≤ X) (hτ1 : 1 ≤ τ)
    (hS : ∀ p ∈ S, (∀ t, |p t| ≤ X) ∧ PluckerRel p ∧ p (piv p) ≠ 0)
    (hτ : ∀ m ∈ Icc 1 X, m.divisors.card ≤ τ)
    {T H K : ℝ} (hT : 0 ≤ T) (hH : 0 ≤ H)
    (hcount : T ≤ K * Real.sqrt H * ∑ p ∈ S, Real.sqrt ((1 : ℝ) / shortR p)) :
    T ^ 6 ≤ K ^ 6 * H ^ 3 *
      ((14581 * (14581 + 8 * 393660) : ℝ) ^ 3 * (X : ℝ) ^ 29 * (τ : ℝ) ^ 9) := by
  have hw := half_weight_minor_bound hX hτ1 hS hτ
  calc T ^ 6 ≤ (K * Real.sqrt H * ∑ p ∈ S, Real.sqrt ((1 : ℝ) / shortR p)) ^ 6 :=
        pow_le_pow_left₀ hT hcount 6
    _ = K ^ 6 * H ^ 3 * (∑ p ∈ S, Real.sqrt ((1 : ℝ) / shortR p)) ^ 6 := by
      rw [mul_pow, mul_pow, show (Real.sqrt H) ^ 6 = H ^ 3 by
        rw [show (Real.sqrt H) ^ 6 = ((Real.sqrt H) ^ 2) ^ 3 by ring,
          Real.sq_sqrt hH]]
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)

end PierceLengthBound.FixedDividend
