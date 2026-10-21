/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendWeights
public import PierceLengthBound.IntegralLiftPatternCount
public import PierceLengthBound.RealPowerBounds

/-!
# Fractional lattice weights over patterns

The reciprocal estimate `∑ 1/λ_p ≪ X^{14/3}` (`reciprocal_sum_bound` with `short_count`) and the
pattern count `#S ≪ X⁵` combine by concavity of `x ↦ xᵗ` into
`∑_p λ_p^{-t} ≪ X^{5 - t/3}` for every `0 ≤ t ≤ 1` (`shortR_weight_sum`). Both weights needed by
the exterior lattice coordinates, `1/h` and `2m/h`, lie in this range.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

/-- **Fractional lattice weights** (paper, `lem:weights`). For `0 ≤ t ≤ 1`,
`∑_p λ_p^{-t} ≤ 3163861 τ² X^{5 - t/3}`. Here `3163861 = 14581 + 8 · 393660`: `14581` is the
constant of the pattern count `ordinary_minor_count`, and `8 · 393660` comes from the short-vector
count `short_count` with `L³ ≤ 8X`. -/
theorem shortR_weight_sum {S : Finset (Fin 10 → ℤ)} {X τ : ℕ}
    (hX : 1 ≤ X) (hτ1 : 1 ≤ τ)
    (hS : ∀ p ∈ S, (∀ t, |p t| ≤ X) ∧ PluckerRel p ∧ p (piv p) ≠ 0)
    (hτ : ∀ m ∈ Icc 1 X, m.divisors.card ≤ τ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∑ p ∈ S, ((shortR p : ℝ)⁻¹) ^ t ≤
      3163861 * (τ : ℝ) ^ 2 * (X : ℝ) ^ (5 - t / 3) := by
  classical
  have hSc : S.card ≤ 14581 * τ * X ^ 5 :=
    ordinary_minor_count hX hτ1 (fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩) hτ
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
  set A : ℝ := 3163861 * (τ : ℝ) ^ 2 * (X : ℝ) ^ 5
  have hXr : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hτr : (1 : ℝ) ≤ τ := by exact_mod_cast hτ1
  have hA : 0 < A := by positivity
  have hNA : (S.card : ℝ) ≤ A := by
    have : (S.card : ℝ) ≤ 14581 * τ * (X : ℝ) ^ 5 := by exact_mod_cast hSc
    have : (τ : ℝ) ≤ (τ : ℝ) ^ 2 := by nlinarith
    simp only [A]
    nlinarith [pow_pos (show (0 : ℝ) < (X : ℝ) by linarith) 5]
  -- the reciprocal sum
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL1
  have hL3 : (L : ℝ) ^ 3 ≤ 8 * (X : ℝ) := by exact_mod_cast hLX8
  have hXL : (X : ℝ) ^ (1 / 3 : ℝ) ≤ L := by
    have h : (X : ℝ) ≤ (L : ℝ) ^ (3 : ℝ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; exact_mod_cast hLX
    calc (X : ℝ) ^ (1 / 3 : ℝ) ≤ ((L : ℝ) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) :=
          Real.rpow_le_rpow (by linarith) h (by norm_num)
      _ = L := by rw [← Real.rpow_mul hLr.le]; norm_num
  have hrec : ∑ p ∈ S, (shortR p : ℝ)⁻¹ ≤ A * (X : ℝ) ^ (-(1 / 3 : ℝ)) := by
    have h1 : (L : ℝ) * ∑ p ∈ S, (shortR p : ℝ)⁻¹ ≤ A := by
      have hab' : (L : ℝ) * ∑ p ∈ S, (1 : ℝ) / shortR p ≤
          S.card + (393660 * X ^ 4 * τ ^ 2 : ℕ) * (L : ℝ) ^ 3 := hab
      simp only [one_div] at hab'
      refine hab'.trans ?_
      push_cast
      have : (τ : ℝ) ≤ (τ : ℝ) ^ 2 := by nlinarith
      have hc : (393660 : ℝ) * (X : ℝ) ^ 4 * (τ : ℝ) ^ 2 * (L : ℝ) ^ 3 ≤
          393660 * (X : ℝ) ^ 4 * (τ : ℝ) ^ 2 * (8 * (X : ℝ)) := by gcongr
      have hS' : (S.card : ℝ) ≤ 14581 * τ * (X : ℝ) ^ 5 := by exact_mod_cast hSc
      simp only [A]
      nlinarith [pow_pos (show (0 : ℝ) < (X : ℝ) by linarith) 5,
        pow_pos (show (0 : ℝ) < (X : ℝ) by linarith) 4]
    have hX13 : 0 < (X : ℝ) ^ (1 / 3 : ℝ) := by positivity
    have h2 : (X : ℝ) ^ (1 / 3 : ℝ) * ∑ p ∈ S, (shortR p : ℝ)⁻¹ ≤ A :=
      (mul_le_mul_of_nonneg_right hXL (sum_nonneg fun p _ => by positivity)).trans h1
    rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hX13]
    linarith
  -- concavity
  have hc := sum_rpow_le_card_rpow_mul S (fun p => (shortR p : ℝ)⁻¹)
    (fun p _ => by positivity) ht0 ht1
  have hrec_pow : (∑ p ∈ S, (shortR p : ℝ)⁻¹) ^ t ≤ A ^ t * (X : ℝ) ^ (-(t / 3)) := by
    calc (∑ p ∈ S, (shortR p : ℝ)⁻¹) ^ t ≤ (A * (X : ℝ) ^ (-(1 / 3 : ℝ))) ^ t :=
          Real.rpow_le_rpow (sum_nonneg fun p _ => by positivity) hrec ht0
      _ = A ^ t * (X : ℝ) ^ (-(t / 3)) := by
        rw [Real.mul_rpow hA.le (by positivity), ← Real.rpow_mul (by linarith)]
        congr 2; ring
  have hN_pow : (S.card : ℝ) ^ (1 - t) ≤ A ^ (1 - t) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hNA (by linarith)
  calc ∑ p ∈ S, ((shortR p : ℝ)⁻¹) ^ t ≤ (S.card : ℝ) ^ (1 - t) *
        (∑ p ∈ S, (shortR p : ℝ)⁻¹) ^ t := hc
    _ ≤ A ^ (1 - t) * (A ^ t * (X : ℝ) ^ (-(t / 3))) := by
        gcongr
    _ = A * (X : ℝ) ^ (-(t / 3)) := by
        rw [← mul_assoc, ← Real.rpow_add hA, sub_add_cancel, Real.rpow_one]
    _ = 3163861 * (τ : ℝ) ^ 2 * (X : ℝ) ^ (5 - t / 3) := by
        simp only [A]
        rw [sub_eq_add_neg, Real.rpow_add (by linarith),
          show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        ring

/-- The slack in the fractional weights: the divisor bound, squared. -/
def latticeWeightSlack (a : ℕ) : ℕ := 3163861 * tauMax (10 ^ 16 * a ^ 7) ^ 2

lemma latticeWeightSlack_slow : SlowGrowth latticeWeightSlack := by
  have hc := slowGrowth_const 3163861
  have ht := tauMax_slow (10 ^ 16) 7
  have he : latticeWeightSlack = fun a => 3163861 * (tauMax (10 ^ 16 * a ^ 7) *
      tauMax (10 ^ 16 * a ^ 7)) := by
    funext a; simp only [latticeWeightSlack, pow_two]
  rw [he]
  exact hc.mul (ht.mul ht)

/-- The fractional weights of the selected full patterns. -/
theorem selected_pattern_weight_sum {a b s T A : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hT : 36 ≤ T) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∑ p ∈ (selectedStarts a b s T A).image (fun i => plk (Mi a b i)),
        ((shortR p : ℝ)⁻¹) ^ t ≤
      latticeWeightSlack a * (selectedMinorHeight a A T : ℝ) ^ (5 - t / 3) := by
  have hX := selectedMinorHeight_pos hba hmem hsT hT
  have hXb := selectedMinorHeight_le hba hmem hT
  have hτ : 1 ≤ tauMax (10 ^ 16 * a ^ 7) := by
    simpa using (tau_le_tauMax (hX.trans hXb) : (1 : ℕ).divisors.card ≤ _)
  have h := shortR_weight_sum hX hτ (S := (selectedStarts a b s T A).image
    (fun i => plk (Mi a b i))) ?_ (fun m hm => tau_le_tauMax ((mem_Icc.mp hm).2.trans hXb))
    ht0 ht1
  · simpa only [latticeWeightSlack, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    have hP := (selectedStart_spec hmem hsT hi).1
    exact ⟨selectedStart_minor_height hba hmem hsT hi, plucker _,
      piv_ne_zero (orbit_pattern_first hba (by omega))⟩

end
end PierceLengthBound.FixedDividend
