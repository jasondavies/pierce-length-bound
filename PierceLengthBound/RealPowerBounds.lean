/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib

/-!
# Real-power inequalities

Elementary inequalities for real powers used when summing local estimates: concavity of
`x ↦ xᵗ` over a finite sum, powers of maxima, and turning a sum of five terms into one dominant
term.
-/

@[expose] public section
namespace PierceLengthBound
open Finset

/-- Concavity: `∑ zᵢᵗ ≤ N^{1-t} (∑ zᵢ)ᵗ` for `0 ≤ t ≤ 1`. -/
theorem sum_rpow_le_card_rpow_mul {ι : Type*} (s : Finset ι) (z : ι → ℝ)
    (hz : ∀ i ∈ s, 0 ≤ z i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∑ i ∈ s, z i ^ t ≤ (s.card : ℝ) ^ (1 - t) * (∑ i ∈ s, z i) ^ t := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp only [sum_empty]; positivity
  have hN : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hw : ∑ _i ∈ s, (s.card : ℝ)⁻¹ = 1 := by
    rw [sum_const, nsmul_eq_mul]; field_simp
  have hj := (Real.concaveOn_rpow ht0 ht1).le_map_sum (t := s) (w := fun _ => (s.card : ℝ)⁻¹)
    (p := z) (fun _ _ => by positivity) hw (fun i hi => Set.mem_Ici.mpr (hz i hi))
  simp only [smul_eq_mul, ← mul_sum] at hj
  have hsum : 0 ≤ ∑ i ∈ s, z i := sum_nonneg hz
  rw [Real.mul_rpow (by positivity) hsum, Real.inv_rpow hN.le] at hj
  have hsplit : (s.card : ℝ) ^ (1 - t) = (s.card : ℝ) * ((s.card : ℝ) ^ t)⁻¹ := by
    rw [Real.rpow_sub hN, Real.rpow_one, div_eq_mul_inv]
  rw [hsplit]
  have := mul_le_mul_of_nonneg_left hj hN.le
  rw [← mul_assoc (s.card : ℝ) (s.card : ℝ)⁻¹, mul_inv_cancel₀ hN.ne', one_mul] at this
  linarith [show (s.card : ℝ) * ((s.card : ℝ) ^ t)⁻¹ * (∑ i ∈ s, z i) ^ t =
    (s.card : ℝ) * (((s.card : ℝ) ^ t)⁻¹ * (∑ i ∈ s, z i) ^ t) by ring]

/-- A power of a maximum is at most the sum of the powers. -/
lemma max_rpow_le_add {u v r : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (max u v) ^ r ≤ u ^ r + v ^ r := by
  rcases le_total u v with h | h
  · rw [max_eq_right h]; linarith [Real.rpow_nonneg hu r]
  · rw [max_eq_left h]; linarith [Real.rpow_nonneg hv r]

/-- For `c ≥ 1`, powers with exponent at most `1` are at most `c`. -/
lemma rpow_le_self_of_le_one {c r : ℝ} (hc : 1 ≤ c) (hr : r ≤ 1) : c ^ r ≤ c := by
  calc c ^ r ≤ c ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc hr
    _ = c := Real.rpow_one c

/-- `((y ^ k : ℕ) : ℝ) ^ (1 / h) = y ^ (k / h)`. -/
lemma natCast_pow_rpow (y : ℕ) (k : ℕ) {h : ℝ} :
    (((y ^ k : ℕ) : ℝ)) ^ (1 / h) = (y : ℝ) ^ ((k : ℝ) / h) := by
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1; ring

/-- An integer power of a real power with an integer product exponent. -/
lemma rpow_pow_natCast {x r : ℝ} (hx : 0 ≤ x) (k : ℕ) {e : ℕ} (he : r * k = e) :
    (x ^ r) ^ k = x ^ e := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, he, Real.rpow_natCast]

/-- If `T` is at most `R` times a sum of five nonnegative terms, it is at most `5 (R + 1)` times
one of them. -/
lemma le_of_le_sum_five {T R t₀ t₁ t₂ t₃ t₄ : ℝ} (h₀ : 0 ≤ t₀) (h₁ : 0 ≤ t₁) (h₂ : 0 ≤ t₂)
    (h₃ : 0 ≤ t₃) (h₄ : 0 ≤ t₄) (hT : T ≤ R * (t₀ + t₁ + t₂ + t₃ + t₄)) :
    T ≤ 5 * (R + 1) * t₀ ∨ T ≤ 5 * (R + 1) * t₁ ∨ T ≤ 5 * (R + 1) * t₂ ∨
      T ≤ 5 * (R + 1) * t₃ ∨ T ≤ 5 * (R + 1) * t₄ := by
  by_contra hc
  push Not at hc
  obtain ⟨c₀, c₁, c₂, c₃, c₄⟩ := hc
  nlinarith

end PierceLengthBound
