/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.MinorHeight
public import PierceLengthBound.ElevenMain

/-!
# `P(a, b) ≪_ε a^{8/27 + ε}`

The seven pattern integers are signed coordinates of the vector of ten minors of `𝓜ᵢ`
(`theta_eq`, in `OrbitPattern`). Counting minor vectors (`minor_vector_count`) instead of seven
independent integers replaces `X⁷` by `X⁵ τ`, and the uniform minor bound (`minor_height`)
removes the scale condition. This gives `T⁵⁴ ≤ C Δ¹⁴ Ξ(a)²⁸ a¹⁶` per window, hence
`P ≪ a^{8/27 + ε}`.
-/

@[expose] public section

namespace PierceLengthBound

open Finset

variable {a b : ℕ}

section Window

/-- At the good starts, every minor is bounded by `⌊3609600 A⁴ H⁶ / a³⌋` (`minor_height`). -/
lemma goodStarts_minor_le (hba : b < a) {s T A H : ℕ}
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) (hsT : s + T ≤ P a b) :
    ∀ i ∈ goodStarts a b s T H, ∀ t,
      |plk (Mi a b i) t| ≤ ((3609600 * A ^ 4 * H ^ 6 / a ^ 3 : ℕ) : ℤ) := by
  intro i hi t
  obtain ⟨hP, hk, hb0, -⟩ := mem_goodStarts hmem hsT hi
  exact abs_le_div (pow_pos (by omega) 3) (by exact_mod_cast minor_height (A := A) hba hP hb0 hk t)

/-- **The window bound with minor vectors.** -/
theorem two_state_window_54 (hba : b < a) {s T A : ℕ}
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) (hsT : s + T ≤ P a b)
    (hT : 36 ≤ T) :
    T ≤ 24 * 14581 * (3609600 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3 + 1) ^ 5 *
      (28 * a / (A * T) + 1) * Xi a ^ 2 := by
  obtain ⟨hH29, hMb⟩ := run_height_le hba hmem (by omega) 3609600
  obtain ⟨P1, P2, P3⟩ := pbig1_bounds (by omega) hH29
    (hMb.trans (Nat.mul_le_mul_right _ (by norm_num)))
  set H : ℕ := 28 * a / (A * T) + 1 with hH
  set M : ℕ := 3609600 * A ^ 4 * H ^ 6 / a ^ 3 with hM
  have hH1 : 1 ≤ H := Nat.le_add_left 1 _
  set G := goodStarts a b s T H
  have hp := goodStarts_patternHyps (H := H) hba hmem hsT
  have hminor : ∀ i ∈ G, ∀ t, |plk (Mi a b i) t| ≤ M := goodStarts_minor_le hba hmem hsT
  set S := G.image fun i => plk (Mi a b i)
  set B := S.image projθ
  have hB : B.card ≤ 14581 * (M + 1) ^ 5 * Xi a := by
    have h1 : S.card ≤ 1 + 20 * ∑ m ∈ Icc 1 M, 729 * m ^ 4 * m.divisors.card :=
      minor_vector_count fun p hp => by
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
        exact ⟨hminor i hi, plucker _⟩
    have h2 : ∑ m ∈ Icc 1 M, 729 * m ^ 4 * m.divisors.card ≤ 729 * M ^ 5 * Xi a := by
      have hτ : ∀ m ∈ Icc 1 M, m.divisors.card ≤ Xi a := fun m hm => by
        have := (mem_Icc.mp hm).2
        exact (tau_le_tauMax (this.trans P3)).trans (tauMax_le_xiOf _ _ _)
      calc ∑ m ∈ Icc 1 M, 729 * m ^ 4 * m.divisors.card ≤ ∑ _m ∈ Icc 1 M, 729 * M ^ 4 * Xi a :=
            sum_le_sum fun m hm => by
              have := (mem_Icc.mp hm).2
              gcongr
              exact hτ m hm
        _ = 729 * M ^ 5 * Xi a := by
          rw [sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]; ring
    have h3 : M ^ 5 ≤ (M + 1) ^ 5 := Nat.pow_le_pow_left (by omega) 5
    calc B.card ≤ S.card := card_image_le
      _ ≤ 1 + 20 * (729 * M ^ 5 * Xi a) := by omega
      _ ≤ 14581 * (M + 1) ^ 5 * Xi a := by
          have : 1 ≤ (M + 1) ^ 5 * Xi a := Nat.one_le_iff_ne_zero.mpr
            (Nat.mul_ne_zero (by positivity) (Nat.pos_iff_ne_zero.mp (one_le_xiOf _ _ _)))
          nlinarith
  have hθ : ∀ i ∈ G, ∀ t, |theta a b i t| ≤ M := by
    intro i hi t
    rw [theta_eq]
    have hm := hminor i hi
    fin_cases t <;> simp only [projθ, Fin.isValue, Fin.mk_one, Matrix.cons_val_one,
        Matrix.cons_val_zero, ge_iff_le, Fin.reduceFinMk, Matrix.cons_val, abs_neg,
        Fin.zero_eta] <;> exact hm _
  have hcount := pattern_count_slice_gen (B := B) hH1
    (fun i hi => by rw [theta_eq]; exact mem_image.mpr ⟨_, mem_image.mpr ⟨i, hi, rfl⟩, rfl⟩)
    hp.inj hθ hp.gaps hp.pos0 hp.pos1 hp.e0 hp.e4 hp.e3 hp.mult (slack_le_range P1 P2)
  calc T ≤ 2 * G.card := good_card hba hmem hsT hT
    _ ≤ 2 * (4 * B.card * ((2 * H + 1) * Xi a)) := Nat.mul_le_mul_left _ hcount
    _ ≤ 2 * (4 * (14581 * (M + 1) ^ 5 * Xi a) * ((3 * H) * Xi a)) := by gcongr; omega
    _ = 24 * 14581 * (M + 1) ^ 5 * H * Xi a ^ 2 := by ring

end Window

section Exponent

/-- The constant in `window_54`. -/
def C54 : ℕ := 122449 ^ 14 + (448 * (24 * 14581)) ^ 14 +
  8 ^ 11 * (32 * (24 * 14581) * 3609600 ^ 5) * 56 ^ 31

/-- **The exponent arithmetic.** Every window run satisfies `T⁵⁴ ≤ C₅₄ Δ¹⁴ Ξ²⁸ a¹⁶`. -/
theorem window_54 {a A T Δ X : ℕ}
    (hT : 36 ≤ T) (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3) (hdrop : T * (T - 1) ≤ 4 * A * Δ)
    (hwin : T ≤ 24 * 14581 * (3609600 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3 + 1) ^ 5 *
      (28 * a / (A * T) + 1) * X ^ 2) :
    T ^ 54 ≤ C54 * Δ ^ 14 * X ^ 28 * a ^ 16 := by
  obtain ⟨hA, hΔ, ha, hT2⟩ := window_facts (by omega) hsix hdrop
  have hX : 1 ≤ X := Nat.pos_of_ne_zero fun h => by simp [h] at hwin; omega
  set H := 28 * a / (A * T) + 1 with hH
  set Y := 3609600 * A ^ 4 * H ^ 6 / a ^ 3 with hY
  have hT56 : T ^ 54 ≤ T ^ 56 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hmono : ∀ c : ℕ, c ≤ C54 → ∀ e f g : ℕ, e ≤ 14 → f ≤ 28 → g ≤ 16 →
      c * Δ ^ e * X ^ f * a ^ g ≤ C54 * Δ ^ 14 * X ^ 28 * a ^ 16 := by
    intro c hc e f g he hf hg
    have e1 : Δ ^ e ≤ Δ ^ 14 := Nat.pow_le_pow_right hΔ he
    have e2 : X ^ f ≤ X ^ 28 := Nat.pow_le_pow_right hX hf
    have e3 : a ^ g ≤ a ^ 16 := Nat.pow_le_pow_right ha hg
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hc e1) e2) e3
  by_cases hbig : 28 * a < A * T
  · have h2 := window_large_mean_gap ha hsix hbig
    calc T ^ 54 ≤ T ^ 56 := hT56
      _ = (T ^ 4) ^ 14 := by ring
      _ ≤ (122449 * a) ^ 14 := Nat.pow_le_pow_left h2 14
      _ = 122449 ^ 14 * Δ ^ 0 * X ^ 0 * a ^ 14 := by ring
      _ ≤ _ := hmono _ (by unfold C54; omega) _ _ _ (by norm_num) (by norm_num) (by norm_num)
  push Not at hbig
  have hHAT : H * (A * T) ≤ 56 * a := gap_height_mul_le hbig
  set c := 24 * 14581
  rcases Nat.eq_zero_or_pos Y with hY0 | hY1
  · rw [hY0] at hwin
    simp only [zero_add, one_pow, mul_one] at hwin
    have h1 : T ^ 2 * A ≤ 56 * c * X ^ 2 * a := by
      have : (T ^ 2 * A) * 1 ≤ (56 * c * X ^ 2 * a) * 1 := by
        calc (T ^ 2 * A) * 1 = T * (A * T) := by ring
          _ ≤ c * H * X ^ 2 * (A * T) := Nat.mul_le_mul_right _ hwin
          _ = c * X ^ 2 * (H * (A * T)) := by ring
          _ ≤ c * X ^ 2 * (56 * a) := Nat.mul_le_mul_left _ hHAT
          _ = (56 * c * X ^ 2 * a) * 1 := by ring
      omega
    have h2 : T ^ 4 ≤ 448 * c * Δ * X ^ 2 * a := by
      calc T ^ 4 = T ^ 2 * T ^ 2 := by ring
        _ ≤ (8 * A * Δ) * T ^ 2 := Nat.mul_le_mul_right _ hT2
        _ = 8 * Δ * (T ^ 2 * A) := by ring
        _ ≤ 8 * Δ * (56 * c * X ^ 2 * a) := Nat.mul_le_mul_left _ h1
        _ = 448 * c * Δ * X ^ 2 * a := by ring
    calc T ^ 54 ≤ T ^ 56 := hT56
      _ = (T ^ 4) ^ 14 := by ring
      _ ≤ (448 * c * Δ * X ^ 2 * a) ^ 14 := Nat.pow_le_pow_left h2 14
      _ = (448 * c) ^ 14 * Δ ^ 14 * X ^ 28 * a ^ 14 := by ring
      _ ≤ _ := hmono _ (by simp only [c]; unfold C54; omega) _ _ _ (by norm_num) (by norm_num)
          (by norm_num)
  · have hYa : Y * a ^ 3 ≤ 3609600 * A ^ 4 * H ^ 6 := Nat.div_mul_le_self _ _
    have hw' : T ≤ 32 * c * Y ^ 5 * H * X ^ 2 := by
      calc T ≤ c * (Y + 1) ^ 5 * H * X ^ 2 := hwin
        _ ≤ c * (2 * Y) ^ 5 * H * X ^ 2 := by
            have : (Y + 1) ^ 5 ≤ (2 * Y) ^ 5 := Nat.pow_le_pow_left (by omega) 5
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this))
        _ = 32 * c * Y ^ 5 * H * X ^ 2 := by ring
    have h1 : T * a ^ 15 ≤ 32 * c * 3609600 ^ 5 * A ^ 20 * H ^ 31 * X ^ 2 := by
      calc T * a ^ 15 ≤ 32 * c * Y ^ 5 * H * X ^ 2 * a ^ 15 := Nat.mul_le_mul_right _ hw'
        _ = 32 * c * H * X ^ 2 * (Y * a ^ 3) ^ 5 := by ring
        _ ≤ 32 * c * H * X ^ 2 * (3609600 * A ^ 4 * H ^ 6) ^ 5 := by gcongr
        _ = 32 * c * 3609600 ^ 5 * A ^ 20 * H ^ 31 * X ^ 2 := by ring
    have h2 : (T ^ 32 * A ^ 11) * (A ^ 20 * a ^ 15) ≤
        (32 * c * 3609600 ^ 5 * 56 ^ 31 * X ^ 2 * a ^ 16) * (A ^ 20 * a ^ 15) := by
      calc (T ^ 32 * A ^ 11) * (A ^ 20 * a ^ 15) = T * a ^ 15 * (A * T) ^ 31 := by ring
        _ ≤ 32 * c * 3609600 ^ 5 * A ^ 20 * H ^ 31 * X ^ 2 * (A * T) ^ 31 :=
            Nat.mul_le_mul_right _ h1
        _ = 32 * c * 3609600 ^ 5 * A ^ 20 * X ^ 2 * (H * (A * T)) ^ 31 := by ring
        _ ≤ 32 * c * 3609600 ^ 5 * A ^ 20 * X ^ 2 * (56 * a) ^ 31 := by gcongr
        _ = (32 * c * 3609600 ^ 5 * 56 ^ 31 * X ^ 2 * a ^ 16) * (A ^ 20 * a ^ 15) := by ring
    have h3 := Nat.le_of_mul_le_mul_right h2 (by positivity)
    calc T ^ 54 = T ^ 32 * (T ^ 2) ^ 11 := by ring
      _ ≤ T ^ 32 * (8 * A * Δ) ^ 11 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hT2 11)
      _ = 8 ^ 11 * Δ ^ 11 * (T ^ 32 * A ^ 11) := by ring
      _ ≤ 8 ^ 11 * Δ ^ 11 * (32 * c * 3609600 ^ 5 * 56 ^ 31 * X ^ 2 * a ^ 16) :=
          Nat.mul_le_mul_left _ h3
      _ = 8 ^ 11 * (32 * c * 3609600 ^ 5) * 56 ^ 31 * Δ ^ 11 * X ^ 2 * a ^ 16 := by ring
      _ ≤ _ := hmono _ (by simp only [c]; unfold C54; omega) _ _ _ (by norm_num) (by norm_num)
          (by norm_num)

end Exponent

section Global

/-- Every dyadic window satisfies `T ≤ 35` or `T⁵⁴ ≤ C₅₄ Δ¹⁴ Ξ(a)²⁸ a¹⁶`. -/
theorem visits_54 {a b k Δ : ℕ} (hba : b < a) (hΔ : DivBound a Δ) :
    (visits a b k).card ≤ 35 ∨ (visits a b k).card ^ 54 ≤ C54 * Δ ^ 14 * Xi a ^ 28 * a ^ 16 := by
  refine or_iff_not_imp_left.mpr fun hT => ?_
  obtain ⟨s, W, hsT⟩ := visits_run (k := k) hba.le (by omega)
  exact window_54 (by omega) (six_step_bound W (by omega)) (drop_bound W hΔ (by omega))
    (two_state_window_54 hba W.mem hsT (by omega))

/-- **Theorem.** `P(a, b) ≪_ε a^{8/27 + ε}` uniformly in `0 < b < a`. -/
theorem P_le_8_27 : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((8 : ℝ) / 27 + ε) := by
  have h := P_le_of_visits (N := 54) (r := 16) (K := C54) (by norm_num)
    (((tauMax_slow 32 7).pow 14).mul (slack_le.pow 28)) fun a b k _ hba =>
      (visits_54 (k := k) hba (tauMax_divBound a)).imp id fun h => h.trans_eq (by ring)
  norm_num at h ⊢
  exact h

end Global

end PierceLengthBound
