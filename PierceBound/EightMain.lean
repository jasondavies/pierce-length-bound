import PierceBound.MinorHeight
import PierceBound.ElevenMain

/-!
# `P(a, b) ≪_ε a^{8/27 + ε}`

The seven pattern integers are signed coordinates of the vector of ten minors of `𝓜ᵢ`
(`theta_eq`). Counting minor vectors (`minor_vector_count`) instead of seven independent
integers replaces `X⁷` by `X⁵ τ`, and the uniform minor bound (`minor_height`) removes the scale
condition. This gives `T⁵⁴ ≤ C Δ¹⁴ Ξ(a)²⁸ a¹⁶` per window, hence `P ≪ a^{8/27 + ε}`.
-/

namespace PierceBound

open Finset

variable {a b : ℕ}

/-- The pattern as signed minors. -/
def projθ (p : Fin 10 → ℤ) : Fin 7 → ℤ := ![p 0, p 6, p 9, p 3, -p 1, p 8, -p 7]

theorem theta_eq (i : ℕ) : theta a b i = projθ (plk (Mi a b i)) := by
  funext t
  fin_cases t <;>
  simp [theta, projθ, plk, Mi, trip, minor3, Lz, U1z, U2z, sixL, pU1, pU2, rq, sq, kq, dq,
    Nat.add_assoc] <;> ring

set_option exponentiation.threshold 400 in
/-- The polynomial range bound for patterns of height `≤ 10¹⁶ a⁷`. -/
lemma pbig_bounds16 {a M H : ℕ} (ha : 1 ≤ a) (hH : H ≤ 29 * a) (hM : M ≤ 10 ^ 16 * a ^ 7) :
    116 * (4 * M ^ 2) ^ 4 * H ^ 2 ≤ Pbig a ∧
      (11 * (4 * M ^ 2) ^ 2 * H * (3 * (4 * M ^ 2) + 2)) ^ 2 ≤ Pbig a ∧ M ≤ Pbig a := by
  have hK : 4 * M ^ 2 ≤ 4 * 10 ^ 32 * a ^ 14 := by
    calc 4 * M ^ 2 ≤ 4 * (10 ^ 16 * a ^ 7) ^ 2 := by gcongr
      _ = 4 * 10 ^ 32 * a ^ 14 := by ring
  have ha1 : 1 ≤ a ^ 14 := Nat.one_le_pow _ _ ha
  have hP : Pbig a = 10 ^ 300 * a ^ 100 := rfl
  have hmono : ∀ k, k ≤ 100 → a ^ k ≤ a ^ 100 := fun k hk => Nat.pow_le_pow_right ha hk
  refine ⟨?_, ?_, ?_⟩
  · calc 116 * (4 * M ^ 2) ^ 4 * H ^ 2 ≤ 116 * (4 * 10 ^ 32 * a ^ 14) ^ 4 * (29 * a) ^ 2 := by
          gcongr
      _ = (116 * 4 ^ 4 * 10 ^ 128 * 29 ^ 2) * a ^ 58 := by ring
      _ ≤ 10 ^ 300 * a ^ 100 := Nat.mul_le_mul (by norm_num) (hmono 58 (by norm_num))
      _ = Pbig a := hP.symm
  · have h3 : 3 * (4 * M ^ 2) + 2 ≤ 5 * (4 * 10 ^ 32 * a ^ 14) := by
      have : 1 ≤ 4 * 10 ^ 32 * a ^ 14 := by nlinarith
      omega
    calc (11 * (4 * M ^ 2) ^ 2 * H * (3 * (4 * M ^ 2) + 2)) ^ 2
        ≤ (11 * (4 * 10 ^ 32 * a ^ 14) ^ 2 * (29 * a) * (5 * (4 * 10 ^ 32 * a ^ 14))) ^ 2 := by
          gcongr
      _ = (11 * 16 * 10 ^ 64 * 29 * 20 * 10 ^ 32) ^ 2 * a ^ 86 := by ring
      _ ≤ 10 ^ 300 * a ^ 100 := Nat.mul_le_mul (by norm_num) (hmono 86 (by norm_num))
      _ = Pbig a := hP.symm
  · calc M ≤ 10 ^ 16 * a ^ 7 := hM
      _ ≤ 10 ^ 300 * a ^ 100 := Nat.mul_le_mul (by norm_num) (hmono 7 (by norm_num))
      _ = Pbig a := hP.symm

lemma tau_le_tauMax {n X : ℕ} (h : n ≤ X) : n.divisors.card ≤ tauMax X :=
  le_sup (f := fun n => n.divisors.card) (mem_range.mpr (by omega))

section Window

/-- **The window bound with minor vectors.** -/
theorem two_state_window_eight (hba : b < a) {s T A : ℕ} (hA : 1 ≤ A)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) (hsT : s + T ≤ P a b)
    (hT : 36 ≤ T) :
    T ≤ 24 * 14581 * (3609600 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3 + 1) ^ 5 *
      (28 * a / (A * T) + 1) * Xi a ^ 2 := by
  set H : ℕ := 28 * a / (A * T) + 1 with hH
  set M : ℕ := 3609600 * A ^ 4 * H ^ 6 / a ^ 3 with hM
  set G := (Ico s (s + T)).filter fun i => i + 9 ≤ s + T ∧
    ∀ m ∈ range 7, kq a b (i + m) ≤ (H : ℤ)
  have hgood := good_card hba hA hmem hsT hT
  have ha : 0 < a := by omega
  have ha3 : 0 < a ^ 3 := by positivity
  have facts : ∀ i ∈ G, i + 8 < P a b ∧ (∀ m, m < 7 → 1 ≤ kq a b (i + m) ∧ kq a b (i + m) ≤ H) ∧
      orb a b i < 2 * A ∧ orb a b (i + 1) < 2 * A ∧ orb a b (i + 2) < 2 * A := by
    intro i hi
    obtain ⟨hiI, h9, hk⟩ := mem_filter.mp hi
    have := mem_Ico.mp hiI
    refine ⟨by omega, fun m hm => ⟨kq_pos (by omega), hk m (mem_range.mpr hm)⟩, ?_, ?_, ?_⟩
    · have := (hmem (i - s) (by omega)).2; rwa [show s + (i - s) = i by omega] at this
    · have := (hmem (i + 1 - s) (by omega)).2; rwa [show s + (i + 1 - s) = i + 1 by omega] at this
    · have := (hmem (i + 2 - s) (by omega)).2; rwa [show s + (i + 2 - s) = i + 2 by omega] at this
  have hH1 : 1 ≤ H := by rw [hH]; exact Nat.le_add_left 1 _
  have hH29 : H ≤ 29 * a := by
    have : 28 * a / (A * T) ≤ 28 * a := Nat.div_le_self _ _
    omega
  have hA_a : A ≤ a := by
    have := (hmem 0 (by omega)).1
    have := (orb_le a b (s + 0)).trans hba.le
    omega
  have hMb : M ≤ 10 ^ 16 * a ^ 7 := by
    have h1 : M * a ^ 3 ≤ 3609600 * A ^ 4 * H ^ 6 := Nat.div_mul_le_self _ _
    have h2 : 3609600 * A ^ 4 * H ^ 6 ≤ 3609600 * a ^ 4 * (29 * a) ^ 6 := by gcongr
    have h3 : M * a ^ 3 ≤ (10 ^ 16 * a ^ 7) * a ^ 3 := by
      calc M * a ^ 3 ≤ 3609600 * a ^ 4 * (29 * a) ^ 6 := h1.trans h2
        _ = 2147074259481600 * a ^ 7 * a ^ 3 := by ring
        _ ≤ (10 ^ 16 * a ^ 7) * a ^ 3 := by gcongr; norm_num
    exact Nat.le_of_mul_le_mul_right h3 (by positivity)
  obtain ⟨P1, P2, P3⟩ := pbig_bounds16 (by omega) hH29 hMb
  -- every minor is bounded by `M`
  have hminor : ∀ i ∈ G, ∀ t, |plk (Mi a b i) t| ≤ M := by
    intro i hi t
    obtain ⟨hP, hk, hb0, -, -⟩ := facts i hi
    exact abs_le_div ha3 (by exact_mod_cast minor_height (A := A) hba hP hb0 hk t)
  set S := G.image fun i => plk (Mi a b i)
  set B := S.image projθ
  have hXi1 : 1 ≤ Xi a := by unfold Xi; omega
  have hB : B.card ≤ 14581 * (M + 1) ^ 5 * Xi a := by
    have h1 : S.card ≤ 1 + 20 * ∑ m ∈ Icc 1 M, 729 * m ^ 4 * m.divisors.card :=
      minor_vector_count fun p hp => by
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
        exact ⟨hminor i hi, plucker _⟩
    have h2 : ∑ m ∈ Icc 1 M, 729 * m ^ 4 * m.divisors.card ≤ 729 * M ^ 5 * Xi a := by
      have hτ : ∀ m ∈ Icc 1 M, m.divisors.card ≤ Xi a := fun m hm => by
        have := (mem_Icc.mp hm).2
        calc m.divisors.card ≤ tauMax (Pbig a) := tau_le_tauMax (this.trans P3)
          _ ≤ Xi a := by
              unfold Xi
              have : tauMax (Pbig a) ≤ tauMax (Pbig a) ^ 3 := Nat.le_self_pow (by norm_num) _
              nlinarith
      calc ∑ m ∈ Icc 1 M, 729 * m ^ 4 * m.divisors.card ≤ ∑ _m ∈ Icc 1 M, 729 * M ^ 4 * Xi a :=
            sum_le_sum fun m hm => by
              have := (mem_Icc.mp hm).2
              gcongr
              exact hτ m hm
        _ = 729 * M ^ 5 * Xi a := by rw [sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]; ring
    have h3 : M ^ 5 ≤ (M + 1) ^ 5 := Nat.pow_le_pow_left (by omega) 5
    calc B.card ≤ S.card := card_image_le
      _ ≤ 1 + 20 * (729 * M ^ 5 * Xi a) := by omega
      _ ≤ 14581 * (M + 1) ^ 5 * Xi a := by
          have : 1 ≤ (M + 1) ^ 5 * Xi a := Nat.one_le_iff_ne_zero.mpr (by positivity)
          nlinarith
  have hcount := pattern_count_gen (G := G) (θ := theta a b) (κ := kap a b)
    (Q := fun i => (qq a b i : ℤ)) (a := (a : ℤ)) (M := M) (H := H) (B := B)
    (W := 2 * tauMax (Pbig a) ^ 3 * (Nat.log 3 (Pbig a) + 1)) hH1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have hg2 : T ≤ 2 * G.card := hgood
    have hXi : 2 * tauMax (Pbig a) ^ 3 * (Nat.log 3 (Pbig a) + 1) + 4 = Xi a := rfl
    rw [hXi] at hcount
    calc T ≤ 2 * G.card := hg2
      _ ≤ 2 * (4 * B.card * ((2 * H + 1) * Xi a)) := Nat.mul_le_mul_left _ hcount
      _ ≤ 2 * (4 * (14581 * (M + 1) ^ 5 * Xi a) * ((3 * H) * Xi a)) := by
          gcongr; omega
      _ = 24 * 14581 * (M + 1) ^ 5 * H * Xi a ^ 2 := by ring
  -- the patterns lie in `B`
  · intro i hi
    rw [theta_eq]
    exact mem_image.mpr ⟨_, mem_image.mpr ⟨i, hi, rfl⟩, rfl⟩
  -- injectivity of the quotient
  · intro i hi i' hi' h
    have hP := (facts i hi).1
    have hP' := (facts i' hi').1
    simp only [Nat.cast_inj] at h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (qq_strictMono (a := a) (b := b) hlt (by omega)).ne h
    · exact (qq_strictMono (a := a) (b := b) hlt (by omega)).ne h.symm
  -- the pattern bound
  · intro i hi t
    rw [theta_eq]
    have hm := hminor i hi
    fin_cases t <;> simp [projθ] <;> exact hm _
  -- the gaps
  · intro i hi t
    obtain ⟨-, hk, -⟩ := facts i hi
    fin_cases t
    · simpa [kap] using hk 0 (by norm_num)
    · simpa [kap] using hk 1 (by norm_num)
    · simpa [kap] using hk 2 (by norm_num)
    · simpa [kap] using hk 3 (by norm_num)
    · simpa [kap] using hk 4 (by norm_num)
  · intro i hi; simpa [theta] using Lz_pos hba (i := i) (by have := (facts i hi).1; omega)
  · intro i hi; simpa [theta] using Lz_pos hba (i := i + 1) (by have := (facts i hi).1; omega)
  · intro i _; simpa [theta, kap] using e0_at (a := a) (b := b) i
  · intro i _; simpa [theta, kap, add_assoc] using e0_at (a := a) (b := b) (i + 1)
  · intro i _; simpa [theta, kap] using e3_at (a := a) (b := b) i
  · intro i hi; simpa [theta, kap] using mult_at (a := a) (b := b) (i := i)
      (by have := (facts i hi).1; omega)
  -- the divisor and logarithm bounds
  · intro M' hM' hb
    have hτ : M'.natAbs.divisors.card ≤ tauMax (Pbig a) := by
      refine tau_le_tauMax ?_
      have : M'.natAbs ≤ 116 * (4 * M ^ 2) ^ 4 * H ^ 2 := by
        have h' : (M'.natAbs : ℤ) ≤ ((116 * (4 * M ^ 2) ^ 4 * H ^ 2 : ℕ) : ℤ) := by
          rw [Int.natCast_natAbs]; push_cast at hb ⊢; linarith
        exact_mod_cast h'
      omega
    have hlog : Nat.log 3 ((11 * (4 * M ^ 2) ^ 2 * H * (3 * (4 * M ^ 2) + 2)) ^ 2) ≤
        Nat.log 3 (Pbig a) := Nat.log_mono_right P2
    gcongr

end Window

section Exponent

/-- The constant in `window_54`. -/
def C54 : ℕ := 122449 ^ 14 + (448 * (24 * 14581)) ^ 14 +
  8 ^ 11 * (32 * (24 * 14581) * 3609600 ^ 5) * 56 ^ 31

/-- **The exponent arithmetic.** Every window run satisfies `T⁵⁴ ≤ C₅₄ Δ¹⁴ Ξ²⁸ a¹⁶`. -/
theorem window_54 {a A T Δ X : ℕ} (ha : 1 ≤ a) (hA : 1 ≤ A) (hΔ : 1 ≤ Δ) (hX : 1 ≤ X)
    (hT : 36 ≤ T) (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3) (hdrop : T * (T - 1) ≤ 4 * A * Δ)
    (hwin : T ≤ 24 * 14581 * (3609600 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3 + 1) ^ 5 *
      (28 * a / (A * T) + 1) * X ^ 2) :
    T ^ 54 ≤ C54 * Δ ^ 14 * X ^ 28 * a ^ 16 := by
  set H := 28 * a / (A * T) + 1 with hH
  set Y := 3609600 * A ^ 4 * H ^ 6 / a ^ 3 with hY
  have ha0 : 0 < a := by omega
  have hT2 : T ^ 2 ≤ 8 * A * Δ := by
    have : T ^ 2 ≤ 2 * (T * (T - 1)) := by
      have : T ≤ 2 * (T - 1) := by omega
      calc T ^ 2 = T * T := pow_two T
        _ ≤ T * (2 * (T - 1)) := Nat.mul_le_mul_left _ this
        _ = 2 * (T * (T - 1)) := by ring
    calc T ^ 2 ≤ 2 * (T * (T - 1)) := this
      _ ≤ 2 * (4 * A * Δ) := Nat.mul_le_mul_left _ hdrop
      _ = 8 * A * Δ := by ring
  have hT56 : T ^ 54 ≤ T ^ 56 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hmono : ∀ c : ℕ, c ≤ C54 → ∀ e f g : ℕ, e ≤ 14 → f ≤ 28 → g ≤ 16 →
      c * Δ ^ e * X ^ f * a ^ g ≤ C54 * Δ ^ 14 * X ^ 28 * a ^ 16 := by
    intro c hc e f g he hf hg
    have e1 : Δ ^ e ≤ Δ ^ 14 := Nat.pow_le_pow_right hΔ he
    have e2 : X ^ f ≤ X ^ 28 := Nat.pow_le_pow_right hX hf
    have e3 : a ^ g ≤ a ^ 16 := Nat.pow_le_pow_right ha hg
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hc e1) e2) e3
  by_cases hbig : 28 * a < A * T
  · have h1 : (28 * a) ^ 2 * T ^ 4 ≤ 96000000 * a ^ 3 := by
      calc (28 * a) ^ 2 * T ^ 4 ≤ (A * T) ^ 2 * T ^ 4 :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hbig.le 2)
        _ = T ^ 6 * A ^ 2 := by ring
        _ ≤ _ := hsix
    have h2 : T ^ 4 ≤ 122449 * a := by
      have : (784 * T ^ 4) * a ^ 2 ≤ (784 * (122449 * a)) * a ^ 2 := by
        calc (784 * T ^ 4) * a ^ 2 = (28 * a) ^ 2 * T ^ 4 := by ring
          _ ≤ 96000000 * a ^ 3 := h1
          _ ≤ (784 * (122449 * a)) * a ^ 2 := by ring_nf; omega
      have := Nat.le_of_mul_le_mul_right this (by positivity)
      omega
    calc T ^ 54 ≤ T ^ 56 := hT56
      _ = (T ^ 4) ^ 14 := by ring
      _ ≤ (122449 * a) ^ 14 := Nat.pow_le_pow_left h2 14
      _ = 122449 ^ 14 * Δ ^ 0 * X ^ 0 * a ^ 14 := by ring
      _ ≤ _ := hmono _ (by unfold C54; omega) _ _ _ (by norm_num) (by norm_num) (by norm_num)
  push Not at hbig
  have hHAT : H * (A * T) ≤ 56 * a := by
    have := Nat.div_mul_le_self (28 * a) (A * T)
    calc H * (A * T) = 28 * a / (A * T) * (A * T) + A * T := by rw [hH]; ring
      _ ≤ 56 * a := by omega
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
theorem visits_54 {a b k Δ : ℕ} (hba : b < a) (hΔ : DivBound a Δ) (hΔ1 : 1 ≤ Δ) :
    (visits a b k).card ≤ 35 ∨ (visits a b k).card ^ 54 ≤ C54 * Δ ^ 14 * Xi a ^ 28 * a ^ 16 := by
  by_cases hT : (visits a b k).card ≤ 35
  · exact Or.inl hT
  right
  set T := (visits a b k).card
  have hne : (visits a b k).Nonempty := by rw [← card_pos]; omega
  have W := visits_window hba.le hne
  set s := (visits a b k).min' hne
  have hmem : ∀ j < T, 2 ^ k ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * 2 ^ k := W.mem
  have hsT : s + T ≤ P a b := by
    have h := (hmem (T - 1) (by omega)).1
    have := lt_P_of_orb_pos (a := a) (b := b) (i := s + (T - 1))
      (lt_of_lt_of_le (Nat.two_pow_pos k) h)
    omega
  exact window_54 (by omega) Nat.one_le_two_pow hΔ1 (by unfold Xi; omega) (by omega)
    (six_step_bound W (by omega)) (drop_bound W hΔ (by omega))
    (two_state_window_eight hba Nat.one_le_two_pow hmem hsT (by omega))

/-- **Theorem.** `P(a, b) ≪_ε a^{8/27 + ε}` uniformly in `0 < b < a`. -/
theorem P_le_8_27 : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((8 : ℝ) / 27 + ε) := by
  intro ε hε
  obtain ⟨Cs, hCs, hslack⟩ := slack_le (ε / 4) (by positivity)
  obtain ⟨CL, hCL, hlog⟩ := log_add_one_le_rpow (ε / 2) (by positivity)
  set K : ℝ := (C54 : ℝ) * Cs ^ 42
  set C2 : ℝ := K ^ ((54 : ℝ)⁻¹)
  have hK : 0 < K := by
    have : (0 : ℝ) < C54 := by unfold C54; positivity
    positivity
  have hC2 : 0 ≤ C2 := by positivity
  refine ⟨CL * (35 + C2), by positivity, fun a b hb hba => ?_⟩
  have ha1 : 1 ≤ a := by omega
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  set Δ := tauMax (32 * a ^ 7)
  have hΔ : DivBound a Δ := fun n _ hn =>
    le_sup (f := fun n => n.divisors.card) (mem_range.mpr (by omega))
  have hΔ1 : 1 ≤ Δ := by
    have h7 : 1 ≤ a ^ 7 := Nat.one_le_pow _ _ ha1
    have h1 : (1 : ℕ).divisors.card ≤ Δ :=
      le_sup (f := fun n => n.divisors.card) (mem_range.mpr (by omega))
    rw [Nat.divisors_one, card_singleton] at h1
    exact h1
  obtain ⟨hsΔ, hsX⟩ := hslack a ha1
  set β : ℝ := 8 / 27 + ε / 2
  have hβ : 1 ≤ (a : ℝ) ^ β := Real.one_le_rpow ha (by positivity)
  have hwin : ∀ k, ((visits a b k).card : ℝ) ≤ (35 + C2) * (a : ℝ) ^ β := by
    intro k
    rcases visits_54 (k := k) hba hΔ hΔ1 with h | h
    · have : ((visits a b k).card : ℝ) ≤ 35 := by exact_mod_cast h
      nlinarith
    · set T := (visits a b k).card
      have hTr : (T : ℝ) ^ 54 ≤ K * (a : ℝ) ^ (16 + 42 * (ε / 4)) := by
        have h' : (T : ℝ) ^ 54 ≤ (C54 : ℝ) * (Δ : ℝ) ^ 14 * (Xi a : ℝ) ^ 28 * (a : ℝ) ^ 16 := by
          exact_mod_cast h
        have p1 : (Δ : ℝ) ^ 14 ≤ (Cs * (a : ℝ) ^ (ε / 4)) ^ 14 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hsΔ 14
        have p2 : (Xi a : ℝ) ^ 28 ≤ (Cs * (a : ℝ) ^ (ε / 4)) ^ 28 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hsX 28
        have q1 : ((a : ℝ) ^ (ε / 4)) ^ 42 = (a : ℝ) ^ (42 * (ε / 4)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num; ring_nf
        have q2 : (a : ℝ) ^ (16 : ℕ) = (a : ℝ) ^ (16 : ℝ) := by
          rw [← Real.rpow_natCast]; norm_num
        calc (T : ℝ) ^ 54 ≤ (C54 : ℝ) * (Δ : ℝ) ^ 14 * (Xi a : ℝ) ^ 28 * (a : ℝ) ^ 16 := h'
          _ ≤ (C54 : ℝ) * (Cs * (a : ℝ) ^ (ε / 4)) ^ 14 * (Cs * (a : ℝ) ^ (ε / 4)) ^ 28 *
              (a : ℝ) ^ 16 := by gcongr
          _ = (C54 : ℝ) * Cs ^ 42 * ((a : ℝ) ^ (ε / 4)) ^ 42 * (a : ℝ) ^ (16 : ℕ) := by ring
          _ = K * (a : ℝ) ^ (16 + 42 * (ε / 4)) := by
              rw [q1, q2, Real.rpow_add (by positivity)]; simp only [K]; ring
      have hroot : (T : ℝ) ≤ C2 * (a : ℝ) ^ ((16 + 42 * (ε / 4)) / 54) := by
        have h1 : ((T : ℝ) ^ 54) ^ ((54 : ℝ)⁻¹) ≤
            (K * (a : ℝ) ^ (16 + 42 * (ε / 4))) ^ ((54 : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) hTr (by positivity)
        rw [show (54 : ℝ) = ((54 : ℕ) : ℝ) by norm_num, Real.pow_rpow_inv_natCast (Nat.cast_nonneg _)
          (by norm_num), Real.mul_rpow hK.le (by positivity), ← Real.rpow_mul (by positivity)] at h1
        simp only [C2]
        convert h1 using 2
        all_goals norm_num
        all_goals (congr 1; ring)
      have hexp : (16 + 42 * (ε / 4)) / 54 ≤ β := by simp only [β]; nlinarith
      have := Real.rpow_le_rpow_of_exponent_le ha hexp
      nlinarith [mul_le_mul_of_nonneg_left this hC2]
  have hP : (P a b : ℝ) ≤ ((Nat.log 2 a + 1 : ℕ) : ℝ) * ((35 + C2) * (a : ℝ) ^ β) := by
    rw [P_eq_sum_visits hba.le]
    push_cast
    calc ∑ k ∈ range (Nat.log 2 a + 1), ((visits a b k).card : ℝ)
        ≤ ∑ _k ∈ range (Nat.log 2 a + 1), (35 + C2) * (a : ℝ) ^ β :=
          sum_le_sum fun k _ => hwin k
      _ = _ := by simp
  have hL := hlog a ha1
  calc (P a b : ℝ) ≤ ((Nat.log 2 a + 1 : ℕ) : ℝ) * ((35 + C2) * (a : ℝ) ^ β) := hP
    _ ≤ (CL * (a : ℝ) ^ (ε / 2)) * ((35 + C2) * (a : ℝ) ^ β) :=
        mul_le_mul_of_nonneg_right hL (by positivity)
    _ = CL * (35 + C2) * ((a : ℝ) ^ (ε / 2) * (a : ℝ) ^ β) := by ring
    _ = CL * (35 + C2) * (a : ℝ) ^ ((8 : ℝ) / 27 + ε) := by
        rw [← Real.rpow_add (by positivity)]
        congr 2
        simp only [β]; ring

end Global

end PierceBound
