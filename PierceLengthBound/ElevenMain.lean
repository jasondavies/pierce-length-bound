/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ElevenCount
public import PierceLengthBound.TwentyThreeMain

/-!
# `P(a, b) ≪_ε a^{11/37 + ε}`

For a polynomial range `[1, N]`, `N = 10ᶜ aᵉ` (`PbigOf`), the slack factor
`XiOf c e a = 2 τ_max(N)³ (log₃ N + 1) + 4` collects the divisor and logarithm factors of
`norm_count` over the range, and is `O_η(a^η)` (`xiOf_slow`). `pbig_bounds` places the
quantities of a slice count in the range, and `slack_le_range` bounds their factors by those of
the range. `EightMain` and `FortyFiveMain` reuse these.

The patterns of the good starts, bounded as in `TwentyThreeMain` and counted with the ternary
quadratic of `ElevenCount`, give `T ≤ 24 (2M+1)⁷ H Ξ(a)` for a window run
(`two_state_window_74`), where `Ξ(a) = XiOf 300 100 a` for the range `P(a) = 10³⁰⁰ a¹⁰⁰`. With
the six-step and drop bounds this gives `T⁷⁴ ≤ C Δ¹⁹ Ξ(a)¹⁹ a²²` (`window_74`). Both `Δ` and
`Ξ(a)` are `O_η(a^η)`, which gives the theorem (`P_le_11_37`).

This is the `11/37` row of the table in the paper's introduction; the paper omits its proof.
-/

@[expose] public section

namespace PierceLengthBound

open Finset

/-- The polynomial range `10ᶜ aᵉ`. -/
def PbigOf (c e a : ℕ) : ℕ := 10 ^ c * a ^ e

/-- The slack factor `Ξ` of the polynomial range `10ᶜ aᵉ`: the divisor and logarithm factors of
the slice counts over `[1, 10ᶜ aᵉ]`. -/
def XiOf (c e a : ℕ) : ℕ := 2 * tauMax (PbigOf c e a) ^ 3 * (Nat.log 3 (PbigOf c e a) + 1) + 4

lemma one_le_xiOf (c e a : ℕ) : 1 ≤ XiOf c e a := by unfold XiOf; omega

lemma tauMax_le_xiOf (c e a : ℕ) : tauMax (PbigOf c e a) ≤ XiOf c e a := by
  unfold XiOf
  have : tauMax (PbigOf c e a) ≤ tauMax (PbigOf c e a) ^ 3 := Nat.le_self_pow (by norm_num) _
  nlinarith

/-- **The slack factor of a polynomial range is `O_η(a^η)`**, as `log₃ P + 1 ≤ τ*(P)`. -/
lemma xiOf_slow (c e : ℕ) : SlowGrowth (XiOf c e) := by
  refine (slowGrowth_add ((slowGrowth_const 2).mul ((tauMax_slow (10 ^ c) e).pow 4))
    (slowGrowth_const 4)).of_le fun a ha => ?_
  have hlog : Nat.log 3 (PbigOf c e a) + 1 ≤ tauMax (PbigOf c e a) :=
    (Nat.succ_le_succ (Nat.log_anti_left (by norm_num) (by norm_num))).trans
      (log_add_one_le_tauMax (Nat.mul_ne_zero (by positivity) (pow_ne_zero _ (by omega))))
  have := Nat.mul_le_mul_left (2 * tauMax (PbigOf c e a) ^ 3) hlog
  unfold XiOf
  unfold PbigOf at this ⊢
  rw [pow_succ]
  linarith

/-- The quantities of the slice counts lie in the polynomial range `[1, 10ᶜ aᵉ]` once
`K ≤ k aᵖ`, `H ≤ h a` and `M ≤ m a^q`, with constants and exponents that fit. -/
lemma pbig_bounds {c e a K H M k p h m q : ℕ} (ha : 1 ≤ a) (hk : 1 ≤ k) (hK : K ≤ k * a ^ p)
    (hH : H ≤ h * a) (hM : M ≤ m * a ^ q) (hc1 : 116 * k ^ 4 * h ^ 2 ≤ 10 ^ c)
    (hc2 : (55 * k ^ 3 * h) ^ 2 ≤ 10 ^ c) (hm : m ≤ 10 ^ c) (he1 : 4 * p + 2 ≤ e)
    (he2 : 6 * p + 2 ≤ e) (hq : q ≤ e) :
    116 * K ^ 4 * H ^ 2 ≤ PbigOf c e a ∧
      (11 * K ^ 2 * H * (3 * K + 2)) ^ 2 ≤ PbigOf c e a ∧ M ≤ PbigOf c e a := by
  have hka : 1 ≤ k * a ^ p := Nat.mul_le_mul hk (Nat.one_le_pow _ _ ha)
  unfold PbigOf
  refine ⟨?_, ?_, hM.trans (Nat.mul_le_mul hm (Nat.pow_le_pow_right ha hq))⟩
  · calc 116 * K ^ 4 * H ^ 2 ≤ 116 * (k * a ^ p) ^ 4 * (h * a) ^ 2 := by gcongr
      _ = (116 * k ^ 4 * h ^ 2) * a ^ (4 * p + 2) := by ring
      _ ≤ 10 ^ c * a ^ e := Nat.mul_le_mul hc1 (Nat.pow_le_pow_right ha he1)
  · calc (11 * K ^ 2 * H * (3 * K + 2)) ^ 2
        ≤ (11 * (k * a ^ p) ^ 2 * (h * a) * (5 * (k * a ^ p))) ^ 2 := by gcongr; omega
      _ = (55 * k ^ 3 * h) ^ 2 * a ^ (6 * p + 2) := by ring
      _ ≤ 10 ^ c * a ^ e := Nat.mul_le_mul hc2 (Nat.pow_le_pow_right ha he2)

/-- The divisor and logarithm factor of a slice count is at most that of the range `[1, N]`. -/
lemma slack_le_range {K H N : ℕ} (P1 : 116 * K ^ 4 * H ^ 2 ≤ N)
    (P2 : (11 * K ^ 2 * H * (3 * K + 2)) ^ 2 ≤ N) (M' : ℤ) (_hM' : M' ≠ 0)
    (hb : |M'| ≤ 116 * (K : ℤ) ^ 4 * (H : ℤ) ^ 2) :
    2 * M'.natAbs.divisors.card ^ 3 * (Nat.log 3 ((11 * K ^ 2 * H * (3 * K + 2)) ^ 2) + 1) ≤
      2 * tauMax N ^ 3 * (Nat.log 3 N + 1) := by
  have hτ : M'.natAbs.divisors.card ≤ tauMax N := by
    refine tau_le_tauMax (le_trans ?_ P1)
    have h' : (M'.natAbs : ℤ) ≤ ((116 * K ^ 4 * H ^ 2 : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]; push_cast; linarith
    exact_mod_cast h'
  have hlog := Nat.log_mono_right (b := 3) P2
  gcongr

/-- The polynomial range `P(a) = 10³⁰⁰ a¹⁰⁰` containing all norm-equation right sides. -/
abbrev Pbig1 : ℕ → ℕ := PbigOf 300 100

/-- The slack factor `Ξ(a)`. -/
abbrev Xi : ℕ → ℕ := XiOf 300 100

/-- **The slack factor `Ξ(a)` is `O_η(a^η)`.** -/
lemma slack_le : SlowGrowth Xi := xiOf_slow 300 100

set_option exponentiation.threshold 400 in
-- `norm_num` must evaluate the constant `10 ^ 300` of `Pbig1`.
/-- The quantities controlled by `Ξ(a)` lie in `[1, P(a)]`, for patterns of height `≤ 10¹⁶ a⁷`. -/
lemma pbig1_bounds {a M H : ℕ} (ha : 1 ≤ a) (hH : H ≤ 29 * a) (hM : M ≤ 10 ^ 16 * a ^ 7) :
    116 * (4 * M ^ 2) ^ 4 * H ^ 2 ≤ Pbig1 a ∧
      (11 * (4 * M ^ 2) ^ 2 * H * (3 * (4 * M ^ 2) + 2)) ^ 2 ≤ Pbig1 a ∧ M ≤ Pbig1 a :=
  pbig_bounds (k := 4 * 10 ^ 32) (p := 14) ha (by norm_num)
    ((Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hM 2)).trans_eq (by ring)) hH hM
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- In a window run, the gap height is `≤ 29 a` and a height `⌊c A⁴ H⁶ / a³⌋` is `≤ 29⁶ c a⁷`. -/
lemma run_height_le {a b s T A : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) (hT : 0 < T) (c : ℕ) :
    28 * a / (A * T) + 1 ≤ 29 * a ∧
      c * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3 ≤ 29 ^ 6 * c * a ^ 7 := by
  have hA : A ≤ a := by
    have := (hmem 0 hT).1; have := (orb_le a b (s + 0)).trans hba.le; omega
  have hH : 28 * a / (A * T) + 1 ≤ 29 * a := by have := Nat.div_le_self (28 * a) (A * T); omega
  refine ⟨hH, Nat.le_of_mul_le_mul_right ((Nat.div_mul_le_self _ _).trans ?_)
    (pow_pos (by omega : 0 < a) 3)⟩
  calc c * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 ≤ c * a ^ 4 * (29 * a) ^ 6 := by gcongr
    _ = 29 ^ 6 * c * a ^ 7 * a ^ 3 := by ring

section Window

variable {a b : ℕ}

/-- **The window theorem with slices.** For a window run of `T ≥ 36` terms in `[A, 2A)` and
`H = ⌊28a/(AT)⌋ + 1`, the scale condition `237568 A⁴ H⁵ ≤ a³` gives `T ≤ 24 (2M + 1)⁷ H Ξ(a)`
with `M = ⌊172032 A⁴ H⁶ / a³⌋`. -/
theorem two_state_window_74 (hba : b < a) {s T A : ℕ}
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) (hsT : s + T ≤ P a b)
    (hT : 36 ≤ T)
    (hc : 237568 * A ^ 4 * (28 * a / (A * T) + 1) ^ 5 ≤ a ^ 3) :
    T ≤ 24 * (2 * (172032 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3) + 1) ^ 7 *
      (28 * a / (A * T) + 1) * Xi a := by
  obtain ⟨hH29, hMb⟩ := run_height_le hba hmem (by omega) 172032
  obtain ⟨P1, P2, -⟩ := pbig1_bounds (by omega) hH29
    (hMb.trans (Nat.mul_le_mul_right _ (by norm_num)))
  set H : ℕ := 28 * a / (A * T) + 1 with hH
  set M : ℕ := 172032 * A ^ 4 * H ^ 6 / a ^ 3 with hM
  have hH1 : 1 ≤ H := Nat.le_add_left 1 _
  have hp := goodStarts_patternHyps (H := H) hba hmem hsT
  have hcount := pattern_count_slice hH1 hp.inj (goodStarts_theta_le hba hmem hsT hc) hp.gaps
    hp.pos0 hp.pos1 hp.e0 hp.e4 hp.e3 hp.mult (slack_le_range P1 P2)
  calc T ≤ 2 * (goodStarts a b s T H).card := good_card hba hmem hsT hT
    _ ≤ 2 * (4 * (2 * M + 1) ^ 7 * ((2 * H + 1) * Xi a)) := Nat.mul_le_mul_left _ hcount
    _ ≤ 2 * (4 * (2 * M + 1) ^ 7 * ((3 * H) * Xi a)) := by gcongr; omega
    _ = 24 * (2 * M + 1) ^ 7 * H * Xi a := by ring

end Window

section Exponent

/-- The constant in `window_74`. -/
def C74 : ℕ := 122449 ^ 19 + (8 * 237568 * 56 ^ 5) ^ 11 + 10752 ^ 19 +
  8 ^ 15 * (24 * 3 ^ 7 * 172032 ^ 7) * 56 ^ 43

/-- **The exponent arithmetic.** The six-step bound, the drop bound and the window theorem
with a slack factor `X ≥ 1` in place of `Ξ(a)` (for `T ≥ 36`) give
`T⁷⁴ ≤ C₇₄ Δ¹⁹ X¹⁹ a²²`. -/
theorem window_74 {a A T Δ X : ℕ} (hX : 1 ≤ X)
    (hT : 36 ≤ T) (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3) (hdrop : T * (T - 1) ≤ 4 * A * Δ)
    (hwin : 237568 * A ^ 4 * (28 * a / (A * T) + 1) ^ 5 ≤ a ^ 3 →
      T ≤ 24 * (2 * (172032 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3) + 1) ^ 7 *
        (28 * a / (A * T) + 1) * X) :
    T ^ 74 ≤ C74 * Δ ^ 19 * X ^ 19 * a ^ 22 := by
  obtain ⟨hA, hΔ, ha, hT2⟩ := window_facts (by omega) hsix hdrop
  set H := 28 * a / (A * T) + 1 with hH
  set M := 172032 * A ^ 4 * H ^ 6 / a ^ 3 with hM
  have hT74 : T ^ 74 ≤ T ^ 76 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hT77 : T ^ 74 ≤ T ^ 77 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hmono : ∀ c : ℕ, c ≤ C74 → ∀ e f g : ℕ, e ≤ 19 → f ≤ 19 → g ≤ 22 →
      c * Δ ^ e * X ^ f * a ^ g ≤ C74 * Δ ^ 19 * X ^ 19 * a ^ 22 := by
    intro c hc e f g he hf hg
    have e1 : Δ ^ e ≤ Δ ^ 19 := Nat.pow_le_pow_right hΔ he
    have e2 : X ^ f ≤ X ^ 19 := Nat.pow_le_pow_right hX hf
    have e3 : a ^ g ≤ a ^ 22 := Nat.pow_le_pow_right ha hg
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hc e1) e2) e3
  by_cases hbig : 28 * a < A * T
  · have h2 := window_large_mean_gap ha hsix hbig
    calc T ^ 74 ≤ T ^ 76 := hT74
      _ = (T ^ 4) ^ 19 := by ring
      _ ≤ (122449 * a) ^ 19 := Nat.pow_le_pow_left h2 19
      _ = 122449 ^ 19 * Δ ^ 0 * X ^ 0 * a ^ 19 := by ring
      _ ≤ _ := hmono _ (by unfold C74; omega) _ _ _ (by norm_num) (by norm_num) (by norm_num)
  push Not at hbig
  have hHAT : H * (A * T) ≤ 56 * a := gap_height_mul_le hbig
  by_cases hcond : 237568 * A ^ 4 * H ^ 5 ≤ a ^ 3
  · have hw := hwin hcond
    rcases Nat.eq_zero_or_pos M with hM0 | hM1
    · rw [hM0] at hw
      simp only [mul_zero, zero_add, one_pow, mul_one] at hw
      have h1 : T ^ 2 * A ≤ 1344 * X * a := by
        have : (T ^ 2 * A) * 1 ≤ (1344 * X * a) * 1 := by
          calc (T ^ 2 * A) * 1 = T * (A * T) := by ring
            _ ≤ 24 * H * X * (A * T) := Nat.mul_le_mul_right _ hw
            _ = 24 * X * (H * (A * T)) := by ring
            _ ≤ 24 * X * (56 * a) := Nat.mul_le_mul_left _ hHAT
            _ = (1344 * X * a) * 1 := by ring
        omega
      have h2 : T ^ 4 ≤ 10752 * Δ * X * a := by
        calc T ^ 4 = T ^ 2 * T ^ 2 := by ring
          _ ≤ (8 * A * Δ) * T ^ 2 := Nat.mul_le_mul_right _ hT2
          _ = 8 * Δ * (T ^ 2 * A) := by ring
          _ ≤ 8 * Δ * (1344 * X * a) := Nat.mul_le_mul_left _ h1
          _ = 10752 * Δ * X * a := by ring
      calc T ^ 74 ≤ T ^ 76 := hT74
        _ = (T ^ 4) ^ 19 := by ring
        _ ≤ (10752 * Δ * X * a) ^ 19 := Nat.pow_le_pow_left h2 19
        _ = 10752 ^ 19 * Δ ^ 19 * X ^ 19 * a ^ 19 := by ring
        _ ≤ _ := hmono _ (by unfold C74; omega) _ _ _ (by norm_num) (by norm_num) (by norm_num)
    · have hMa : M * a ^ 3 ≤ 172032 * A ^ 4 * H ^ 6 := Nat.div_mul_le_self _ _
      have h3M : 2 * M + 1 ≤ 3 * M := by omega
      have hw' : T ≤ 24 * 3 ^ 7 * M ^ 7 * H * X := by
        calc T ≤ 24 * (2 * M + 1) ^ 7 * H * X := hw
          _ ≤ 24 * (3 * M) ^ 7 * H * X := by gcongr
          _ = 24 * 3 ^ 7 * M ^ 7 * H * X := by ring
      have h1 : T * a ^ 21 ≤ 24 * 3 ^ 7 * 172032 ^ 7 * A ^ 28 * H ^ 43 * X := by
        calc T * a ^ 21 ≤ 24 * 3 ^ 7 * M ^ 7 * H * X * a ^ 21 := Nat.mul_le_mul_right _ hw'
          _ = 24 * 3 ^ 7 * H * X * (M * a ^ 3) ^ 7 := by ring
          _ ≤ 24 * 3 ^ 7 * H * X * (172032 * A ^ 4 * H ^ 6) ^ 7 := by gcongr
          _ = 24 * 3 ^ 7 * 172032 ^ 7 * A ^ 28 * H ^ 43 * X := by ring
      have h2 : (T ^ 44 * A ^ 15) * (A ^ 28 * a ^ 21) ≤
          (24 * 3 ^ 7 * 172032 ^ 7 * 56 ^ 43 * X * a ^ 22) * (A ^ 28 * a ^ 21) := by
        calc (T ^ 44 * A ^ 15) * (A ^ 28 * a ^ 21) = T * a ^ 21 * (A * T) ^ 43 := by ring
          _ ≤ 24 * 3 ^ 7 * 172032 ^ 7 * A ^ 28 * H ^ 43 * X * (A * T) ^ 43 :=
              Nat.mul_le_mul_right _ h1
          _ = 24 * 3 ^ 7 * 172032 ^ 7 * A ^ 28 * X * (H * (A * T)) ^ 43 := by ring
          _ ≤ 24 * 3 ^ 7 * 172032 ^ 7 * A ^ 28 * X * (56 * a) ^ 43 := by gcongr
          _ = (24 * 3 ^ 7 * 172032 ^ 7 * 56 ^ 43 * X * a ^ 22) * (A ^ 28 * a ^ 21) := by ring
      have h3 := Nat.le_of_mul_le_mul_right h2 (by positivity)
      calc T ^ 74 = T ^ 44 * (T ^ 2) ^ 15 := by ring
        _ ≤ T ^ 44 * (8 * A * Δ) ^ 15 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hT2 15)
        _ = 8 ^ 15 * Δ ^ 15 * (T ^ 44 * A ^ 15) := by ring
        _ ≤ 8 ^ 15 * Δ ^ 15 * (24 * 3 ^ 7 * 172032 ^ 7 * 56 ^ 43 * X * a ^ 22) :=
            Nat.mul_le_mul_left _ h3
        _ = 8 ^ 15 * (24 * 3 ^ 7 * 172032 ^ 7) * 56 ^ 43 * Δ ^ 15 * X ^ 1 * a ^ 22 := by ring
        _ ≤ _ := hmono _ (by unfold C74; omega) _ _ _ (by norm_num) (by norm_num) (by norm_num)
  · push Not at hcond
    have h1 : (A * T ^ 5) * (A ^ 4 * a ^ 3) ≤ (237568 * 56 ^ 5 * a ^ 2) * (A ^ 4 * a ^ 3) := by
      calc (A * T ^ 5) * (A ^ 4 * a ^ 3) = a ^ 3 * (A * T) ^ 5 := by ring
        _ ≤ 237568 * A ^ 4 * H ^ 5 * (A * T) ^ 5 := Nat.mul_le_mul_right _ hcond.le
        _ = 237568 * A ^ 4 * (H * (A * T)) ^ 5 := by ring
        _ ≤ 237568 * A ^ 4 * (56 * a) ^ 5 := by gcongr
        _ = (237568 * 56 ^ 5 * a ^ 2) * (A ^ 4 * a ^ 3) := by ring
    have h2 := Nat.le_of_mul_le_mul_right h1 (by positivity)
    have h3 : T ^ 7 ≤ 8 * 237568 * 56 ^ 5 * Δ * a ^ 2 := by
      calc T ^ 7 = T ^ 5 * T ^ 2 := by ring
        _ ≤ T ^ 5 * (8 * A * Δ) := Nat.mul_le_mul_left _ hT2
        _ = 8 * Δ * (A * T ^ 5) := by ring
        _ ≤ 8 * Δ * (237568 * 56 ^ 5 * a ^ 2) := Nat.mul_le_mul_left _ h2
        _ = 8 * 237568 * 56 ^ 5 * Δ * a ^ 2 := by ring
    calc T ^ 74 ≤ T ^ 77 := hT77
      _ = (T ^ 7) ^ 11 := by ring
      _ ≤ (8 * 237568 * 56 ^ 5 * Δ * a ^ 2) ^ 11 := Nat.pow_le_pow_left h3 11
      _ = (8 * 237568 * 56 ^ 5) ^ 11 * Δ ^ 11 * X ^ 0 * a ^ 22 := by ring
      _ ≤ _ := hmono _ (by unfold C74; omega) _ _ _ (by norm_num) (by norm_num) (by norm_num)

end Exponent

section Global

/-- Every dyadic window satisfies `T ≤ 35` or `T⁷⁴ ≤ C₇₄ Δ¹⁹ Ξ(a)¹⁹ a²²`. -/
theorem visits_74 {a b k Δ : ℕ} (hba : b < a) (hΔ : DivBound a Δ) :
    (visits a b k).card ≤ 35 ∨ (visits a b k).card ^ 74 ≤ C74 * Δ ^ 19 * Xi a ^ 19 * a ^ 22 := by
  refine or_iff_not_imp_left.mpr fun hT => ?_
  obtain ⟨s, W, hsT⟩ := visits_run (k := k) hba.le (by omega)
  exact window_74 (one_le_xiOf _ _ _) (by omega) (six_step_bound W (by omega))
    (drop_bound W hΔ (by omega)) (fun hc => two_state_window_74 hba W.mem hsT (by omega) hc)

/-- **Theorem.** `P(a, b) ≪_ε a^{11/37 + ε}` uniformly in `0 < b < a`. -/
theorem P_le_11_37 : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((11 : ℝ) / 37 + ε) := by
  have h := P_le_of_visits (N := 74) (r := 22) (K := C74) (by norm_num)
    ((tauMax_two_mul_slow.pow 19).mul (slack_le.pow 19)) fun a b k _ hba =>
      (visits_74 (k := k) hba (tauMax_divBound a)).imp id fun h => h.trans_eq (by ring)
  norm_num at h ⊢
  exact h

end Global

end PierceLengthBound
