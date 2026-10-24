/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PatternBound
public import PierceLengthBound.PatternCount
public import PierceLengthBound.Main
public import PierceLengthBound.OrbitPattern

/-!
# `P(a, b) ≪_ε a^{23/77 + ε}`

As in `OrbitPattern`, for an orbit state `i` put `kᵢ = q_{i+1} - qᵢ`, `dᵢ = bᵢ - b_{i+1}`
(`kq`, `dq`), the six-step integer `L(i)` (`Lz`, equal to `I₄(i)`), and the cofactors `U₁(i)`,
`U₂(i)`. The *pattern* of `i` is `θ(i) = (L(i), L(i+1), L(i+2), U₁(i), U₂(i), U₁(i+1), U₂(i+1))
∈ ℤ⁷` and its gaps are `κ(i) = (kᵢ, …, k_{i+4})`.

In a window run of `T ≥ 36` terms in `[A, 2A)` take `H = ⌊28a/(AT)⌋ + 1`. At least `T/2`
starts have their next seven increments `≤ H` (`good_card`, Lemma 7.6 of the paper). The label
bound in window form (`label_at`, Lemmas 7.4 and 2.4) and `state_bound` show that, if
`237568 A⁴ H⁵ ≤ a³`, their patterns are bounded by `M = ⌊172032 A⁴ H⁶ / a³⌋`
(`goodStarts_theta_le`), so the counting lemma `pattern_count` gives `T ≤ 16 (2M+1)⁷ H²`
(`two_state_window_77`). Combined with the six-step bound and the drop bound, every window has
`T⁷⁷ ≤ C₇₇ Δ²² a²³` (`window_77`, `visits_77`), and the dyadic decomposition gives the theorem
(`P_le_23_77`).

This is the `23/77` row of the table in the paper's introduction; the paper omits its proof.
-/

@[expose] public section

namespace PierceLengthBound

open Finset

section State

variable {a b : ℕ}

/-- **The label bound in window form** (Lemmas 7.4 and 2.4). If `bᵢ < 2A`, then
`L(i) a³ ≤ 256 A⁴ 𝒢(kᵢ, …, k_{i+4})`, where `𝒢 = gramP`. -/
lemma label_at {A i : ℕ} (hba : b < a) (h : i + 6 < P a b) (hi : orb a b i < 2 * A) :
    Lz a b i * (a : ℤ) ^ 3 ≤ 256 * (A : ℤ) ^ 4 *
      gramP (kq a b i) (kq a b (i + 1)) (kq a b (i + 2)) (kq a b (i + 3)) (kq a b (i + 4)) := by
  have hl := label_bound hba h
  have h4 := a_le_four hba (by omega : i + 1 < P a b) hi
  have hL := Lz_pos hba (i := i) (by omega)
  have ha : (0 : ℤ) < a := by exact_mod_cast (show 0 < a by omega)
  change Lz a b i * (qq a b i : ℤ) ^ 4 ≤ a * gramP (kq a b i) (kq a b (i + 1)) (kq a b (i + 2))
    (kq a b (i + 3)) (kq a b (i + 4)) at hl
  have h4' : (a : ℤ) ≤ 4 * A * qq a b i := by exact_mod_cast h4
  have hp : (a : ℤ) ^ 4 ≤ (4 * A * qq a b i) ^ 4 := pow_le_pow_left₀ ha.le h4' 4
  have : Lz a b i * (a : ℤ) ^ 4 ≤ 256 * (A : ℤ) ^ 4 * (a *
      gramP (kq a b i) (kq a b (i + 1)) (kq a b (i + 2)) (kq a b (i + 3)) (kq a b (i + 4))) := by
    calc Lz a b i * (a : ℤ) ^ 4 ≤ Lz a b i * (4 * A * qq a b i) ^ 4 :=
          mul_le_mul_of_nonneg_left hp (by linarith)
      _ = 256 * (A : ℤ) ^ 4 * (Lz a b i * (qq a b i : ℤ) ^ 4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
  have : (Lz a b i * (a : ℤ) ^ 3) * a ≤ (256 * (A : ℤ) ^ 4 *
      gramP (kq a b i) (kq a b (i + 1)) (kq a b (i + 2)) (kq a b (i + 3)) (kq a b (i + 4)))
          * a := by
    calc (Lz a b i * (a : ℤ) ^ 3) * a = Lz a b i * (a : ℤ) ^ 4 := by ring
      _ ≤ _ := this
      _ = _ := by ring
  exact le_of_mul_le_mul_right this ha

end State

section Window

variable {a b : ℕ}

/-- **The pattern height.** Under the scale condition `237568 A⁴ H⁵ ≤ a³`, the patterns at the
good starts have height `≤ ⌊172032 A⁴ H⁶ / a³⌋` (`state_bound`). -/
theorem goodStarts_theta_le (hba : b < a) {s T A H : ℕ}
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) (hsT : s + T ≤ P a b)
    (hc : 237568 * A ^ 4 * H ^ 5 ≤ a ^ 3) :
    ∀ i ∈ goodStarts a b s T H, ∀ t,
      |theta a b i t| ≤ ((172032 * A ^ 4 * H ^ 6 / a ^ 3 : ℕ) : ℤ) := by
  intro i hi t
  obtain ⟨hP, hk, hb0, hb1, hb2⟩ := mem_goodStarts hmem hsT hi
  have hcZ : (237568 : ℤ) * (A : ℤ) ^ 4 * (H : ℤ) ^ 5 ≤ (a : ℤ) ^ 3 := by exact_mod_cast hc
  have hAZ : (1 : ℤ) ≤ A := by exact_mod_cast (show 1 ≤ A by omega)
  have K := fun m (hm : m < 7) => hk m hm
  have L0 := label_at (A := A) hba (i := i) (by omega) hb0
  have L1 := label_at (A := A) hba (i := i + 1) (by omega) hb1
  have L2 := label_at (A := A) hba (i := i + 2) (by omega) hb2
  have P0 := Lz_pos hba (i := i) (by omega)
  have P1 := Lz_pos hba (i := i + 1) (by omega)
  have P2 := Lz_pos hba (i := i + 2) (by omega)
  have SB0 := state_bound (K 0 (by norm_num)).1 (K 1 (by norm_num)).1 (K 2 (by norm_num)).1
    (K 3 (by norm_num)).1 (K 4 (by norm_num)).1 (K 5 (by norm_num)).1 (K 0 (by norm_num)).2
    (K 1 (by norm_num)).2 (K 2 (by norm_num)).2 (K 3 (by norm_num)).2 (K 4 (by norm_num)).2
    (K 5 (by norm_num)).2 hAZ P0 P1 L0 L1 hcZ (e0_at i) (e3_at i)
  have SB1 := state_bound (K 1 (by norm_num)).1 (K 2 (by norm_num)).1 (K 3 (by norm_num)).1
    (K 4 (by norm_num)).1 (K 5 (by norm_num)).1 (K 6 (by norm_num)).1 (K 1 (by norm_num)).2
    (K 2 (by norm_num)).2 (K 3 (by norm_num)).2 (K 4 (by norm_num)).2 (K 5 (by norm_num)).2
    (K 6 (by norm_num)).2 hAZ P1 P2 L1 L2 hcZ (e0_at (i + 1)) (e3_at (i + 1))
  have cv : ∀ z : ℤ, |z| * (a : ℤ) ^ 3 ≤ 172032 * (A : ℤ) ^ 4 * (H : ℤ) ^ 6 →
      |z| ≤ ((172032 * A ^ 4 * H ^ 6 / a ^ 3 : ℕ) : ℤ) :=
    fun z hz => abs_le_div (pow_pos (by omega) 3) (by exact_mod_cast hz)
  have cvL : ∀ z : ℤ, 1 ≤ z → z * (a : ℤ) ^ 3 ≤ 172032 * (A : ℤ) ^ 4 * (H : ℤ) ^ 6 →
      |z| ≤ ((172032 * A ^ 4 * H ^ 6 / a ^ 3 : ℕ) : ℤ) :=
    fun z hz h => cv z (by rwa [abs_of_pos (by omega)])
  fin_cases t
  · exact cvL _ P0 SB0.2.2.1
  · exact cvL _ P1 SB0.2.2.2
  · exact cvL _ P2 SB1.2.2.2
  · exact cv _ SB0.1
  · exact cv _ SB0.2.1
  · exact cv _ SB1.1
  · exact cv _ SB1.2.1

/-- **The window theorem.** For a window run of `T ≥ 36` terms in `[A, 2A)` and
`H = ⌊28a/(AT)⌋ + 1`, the scale condition `237568 A⁴ H⁵ ≤ a³` gives `T ≤ 16 (2M + 1)⁷ H²` with
`M = ⌊172032 A⁴ H⁶ / a³⌋`. -/
theorem two_state_window_77 (hba : b < a) {s T A : ℕ}
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) (hsT : s + T ≤ P a b)
    (hT : 36 ≤ T)
    (hc : 237568 * A ^ 4 * (28 * a / (A * T) + 1) ^ 5 ≤ a ^ 3) :
    T ≤ 16 * (2 * (172032 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3) + 1) ^ 7 *
      (28 * a / (A * T) + 1) ^ 2 := by
  have hp := goodStarts_patternHyps (H := 28 * a / (A * T) + 1) hba hmem hsT
  have hcount := pattern_count hp.inj (goodStarts_theta_le hba hmem hsT hc) hp.gaps hp.pos0
    hp.pos1 hp.e0 hp.e4 hp.e3 hp.mult
  calc T ≤ 2 * (goodStarts a b s T (28 * a / (A * T) + 1)).card := good_card hba hmem hsT hT
    _ ≤ 2 * (8 * (2 * (172032 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3) + 1) ^ 7 *
        (28 * a / (A * T) + 1) ^ 2) := Nat.mul_le_mul_left _ hcount
    _ = _ := by ring

end Window

section Exponent

/-- The constant in `window_77`. -/
def C77 : ℕ := 122449 ^ 20 + (8 * 237568 * 56 ^ 5) ^ 11 + (64 * 50176) ^ 11 +
  8 ^ 16 * (16 * 3 ^ 7 * 172032 ^ 7) * 56 ^ 44

/-- **The exponent arithmetic.** The six-step bound, the drop bound and the window theorem
(for `T ≥ 36`) give `T⁷⁷ ≤ C₇₇ Δ²² a²³`. -/
theorem window_77 {a A T Δ : ℕ} (hT : 36 ≤ T)
    (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3) (hdrop : T * (T - 1) ≤ 4 * A * Δ)
    (hwin : 237568 * A ^ 4 * (28 * a / (A * T) + 1) ^ 5 ≤ a ^ 3 →
      T ≤ 16 * (2 * (172032 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3) + 1) ^ 7 *
        (28 * a / (A * T) + 1) ^ 2) :
    T ^ 77 ≤ C77 * Δ ^ 22 * a ^ 23 := by
  obtain ⟨hA, hΔ, ha, hT2⟩ := window_facts (by omega) hsix hdrop
  set H := 28 * a / (A * T) + 1 with hH
  set M := 172032 * A ^ 4 * H ^ 6 / a ^ 3 with hM
  have hC : ∀ c : ℕ, c ≤ C77 → ∀ x : ℕ, x ≤ c * Δ ^ 22 * a ^ 23 →
      x ≤ C77 * Δ ^ 22 * a ^ 23 := fun c hc x hx =>
    hx.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc))
  by_cases hbig : 28 * a < A * T
  · have h2 := window_large_mean_gap ha hsix hbig
    have h3 : T ≤ 122449 * a :=
      (Nat.le_self_pow (by norm_num) T).trans h2
    refine hC (122449 ^ 20) (by unfold C77; omega) _ ?_
    calc T ^ 77 = (T ^ 4) ^ 19 * T := by ring
      _ ≤ (122449 * a) ^ 19 * (122449 * a) := Nat.mul_le_mul (Nat.pow_le_pow_left h2 19) h3
      _ = 122449 ^ 20 * 1 * a ^ 20 := by ring
      _ ≤ 122449 ^ 20 * Δ ^ 22 * a ^ 23 := by
          gcongr
          · exact Nat.one_le_pow _ _ hΔ
          · omega
  push Not at hbig
  have hHAT : H * (A * T) ≤ 56 * a := gap_height_mul_le hbig
  by_cases hcond : 237568 * A ^ 4 * H ^ 5 ≤ a ^ 3
  · have hw := hwin hcond
    rcases Nat.eq_zero_or_pos M with hM0 | hM1
    · -- `M = 0`
      rw [hM0] at hw
      simp only [mul_zero, zero_add, one_pow, mul_one] at hw
      have h1 : T * (A * T) ^ 2 ≤ 50176 * a ^ 2 := by
        calc T * (A * T) ^ 2 ≤ 16 * H ^ 2 * (A * T) ^ 2 := Nat.mul_le_mul_right _ hw
          _ = 16 * (H * (A * T)) ^ 2 := by ring
          _ ≤ 16 * (56 * a) ^ 2 := by gcongr
          _ = 50176 * a ^ 2 := by ring
      have h2 : T ^ 7 ≤ 64 * 50176 * Δ ^ 2 * a ^ 2 := by
        calc T ^ 7 = T ^ 3 * (T ^ 2) ^ 2 := by ring
          _ ≤ T ^ 3 * (8 * A * Δ) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hT2 2)
          _ = 64 * Δ ^ 2 * (T * (A * T) ^ 2) := by ring
          _ ≤ 64 * Δ ^ 2 * (50176 * a ^ 2) := Nat.mul_le_mul_left _ h1
          _ = 64 * 50176 * Δ ^ 2 * a ^ 2 := by ring
      refine hC ((64 * 50176) ^ 11) (by unfold C77; omega) _ ?_
      calc T ^ 77 = (T ^ 7) ^ 11 := by ring
        _ ≤ (64 * 50176 * Δ ^ 2 * a ^ 2) ^ 11 := Nat.pow_le_pow_left h2 11
        _ = (64 * 50176) ^ 11 * Δ ^ 22 * a ^ 22 := by ring
        _ ≤ (64 * 50176) ^ 11 * Δ ^ 22 * a ^ 23 := by gcongr; omega
    · -- `M ≥ 1`
      have hMa : M * a ^ 3 ≤ 172032 * A ^ 4 * H ^ 6 := Nat.div_mul_le_self _ _
      have h3M : 2 * M + 1 ≤ 3 * M := by omega
      have hw' : T ≤ 16 * 3 ^ 7 * M ^ 7 * H ^ 2 := by
        calc T ≤ 16 * (2 * M + 1) ^ 7 * H ^ 2 := hw
          _ ≤ 16 * (3 * M) ^ 7 * H ^ 2 := by gcongr
          _ = 16 * 3 ^ 7 * M ^ 7 * H ^ 2 := by ring
      have h1 : T * a ^ 21 ≤ 16 * 3 ^ 7 * 172032 ^ 7 * A ^ 28 * H ^ 44 := by
        calc T * a ^ 21 ≤ 16 * 3 ^ 7 * M ^ 7 * H ^ 2 * a ^ 21 := Nat.mul_le_mul_right _ hw'
          _ = 16 * 3 ^ 7 * H ^ 2 * (M * a ^ 3) ^ 7 := by ring
          _ ≤ 16 * 3 ^ 7 * H ^ 2 * (172032 * A ^ 4 * H ^ 6) ^ 7 := by gcongr
          _ = 16 * 3 ^ 7 * 172032 ^ 7 * A ^ 28 * H ^ 44 := by ring
      have h2 : (T ^ 45 * A ^ 16) * (A ^ 28 * a ^ 21) ≤
          (16 * 3 ^ 7 * 172032 ^ 7 * 56 ^ 44 * a ^ 23) * (A ^ 28 * a ^ 21) := by
        calc (T ^ 45 * A ^ 16) * (A ^ 28 * a ^ 21) = T * a ^ 21 * (A * T) ^ 44 := by ring
          _ ≤ 16 * 3 ^ 7 * 172032 ^ 7 * A ^ 28 * H ^ 44 * (A * T) ^ 44 :=
              Nat.mul_le_mul_right _ h1
          _ = 16 * 3 ^ 7 * 172032 ^ 7 * A ^ 28 * (H * (A * T)) ^ 44 := by ring
          _ ≤ 16 * 3 ^ 7 * 172032 ^ 7 * A ^ 28 * (56 * a) ^ 44 := by gcongr
          _ = (16 * 3 ^ 7 * 172032 ^ 7 * 56 ^ 44 * a ^ 23) * (A ^ 28 * a ^ 21) := by ring
      have h3 := Nat.le_of_mul_le_mul_right h2 (by positivity)
      refine hC (8 ^ 16 * (16 * 3 ^ 7 * 172032 ^ 7) * 56 ^ 44) (by unfold C77; omega) _ ?_
      calc T ^ 77 = T ^ 45 * (T ^ 2) ^ 16 := by ring
        _ ≤ T ^ 45 * (8 * A * Δ) ^ 16 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hT2 16)
        _ = 8 ^ 16 * Δ ^ 16 * (T ^ 45 * A ^ 16) := by ring
        _ ≤ 8 ^ 16 * Δ ^ 16 * (16 * 3 ^ 7 * 172032 ^ 7 * 56 ^ 44 * a ^ 23) :=
            Nat.mul_le_mul_left _ h3
        _ = 8 ^ 16 * (16 * 3 ^ 7 * 172032 ^ 7) * 56 ^ 44 * Δ ^ 16 * a ^ 23 := by ring
        _ ≤ 8 ^ 16 * (16 * 3 ^ 7 * 172032 ^ 7) * 56 ^ 44 * Δ ^ 22 * a ^ 23 := by
            gcongr; norm_num
  · -- the scale condition fails
    push Not at hcond
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
    refine hC ((8 * 237568 * 56 ^ 5) ^ 11) (by unfold C77; omega) _ ?_
    calc T ^ 77 = (T ^ 7) ^ 11 := by ring
      _ ≤ (8 * 237568 * 56 ^ 5 * Δ * a ^ 2) ^ 11 := Nat.pow_le_pow_left h3 11
      _ = (8 * 237568 * 56 ^ 5) ^ 11 * Δ ^ 11 * a ^ 22 := by ring
      _ ≤ (8 * 237568 * 56 ^ 5) ^ 11 * Δ ^ 22 * a ^ 23 := by
          gcongr <;> norm_num

/-- Every dyadic window satisfies `T ≤ 35` or `T⁷⁷ ≤ C₇₇ Δ²² a²³`. -/
theorem visits_77 {a b k Δ : ℕ} (hba : b < a) (hΔ : DivBound a Δ) :
    (visits a b k).card ≤ 35 ∨ (visits a b k).card ^ 77 ≤ C77 * Δ ^ 22 * a ^ 23 := by
  refine or_iff_not_imp_left.mpr fun hT => ?_
  obtain ⟨s, W, hsT⟩ := visits_run (k := k) hba.le (by omega)
  exact window_77 (by omega) (six_step_bound W (by omega)) (drop_bound W hΔ (by omega))
    (fun hc => two_state_window_77 hba W.mem hsT (by omega) hc)

/-- **Theorem.** `P(a, b) ≪_ε a^{23/77 + ε}` uniformly in `0 < b < a`. -/
theorem P_le_23_77 : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((23 : ℝ) / 77 + ε) := by
  simpa only [Nat.cast_ofNat] using P_le_of_visits (N := 77) (r := 23) (K := C77) (by norm_num)
    (tauMax_two_mul_slow.pow 22) fun a b k _ hba => visits_77 (k := k) hba (tauMax_divBound a)

end Exponent

end PierceLengthBound
