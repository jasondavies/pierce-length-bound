/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ShortSum
public import PierceLengthBound.Geometric
public import PierceLengthBound.Main

/-!
# `P(a, b) ≪ a^{3/10} G(a)^{1/5}` from a short-interval divisor bound

`ShortDivisorBound G` says that, for `x ≥ x₀`, `x^{1/4} ≤ y ≤ x` and `A ≥ 1`,
`∑_{x < n ≤ x + y} #{d ∣ n : A ≤ d < 2A} ≤ C y G(x)`.

From it, each window run satisfies both `T ≪ a^{1/2} A^{-1/3}` (`six_step_bound`, no
hypothesis) and `T ≪ (G(a) A)^{1/2} + G(a) a^{1/4}` (`drop_count_bound'`). Summing the minimum
over the dyadic ranges (`sum_min_le`) gives `P(a, b) ≪ a^{3/10} G(a)^{1/5}`
(`P_le_of_shortDivisorBound`).
-/

@[expose] public section

namespace PierceLengthBound

open Finset

/-- A uniform bound for the number of divisors in `[A, 2A)` over short intervals. -/
def ShortDivisorBound (G : ℕ → ℝ) : Prop :=
  ∃ C x₀ : ℝ, 0 < C ∧ ∀ x y A : ℕ, x₀ ≤ x → (x : ℝ) ^ (1 / 4 : ℝ) ≤ y → y ≤ x → 1 ≤ A →
    (∑ n ∈ Ioc x (x + y), (dcount A n : ℝ)) ≤ C * y * G x

/-- Solving `T(T-1) ≤ c(2A + β₀(T-1))`: `T ≤ 2cβ₀ + √(8cA)`. -/
lemma quadratic_solve {T c β₀ H A : ℝ} (hT : 2 ≤ T) (hc : 0 ≤ c) (hβ : 0 ≤ β₀)
    (h1 : T ≤ c * (H + β₀)) (h2 : H * (T - 1) ≤ 2 * A) :
    T ≤ 2 * c * β₀ + Real.sqrt (8 * c * A) := by
  have hTT : T * (T - 1) ≤ c * (2 * A + β₀ * (T - 1)) := by
    have := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ T - 1)
    nlinarith
  by_cases hsmall : T ≤ 2 * c * β₀
  · have := Real.sqrt_nonneg (8 * c * A); linarith
  · push Not at hsmall
    have h3 : T ^ 2 ≤ 8 * c * A := by nlinarith
    have : T ≤ Real.sqrt (8 * c * A) := Real.le_sqrt_of_sq_le h3
    nlinarith

/-- `T^6 A² ≤ K a³` gives `T ≤ K^{1/6} a^{1/2} A^{-1/3}`. -/
lemma six_root {T A a K : ℕ} (hA : 1 ≤ A) (h : T ^ 6 * A ^ 2 ≤ K * a ^ 3) :
    (T : ℝ) ≤ (K : ℝ) ^ (1 / 6 : ℝ) * (a : ℝ) ^ (1 / 2 : ℝ) * (A : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  have e1 : ((K : ℝ) ^ (1 / 6 : ℝ)) ^ 6 = K := by
    rw [← Real.rpow_mul_natCast (by positivity)]; norm_num
  have e2 : ((a : ℝ) ^ (1 / 2 : ℝ)) ^ 6 = (a : ℝ) ^ 3 := by
    rw [← Real.rpow_mul_natCast (by positivity)]; norm_num
  have e3 : ((A : ℝ) ^ (-(1 / 3 : ℝ))) ^ 6 * (A : ℝ) ^ 2 = 1 := by
    rw [← Real.rpow_mul_natCast (by positivity), ← Real.rpow_natCast (A : ℝ) 2,
      ← Real.rpow_add hA']
    norm_num
  have hR : 0 ≤ (K : ℝ) ^ (1 / 6 : ℝ) * (a : ℝ) ^ (1 / 2 : ℝ) * (A : ℝ) ^ (-(1 / 3 : ℝ)) := by
    positivity
  have hR6 : ((K : ℝ) ^ (1 / 6 : ℝ) * (a : ℝ) ^ (1 / 2 : ℝ) * (A : ℝ) ^ (-(1 / 3 : ℝ))) ^ 6 *
      (A : ℝ) ^ 2 = (K : ℝ) * (a : ℝ) ^ 3 := by
    rw [mul_pow, mul_pow, e1, e2, mul_assoc, e3, mul_one]
  have h' : (T : ℝ) ^ 6 * (A : ℝ) ^ 2 ≤
      ((K : ℝ) ^ (1 / 6 : ℝ) * (a : ℝ) ^ (1 / 2 : ℝ) * (A : ℝ) ^ (-(1 / 3 : ℝ))) ^ 6 *
        (A : ℝ) ^ 2 := by
    rw [hR6]; exact_mod_cast h
  have h6 := le_of_mul_le_mul_right h' (by positivity)
  exact (pow_le_pow_iff_left₀ (by positivity) hR (by norm_num)).mp h6

/-- **One window, both bounds.** For `x₀ ≤ a`, the number of visits to `[2^k, 2^{k+1})` is at
most `19 + γ + min(α (2^k)^{-1/3}, β (2^k)^{1/2})`. -/
theorem visits_real_bound {G : ℕ → ℝ} {C x₀ : ℝ} (hC : 0 < C)
    (hshort : ∀ x y A : ℕ, x₀ ≤ x → (x : ℝ) ^ (1 / 4 : ℝ) ≤ y → y ≤ x → 1 ≤ A →
      (∑ n ∈ Ioc x (x + y), (dcount A n : ℝ)) ≤ C * y * G x)
    (hG1 : ∀ x, 1 ≤ G x) {a b k : ℕ} (hba : b ≤ a) (ha : 1 ≤ a) (hx₀ : x₀ ≤ a) :
    ((visits a b k).card : ℝ) ≤ 19 + 4 * C * G a * ((a : ℝ) ^ (1 / 4 : ℝ) + 1) +
      min (((96000000 : ℕ) : ℝ) ^ (1 / 6 : ℝ) * (a : ℝ) ^ (1 / 2 : ℝ) *
          ((2 : ℝ) ^ k) ^ (-(1 / 3 : ℝ)))
        (4 * Real.sqrt (C * G a) * ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ)) := by
  set T := (visits a b k).card with hTdef
  have hG := hG1 a
  have hγ : 0 ≤ 4 * C * G a * ((a : ℝ) ^ (1 / 4 : ℝ) + 1) := by positivity
  by_cases hT : T ≤ 19
  · have : (T : ℝ) ≤ 19 := by exact_mod_cast hT
    have : 0 ≤ min (((96000000 : ℕ) : ℝ) ^ (1 / 6 : ℝ) * (a : ℝ) ^ (1 / 2 : ℝ) *
          ((2 : ℝ) ^ k) ^ (-(1 / 3 : ℝ)))
        (4 * Real.sqrt (C * G a) * ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ)) := le_min (by positivity)
          (by positivity)
    linarith
  have hne : (visits a b k).Nonempty := by rw [← card_pos]; omega
  have W := visits_window hba hne
  set A := 2 ^ k with hA
  have hA1 : 1 ≤ A := Nat.one_le_two_pow
  have hAa : A ≤ a := (W.mem 0 (by omega)).1.trans (W.le_a 0 (by omega))
  -- bound (i): six steps
  have h6 := six_step_bound W (by omega)
  have b1 := six_root hA1 h6
  push_cast [hA] at b1
  -- bound (ii): drops and the short-interval hypothesis
  set H := 2 * A / (T - 1) with hH
  set Y := max H ⌈(a : ℝ) ^ (1 / 4 : ℝ)⌉₊ with hY
  have hHa : H ≤ a := by
    have : H ≤ A := Nat.div_le_of_le_mul (by
      have : 2 ≤ T - 1 := by omega
      nlinarith)
    omega
  have hroot : (a : ℝ) ^ (1 / 4 : ℝ) ≤ a := by
    have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
    calc (a : ℝ) ^ (1 / 4 : ℝ) ≤ (a : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le ha' (by norm_num)
      _ = a := Real.rpow_one _
  have hceil : ⌈(a : ℝ) ^ (1 / 4 : ℝ)⌉₊ ≤ a := Nat.ceil_le.mpr hroot
  have hYa : Y ≤ a := max_le hHa hceil
  have hYlo : (a : ℝ) ^ (1 / 4 : ℝ) ≤ Y :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right H _)
  have hdrop := drop_count_bound' (Y := Y) W (by omega) (le_max_left _ _)
  have hsum := hshort a Y A hx₀ hYlo (by exact_mod_cast hYa) hA1
  have hT2 : (T : ℝ) ≤ 2 * C * G a * ((H : ℝ) + ((a : ℝ) ^ (1 / 4 : ℝ) + 1)) := by
    have e1 : (T : ℝ) ≤ 2 * ∑ n ∈ Ioc a (a + Y), (dcount A n : ℝ) := by exact_mod_cast hdrop
    have e2 : (Y : ℝ) ≤ H + ((a : ℝ) ^ (1 / 4 : ℝ) + 1) := by
      have : (Y : ℝ) ≤ (H : ℝ) + (⌈(a : ℝ) ^ (1 / 4 : ℝ)⌉₊ : ℝ) := by
        have : Y ≤ H + ⌈(a : ℝ) ^ (1 / 4 : ℝ)⌉₊ :=
          max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
        exact_mod_cast this
      have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (a : ℝ) ^ (1 / 4 : ℝ) by positivity)
      linarith
    have hCG : 0 ≤ C * G a := by positivity
    calc (T : ℝ) ≤ 2 * (C * Y * G a) := by linarith
      _ = 2 * (C * G a) * Y := by ring
      _ ≤ 2 * (C * G a) * (H + ((a : ℝ) ^ (1 / 4 : ℝ) + 1)) := by gcongr
      _ = _ := by ring
  have hHT : (H : ℝ) * ((T : ℝ) - 1) ≤ 2 * A := by
    have : H * (T - 1) ≤ 2 * A := Nat.div_mul_le_self _ _
    have h' : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [← h']; exact_mod_cast this
  have b2 := quadratic_solve (T := T) (c := 2 * C * G a) (β₀ := (a : ℝ) ^ (1 / 4 : ℝ) + 1)
    (H := H) (A := A) (by exact_mod_cast (show 2 ≤ T by omega)) (by positivity) (by positivity) hT2
        hHT
  have hsq : Real.sqrt (8 * (2 * C * G a) * A) = 4 * Real.sqrt (C * G a)
      * (A : ℝ) ^ (1 / 2 : ℝ) := by
    rw [show 8 * (2 * C * G a) * A = 4 ^ 2 * ((C * G a) * A) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num),
      Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow (A : ℝ)]
    ring
  rw [hsq] at b2
  push_cast [hA] at b2
  have : (T : ℝ) ≤ 4 * C * G a * ((a : ℝ) ^ (1 / 4 : ℝ) + 1) +
      min (((96000000 : ℕ) : ℝ) ^ (1 / 6 : ℝ) * (a : ℝ) ^ (1 / 2 : ℝ) *
          ((2 : ℝ) ^ k) ^ (-(1 / 3 : ℝ)))
        (4 * Real.sqrt (C * G a) * ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ)) := by
    rcases le_total (((96000000 : ℕ) : ℝ) ^ (1 / 6 : ℝ) * (a : ℝ) ^ (1 / 2 : ℝ) *
          ((2 : ℝ) ^ k) ^ (-(1 / 3 : ℝ)))
        (4 * Real.sqrt (C * G a) * ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ)) with hm | hm
    · rw [min_eq_left hm]; push_cast at b1 ⊢; linarith
    · rw [min_eq_right hm]; linarith
  linarith

/-- **The conditional theorem.** A short-interval divisor bound with growth `G` gives
`P(a, b) ≪ a^{3/10} G(a)^{1/5}`. -/
theorem P_le_of_shortDivisorBound {G : ℕ → ℝ} (hG : ShortDivisorBound G) (hG1 : ∀ x, 1 ≤ G x)
    (hGs : ∃ C' : ℝ, ∀ x : ℕ, 1 ≤ x → G x ≤ C' * (x : ℝ) ^ (1 / 40 : ℝ)) :
    ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ (3 / 10 : ℝ) * G a ^ (1 / 5 : ℝ) := by
  obtain ⟨C, x₀, hC, hshort⟩ := hG
  obtain ⟨C', hC'⟩ := hGs
  obtain ⟨CL, hCL, hlog⟩ := log_add_one_le_rpow (1 / 100) (by norm_num)
  obtain ⟨K6, hK6d⟩ : ∃ K6 : ℝ, K6 = ((96000000 : ℕ) : ℝ) ^ (1 / 6 : ℝ) := ⟨_, rfl⟩
  have hK6 : 0 < K6 := by rw [hK6d]; positivity
  set C'' : ℝ := max C' 1
  set N0 : ℝ := max x₀ 1
  set Cbig : ℝ := 19 * CL + 8 * CL * C * C'' ^ (4 / 5 : ℝ) +
    9 * (K6 ^ (3 / 5 : ℝ) * (4 : ℝ) ^ (2 / 5 : ℝ) * C ^ (1 / 5 : ℝ)) + N0
  have hN0 : 1 ≤ N0 := le_max_right _ _
  refine ⟨Cbig, by positivity, fun a b hb hba => ?_⟩
  have ha1 : 1 ≤ a := by omega
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have ha0 : (0 : ℝ) < a := by linarith
  have hGa := hG1 a
  have hG5 : 1 ≤ G a ^ (1 / 5 : ℝ) := Real.one_le_rpow hGa (by norm_num)
  have ha310 : 1 ≤ (a : ℝ) ^ (3 / 10 : ℝ) := Real.one_le_rpow ha (by norm_num)
  have hmain0 : 0 ≤ (a : ℝ) ^ (3 / 10 : ℝ) * G a ^ (1 / 5 : ℝ) := by positivity
  have hone : 1 ≤ (a : ℝ) ^ (3 / 10 : ℝ) * G a ^ (1 / 5 : ℝ) := by nlinarith
  have hCbig : N0 ≤ Cbig := by
    have : 0 ≤ 19 * CL + 8 * CL * C * C'' ^ (4 / 5 : ℝ) +
        9 * (K6 ^ (3 / 5 : ℝ) * (4 : ℝ) ^ (2 / 5 : ℝ) * C ^ (1 / 5 : ℝ)) := by positivity
    simp only [Cbig]; linarith
  -- small `a`
  by_cases hsmall : (a : ℝ) < x₀
  · have hP : (P a b : ℝ) ≤ a := by exact_mod_cast (P_le_self a b).trans hba.le
    calc (P a b : ℝ) ≤ N0 := hP.trans (le_max_of_le_left hsmall.le)
      _ ≤ Cbig := hCbig
      _ = Cbig * 1 := by ring
      _ ≤ Cbig * ((a : ℝ) ^ (3 / 10 : ℝ) * G a ^ (1 / 5 : ℝ)) := by gcongr
      _ = _ := by ring
  push Not at hsmall
  -- the window bounds
  set γ : ℝ := 4 * C * G a * ((a : ℝ) ^ (1 / 4 : ℝ) + 1)
  set α : ℝ := K6 * (a : ℝ) ^ (1 / 2 : ℝ)
  set β : ℝ := 4 * Real.sqrt (C * G a)
  have hα : 0 < α := by positivity
  have hβ : 0 < β := by
    have : 0 < C * G a := by positivity
    positivity
  set L := Nat.log 2 a + 1
  have hP : (P a b : ℝ) ≤ L * (19 + γ) + 9 * (α ^ (3 / 5 : ℝ) * β ^ (2 / 5 : ℝ)) := by
    rw [P_eq_sum_visits hba.le]
    push_cast
    calc ∑ k ∈ range L, ((visits a b k).card : ℝ)
        ≤ ∑ k ∈ range L, ((19 + γ) + min (α * ((2 : ℝ) ^ k) ^ (-(1 / 3 : ℝ)))
            (β * ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ))) := by
          refine sum_le_sum fun k _ => ?_
          have := visits_real_bound (k := k) hC hshort hG1 hba.le ha1 hsmall
          rw [← hK6d] at this
          simp only [γ, α, β]
          linarith
      _ = L * (19 + γ) + ∑ k ∈ range L, min (α * ((2 : ℝ) ^ k) ^ (-(1 / 3 : ℝ)))
            (β * ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ)) := by
          rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
      _ ≤ L * (19 + γ) + 9 * (α ^ (3 / 5 : ℝ) * β ^ (2 / 5 : ℝ)) := by
          gcongr; exact sum_min_le hα hβ L
  -- the main term
  have hmain : α ^ (3 / 5 : ℝ) * β ^ (2 / 5 : ℝ) =
      K6 ^ (3 / 5 : ℝ) * (4 : ℝ) ^ (2 / 5 : ℝ) * C ^ (1 / 5 : ℝ) *
        ((a : ℝ) ^ (3 / 10 : ℝ) * G a ^ (1 / 5 : ℝ)) := by
    have e1 : α ^ (3 / 5 : ℝ) = K6 ^ (3 / 5 : ℝ) * (a : ℝ) ^ (3 / 10 : ℝ) := by
      simp only [α]
      rw [Real.mul_rpow hK6.le (by positivity), ← Real.rpow_mul (by positivity)]
      norm_num
    have e2 : β ^ (2 / 5 : ℝ) = (4 : ℝ) ^ (2 / 5 : ℝ) * (C ^ (1 / 5 : ℝ) * G a ^ (1 / 5 : ℝ)) := by
      simp only [β]
      rw [Real.mul_rpow (by norm_num) (by positivity), Real.sqrt_eq_rpow,
        ← Real.rpow_mul (by positivity), Real.mul_rpow hC.le (by linarith)]
      norm_num
    rw [e1, e2]
    ring
  -- the secondary terms
  have hLa : (L : ℝ) ≤ CL * (a : ℝ) ^ (1 / 100 : ℝ) := hlog a ha1
  have hG45 : G a ^ (4 / 5 : ℝ) ≤ C'' ^ (4 / 5 : ℝ) * (a : ℝ) ^ (1 / 50 : ℝ) := by
    have h1 : G a ≤ C'' * (a : ℝ) ^ (1 / 40 : ℝ) :=
      (hC' a ha1).trans (by gcongr; exact le_max_left _ _)
    calc G a ^ (4 / 5 : ℝ) ≤ (C'' * (a : ℝ) ^ (1 / 40 : ℝ)) ^ (4 / 5 : ℝ) :=
          Real.rpow_le_rpow (by linarith) h1 (by norm_num)
      _ = C'' ^ (4 / 5 : ℝ) * (a : ℝ) ^ (1 / 50 : ℝ) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)]
          norm_num
  have hGsplit : G a = G a ^ (1 / 5 : ℝ) * G a ^ (4 / 5 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have hγle : γ ≤ 8 * C * C'' ^ (4 / 5 : ℝ) * ((a : ℝ) ^ (1 / 50 : ℝ) * (a : ℝ) ^ (1 / 4 : ℝ)) *
      G a ^ (1 / 5 : ℝ) := by
    have h14 : 1 ≤ (a : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow ha (by norm_num)
    have : γ ≤ 8 * C * G a * (a : ℝ) ^ (1 / 4 : ℝ) := by
      simp only [γ]
      have : 0 ≤ C * G a := by positivity
      nlinarith
    calc γ ≤ 8 * C * G a * (a : ℝ) ^ (1 / 4 : ℝ) := this
      _ = 8 * C * (a : ℝ) ^ (1 / 4 : ℝ) * G a ^ (1 / 5 : ℝ) * G a ^ (4 / 5 : ℝ) := by
          conv_lhs => rw [hGsplit]
          ring
      _ ≤ 8 * C * (a : ℝ) ^ (1 / 4 : ℝ) * G a ^ (1 / 5 : ℝ) *
            (C'' ^ (4 / 5 : ℝ) * (a : ℝ) ^ (1 / 50 : ℝ)) := by gcongr
      _ = _ := by ring
  have hexp : (a : ℝ) ^ (1 / 100 : ℝ) * ((a : ℝ) ^ (1 / 50 : ℝ) * (a : ℝ) ^ (1 / 4 : ℝ)) ≤
      (a : ℝ) ^ (3 / 10 : ℝ) := by
    rw [← Real.rpow_add ha0, ← Real.rpow_add ha0]
    exact Real.rpow_le_rpow_of_exponent_le ha (by norm_num)
  have h100 : (a : ℝ) ^ (1 / 100 : ℝ) ≤ (a : ℝ) ^ (3 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le ha (by norm_num)
  have hsec : (L : ℝ) * (19 + γ) ≤ (19 * CL + 8 * CL * C * C'' ^ (4 / 5 : ℝ)) *
      ((a : ℝ) ^ (3 / 10 : ℝ) * G a ^ (1 / 5 : ℝ)) := by
    have hL0 : (0 : ℝ) ≤ L := by positivity
    have hγ0 : 0 ≤ γ := by positivity
    have hC''0 : 0 ≤ C'' ^ (4 / 5 : ℝ) := by positivity
    have hp0 : 0 ≤ (a : ℝ) ^ (1 / 100 : ℝ) := by positivity
    calc (L : ℝ) * (19 + γ) = 19 * L + L * γ := by ring
      _ ≤ 19 * (CL * (a : ℝ) ^ (1 / 100 : ℝ)) + (CL * (a : ℝ) ^ (1 / 100 : ℝ)) *
            (8 * C * C'' ^ (4 / 5 : ℝ) * ((a : ℝ) ^ (1 / 50 : ℝ) * (a : ℝ) ^ (1 / 4 : ℝ)) *
              G a ^ (1 / 5 : ℝ)) := by gcongr
      _ = 19 * CL * (a : ℝ) ^ (1 / 100 : ℝ) + 8 * CL * C * C'' ^ (4 / 5 : ℝ) *
            ((a : ℝ) ^ (1 / 100 : ℝ) * ((a : ℝ) ^ (1 / 50 : ℝ) * (a : ℝ) ^ (1 / 4 : ℝ))) *
              G a ^ (1 / 5 : ℝ) := by ring
      _ ≤ 19 * CL * ((a : ℝ) ^ (3 / 10 : ℝ) * G a ^ (1 / 5 : ℝ)) +
            8 * CL * C * C'' ^ (4 / 5 : ℝ) * (a : ℝ) ^ (3 / 10 : ℝ) * G a ^ (1 / 5 : ℝ) := by
          gcongr
          calc (a : ℝ) ^ (1 / 100 : ℝ) ≤ (a : ℝ) ^ (3 / 10 : ℝ) := h100
            _ = (a : ℝ) ^ (3 / 10 : ℝ) * 1 := by ring
            _ ≤ (a : ℝ) ^ (3 / 10 : ℝ) * G a ^ (1 / 5 : ℝ) := by gcongr
      _ = _ := by ring
  rw [hmain] at hP
  calc (P a b : ℝ) ≤ (19 * CL + 8 * CL * C * C'' ^ (4 / 5 : ℝ)) *
        ((a : ℝ) ^ (3 / 10 : ℝ) * G a ^ (1 / 5 : ℝ)) + 9 * (K6 ^ (3 / 5 : ℝ) *
          (4 : ℝ) ^ (2 / 5 : ℝ) * C ^ (1 / 5 : ℝ) * ((a : ℝ) ^ (3 / 10 : ℝ) *
            G a ^ (1 / 5 : ℝ))) := by linarith
    _ ≤ Cbig * ((a : ℝ) ^ (3 / 10 : ℝ) * G a ^ (1 / 5 : ℝ)) := by
        simp only [Cbig]; nlinarith
    _ = _ := by ring

end PierceLengthBound
