/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
import PierceBound.Window
import OAI.NumberTheory.Ostmann.Preliminaries.DivisorPowerBound

/-!
# `P(a, b) ≪_ε a^{3/10 + ε}`

Split the positive terms of the orbit according to `⌊log₂ bᵢ⌋ = k`. The terms with a given
`k` are consecutive and lie in `[2^k, 2^{k+1})`, so they form a window run
(`visits_window`), and `window_bound` gives `T¹⁰ ≪ a³ Δ³` when `T ≥ 12`, where
`Δ = max_{n ≤ 32 a⁷} τ(n)`. The divisor bound `τ(n)^k ≪_k n` gives `Δ ≪_η a^η`
(`tauMax_slow`), so `T ≪_η a^{3/10 + η}`, and there are `≤ log₂ a + 1` values of `k`.

The last step is shared by all the main theorems: `P_le_of_visits` turns a window bound
`T ≤ 35` or `T^N ≤ K S(a) a^r`, with `S(a) ≪_η a^η` (`SlowGrowth S`), into
`P(a, b) ≪_ε a^{r/N + ε}`.
-/

namespace PierceBound

open Finset

/-- The indices `i < P(a,b)` with `⌊log₂ bᵢ₊₁⌋ = k`, i.e. `2^k ≤ bᵢ₊₁ < 2^{k+1}`. -/
def visits (a b k : ℕ) : Finset ℕ := (range (P a b)).filter fun i => Nat.log 2 (orb a b i) = k

/-- `P(a, b)` is the total number of visits to the dyadic windows. -/
theorem P_eq_sum_visits {a b : ℕ} (hba : b ≤ a) :
    P a b = ∑ k ∈ range (Nat.log 2 a + 1), (visits a b k).card := by
  classical
  rw [← card_range (P a b)]
  apply card_eq_sum_card_fiberwise
  intro i _
  exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right ((orb_le a b i).trans hba)))

/-- The visits to one dyadic window form a window run. -/
theorem visits_window {a b k : ℕ} (hba : b ≤ a) (h : (visits a b k).Nonempty) :
    Window a (2 ^ k) (visits a b k).card (fun j => orb a b ((visits a b k).min' h + j)) := by
  classical
  set I := visits a b k with hI
  set s := I.min' h
  set m := I.max' h
  have hmem : ∀ i ∈ I, i < P a b ∧ Nat.log 2 (orb a b i) = k := fun i hi => by
    simpa [I, visits] using hi
  have hs := hmem s (I.min'_mem h)
  have hm := hmem m (I.max'_mem h)
  have hconv : ∀ i, s ≤ i → i ≤ m → i ∈ I := by
    intro i h1 h2
    have hiP : i < P a b := lt_of_le_of_lt h2 hm.1
    have l1 := Nat.log_mono_right (b := 2) (orb_antitone a b h1)
    have l2 := Nat.log_mono_right (b := 2) (orb_antitone a b h2)
    simp only [I, visits, mem_filter, mem_range]
    refine ⟨hiP, ?_⟩
    rw [hs.2] at l1; rw [hm.2] at l2
    omega
  have hcard : I.card ≤ m + 1 - s := by
    have : I ⊆ Icc s m := fun i hi => mem_Icc.mpr ⟨I.min'_le i hi, I.le_max' i hi⟩
    simpa using card_le_card this
  have hrun : ∀ j < I.card, s + j ∈ I := fun j hj => hconv _ (by omega) (by omega)
  have hwin : ∀ i ∈ I, orb a b i ≠ 0 ∧ 2 ^ k ≤ orb a b i ∧ orb a b i < 2 * 2 ^ k := by
    intro i hi
    obtain ⟨hiP, hlog⟩ := hmem i hi
    have hne := orb_ne_zero_of_lt hiP
    refine ⟨hne, hlog ▸ Nat.pow_log_le_self 2 hne, ?_⟩
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (orb a b i)
    rw [hlog, pow_succ] at this
    omega
  refine ⟨Nat.one_le_two_pow, fun j hj => ?_, fun j _ => (orb_le a b _).trans hba, fun j hj => ?_⟩
  · obtain ⟨-, h1, h2⟩ := hwin _ (hrun j hj); exact ⟨h1, h2⟩
  · rw [← add_assoc]
    exact orb_succ_of_ne (hwin _ (hrun j (Nat.lt_of_succ_lt hj))).1

/-- The number of visits to a window is `≤ 11` or satisfies `T¹⁰ ≤ 63700992 a³ Δ³`. -/
theorem visits_bound {a b k Δ : ℕ} (hba : b ≤ a) (hΔ : DivBound a Δ) :
    (visits a b k).card ≤ 11 ∨ (visits a b k).card ^ 10 ≤ 63700992 * a ^ 3 * Δ ^ 3 := by
  by_cases hT : (visits a b k).card ≤ 11
  · exact Or.inl hT
  · right
    have h : (visits a b k).Nonempty := by
      rw [← card_pos]; omega
    exact window_bound (visits_window hba h) hΔ (by omega)

/-- `log₂ n + 1 ≪_ε n^ε`. -/
lemma log_add_one_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n → ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ C * (n : ℝ) ^ ε := by
  refine ⟨1 / (ε * Real.log 2) + 1, by positivity, fun n hn => ?_⟩
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ n := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hlog : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
  have hlogn := Real.log_le_rpow_div (show (0 : ℝ) ≤ n by positivity) hε
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ ε := Real.one_le_rpow hn' hε.le
  have h2 : (Nat.log 2 n : ℝ) ≤ (n : ℝ) ^ ε / ε / Real.log 2 := by
    rw [le_div_iff₀ hl2]; linarith
  push_cast
  have : (n : ℝ) ^ ε / ε / Real.log 2 = 1 / (ε * Real.log 2) * (n : ℝ) ^ ε := by
    field_simp
  nlinarith

/-- An `n`-th root bound: `T^n ≤ X` gives `T ≤ X^{1/n}`. -/
lemma le_rpow_inv_of_pow_le {T X n : ℕ} (hn : n ≠ 0) (h : T ^ n ≤ X) :
    (T : ℝ) ≤ (X : ℝ) ^ ((n : ℝ)⁻¹) := by
  rw [← Real.pow_rpow_inv_natCast (Nat.cast_nonneg T) hn]
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast h) (by positivity)

/-- `max_{n ≤ X} τ(n)`. -/
def tauMax (X : ℕ) : ℕ := (range (X + 1)).sup fun n => n.divisors.card

lemma tau_le_tauMax {n X : ℕ} (h : n ≤ X) : n.divisors.card ≤ tauMax X :=
  le_sup (f := fun n => n.divisors.card) (mem_range.mpr (by omega))

lemma tauMax_divBound (a : ℕ) : DivBound a (tauMax (32 * a ^ 7)) := fun _ _ hn => tau_le_tauMax hn

/-- `max_{n ≤ X} τ(n)^k ≤ D X` from the divisor bound. -/
lemma tauMax_pow_le {k D : ℕ} (hk : k ≠ 0) (hdiv : ∀ n : ℕ, n ≠ 0 → n.divisors.card ^ k ≤ D * n)
    (X : ℕ) : tauMax X ^ k ≤ D * X := by
  obtain ⟨n0, hn0, he⟩ := exists_mem_eq_sup (range (X + 1)) nonempty_range_add_one
    fun n => n.divisors.card
  unfold tauMax
  rw [he]
  have hn0' : n0 ≤ X := by have := mem_range.mp hn0; omega
  by_cases h0 : n0 = 0
  · subst h0; simp [zero_pow hk]
  · exact (hdiv n0 h0).trans (Nat.mul_le_mul_left _ hn0')

/-- A root bound: `x^k ≤ D c a^e` gives `x ≤ (D c)^{1/k} a^η` once `e/k ≤ η`. -/
lemma root_le {x D c e k a : ℕ} (hk : k ≠ 0) (ha : 1 ≤ a) (h : x ^ k ≤ D * (c * a ^ e))
    {η : ℝ} (hη : (e : ℝ) / k ≤ η) :
    (x : ℝ) ≤ ((D * c : ℕ) : ℝ) ^ ((k : ℝ)⁻¹) * (a : ℝ) ^ η := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have h1 := le_rpow_inv_of_pow_le hk h
  have e1 : ((D * (c * a ^ e) : ℕ) : ℝ) ^ ((k : ℝ)⁻¹) =
      ((D * c : ℕ) : ℝ) ^ ((k : ℝ)⁻¹) * (a : ℝ) ^ ((e : ℝ) / k) := by
    rw [show D * (c * a ^ e) = D * c * a ^ e by ring, Nat.cast_mul,
      Real.mul_rpow (by positivity) (by positivity), Nat.cast_pow,
      ← Real.rpow_natCast (a : ℝ) e, ← Real.rpow_mul (by positivity), div_eq_mul_inv]
  rw [e1] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ha' hη)
    (by positivity))

/-- `f(a) ≪_η a^η` for every `η > 0`. -/
def SlowGrowth (f : ℕ → ℕ) : Prop :=
  ∀ η > (0 : ℝ), ∃ C > 0, ∀ a : ℕ, 1 ≤ a → (f a : ℝ) ≤ C * (a : ℝ) ^ η

lemma SlowGrowth.mul {f g : ℕ → ℕ} (hf : SlowGrowth f) (hg : SlowGrowth g) :
    SlowGrowth fun a => f a * g a := by
  intro η hη
  obtain ⟨C1, hC1, h1⟩ := hf (η / 2) (by positivity)
  obtain ⟨C2, hC2, h2⟩ := hg (η / 2) (by positivity)
  refine ⟨C1 * C2, by positivity, fun a ha => ?_⟩
  have h := mul_le_mul (h1 a ha) (h2 a ha) (Nat.cast_nonneg _) (by positivity)
  push_cast
  calc (f a : ℝ) * g a ≤ C1 * (a : ℝ) ^ (η / 2) * (C2 * (a : ℝ) ^ (η / 2)) := h
    _ = C1 * C2 * ((a : ℝ) ^ (η / 2) * (a : ℝ) ^ (η / 2)) := by ring
    _ = C1 * C2 * (a : ℝ) ^ η := by rw [← Real.rpow_add (by positivity)]; ring_nf

lemma SlowGrowth.pow {f : ℕ → ℕ} (hf : SlowGrowth f) (n : ℕ) : SlowGrowth fun a => f a ^ n := by
  induction n with
  | zero =>
    intro η hη
    exact ⟨1, one_pos, fun a ha => by
      simpa using Real.one_le_rpow (by exact_mod_cast ha : (1 : ℝ) ≤ a) hη.le⟩
  | succ n ih => simpa only [pow_succ] using ih.mul hf

/-- **The divisor maximum on a polynomial range grows slowly**: `τ*(c aᵉ) ≪_η a^η`. -/
lemma tauMax_slow (c e : ℕ) : SlowGrowth fun a => tauMax (c * a ^ e) := by
  intro η hη
  obtain ⟨k, hk⟩ := exists_nat_gt (e / η)
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (by positivity) hk
  have hk1 : k ≠ 0 := by rintro rfl; simp at hk0
  have hkη : (e : ℝ) / k ≤ η := by
    rw [div_le_iff₀ hk0]; rw [div_lt_iff₀ hη] at hk; linarith
  obtain ⟨Dc, -, hdiv⟩ := OAI.Ostmann.exists_divisors_power_bound k
  refine ⟨((Dc * c : ℕ) : ℝ) ^ ((k : ℝ)⁻¹) + 1, by positivity, fun a ha => ?_⟩
  have h := root_le (c := c) hk1 ha (tauMax_pow_le hk1 hdiv (c * a ^ e)) hkη
  nlinarith [Real.rpow_nonneg (Nat.cast_nonneg a) η]

/-- **From window bounds to `P(a, b)`.** If every dyadic window has `T ≤ 35` or
`T^N ≤ K S(a) a^r` with `S` slowly growing, then `P(a, b) ≪_ε a^{r/N + ε}`. -/
theorem P_le_of_visits {N r K : ℕ} {S : ℕ → ℕ} (hN : N ≠ 0) (hS : SlowGrowth S)
    (hvis : ∀ a b k : ℕ, 0 < b → b < a →
      (visits a b k).card ≤ 35 ∨ (visits a b k).card ^ N ≤ K * S a * a ^ r) :
    ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ ((r : ℝ) / N + ε) := by
  intro ε hε
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  obtain ⟨Cs, hCs, hSle⟩ := hS (N * (ε / 2)) (by positivity)
  obtain ⟨CL, hCL, hlog⟩ := log_add_one_le_rpow (ε / 2) (by positivity)
  set C2 : ℝ := ((K : ℝ) * Cs) ^ ((N : ℝ)⁻¹)
  have hC2 : 0 ≤ C2 := by positivity
  set β : ℝ := (r : ℝ) / N + ε / 2
  refine ⟨CL * (35 + C2), by positivity, fun a b hb hba => ?_⟩
  have ha1 : 1 ≤ a := by omega
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have hβ : 1 ≤ (a : ℝ) ^ β := Real.one_le_rpow ha (by positivity)
  -- each window is visited `≤ (35 + C2) a^β` times
  have hwin : ∀ k, ((visits a b k).card : ℝ) ≤ (35 + C2) * (a : ℝ) ^ β := by
    intro k
    rcases hvis a b k hb hba with h | h
    · have : ((visits a b k).card : ℝ) ≤ 35 := by exact_mod_cast h
      nlinarith
    · set T := (visits a b k).card
      have h1 : (T : ℝ) ^ N ≤ ((K : ℝ) * Cs) * (a : ℝ) ^ ((r : ℝ) + N * (ε / 2)) := by
        have h' : (T : ℝ) ^ N ≤ (K : ℝ) * S a * (a : ℝ) ^ r := by exact_mod_cast h
        calc (T : ℝ) ^ N ≤ (K : ℝ) * S a * (a : ℝ) ^ r := h'
          _ ≤ (K : ℝ) * (Cs * (a : ℝ) ^ (N * (ε / 2))) * (a : ℝ) ^ r := by
              gcongr; exact hSle a ha1
          _ = ((K : ℝ) * Cs) * (a : ℝ) ^ ((r : ℝ) + N * (ε / 2)) := by
              rw [Real.rpow_add (by positivity), Real.rpow_natCast]; ring
      have h2 := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹)
      rw [Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) hN,
        Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity),
        show ((r : ℝ) + N * (ε / 2)) * (N : ℝ)⁻¹ = β by simp only [β]; field_simp] at h2
      nlinarith
  -- sum over the `log₂ a + 1` windows
  have hP : (P a b : ℝ) ≤ ((Nat.log 2 a + 1 : ℕ) : ℝ) * ((35 + C2) * (a : ℝ) ^ β) := by
    rw [P_eq_sum_visits hba.le]
    push_cast
    calc ∑ k ∈ range (Nat.log 2 a + 1), ((visits a b k).card : ℝ)
        ≤ ∑ _k ∈ range (Nat.log 2 a + 1), (35 + C2) * (a : ℝ) ^ β := sum_le_sum fun k _ => hwin k
      _ = _ := by simp
  calc (P a b : ℝ) ≤ ((Nat.log 2 a + 1 : ℕ) : ℝ) * ((35 + C2) * (a : ℝ) ^ β) := hP
    _ ≤ (CL * (a : ℝ) ^ (ε / 2)) * ((35 + C2) * (a : ℝ) ^ β) :=
        mul_le_mul_of_nonneg_right (hlog a ha1) (by positivity)
    _ = CL * (35 + C2) * ((a : ℝ) ^ (ε / 2) * (a : ℝ) ^ β) := by ring
    _ = CL * (35 + C2) * (a : ℝ) ^ ((r : ℝ) / N + ε) := by
        rw [← Real.rpow_add (by positivity)]
        congr 2
        simp only [β]; ring

/-- **Theorem 1.1 (the `3/10` bound).** `P(a, b) ≪_ε a^{3/10 + ε}` uniformly in `0 < b < a`. -/
theorem P_le : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((3 : ℝ) / 10 + ε) := by
  have h := P_le_of_visits (N := 10) (r := 3) (K := 63700992) (by norm_num)
    ((tauMax_slow 32 7).pow 3) fun a b k _ hba =>
      (visits_bound (k := k) hba.le (tauMax_divBound a)).imp (fun h => by omega)
        fun h => h.trans_eq (by ring)
  intro ε hε
  obtain ⟨C, hC, hP⟩ := h ε hε
  refine ⟨C, hC, fun a b hb hba => ?_⟩
  have := hP a b hb hba
  norm_num at this ⊢
  exact this

end PierceBound
