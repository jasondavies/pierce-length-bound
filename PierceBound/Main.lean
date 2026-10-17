import PierceBound.Window
import OAI.NumberTheory.Ostmann.Preliminaries.DivisorPowerBound

/-!
# `P(a, b) ≪_ε a^{3/10 + ε}`

Split the positive terms of the orbit according to `⌊log₂ bᵢ⌋ = k`. The terms with a given
`k` are consecutive and lie in `[2^k, 2^{k+1})`, so they form a window run
(`visits_window`), and `window_bound` gives `T¹⁰ ≪ a³ Δ³` when `T ≥ 12`, where
`Δ = max_{n ≤ 32 a⁷} τ(n)`. The divisor bound `τ(n)^k ≪_k n` with `k = 3m` turns this into
`T ≪ a^{3/10 + 7/(10m)}` for every `m ≥ 1`, and there are `≤ log₂ a + 1` values of `k`.
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

/-- **Theorem 1.1 (the `3/10` bound).** `P(a, b) ≪_ε a^{3/10 + ε}` uniformly in `0 < b < a`. -/
theorem P_le : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((3 : ℝ) / 10 + ε) := by
  intro ε hε
  -- choose `m` with `7 / (10 m) ≤ ε / 2`
  obtain ⟨m, hm⟩ := exists_nat_gt (7 / (5 * ε))
  have hm0 : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm
  have hm1 : m ≠ 0 := by rintro rfl; simp at hm0
  have hexp : ((3 * m + 7 : ℕ) : ℝ) * ((10 * m : ℕ) : ℝ)⁻¹ ≤ 3 / 10 + ε / 2 := by
    push_cast
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    have : 7 < 5 * ε * m := by rwa [div_lt_iff₀ (by positivity), mul_comm] at hm
    nlinarith
  obtain ⟨Dc, hDc, hdiv⟩ := OAI.Ostmann.exists_divisors_power_bound (3 * m)
  obtain ⟨CL, hCL, hlog⟩ := log_add_one_le_rpow (ε / 2) (by positivity)
  set K : ℕ := 63700992 ^ m * Dc * 32
  set C2 : ℝ := (K : ℝ) ^ (((10 * m : ℕ) : ℝ)⁻¹)
  have hC2 : 0 ≤ C2 := by positivity
  refine ⟨CL * (11 + C2), by positivity, fun a b hb hba => ?_⟩
  have ha1 : 1 ≤ a := by omega
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  set Δ := (range (32 * a ^ 7 + 1)).sup fun n => n.divisors.card
  have hΔ : DivBound a Δ := fun n _ hn =>
    le_sup (f := fun n => n.divisors.card) (mem_range.mpr (by omega))
  have hΔpow : Δ ^ (3 * m) ≤ Dc * (32 * a ^ 7) := by
    obtain ⟨n0, hn0, he⟩ := exists_mem_eq_sup (range (32 * a ^ 7 + 1)) nonempty_range_add_one
      fun n => n.divisors.card
    rw [show Δ = n0.divisors.card from he]
    have hn0' : n0 ≤ 32 * a ^ 7 := by have := mem_range.mp hn0; omega
    by_cases h0 : n0 = 0
    · subst h0; simp [zero_pow (show 3 * m ≠ 0 by omega)]
    · exact (hdiv n0 h0).trans (Nat.mul_le_mul_left _ hn0')
  set β : ℝ := 3 / 10 + ε / 2
  have hβ : 1 ≤ (a : ℝ) ^ β := Real.one_le_rpow ha (by positivity)
  -- each window is visited `≤ (11 + C2) a^β` times
  have hwin : ∀ k, ((visits a b k).card : ℝ) ≤ (11 + C2) * (a : ℝ) ^ β := by
    intro k
    rcases visits_bound (k := k) hba.le hΔ with h | h
    · have : ((visits a b k).card : ℝ) ≤ 11 := by exact_mod_cast h
      nlinarith
    · set T := (visits a b k).card
      have hpow : T ^ (10 * m) ≤ K * a ^ (3 * m + 7) := by
        calc T ^ (10 * m) = (T ^ 10) ^ m := by rw [pow_mul]
          _ ≤ (63700992 * a ^ 3 * Δ ^ 3) ^ m := Nat.pow_le_pow_left h m
          _ = 63700992 ^ m * a ^ (3 * m) * Δ ^ (3 * m) := by ring
          _ ≤ 63700992 ^ m * a ^ (3 * m) * (Dc * (32 * a ^ 7)) := by gcongr
          _ = K * a ^ (3 * m + 7) := by simp only [K]; ring
      have hroot := le_rpow_inv_of_pow_le (by omega) hpow
      have hsplit : ((K * a ^ (3 * m + 7) : ℕ) : ℝ) ^ (((10 * m : ℕ) : ℝ)⁻¹) =
          C2 * (a : ℝ) ^ (((3 * m + 7 : ℕ) : ℝ) * ((10 * m : ℕ) : ℝ)⁻¹) := by
        rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity), Nat.cast_pow,
          ← Real.rpow_natCast (a : ℝ) (3 * m + 7), ← Real.rpow_mul (by positivity)]
      rw [hsplit] at hroot
      have : (a : ℝ) ^ (((3 * m + 7 : ℕ) : ℝ) * ((10 * m : ℕ) : ℝ)⁻¹) ≤ (a : ℝ) ^ β :=
        Real.rpow_le_rpow_of_exponent_le ha hexp
      nlinarith [mul_le_mul_of_nonneg_left this hC2]
  -- sum over the `log₂ a + 1` windows
  have hP : (P a b : ℝ) ≤ ((Nat.log 2 a + 1 : ℕ) : ℝ) * ((11 + C2) * (a : ℝ) ^ β) := by
    rw [P_eq_sum_visits hba.le]
    push_cast
    calc ∑ k ∈ range (Nat.log 2 a + 1), ((visits a b k).card : ℝ)
        ≤ ∑ _k ∈ range (Nat.log 2 a + 1), (11 + C2) * (a : ℝ) ^ β := sum_le_sum fun k _ => hwin k
      _ = _ := by simp
  have hL := hlog a ha1
  calc (P a b : ℝ) ≤ ((Nat.log 2 a + 1 : ℕ) : ℝ) * ((11 + C2) * (a : ℝ) ^ β) := hP
    _ ≤ (CL * (a : ℝ) ^ (ε / 2)) * ((11 + C2) * (a : ℝ) ^ β) :=
        mul_le_mul_of_nonneg_right hL (by positivity)
    _ = CL * (11 + C2) * ((a : ℝ) ^ (ε / 2) * (a : ℝ) ^ β) := by ring
    _ = CL * (11 + C2) * (a : ℝ) ^ ((3 : ℝ) / 10 + ε) := by
        rw [← Real.rpow_add (by positivity)]
        congr 2
        simp only [β]; ring

end PierceBound
