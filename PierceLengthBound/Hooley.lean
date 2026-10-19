/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.Conditional

/-!
# The Erdős–Hooley `Δ` function and the `√(log log a)` bound

`hooleyDelta n = max_u #{d ∣ n : e^u < d ≤ e^{u+1}}` (Hooley; de la Bretèche–Tenenbaum use
exactly this definition). Two published theorems are stated as propositions:

* `NairTenenbaumDelta`: Nair–Tenenbaum, *Short sums of certain arithmetic functions*,
  Acta Math. 180 (1998), the displayed consequence of their Theorem 1 for `F = Δ`, `t = 1`,
  `Q(X) = X` (so `ρ = 1`), with short-interval exponent `1/4` (their `y ≥ x^ε` with `ε = 1/4`;
  `Δ` lies in their class `M(A, B, ε)` for every `ε > 0`):
  `∑_{x<n≤x+y} Δ(n) ≪ (y / log x) ∑_{n≤x} Δ(n)/n` for `x^{1/4} ≤ y ≤ x`, `x` large.
* `BretecheTenenbaumMean`: de la Bretèche–Tenenbaum, *Note on the mean value of the
  Erdős–Hooley Delta-function*, Acta Arith. 219 (2025), Theorem 1.1:
  `∑_{n≤x} Δ(n) ≪ x (log log x)^{5/2}` for `x` large.

From them we prove `ShortDivisorBound` with `G = (log log x)^{5/2}` (partial summation,
`shortDivisorBound_of_hooley`) and hence `P(a, b) ≪ a^{3/10} √(log log 3a)` (`P_le_loglog`).
-/

@[expose] public section

namespace PierceLengthBound

open Finset

/-- The divisors of `n` in `(e^u, e^{u+1}]`. -/
noncomputable def hooleyCount (n : ℕ) (u : ℝ) : ℕ :=
  (n.divisors.filter fun d : ℕ => Real.exp u < (d : ℝ) ∧ (d : ℝ) ≤ Real.exp (u + 1)).card

/-- The Erdős–Hooley function `Δ(n) = max_u #{d ∣ n : e^u < d ≤ e^{u+1}}`. -/
noncomputable def hooleyDelta (n : ℕ) : ℕ := ⨆ u : ℝ, hooleyCount n u

lemma hooleyCount_le (n : ℕ) (u : ℝ) : hooleyCount n u ≤ n.divisors.card := by
  unfold hooleyCount; exact card_le_card (filter_subset _ _)

lemma le_hooleyDelta (n : ℕ) (u : ℝ) : hooleyCount n u ≤ hooleyDelta n :=
  le_ciSup ⟨n.divisors.card, by rintro _ ⟨u, rfl⟩; exact hooleyCount_le n u⟩ u

/-- Divisors in `[A, 2A)` lie in one interval `(e^u, e^{u+1}]` (take `e^{u+1} = 2A`). -/
lemma dcount_le_hooleyDelta {A : ℕ} (hA : 1 ≤ A) (n : ℕ) : dcount A n ≤ hooleyDelta n := by
  refine le_trans ?_ (le_hooleyDelta n (Real.log (2 * A) - 1))
  unfold dcount hooleyCount
  apply card_le_card
  intro d hd
  simp only [mem_filter] at hd ⊢
  obtain ⟨hdn, h1, h2⟩ := hd
  have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hpos : (0 : ℝ) < 2 * A := by positivity
  refine ⟨hdn, ?_, ?_⟩
  · rw [Real.exp_sub, Real.exp_log hpos]
    have he : (2 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9; linarith
    rw [div_lt_iff₀ (Real.exp_pos 1)]
    have : (A : ℝ) ≤ d := by exact_mod_cast h1
    nlinarith
  · rw [sub_add_cancel, Real.exp_log hpos]
    have : (d : ℝ) < 2 * A := by exact_mod_cast h2
    linarith

/-- **Nair–Tenenbaum (1998)** for `F = Δ`, `Q(X) = X`, `ε = 1/4`. -/
def NairTenenbaumDelta : Prop :=
  ∃ C x₀ : ℝ, ∀ x y : ℕ, x₀ ≤ x → (x : ℝ) ^ (1 / 4 : ℝ) ≤ y → y ≤ x →
    ∑ n ∈ Ioc x (x + y), (hooleyDelta n : ℝ) ≤
      C * (y / Real.log x) * ∑ n ∈ Icc 1 x, (hooleyDelta n : ℝ) / n

/-- **de la Bretèche–Tenenbaum (2025), Theorem 1.1.** -/
def BretecheTenenbaumMean : Prop :=
  ∃ C x₀ : ℝ, ∀ x : ℕ, x₀ ≤ x →
    ∑ n ∈ Icc 1 x, (hooleyDelta n : ℝ) ≤ C * x * Real.log (Real.log x) ^ (5 / 2 : ℝ)

/-- `ℓ(x) = max(1, log log x)`. -/
noncomputable def ell (x : ℕ) : ℝ := max 1 (Real.log (Real.log x))

lemma one_le_ell (x : ℕ) : 1 ≤ ell x := le_max_left _ _

lemma hooleyDelta_le_self (n : ℕ) : hooleyDelta n ≤ n :=
  ciSup_le' (fun u => (hooleyCount_le n u).trans (Nat.card_divisors_le_self n))

/-- `log log` is monotone on `[16, ∞)` and nonnegative there. -/
lemma loglog_mono {x y : ℝ} (hx : 16 ≤ x) (hxy : x ≤ y) :
    0 ≤ Real.log (Real.log x) ∧ Real.log (Real.log x) ≤ Real.log (Real.log y) := by
  have he : Real.exp 1 < 16 := by have := Real.exp_one_lt_d9; linarith
  have hlx : 1 < Real.log x := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]; linarith
  refine ⟨Real.log_nonneg hlx.le, Real.log_le_log (by linarith)
    (Real.log_le_log (by linarith) hxy)⟩

/-- `ℓ(2x) ≤ 2 ℓ(x)` for `x ≥ 2`. -/
lemma ell_two_mul {x : ℕ} (hx : 2 ≤ x) : ell (2 * x) ≤ 2 * ell x := by
  have hx' : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hl2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx'
  have hl2' : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlx : 0 < Real.log x := by linarith
  have h1 : Real.log ((2 * x : ℕ) : ℝ) ≤ 2 * Real.log x := by
    push_cast
    rw [Real.log_mul (by norm_num) (by linarith)]; linarith
  have h2 : Real.log (Real.log ((2 * x : ℕ) : ℝ)) ≤ Real.log 2 + Real.log (Real.log x) := by
    rw [← Real.log_mul (by norm_num) hlx.ne']
    have : 0 < Real.log ((2 * x : ℕ) : ℝ) := by
      push_cast; rw [Real.log_mul (by norm_num) (by linarith)]; linarith
    exact Real.log_le_log this h1
  have hle2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  unfold ell
  have := le_max_left 1 (Real.log (Real.log x))
  have := le_max_right 1 (Real.log (Real.log x))
  apply max_le <;> linarith

/-- **Partial summation of de la Bretèche–Tenenbaum.**
`∑_{n≤x} Δ(n)/n ≪ log x · ℓ(x)^{5/2}`. -/
theorem sum_hooleyDelta_div_le (hBT : BretecheTenenbaumMean) :
    ∃ C x₁ : ℝ, 0 ≤ C ∧ ∀ x : ℕ, x₁ ≤ x →
      ∑ n ∈ Icc 1 x, (hooleyDelta n : ℝ) / n ≤ C * Real.log x * ell x ^ (5 / 2 : ℝ) := by
  classical
  obtain ⟨C, x₀, hBT⟩ := hBT
  set N0 : ℕ := max 16 ⌈x₀⌉₊
  set Cp : ℝ := max C 0
  refine ⟨N0 + 36 * Cp, N0, by positivity, fun x hx => ?_⟩
  have hxN : N0 ≤ x := by exact_mod_cast hx
  have hx16 : 16 ≤ x := le_trans (le_max_left _ _) hxN
  have hx16' : (16 : ℝ) ≤ x := by exact_mod_cast hx16
  set f : ℕ → ℝ := fun n => (hooleyDelta n : ℝ) / n
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  have hf1 : ∀ n, f n ≤ 1 := fun n => by
    simp only [f]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [div_le_one (by exact_mod_cast hn)]; exact_mod_cast hooleyDelta_le_self n
  -- split off `n < N0`
  rw [← sum_filter_add_sum_filter_not (Icc 1 x) (fun n => n < N0)]
  have hsmall : ∑ n ∈ (Icc 1 x).filter (fun n => n < N0), f n ≤ N0 := by
    calc ∑ n ∈ (Icc 1 x).filter (fun n => n < N0), f n
        ≤ ∑ n ∈ (Icc 1 x).filter (fun n => n < N0), (1 : ℝ) := sum_le_sum fun n _ => hf1 n
      _ = ((Icc 1 x).filter (fun n => n < N0)).card := by simp
      _ ≤ (range N0).card := by
          exact_mod_cast card_le_card fun n hn => mem_range.mpr (mem_filter.mp hn).2
      _ = N0 := by simp
  -- the dyadic blocks
  set S := (Icc 1 x).filter (fun n => ¬ n < N0)
  set Lx := Nat.log 2 x + 1
  have hmaps : ∀ n ∈ S, Nat.log 2 n ∈ range Lx := fun n hn => by
    have := (mem_Icc.mp (mem_filter.mp hn).1).2
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right this))
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hell := one_le_ell x
  have hell52 : 1 ≤ ell x ^ (5 / 2 : ℝ) := Real.one_le_rpow hell (by norm_num)
  have hblock : ∀ j ∈ range Lx, ∑ n ∈ S.filter (fun n => Nat.log 2 n = j), f n ≤
      12 * Cp * ell x ^ (5 / 2 : ℝ) := by
    intro j hj
    rcases (S.filter (fun n => Nat.log 2 n = j)).eq_empty_or_nonempty with he | ⟨n0, hn0⟩
    · rw [he, sum_empty]; positivity
    obtain ⟨hn0S, hn0j⟩ := mem_filter.mp hn0
    obtain ⟨hn0I, hn0N⟩ := mem_filter.mp hn0S
    have hn0x := (mem_Icc.mp hn0I).2
    have hn0pos : n0 ≠ 0 := by have := (mem_Icc.mp hn0I).1; omega
    have hjlo : 2 ^ j ≤ n0 := hn0j ▸ Nat.pow_log_le_self 2 hn0pos
    have hjhi : n0 < 2 ^ (j + 1) := hn0j ▸ Nat.lt_pow_succ_log_self (by norm_num) n0
    set X := 2 ^ (j + 1)
    have hXx0 : x₀ ≤ (X : ℝ) := by
      have : ⌈x₀⌉₊ ≤ X := by have := le_max_right 16 ⌈x₀⌉₊; omega
      exact (Nat.le_ceil x₀).trans (by exact_mod_cast this)
    have hX16 : (16 : ℝ) ≤ X := by
      have : 16 ≤ X := by have := le_max_left 16 ⌈x₀⌉₊; omega
      exact_mod_cast this
    have hX2x : X ≤ 2 * x := by
      have : 2 ^ j ≤ x := hjlo.trans hn0x
      simp only [X, pow_succ]; omega
    -- terms are `≤ Δ(n)/2^j`, and the block lies in `[1, X]`
    have hterm : ∀ n ∈ S.filter (fun n => Nat.log 2 n = j), f n ≤ (hooleyDelta n : ℝ) / 2 ^ j := by
      intro n hn
      obtain ⟨hnS, hnj⟩ := mem_filter.mp hn
      have hnpos : n ≠ 0 := by have := (mem_Icc.mp (mem_filter.mp hnS).1).1; omega
      have : 2 ^ j ≤ n := hnj ▸ Nat.pow_log_le_self 2 hnpos
      simp only [f]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact_mod_cast this
    have hsub : S.filter (fun n => Nat.log 2 n = j) ⊆ Icc 1 X := by
      intro n hn
      obtain ⟨hnS, hnj⟩ := mem_filter.mp hn
      have h1 := (mem_Icc.mp (mem_filter.mp hnS).1).1
      have hnpos : n ≠ 0 := by omega
      have : n < 2 ^ (j + 1) := hnj ▸ Nat.lt_pow_succ_log_self (by norm_num) n
      exact mem_Icc.mpr ⟨h1, this.le⟩
    have hBTX := hBT X hXx0
    obtain ⟨hll0, hllX⟩ := loglog_mono hX16
        (show (X : ℝ) ≤ ((2 * x : ℕ) : ℝ) by exact_mod_cast hX2x)
    have hell2 := ell_two_mul (x := x) (by omega)
    have hpow : Real.log (Real.log X) ^ (5 / 2 : ℝ) ≤ 6 * ell x ^ (5 / 2 : ℝ) := by
      calc Real.log (Real.log X) ^ (5 / 2 : ℝ) ≤ (2 * ell x) ^ (5 / 2 : ℝ) := by
            apply Real.rpow_le_rpow hll0 _ (by norm_num)
            exact hllX.trans ((le_max_right _ _).trans hell2)
        _ = (2 : ℝ) ^ (5 / 2 : ℝ) * ell x ^ (5 / 2 : ℝ) :=
            Real.mul_rpow (by norm_num) (by linarith)
        _ ≤ 6 * ell x ^ (5 / 2 : ℝ) := by
            gcongr
            have : (2 : ℝ) ^ (5 / 2 : ℝ) = 4 * Real.sqrt 2 := by
              rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add (by norm_num),
                Real.sqrt_eq_rpow]
              norm_num
            rw [this]
            have : Real.sqrt 2 ≤ 3 / 2 := by
              rw [Real.sqrt_le_left (by norm_num)]; norm_num
            linarith
    have hX : (X : ℝ) = 2 * 2 ^ j := by simp only [X]; push_cast; ring
    calc ∑ n ∈ S.filter (fun n => Nat.log 2 n = j), f n
        ≤ ∑ n ∈ S.filter (fun n => Nat.log 2 n = j), (hooleyDelta n : ℝ) / 2 ^ j :=
          sum_le_sum hterm
      _ = (∑ n ∈ S.filter (fun n => Nat.log 2 n = j), (hooleyDelta n : ℝ)) / 2 ^ j := by
          rw [sum_div]
      _ ≤ (∑ n ∈ Icc 1 X, (hooleyDelta n : ℝ)) / 2 ^ j := by
          gcongr
      _ ≤ (Cp * X * Real.log (Real.log X) ^ (5 / 2 : ℝ)) / 2 ^ j := by
          gcongr
          refine hBTX.trans ?_
          gcongr
          exact le_max_left _ _
      _ = 2 * Cp * Real.log (Real.log X) ^ (5 / 2 : ℝ) := by
          rw [hX]; field_simp
      _ ≤ 2 * Cp * (6 * ell x ^ (5 / 2 : ℝ)) := by gcongr
      _ = 12 * Cp * ell x ^ (5 / 2 : ℝ) := by ring
  have hlarge : ∑ n ∈ S, f n ≤ Lx * (12 * Cp * ell x ^ (5 / 2 : ℝ)) := by
    rw [← sum_fiberwise_of_maps_to hmaps]
    calc ∑ j ∈ range Lx, ∑ n ∈ S.filter (fun n => Nat.log 2 n = j), f n
        ≤ ∑ _j ∈ range Lx, 12 * Cp * ell x ^ (5 / 2 : ℝ) := sum_le_sum hblock
      _ = _ := by simp
  -- `log₂ x + 1 ≤ 3 log x`
  have hLx : (Lx : ℝ) ≤ 3 * Real.log x := by
    have hpow : ((2 ^ Nat.log 2 x : ℕ) : ℝ) ≤ x := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have hlog : (Nat.log 2 x : ℝ) * Real.log 2 ≤ Real.log x := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
    have hl2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have hlx1 : 1 ≤ Real.log x := by
      have he : Real.exp 1 < 16 := by have := Real.exp_one_lt_d9; linarith
      rw [Real.le_log_iff_exp_le (by linarith)]; linarith
    have : (Nat.log 2 x : ℝ) ≤ 2 * Real.log x := by nlinarith
    simp only [Lx]; push_cast; linarith
  have hprod : 1 ≤ Real.log x * ell x ^ (5 / 2 : ℝ) := by
    have hlx1 : 1 ≤ Real.log x := by
      have he : Real.exp 1 < 16 := by have := Real.exp_one_lt_d9; linarith
      rw [Real.le_log_iff_exp_le (by linarith)]; linarith
    nlinarith
  have hCp : 0 ≤ Cp := le_max_right _ _
  calc ∑ n ∈ (Icc 1 x).filter (fun n => n < N0), f n + ∑ n ∈ S, f n
      ≤ N0 + Lx * (12 * Cp * ell x ^ (5 / 2 : ℝ)) := add_le_add hsmall hlarge
    _ ≤ N0 * (Real.log x * ell x ^ (5 / 2 : ℝ)) +
          3 * Real.log x * (12 * Cp * ell x ^ (5 / 2 : ℝ)) := by
        gcongr
        · calc (N0 : ℝ) = N0 * 1 := by ring
            _ ≤ _ := by gcongr
    _ = (N0 + 36 * Cp) * Real.log x * ell x ^ (5 / 2 : ℝ) := by ring

/-- **The short-interval divisor bound from the two published theorems.** -/
theorem shortDivisorBound_of_hooley (hNT : NairTenenbaumDelta) (hBT : BretecheTenenbaumMean) :
    ShortDivisorBound fun x => ell x ^ (5 / 2 : ℝ) := by
  obtain ⟨C1, x₀, hNT⟩ := hNT
  obtain ⟨C2, x₁, hC2, hmean⟩ := sum_hooleyDelta_div_le hBT
  set C1p := max C1 0
  refine ⟨C1p * C2 + 1, max (max x₀ x₁) 16, by positivity, fun x y A hx hy hyx hA => ?_⟩
  have hx0 : x₀ ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hx1 : x₁ ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hx16 : (16 : ℝ) ≤ x := (le_max_right _ _).trans hx
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hS0 : 0 ≤ ∑ n ∈ Icc 1 x, (hooleyDelta n : ℝ) / n := sum_nonneg fun _ _ => by positivity
  have hy0 : (0 : ℝ) ≤ y := by positivity
  have hell : 0 ≤ ell x ^ (5 / 2 : ℝ) := by have := one_le_ell x; positivity
  calc ∑ n ∈ Ioc x (x + y), (dcount A n : ℝ)
      ≤ ∑ n ∈ Ioc x (x + y), (hooleyDelta n : ℝ) :=
        sum_le_sum fun n _ => by exact_mod_cast dcount_le_hooleyDelta hA n
    _ ≤ C1 * (y / Real.log x) * ∑ n ∈ Icc 1 x, (hooleyDelta n : ℝ) / n := hNT x y hx0 hy hyx
    _ ≤ C1p * (y / Real.log x) * ∑ n ∈ Icc 1 x, (hooleyDelta n : ℝ) / n := by
        gcongr; exact le_max_left _ _
    _ ≤ C1p * (y / Real.log x) * (C2 * Real.log x * ell x ^ (5 / 2 : ℝ)) := by
        gcongr; exact hmean x hx1
    _ = C1p * C2 * y * ell x ^ (5 / 2 : ℝ) := by field_simp
    _ ≤ (C1p * C2 + 1) * y * ell x ^ (5 / 2 : ℝ) := by gcongr; linarith

/-- `ℓ(x)^{5/2} ≪ x^{1/40}`. -/
lemma ell_pow_le (x : ℕ) (hx : 1 ≤ x) : ell x ^ (5 / 2 : ℝ) ≤ 101 ^ (5 / 2 : ℝ)
    * (x : ℝ) ^ (1 / 40 : ℝ) := by
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx'
  have h100 : Real.log x ≤ 100 * (x : ℝ) ^ (1 / 100 : ℝ) := by
    have := Real.log_le_rpow_div (show (0 : ℝ) ≤ x by positivity)
        (show (0 : ℝ) < 1 / 100 by norm_num)
    linarith
  have hll : Real.log (Real.log x) ≤ Real.log x := Real.log_le_self hlx
  have h1 : (1 : ℝ) ≤ (x : ℝ) ^ (1 / 100 : ℝ) := Real.one_le_rpow hx' (by norm_num)
  have hell : ell x ≤ 101 * (x : ℝ) ^ (1 / 100 : ℝ) := by
    unfold ell; apply max_le <;> linarith
  calc ell x ^ (5 / 2 : ℝ) ≤ (101 * (x : ℝ) ^ (1 / 100 : ℝ)) ^ (5 / 2 : ℝ) :=
        Real.rpow_le_rpow (by linarith [one_le_ell x]) hell (by norm_num)
    _ = 101 ^ (5 / 2 : ℝ) * (x : ℝ) ^ (1 / 40 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by positivity)]
        norm_num

/-- **Main conditional theorem.** Assuming the theorems of Nair–Tenenbaum (1998) and
de la Bretèche–Tenenbaum (2025), `P(a, b) ≪ a^{3/10} √(log log 3a)` uniformly in `0 < b < a`. -/
theorem P_le_loglog (hNT : NairTenenbaumDelta) (hBT : BretecheTenenbaumMean) :
    ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
      (P a b : ℝ) ≤ C * (a : ℝ) ^ (3 / 10 : ℝ) * Real.sqrt (Real.log (Real.log (3 * a))) := by
  obtain ⟨C, hC, hP⟩ := P_le_of_shortDivisorBound (shortDivisorBound_of_hooley hNT hBT)
    (fun x => Real.one_le_rpow (one_le_ell x) (by norm_num))
    ⟨_, fun x hx => ell_pow_le x hx⟩
  -- `log log 3 > 0`
  have hl3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have := Real.exp_one_lt_d9; linarith
  set c0 := Real.log (Real.log 3)
  have hc0 : 0 < c0 := Real.log_pos hl3
  set K := 1 + 1 / Real.sqrt c0
  have hK : 0 < K := by positivity
  refine ⟨C * K, by positivity, fun a b hb hba => ?_⟩
  have ha1 : 1 ≤ a := by omega
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have h3a : (3 : ℝ) ≤ 3 * a := by linarith
  have hlog3a : Real.log 3 ≤ Real.log (3 * a) := Real.log_le_log (by norm_num) h3a
  have hll3a : c0 ≤ Real.log (Real.log (3 * a)) := Real.log_le_log (by linarith) hlog3a
  have hsq0 : Real.sqrt c0 ≤ Real.sqrt (Real.log (Real.log (3 * a))) := Real.sqrt_le_sqrt hll3a
  have hsqc0 : 0 < Real.sqrt c0 := Real.sqrt_pos.mpr hc0
  -- `ℓ(a)^{1/2} ≤ K √(log log 3a)`
  have hell : (ell a ^ (5 / 2 : ℝ)) ^ (1 / 5 : ℝ) ≤ K
      * Real.sqrt (Real.log (Real.log (3 * a))) := by
    rw [← Real.rpow_mul (by linarith [one_le_ell a]), show (5 / 2 : ℝ) * (1 /
        5) = 1 / 2 by norm_num,
      ← Real.sqrt_eq_rpow]
    have hs1 : 1 ≤ Real.sqrt (Real.log (Real.log (3 * a))) / Real.sqrt c0 := by
      rw [le_div_iff₀ hsqc0]; linarith
    unfold ell
    rcases le_total 1 (Real.log (Real.log a)) with h | h
    · rw [max_eq_right h]
      have hla : Real.log a ≤ Real.log (3 * a) := Real.log_le_log (by linarith) (by linarith)
      have hlapos : 0 < Real.log a := by
        by_contra hneg; push Not at hneg
        have : Real.log (Real.log a) ≤ 0 := by
          rcases eq_or_lt_of_le hneg with h0 | h0
          · rw [h0]; simp
          · have := Real.log_nonneg ha; linarith
        linarith
      have : Real.sqrt (Real.log (Real.log a)) ≤ Real.sqrt (Real.log (Real.log (3 * a))) :=
        Real.sqrt_le_sqrt (Real.log_le_log hlapos hla)
      have : 0 ≤ Real.sqrt (Real.log (Real.log (3 * a))) / Real.sqrt c0 := by positivity
      calc Real.sqrt (Real.log (Real.log a)) ≤ Real.sqrt (Real.log (Real.log (3 * a))) := by
            assumption
        _ ≤ K * Real.sqrt (Real.log (Real.log (3 * a))) :=
            le_mul_of_one_le_left (Real.sqrt_nonneg _) (by
              simp only [K]
              have : 0 ≤ 1 / Real.sqrt c0 := by positivity
              linarith)
    · rw [max_eq_left h, Real.sqrt_one]
      calc (1 : ℝ) ≤ Real.sqrt (Real.log (Real.log (3 * a))) / Real.sqrt c0 := hs1
        _ = 1 / Real.sqrt c0 * Real.sqrt (Real.log (Real.log (3 * a))) := by ring
        _ ≤ K * Real.sqrt (Real.log (Real.log (3 * a))) := by
            gcongr; simp only [K]; linarith
  calc (P a b : ℝ) ≤ C * (a : ℝ) ^ (3 / 10 : ℝ) * (ell a ^ (5 / 2 : ℝ)) ^ (1 / 5 : ℝ) :=
        hP a b hb hba
    _ ≤ C * (a : ℝ) ^ (3 / 10 : ℝ) * (K * Real.sqrt (Real.log (Real.log (3 * a)))) := by
        gcongr
    _ = C * K * (a : ℝ) ^ (3 / 10 : ℝ) * Real.sqrt (Real.log (Real.log (3 * a))) := by ring

end PierceLengthBound
