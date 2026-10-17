/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
import Mathlib

/-!
# Geometric sums of `min(α 2^{-k/3}, β 2^{k/2})`

`sum_min_le`: `∑_{k < L} min(α (2^k)^{-1/3}, β (2^k)^{1/2}) ≤ 9 α^{3/5} β^{2/5}`, uniformly in `L`.
It is the case `s = 1/3`, `t = 1/2` of `sum_min_le_gen`, which bounds
`∑_{k < L} min(α (2^k)^{-s}, β (2^k)^t)` by `C_{s,t} α^{t/(s+t)} β^{s/(s+t)}`.
This is the reason no factor `log a` appears when the two window bounds are summed over the
dyadic ranges.
-/

namespace PierceBound

open Finset

/-- Increasing geometric terms below `X` sum to at most `ρ X / (ρ - 1)`. -/
lemma geom_low {ρ : ℝ} (hρ : 1 < ρ) {X : ℝ} (hX : 0 ≤ X) (L : ℕ) :
    ∑ k ∈ range L, (if ρ ^ k ≤ X then ρ ^ k else 0) ≤ ρ * X / (ρ - 1) := by
  have hρ1 : 0 < ρ - 1 := by linarith
  suffices h : ∀ L, ∑ k ∈ range L, (if ρ ^ k ≤ X then ρ ^ k else 0) ≤ (ρ ^ L - 1) / (ρ - 1) ∧
      ∑ k ∈ range L, (if ρ ^ k ≤ X then ρ ^ k else 0) ≤ ρ * X / (ρ - 1) from (h L).2
  intro L
  induction L with
  | zero => simp only [range_zero, sum_empty, pow_zero, sub_self, zero_div, Std.le_refl,
      true_and]; positivity
  | succ L ih =>
    rw [sum_range_succ]
    obtain ⟨ih1, ih2⟩ := ih
    have hpow : ρ ^ (L + 1) = ρ * ρ ^ L := by ring
    have hpos : 0 ≤ ρ ^ L := by positivity
    split_ifs with hk
    · have e : (ρ ^ L - 1) / (ρ - 1) + ρ ^ L = (ρ ^ (L + 1) - 1) / (ρ - 1) := by
        field_simp; ring
      refine ⟨by linarith, ?_⟩
      calc _ ≤ (ρ ^ (L + 1) - 1) / (ρ - 1) := by linarith
        _ ≤ ρ ^ (L + 1) / (ρ - 1) := by gcongr; linarith
        _ = ρ * ρ ^ L / (ρ - 1) := by rw [hpow]
        _ ≤ ρ * X / (ρ - 1) := by gcongr
    · refine ⟨?_, by linarith⟩
      have : (ρ ^ L - 1) / (ρ - 1) ≤ (ρ ^ (L + 1) - 1) / (ρ - 1) := by
        gcongr <;> linarith
      linarith

/-- Decreasing geometric terms below `Y` sum to at most `Y / (1 - σ)`. -/
lemma geom_high {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {Y : ℝ} (hY : 0 ≤ Y) (L : ℕ) :
    ∑ k ∈ range L, (if σ ^ k ≤ Y then σ ^ k else 0) ≤ Y / (1 - σ) := by
  have h1σ : 0 < 1 - σ := by linarith
  set f : ℕ → ℝ := fun L => ∑ k ∈ range L, (if σ ^ k ≤ Y then σ ^ k else 0) with hf
  suffices h : ∀ L, (Y < σ ^ L → f L = 0) ∧ (σ ^ L ≤ Y → f L ≤ (Y - σ ^ L) / (1 - σ)) by
    change f L ≤ Y / (1 - σ)
    by_cases hL : σ ^ L ≤ Y
    · have := (h L).2 hL
      have : 0 ≤ σ ^ L := by positivity
      calc f L ≤ (Y - σ ^ L) / (1 - σ) := (h L).2 hL
        _ ≤ Y / (1 - σ) := by gcongr; linarith
    · rw [(h L).1 (lt_of_not_ge hL)]; positivity
  intro L
  induction L with
  | zero =>
    refine ⟨fun _ => by simp [f], fun h => ?_⟩
    simp only [f, range_zero, sum_empty, pow_zero] at h ⊢
    exact div_nonneg (by linarith) h1σ.le
  | succ L ih =>
    have hstep : f (L + 1) = f L + (if σ ^ L ≤ Y then σ ^ L else 0) := by
      simp only [f]; rw [sum_range_succ]
    have hpow : σ ^ (L + 1) = σ * σ ^ L := by ring
    have hpos : 0 < σ ^ L := by positivity
    have hle : σ ^ (L + 1) ≤ σ ^ L := by rw [hpow]; nlinarith
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hL : Y < σ ^ L := lt_of_lt_of_le h hle
      rw [hstep, ih.1 hL, ite_eq_right (not_le.mpr hL)]; simp
    · rw [hstep]
      by_cases hL : σ ^ L ≤ Y
      · rw [ite_eq_left hL]
        have := ih.2 hL
        have e : (Y - σ ^ L) / (1 - σ) + σ ^ L = (Y - σ ^ (L + 1)) / (1 - σ) := by
          rw [hpow]; field_simp; ring
        linarith
      · rw [ite_eq_right hL, ih.1 (lt_of_not_ge hL)]
        simp only [zero_add]
        exact div_nonneg (by linarith) h1σ.le

/-- **The dyadic min-sum, general exponents.** For `α, β, s, t > 0`,
`∑_{k < L} min(α (2^k)^{-s}, β (2^k)^t) ≤ C_{s,t} α^{t/(s+t)} β^{s/(s+t)}` with
`C_{s,t} = 1/(1 - 2^{-s}) + 2^t/(2^t - 1)`. -/
theorem sum_min_le_gen {α β s t : ℝ} (hα : 0 < α) (hβ : 0 < β) (hs : 0 < s) (ht : 0 < t)
    (L : ℕ) :
    ∑ k ∈ range L, min (α * ((2 : ℝ) ^ k) ^ (-s)) (β * ((2 : ℝ) ^ k) ^ t) ≤
      (1 / (1 - (2 : ℝ) ^ (-s)) + (2 : ℝ) ^ t / ((2 : ℝ) ^ t - 1)) *
        (α ^ (t / (s + t)) * β ^ (s / (s + t))) := by
  set M := α ^ (t / (s + t)) * β ^ (s / (s + t)) with hM
  have hst : 0 < s + t := by linarith
  have hMpos : 0 < M := by positivity
  set ρ : ℝ := (2 : ℝ) ^ t with hρ
  set σ : ℝ := (2 : ℝ) ^ (-s) with hσ
  have hρk : ∀ k : ℕ, ((2 : ℝ) ^ k) ^ t = ρ ^ k := fun k => by
    rw [hρ, ← Real.rpow_pow_comm (by norm_num)]
  have hσk : ∀ k : ℕ, ((2 : ℝ) ^ k) ^ (-s) = σ ^ k := fun k => by
    rw [hσ, ← Real.rpow_pow_comm (by norm_num)]
  have hρ1 : 1 < ρ := Real.one_lt_rpow (by norm_num) ht
  have hσ0 : 0 < σ := by positivity
  have hσ1 : σ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  -- `M^{s+t} = α^t β^s` and `(σ^k)^t (ρ^k)^s = 1`
  have hMst : M ^ (s + t) = α ^ t * β ^ s := by
    rw [hM, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hα.le,
      ← Real.rpow_mul hβ.le, div_mul_cancel₀ _ hst.ne', div_mul_cancel₀ _ hst.ne']
  have hρσ : ∀ k : ℕ, (σ ^ k) ^ t * (ρ ^ k) ^ s = 1 := by
    intro k
    rw [← hσk, ← hρk, ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
      ← Real.rpow_add (by positivity)]
    rw [show -s * t + t * s = 0 by ring, Real.rpow_zero]
  have hpt : ∀ k : ℕ, min (α * σ ^ k) (β * ρ ^ k) ≤
      (if σ ^ k ≤ M / α then α * σ ^ k else 0) + (if ρ ^ k ≤ M / β then β * ρ ^ k else 0) := by
    intro k
    have hX : 0 < α * σ ^ k := by positivity
    have hY : 0 < β * ρ ^ k := by positivity
    by_cases hYM : β * ρ ^ k ≤ M
    · have h1 : ρ ^ k ≤ M / β := by rw [le_div_iff₀ hβ]; linarith
      rw [ite_eq_left h1]
      have : 0 ≤ (if σ ^ k ≤ M / α then α * σ ^ k else 0) := by split_ifs <;> positivity
      linarith [min_le_right (α * σ ^ k) (β * ρ ^ k)]
    · push Not at hYM
      have hXM : α * σ ^ k < M := by
        by_contra h; push Not at h
        have h3 : M ^ t ≤ (α * σ ^ k) ^ t := Real.rpow_le_rpow hMpos.le h ht.le
        have h2 : M ^ s < (β * ρ ^ k) ^ s := Real.rpow_lt_rpow hMpos.le hYM hs
        have hlt : M ^ t * M ^ s < (α * σ ^ k) ^ t * (β * ρ ^ k) ^ s := by
          calc M ^ t * M ^ s ≤ (α * σ ^ k) ^ t * M ^ s := by gcongr
            _ < (α * σ ^ k) ^ t * (β * ρ ^ k) ^ s := by gcongr
        have e : (α * σ ^ k) ^ t * (β * ρ ^ k) ^ s = M ^ t * M ^ s := by
          rw [Real.mul_rpow hα.le (by positivity), Real.mul_rpow hβ.le (by positivity),
            ← Real.rpow_add hMpos, add_comm t s, hMst]
          calc α ^ t * (σ ^ k) ^ t * (β ^ s * (ρ ^ k) ^ s)
              = α ^ t * β ^ s * ((σ ^ k) ^ t * (ρ ^ k) ^ s) := by ring
            _ = α ^ t * β ^ s := by rw [hρσ, mul_one]
        linarith
      have h1 : σ ^ k ≤ M / α := by rw [le_div_iff₀ hα]; linarith
      rw [ite_eq_left h1]
      have : 0 ≤ (if ρ ^ k ≤ M / β then β * ρ ^ k else 0) := by split_ifs <;> positivity
      linarith [min_le_left (α * σ ^ k) (β * ρ ^ k)]
  have hlow := geom_low hρ1 (div_pos hMpos hβ).le L
  have hhigh := geom_high hσ0 hσ1 (div_pos hMpos hα).le L
  calc ∑ k ∈ range L, min (α * ((2 : ℝ) ^ k) ^ (-s)) (β * ((2 : ℝ) ^ k) ^ t)
      = ∑ k ∈ range L, min (α * σ ^ k) (β * ρ ^ k) := by
        refine sum_congr rfl fun k _ => ?_; rw [hσk, hρk]
    _ ≤ ∑ k ∈ range L, ((if σ ^ k ≤ M / α then α * σ ^ k else 0) +
          (if ρ ^ k ≤ M / β then β * ρ ^ k else 0)) := sum_le_sum fun k _ => hpt k
    _ = α * ∑ k ∈ range L, (if σ ^ k ≤ M / α then σ ^ k else 0) +
          β * ∑ k ∈ range L, (if ρ ^ k ≤ M / β then ρ ^ k else 0) := by
        rw [sum_add_distrib, mul_sum, mul_sum]
        congr 1 <;> refine sum_congr rfl fun k _ => ?_ <;> split_ifs <;> simp
    _ ≤ α * ((M / α) / (1 - σ)) + β * (ρ * (M / β) / (ρ - 1)) := by gcongr
    _ = (1 / (1 - σ) + ρ / (ρ - 1)) * M := by
        have : (1 : ℝ) - σ ≠ 0 := by linarith
        have : ρ - 1 ≠ 0 := by linarith
        field_simp

/-- **The dyadic min-sum.** For `α, β > 0`,
`∑_{k < L} min(α (2^k)^{-1/3}, β (2^k)^{1/2}) ≤ 9 α^{3/5} β^{2/5}`. -/
theorem sum_min_le {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (L : ℕ) :
    ∑ k ∈ range L, min (α * ((2 : ℝ) ^ k) ^ (-(1 / 3 : ℝ))) (β * ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ)) ≤
      9 * (α ^ (3 / 5 : ℝ) * β ^ (2 / 5 : ℝ)) := by
  have h := sum_min_le_gen hα hβ (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num : (0 : ℝ) < 1 / 2) L
  rw [show (1 / 2 : ℝ) / (1 / 3 + 1 / 2) = 3 / 5 by norm_num,
    show (1 / 3 : ℝ) / (1 / 3 + 1 / 2) = 2 / 5 by norm_num] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  -- the constant `1/(1 - 2^{-1/3}) + √2/(√2 - 1) ≈ 8.26`
  set u : ℝ := (2 : ℝ) ^ (1 / 3 : ℝ)
  set v : ℝ := (2 : ℝ) ^ (1 / 2 : ℝ)
  have hu0 : 0 < u := by positivity
  have hv0 : 0 < v := by positivity
  have hu3 : u ^ 3 = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hv2 : v ^ 2 = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hu : 5 / 4 < u := by
    by_contra h; push Not at h; nlinarith [pow_le_pow_left₀ hu0.le h 3]
  have hv : 7 / 5 < v := by
    by_contra h; push Not at h; nlinarith [pow_le_pow_left₀ hv0.le h 2]
  rw [Real.rpow_neg (by norm_num), show 1 / (1 - u⁻¹) = u / (u - 1) by
    field_simp, div_add_div _ _ (by linarith) (by linarith), div_le_iff₀ (by nlinarith)]
  nlinarith [mul_pos (sub_pos.mpr hu) (sub_pos.mpr hv)]

end PierceBound
