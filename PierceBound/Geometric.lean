import Mathlib

/-!
# Geometric sums of `min(α 2^{-k/3}, β 2^{k/2})`

`sum_min_le`: `∑_{k < L} min(α (2^k)^{-1/3}, β (2^k)^{1/2}) ≤ 9 α^{3/5} β^{2/5}`, uniformly in `L`.
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
  | zero => simp; positivity
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
        gcongr <;> first | linarith | omega
      linarith

/-- Decreasing geometric terms below `Y` sum to at most `Y / (1 - σ)`. -/
lemma geom_high {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {Y : ℝ} (hY : 0 ≤ Y) (L : ℕ) :
    ∑ k ∈ range L, (if σ ^ k ≤ Y then σ ^ k else 0) ≤ Y / (1 - σ) := by
  have h1σ : 0 < 1 - σ := by linarith
  set f : ℕ → ℝ := fun L => ∑ k ∈ range L, (if σ ^ k ≤ Y then σ ^ k else 0) with hf
  suffices h : ∀ L, (Y < σ ^ L → f L = 0) ∧ (σ ^ L ≤ Y → f L ≤ (Y - σ ^ L) / (1 - σ)) by
    show f L ≤ Y / (1 - σ)
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
      rw [hstep, ih.1 hL, if_neg (not_le.mpr hL)]; simp
    · rw [hstep]
      by_cases hL : σ ^ L ≤ Y
      · rw [if_pos hL]
        have := ih.2 hL
        have e : (Y - σ ^ L) / (1 - σ) + σ ^ L = (Y - σ ^ (L + 1)) / (1 - σ) := by
          rw [hpow]; field_simp; ring
        linarith
      · rw [if_neg hL, ih.1 (lt_of_not_ge hL)]
        simp only [zero_add]
        exact div_nonneg (by linarith) h1σ.le

/-- **The dyadic min-sum.** For `α, β > 0`,
`∑_{k < L} min(α (2^k)^{-1/3}, β (2^k)^{1/2}) ≤ 9 α^{3/5} β^{2/5}`. -/
theorem sum_min_le {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (L : ℕ) :
    ∑ k ∈ range L, min (α * ((2 : ℝ) ^ k) ^ (-(1 / 3 : ℝ))) (β * ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ)) ≤
      9 * (α ^ (3 / 5 : ℝ) * β ^ (2 / 5 : ℝ)) := by
  set M := α ^ (3 / 5 : ℝ) * β ^ (2 / 5 : ℝ) with hM
  have hMpos : 0 < M := by positivity
  set ρ : ℝ := (2 : ℝ) ^ (1 / 2 : ℝ) with hρ
  set σ : ℝ := (2 : ℝ) ^ (-(1 / 3 : ℝ)) with hσ
  have hρk : ∀ k : ℕ, ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ) = ρ ^ k := by
    intro k
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), mul_comm]
  have hσk : ∀ k : ℕ, ((2 : ℝ) ^ k) ^ (-(1 / 3 : ℝ)) = σ ^ k := by
    intro k
    rw [hσ, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), mul_comm]
  -- `ρ > 1`, `ρ/(ρ-1) ≤ 4`, `0 < σ ≤ 4/5`
  have hρ2 : ρ ^ 2 = 2 := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : 4 / 3 ≤ ρ := by nlinarith
  have hσ3 : σ ^ 3 = 1 / 2 := by
    rw [hσ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hσ0 : 0 < σ := by positivity
  have hσ1 : σ ≤ 4 / 5 := by
    by_contra h; push Not at h
    have : (4 / 5 : ℝ) ^ 3 < σ ^ 3 := by gcongr
    rw [hσ3] at this; norm_num at this
  -- the key relation `X³ Y² = M⁵`
  have hM5 : M ^ 5 = α ^ 3 * β ^ 2 := by
    rw [hM, mul_pow, ← Real.rpow_natCast (α ^ (3 / 5 : ℝ)), ← Real.rpow_natCast (β ^ (2 / 5 : ℝ)),
      ← Real.rpow_mul hα.le, ← Real.rpow_mul hβ.le]
    norm_num
  have hρσ : ∀ k : ℕ, (σ ^ k) ^ 3 * (ρ ^ k) ^ 2 = 1 := by
    intro k
    rw [← pow_mul, ← pow_mul, mul_comm k 3, mul_comm k 2, pow_mul, pow_mul, hσ3, hρ2,
      ← mul_pow]; norm_num
  have hpt : ∀ k : ℕ, min (α * σ ^ k) (β * ρ ^ k) ≤
      (if σ ^ k ≤ M / α then α * σ ^ k else 0) + (if ρ ^ k ≤ M / β then β * ρ ^ k else 0) := by
    intro k
    have hX : 0 < α * σ ^ k := by positivity
    have hY : 0 < β * ρ ^ k := by positivity
    by_cases hYM : β * ρ ^ k ≤ M
    · have h1 : ρ ^ k ≤ M / β := by rw [le_div_iff₀ hβ]; linarith
      rw [if_pos h1]
      have : 0 ≤ (if σ ^ k ≤ M / α then α * σ ^ k else 0) := by split_ifs <;> positivity
      linarith [min_le_right (α * σ ^ k) (β * ρ ^ k)]
    · push Not at hYM
      have hXM : α * σ ^ k < M := by
        by_contra h; push Not at h
        have : M ^ 3 * M ^ 2 < (α * σ ^ k) ^ 3 * (β * ρ ^ k) ^ 2 := by
          have h3 : M ^ 3 ≤ (α * σ ^ k) ^ 3 := by gcongr
          have h2 : M ^ 2 < (β * ρ ^ k) ^ 2 := by gcongr
          calc M ^ 3 * M ^ 2 ≤ (α * σ ^ k) ^ 3 * M ^ 2 := by gcongr
            _ < (α * σ ^ k) ^ 3 * (β * ρ ^ k) ^ 2 := by gcongr
        have e : (α * σ ^ k) ^ 3 * (β * ρ ^ k) ^ 2 = M ^ 3 * M ^ 2 := by
          rw [mul_pow, mul_pow, show M ^ 3 * M ^ 2 = M ^ 5 by ring, hM5]
          calc α ^ 3 * (σ ^ k) ^ 3 * (β ^ 2 * (ρ ^ k) ^ 2)
              = α ^ 3 * β ^ 2 * ((σ ^ k) ^ 3 * (ρ ^ k) ^ 2) := by ring
            _ = α ^ 3 * β ^ 2 := by rw [hρσ, mul_one]
        linarith
      have h1 : σ ^ k ≤ M / α := by rw [le_div_iff₀ hα]; linarith
      rw [if_pos h1]
      have : 0 ≤ (if ρ ^ k ≤ M / β then β * ρ ^ k else 0) := by split_ifs <;> positivity
      linarith [min_le_left (α * σ ^ k) (β * ρ ^ k)]
  have hlow := geom_low (by linarith : 1 < ρ) (div_pos hMpos hβ).le L
  have hhigh := geom_high hσ0 (by linarith : σ < 1) (div_pos hMpos hα).le L
  calc ∑ k ∈ range L, min (α * ((2 : ℝ) ^ k) ^ (-(1 / 3 : ℝ))) (β * ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ))
      = ∑ k ∈ range L, min (α * σ ^ k) (β * ρ ^ k) := by
        refine sum_congr rfl fun k _ => ?_; rw [hσk, hρk]
    _ ≤ ∑ k ∈ range L, ((if σ ^ k ≤ M / α then α * σ ^ k else 0) +
          (if ρ ^ k ≤ M / β then β * ρ ^ k else 0)) := sum_le_sum fun k _ => hpt k
    _ = α * ∑ k ∈ range L, (if σ ^ k ≤ M / α then σ ^ k else 0) +
          β * ∑ k ∈ range L, (if ρ ^ k ≤ M / β then ρ ^ k else 0) := by
        rw [sum_add_distrib, mul_sum, mul_sum]
        congr 1 <;> refine sum_congr rfl fun k _ => ?_ <;> split_ifs <;> simp
    _ ≤ α * ((M / α) / (1 - σ)) + β * (ρ * (M / β) / (ρ - 1)) := by gcongr
    _ = M * (1 / (1 - σ) + ρ / (ρ - 1)) := by field_simp
    _ ≤ M * 9 := by
        gcongr
        have h1 : 1 / (1 - σ) ≤ 5 := by
          rw [div_le_iff₀ (by linarith)]; linarith
        have h2 : ρ / (ρ - 1) ≤ 4 := by
          rw [div_le_iff₀ (by linarith)]; linarith
        linarith
    _ = 9 * M := by ring

end PierceBound
