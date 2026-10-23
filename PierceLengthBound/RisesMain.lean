/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.Rises
public import PierceLengthBound.Geometric
public import PierceLengthBound.Main

/-!
# `P(a, b) ≪ a^{1/4} √R`

`R = rises a b + 1`, where `rises a b` counts the indices `i` with `kᵢ < k_{i+1}` among the
quotient increments `kᵢ = ⌊a/b_{i+1}⌋ - ⌊a/bᵢ⌋` of the whole orbit. Each dyadic window obeys
the three bounds of Proposition 11.4 (`visits_real_rises`), and summing them with
`sum_min_le_gen` gives `P(a, b) ≪ a^{1/4} √R` (`P_le_rises`, Theorem 1.5). In particular an
orbit with nonincreasing quotient increments has length `O(a^{1/4})` (`P_le_of_no_rises`).
-/

@[expose] public section

namespace PierceLengthBound

open Finset

/-- The quotient increment `kᵢ` of the orbit. Its body is fixed by `Challenge.lean`; it is the
window increment `incr` of the orbit (`incrO_eq_incr`). -/
def incrO (a b i : ℕ) : ℕ := a / orb a b (i + 1) - a / orb a b i

lemma incrO_eq_incr (a b i : ℕ) : incrO a b i = incr a (orb a b) i := rfl

/-- The number of rises `kᵢ < k_{i+1}` in the quotient increments of the orbit of `b`. -/
def rises (a b : ℕ) : ℕ := ((range (P a b - 2)).filter
    fun i => incrO a b i < incrO a b (i + 1)).card

/-- The rises inside a window are rises of the orbit. -/
lemma windowRises_le {a b k : ℕ} (hba : b ≤ a) (h : (visits a b k).Nonempty) :
    windowRises a (fun j => orb a b ((visits a b k).min' h + j)) (visits a b k).card ≤
      rises a b := by
  classical
  set s := (visits a b k).min' h
  set T := (visits a b k).card
  have W := visits_window hba h
  unfold windowRises rises
  apply card_le_card_of_injOn (fun j => s + j)
  · intro j hj
    obtain ⟨hjT, hrise⟩ := mem_filter.mp (Finset.mem_coe.mp hj)
    have hjT' := mem_range.mp hjT
    have hpos := W.pos (j := j + 2) (by omega)
    have hlt : s + (j + 2) < P a b := lt_P_of_orb_pos hpos
    refine Finset.mem_coe.mpr (mem_filter.mpr ⟨mem_range.mpr (show s + j < P a b - 2 by omega), ?_⟩)
    rw [incrO_eq_incr, incrO_eq_incr]
    exact hrise
  · intro i _ j _ hij
    simpa using hij

/-- **One window.** The number of visits to `[2^k, 2^{k+1})` is at most
`1 + √R · min(√(8a) (2^k)^{-1/2}, √2 (2^k)^{1/2}) + min(a (2^k)^{-1}, 30 (2^k)^{1/3})`. -/
theorem visits_real_rises {a b k : ℕ} (hba : b ≤ a) :
    ((visits a b k).card : ℝ) ≤ 1 + Real.sqrt (rises a b + 1) *
        min (Real.sqrt (8 * a) * ((2 : ℝ) ^ k) ^ (-(1 / 2 : ℝ)))
          (Real.sqrt 2 * ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ)) +
      min ((a : ℝ) * ((2 : ℝ) ^ k) ^ (-(1 : ℝ))) (30 * ((2 : ℝ) ^ k) ^ (1 / 3 : ℝ)) := by
  set T := (visits a b k).card with hTdef
  set R : ℝ := rises a b + 1
  set Ar : ℝ := (2 : ℝ) ^ k
  have hAr : 1 ≤ Ar := one_le_pow₀ (by norm_num)
  have hAr0 : 0 < Ar := by linarith
  set X := Real.sqrt (8 * a) * Ar ^ (-(1 / 2 : ℝ))
  set Y := Real.sqrt 2 * Ar ^ (1 / 2 : ℝ)
  set Wr := (a : ℝ) * Ar ^ (-(1 : ℝ))
  set Z := 30 * Ar ^ (1 / 3 : ℝ)
  have hR1 : 1 ≤ R := by simp only [R]; linarith [(Nat.cast_nonneg (rises a b) : (0 : ℝ) ≤ _)]
  have hsR : 0 ≤ Real.sqrt R := Real.sqrt_nonneg _
  have hX : 0 ≤ X := by positivity
  have hY : 0 ≤ Y := by positivity
  have hW : 0 ≤ Wr := by positivity
  have hZ : 0 ≤ Z := by positivity
  have hmin1 : 0 ≤ min X Y := le_min hX hY
  have hmin2 : 0 ≤ min Wr Z := le_min hW hZ
  by_cases hT : T ≤ 1
  · have : (T : ℝ) ≤ 1 := by exact_mod_cast hT
    have := mul_nonneg hsR hmin1
    linarith
  have hne : (visits a b k).Nonempty := by rw [← card_pos]; omega
  have W := visits_window hba hne
  have hRw : ((windowRises a (fun j => orb a b ((visits a b k).min' hne + j)) T : ℕ) : ℝ) + 1 ≤
      R := by
    have := windowRises_le hba hne
    simp only [R]
    have : ((windowRises a (fun j => orb a b ((visits a b k).min' hne + j)) T : ℕ) : ℝ) ≤
        rises a b := by exact_mod_cast this
    linarith
  set ρ := windowRises a (fun j => orb a b ((visits a b k).min' hne + j)) T
  have hA1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hAcast : ((2 ^ k : ℕ) : ℝ) = Ar := by push_cast; rfl
  have hT1 : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hsqA : Real.sqrt Ar = Ar ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow Ar
  -- Proposition 11.4(1): `T - 1 ≤ √R Y`
  have hdrop : (T : ℝ) - 1 ≤ Real.sqrt R * Y := by
    have h := W.rises_drop_bound (by omega)
    have h' : (((T - 1) ^ 2 : ℕ) : ℝ) ≤ ((2 * (ρ + 1) * (2 ^ k - 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast [Nat.cast_sub hA1] at h'
    rw [hT1] at h'
    have hle : ((T : ℝ) - 1) ^ 2 ≤ 2 * R * Ar := by
      have : (2 : ℝ) * ((ρ : ℝ) + 1) * ((2 : ℝ) ^ k - 1) ≤ 2 * R * Ar := by
        have : (2 : ℝ) ^ k - 1 ≤ Ar := by simp only [Ar]; linarith
        have hρ0 : (0 : ℝ) ≤ (ρ : ℝ) + 1 := by positivity
        calc (2 : ℝ) * ((ρ : ℝ) + 1) * ((2 : ℝ) ^ k - 1) ≤ 2 * R * ((2 : ℝ) ^ k - 1) := by
              gcongr
          _ ≤ 2 * R * Ar := by gcongr
      linarith
    have := Real.sqrt_le_sqrt hle
    rw [Real.sqrt_sq (by linarith)] at this
    calc (T : ℝ) - 1 ≤ Real.sqrt (2 * R * Ar) := this
      _ = Real.sqrt R * Y := by
        simp only [Y]
        rw [show 2 * R * Ar = R * (2 * Ar) by ring, Real.sqrt_mul (by linarith),
          Real.sqrt_mul (by norm_num), hsqA]
  -- Proposition 11.4(2): `T - 1 ≤ a / A`
  have hquot : (T : ℝ) - 1 ≤ Wr := by
    have h := W.rises_quot_bound (by omega)
    have : ((T - 1 : ℕ) : ℝ) ≤ ((a / 2 ^ k : ℕ) : ℝ) := by exact_mod_cast h
    rw [hT1] at this
    calc (T : ℝ) - 1 ≤ ((a / 2 ^ k : ℕ) : ℝ) := this
      _ ≤ (a : ℝ) / ((2 ^ k : ℕ) : ℝ) := Nat.cast_div_le
      _ = Wr := by rw [hAcast]; simp only [Wr, Real.rpow_neg_one, div_eq_mul_inv]
  have hgoal : (T : ℝ) - 1 ≤ Real.sqrt R * min X Y + min Wr Z := by
    by_cases h6 : 6 * 2 ^ k ≤ a
    · -- Proposition 11.4(3)
      obtain ⟨l, s, hls, hl, hs⟩ := W.rises_incr_bound (by omega) h6
      have hl' : (l : ℝ) ≤ Real.sqrt R * X := by
        have : ((l ^ 2 : ℕ) : ℝ) ≤ ((8 * (ρ + 1) * (a / 2 ^ k) : ℕ) : ℝ) := by exact_mod_cast hl
        push_cast at this
        have hdiv : ((a / 2 ^ k : ℕ) : ℝ) ≤ (a : ℝ) / Ar := by
          rw [← hAcast]; exact Nat.cast_div_le
        have hle : (l : ℝ) ^ 2 ≤ R * (8 * a / Ar) := by
          calc (l : ℝ) ^ 2 ≤ 8 * ((ρ : ℝ) + 1) * ((a / 2 ^ k : ℕ) : ℝ) := this
            _ ≤ 8 * R * ((a : ℝ) / Ar) := by gcongr
            _ = R * (8 * a / Ar) := by ring
        have := Real.sqrt_le_sqrt hle
        rw [Real.sqrt_sq (by positivity)] at this
        calc (l : ℝ) ≤ Real.sqrt (R * (8 * a / Ar)) := this
          _ = Real.sqrt R * X := by
            simp only [X]
            rw [Real.sqrt_mul (by linarith), Real.sqrt_div' _ hAr0.le, hsqA,
              Real.rpow_neg hAr0.le]
            ring
      have hs' : (s : ℝ) ≤ Z := by
        have hs3 : ((s ^ 3 : ℕ) : ℝ) ≤ ((26244 * 2 ^ k : ℕ) : ℝ) := by exact_mod_cast hs
        push_cast at hs3
        have hZ3 : Z ^ 3 = 27000 * Ar := by
          simp only [Z]
          rw [mul_pow, ← Real.rpow_mul_natCast hAr0.le]; norm_num
        have : (s : ℝ) ^ 3 ≤ Z ^ 3 := by rw [hZ3]; simp only [Ar] at hZ3 ⊢; linarith
        exact (pow_le_pow_iff_left₀ (by positivity) hZ (by norm_num)).mp this
      have hTls : (T : ℝ) - 1 = l + s := by rw [← hT1]; exact_mod_cast hls
      by_cases hZW : Z ≤ Wr
      · rw [min_eq_right hZW]
        rcases le_total X Y with hxy | hxy
        · rw [min_eq_left hxy]; linarith
        · rw [min_eq_right hxy]
          have := mul_nonneg hsR hmin1
          linarith
      · push Not at hZW
        rw [min_eq_left hZW.le]
        have := mul_nonneg hsR hmin1
        linarith
    · -- `a < 6A`, so `a / A < 6 ≤ Z`
      push Not at h6
      have hWZ : Wr ≤ Z := by
        have h1 : Wr < 6 := by
          simp only [Wr, Real.rpow_neg_one]
          rw [← div_eq_mul_inv, div_lt_iff₀ hAr0]
          have : (a : ℝ) < 6 * ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast h6
          rw [hAcast] at this; linarith
        have h2 : 1 ≤ Ar ^ (1 / 3 : ℝ) := Real.one_le_rpow hAr (by norm_num)
        simp only [Z]; linarith
      rw [min_eq_left hWZ]
      have := mul_nonneg hsR hmin1
      linarith
  linarith

/-- **Theorem 1.5.** `P(a, b) ≪ a^{1/4} √R`, with `R` one more than the number of rises in the
quotient increments. -/
theorem P_le_rises : ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (rises a b + 1) := by
  obtain ⟨CL, hCL, hlog⟩ := log_add_one_le_rpow (1 / 4) (by norm_num)
  set C1 : ℝ := 1 / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))) + (2 : ℝ) ^ (1 / 2 : ℝ) /
      ((2 : ℝ) ^ (1 / 2 : ℝ) - 1)
  set C2 : ℝ := 1 / (1 - (2 : ℝ) ^ (-(1 : ℝ))) + (2 : ℝ) ^ (1 / 3 : ℝ) / ((2 : ℝ) ^ (1 / 3 : ℝ) - 1)
  have hC1 : 0 < C1 := by
    have h1 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    have h2 : 1 < (2 : ℝ) ^ (1 / 2 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
    have : 0 < 1 / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))) := by apply div_pos one_pos; linarith
    have : 0 < (2 : ℝ) ^ (1 / 2 : ℝ) / ((2 : ℝ) ^ (1 / 2 : ℝ) - 1) := by
      apply div_pos (by positivity); linarith
    simp only [C1]; linarith
  have hC2 : 0 < C2 := by
    have h1 : (2 : ℝ) ^ (-(1 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    have h2 : 1 < (2 : ℝ) ^ (1 / 3 : ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
    have : 0 < 1 / (1 - (2 : ℝ) ^ (-(1 : ℝ))) := by apply div_pos one_pos; linarith
    have : 0 < (2 : ℝ) ^ (1 / 3 : ℝ) / ((2 : ℝ) ^ (1 / 3 : ℝ) - 1) := by
      apply div_pos (by positivity); linarith
    simp only [C2]; linarith
  set K30 : ℝ := (30 : ℝ) ^ (3 / 4 : ℝ)
  refine ⟨CL + 2 * C1 + C2 * K30, by positivity, fun a b hb hba => ?_⟩
  have ha1 : 1 ≤ a := by omega
  have ha : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have ha0 : (0 : ℝ) < a := by linarith
  set R : ℝ := rises a b + 1
  have hR1 : 1 ≤ R := by simp only [R]; linarith [(Nat.cast_nonneg (rises a b) : (0 : ℝ) ≤ _)]
  have hsR : 1 ≤ Real.sqrt R := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hR1
  have ha4 : 1 ≤ (a : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow ha (by norm_num)
  set L := Nat.log 2 a + 1
  have hP : (P a b : ℝ) ≤ L + Real.sqrt R * ∑ k ∈ range L,
        min (Real.sqrt (8 * a) * ((2 : ℝ) ^ k) ^ (-(1 / 2 : ℝ)))
          (Real.sqrt 2 * ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ)) +
      ∑ k ∈ range L, min ((a : ℝ) * ((2 : ℝ) ^ k) ^ (-(1 : ℝ)))
          (30 * ((2 : ℝ) ^ k) ^ (1 / 3 : ℝ)) := by
    rw [P_eq_sum_visits hba.le]
    push_cast
    calc ∑ k ∈ range L, ((visits a b k).card : ℝ)
        ≤ ∑ k ∈ range L, (1 + Real.sqrt R *
            min (Real.sqrt (8 * a) * ((2 : ℝ) ^ k) ^ (-(1 / 2 : ℝ)))
              (Real.sqrt 2 * ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ)) +
          min ((a : ℝ) * ((2 : ℝ) ^ k) ^ (-(1 : ℝ))) (30 * ((2 : ℝ) ^ k) ^ (1 / 3 : ℝ))) :=
          sum_le_sum fun k _ => visits_real_rises hba.le
      _ = _ := by
          rw [sum_add_distrib, sum_add_distrib, ← mul_sum]
          simp
  -- the two geometric sums
  have g1 := sum_min_le_gen (α := Real.sqrt (8 * a)) (β := Real.sqrt 2) (s := 1 / 2) (t := 1 / 2)
    (by positivity) (by positivity) (by norm_num) (by norm_num) L
  have g2 := sum_min_le_gen (α := (a : ℝ)) (β := 30) (s := 1) (t := 1 / 3) ha0 (by norm_num)
    (by norm_num) (by norm_num) L
  have e1 : Real.sqrt (8 * a) ^ ((1 / 2 : ℝ) / (1 / 2 + 1 / 2)) *
      Real.sqrt 2 ^ ((1 / 2 : ℝ) / (1 / 2 + 1 / 2)) = 2 * (a : ℝ) ^ (1 / 4 : ℝ) := by
    rw [show (1 / 2 : ℝ) / (1 / 2 + 1 / 2) = 1 / 2 by norm_num, Real.sqrt_eq_rpow,
      Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by norm_num),
      ← Real.mul_rpow (by positivity) (by norm_num),
      show 8 * (a : ℝ) * 2 = 2 ^ (4 : ℝ) * a by norm_num; ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by norm_num)]
    norm_num
  have e2 : (a : ℝ) ^ ((1 / 3 : ℝ) / (1 + 1 / 3)) * (30 : ℝ) ^ ((1 : ℝ) / (1 + 1 / 3)) =
      (a : ℝ) ^ (1 / 4 : ℝ) * K30 := by
    simp only [K30]; norm_num
  rw [e1] at g1
  rw [e2] at g2
  have hLa : (L : ℝ) ≤ CL * (a : ℝ) ^ (1 / 4 : ℝ) := hlog a ha1
  have g1' : Real.sqrt R * ∑ k ∈ range L,
      min (Real.sqrt (8 * a) * ((2 : ℝ) ^ k) ^ (-(1 / 2 : ℝ)))
        (Real.sqrt 2 * ((2 : ℝ) ^ k) ^ (1 / 2 : ℝ)) ≤
      Real.sqrt R * (C1 * (2 * (a : ℝ) ^ (1 / 4 : ℝ))) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    simpa only [C1] using g1
  have hK : 0 ≤ C2 * K30 := by positivity
  calc (P a b : ℝ) ≤ _ := hP
    _ ≤ CL * (a : ℝ) ^ (1 / 4 : ℝ) + Real.sqrt R * (C1 * (2 * (a : ℝ) ^ (1 / 4 : ℝ))) +
          C2 * ((a : ℝ) ^ (1 / 4 : ℝ) * K30) := by
        have : ∑ k ∈ range L, min ((a : ℝ) * ((2 : ℝ) ^ k) ^ (-(1 : ℝ)))
            (30 * ((2 : ℝ) ^ k) ^ (1 / 3 : ℝ)) ≤ C2 * ((a : ℝ) ^ (1 / 4 : ℝ) * K30) := by
          simpa only [C2] using g2
        linarith
    _ ≤ (CL + 2 * C1 + C2 * K30) * (a : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt R := by
        have h1 : CL * (a : ℝ) ^ (1 / 4 : ℝ) ≤ CL * (a : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt R :=
          le_mul_of_one_le_right (by positivity) hsR
        have h2 : C2 * ((a : ℝ) ^ (1 / 4 : ℝ) * K30) ≤
            C2 * K30 * (a : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt R := by
          have : C2 * ((a : ℝ) ^ (1 / 4 : ℝ) * K30) = C2 * K30 * (a : ℝ) ^ (1 / 4 : ℝ) := by ring
          rw [this]; exact le_mul_of_one_le_right (by positivity) hsR
        nlinarith

/-- **Theorem 1.5, second part.** If the quotient increments never rise,
`P(a, b) ≪ a^{1/4}`. -/
theorem P_le_of_no_rises : ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a → rises a b = 0 →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ (1 / 4 : ℝ) := by
  obtain ⟨C, hC, h⟩ := P_le_rises
  refine ⟨C, hC, fun a b hb hba h0 => ?_⟩
  have := h a b hb hba
  rw [h0] at this
  simpa using this

end PierceLengthBound
