/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.Hankel
public import PierceLengthBound.TwoState
public import PierceLengthBound.MinorCount

/-!
# Orbit states and their patterns

For an orbit state `i` put `kᵢ = q_{i+1} - qᵢ`, `dᵢ = bᵢ - b_{i+1}` (`kq`, `dq`), the six-step
integer `L(i)` (`Lz`, equal to `I₄(i)`), and the cofactors `U₁(i)`, `U₂(i)` (`U1z`, `U2z`). The
*pattern* of `i` is `θ(i) = (L(i), L(i+1), L(i+2), U₁(i), U₂(i), U₁(i+1), U₂(i+1)) ∈ ℤ⁷`
(`theta`) and its gaps are `κ(i) = (kᵢ, …, k_{i+4})` (`kap`).

This module collects the vocabulary shared by the window theorems and the curve counts:

* the basic facts at a state: `kq_pos`, `Lz_pos` (`L(i) ≥ 1`), the `k`- and `r`-relations
  `e0_at`, `e3_at`, the division relations `div_rel`, the normalization identity `mult_at`
  (Lemma 7.3), and `a_le_four` (`a ≤ 4 A qᵢ` when `bᵢ < 2A`);
* the good starts of a window run (Lemma 7.6): `good_card`, `goodStarts`, `mem_goodStarts`,
  with the telescoping `sum_kq` and the rounding lemma `abs_le_div`;
* the hypotheses `PatternHyps` taken by the pattern counts, and `goodStarts_patternHyps`;
* the pattern as signed minors of the `3 × 5` matrix `𝓜ᵢ` with rows `(dⱼ)`, `(kⱼ)`, `(rⱼ)`
  (`Mi`, `projθ`, `theta_eq`, `theta_eq_of_plk_eq`, `orbit_pattern_first`).
-/

@[expose] public section

namespace PierceLengthBound

open Finset

section Defs

variable (a b : ℕ)

/-- The increment `kᵢ = q_{i+1} - qᵢ`, in `ℤ`. -/
def kq (i : ℕ) : ℤ := (qq a b (i + 1) : ℤ) - qq a b i

/-- The drop `dᵢ = bᵢ - b_{i+1}`, in `ℤ`. -/
def dq (i : ℕ) : ℤ := (orb a b i : ℤ) - orb a b (i + 1)

/-- The six-step integer `L(i) = I₄(i)`. -/
def Lz (i : ℕ) : ℤ :=
  sixL (kq a b i) (kq a b (i + 1)) (kq a b (i + 2)) (kq a b (i + 3)) (dq a b i) (dq a b (i + 1))
    (dq a b (i + 2))

/-- The cofactor `U₁(i)`. -/
def U1z (i : ℕ) : ℤ :=
  pU1 (dq a b i) (dq a b (i + 2)) (dq a b (i + 3)) (kq a b i) (kq a b (i + 1)) (kq a b (i + 2))
    (kq a b (i + 3)) (kq a b (i + 4))

/-- The cofactor `U₂(i)`. -/
def U2z (i : ℕ) : ℤ :=
  pU2 (dq a b i) (dq a b (i + 1)) (dq a b (i + 3)) (kq a b i) (kq a b (i + 1)) (kq a b (i + 2))
    (kq a b (i + 3)) (kq a b (i + 4))

/-- The two-state pattern `θ(i)`. -/
def theta (i : ℕ) : Fin 7 → ℤ :=
  ![Lz a b i, Lz a b (i + 1), Lz a b (i + 2), U1z a b i, U2z a b i, U1z a b (i + 1),
    U2z a b (i + 1)]

/-- The gaps `κ(i) = (kᵢ, …, k_{i+4})`. -/
def kap (i : ℕ) : Fin 5 → ℤ :=
  ![kq a b i, kq a b (i + 1), kq a b (i + 2), kq a b (i + 3), kq a b (i + 4)]

end Defs

section State

variable {a b : ℕ}

lemma kq_pos {i : ℕ} (h : i + 1 < P a b) : 1 ≤ kq a b i := by
  have := qq_lt (a := a) (b := b) h
  unfold kq; omega

/-- `L(i) ≥ 1`: it is the positive Hankel invariant `I₄(i)`. -/
lemma Lz_pos (hba : b < a) {i : ℕ} (h : i + 5 < P a b) : 1 ≤ Lz a b i := by
  have h4 := hankelInv_four hba h
  have hp := hankelInv_pos hba (i := i) (r := 4) (by omega) (by omega)
  rw [h4] at hp
  have : (0 : ℤ) < Lz a b i := by
    unfold Lz kq dq; exact_mod_cast hp
  omega

/-- The `k`-relation `∑ₘ Uₘ(i) k_{i+m} = 0`. -/
lemma e0_at (i : ℕ) : -Lz a b (i + 1) * kq a b i + U1z a b i * kq a b (i + 1) +
    U2z a b i * kq a b (i + 2) + Lz a b i * kq a b (i + 3) = 0 :=
  null_k _ _ _ _ _ _ _ _ _

/-- The `r`-relation `∑ₘ Uₘ(i) r_m = 0`. -/
lemma e3_at (i : ℕ) : -Lz a b (i + 1) * (kq a b i ^ 2 + kq a b (i + 1)) +
    U1z a b i * (kq a b (i + 1) * (2 * kq a b i + kq a b (i + 1)) + kq a b (i + 2)) +
    U2z a b i * (kq a b (i + 2) * (2 * kq a b i + 2 * kq a b (i + 1) + kq a b (i + 2)) +
      kq a b (i + 3)) +
    Lz a b i * (kq a b (i + 3) * (2 * kq a b i + 2 * kq a b (i + 1) + 2 * kq a b (i + 2) +
      kq a b (i + 3)) + kq a b (i + 4)) = 0 :=
  null_r _ _ _ _ _ _ _ _ _

/-- The division relation at `i + m`, written with `qᵢ` and the increments. -/
lemma div_rel {i m : ℕ} (h : i + m < P a b) :
    ((qq a b i : ℤ) + ∑ t ∈ range m, kq a b (i + t)) * orb a b (i + m) + orb a b (i + m + 1) =
      a := by
  have e := orb_div (a := a) (b := b) (i := i + m) h
  have hs : (qq a b i : ℤ) + ∑ t ∈ range m, kq a b (i + t) = qq a b (i + m) := by
    clear e h
    induction m with
    | zero => simp
    | succ m ih => rw [sum_range_succ, ← add_assoc, ih]; simp [kq, ← add_assoc]
  rw [hs]
  have : ((orb a b (i + m) * qq a b (i + m) + orb a b (i + m + 1) : ℕ) : ℤ) = a := by
    exact_mod_cast e
  push_cast at this
  linarith

/-- The normalization identity `I₄(i) πᵢ(-qᵢ) = a H₄(kᵢ, …, k_{i+4})` at an orbit state. -/
lemma mult_at {i : ℕ} (h : i + 4 < P a b) :
    quart (-Lz a b (i + 1)) (U1z a b i) (U2z a b i) (Lz a b i) (kq a b i) (kq a b (i + 1))
      (kq a b (i + 2)) (qq a b i) =
    a * muH4 (kq a b i) (kq a b (i + 1)) (kq a b (i + 2)) (kq a b (i + 3)) (kq a b (i + 4)) := by
  have f0 := div_rel (a := a) (b := b) (i := i) (m := 0) (by omega)
  have f1 := div_rel (a := a) (b := b) (i := i) (m := 1) (by omega)
  have f2 := div_rel (a := a) (b := b) (i := i) (m := 2) (by omega)
  have f3 := div_rel (a := a) (b := b) (i := i) (m := 3) (by omega)
  simp only [sum_range_succ, sum_range_zero, zero_add, add_zero] at f0 f1 f2 f3
  have := mult_identity a (qq a b i) (orb a b i) (orb a b (i + 1)) (orb a b (i + 2))
    (orb a b (i + 3)) (orb a b (i + 4)) (kq a b i) (kq a b (i + 1)) (kq a b (i + 2))
    (kq a b (i + 3)) (kq a b (i + 4)) f0 (by simpa using f1) (by simpa [add_assoc] using f2)
    (by simpa [add_assoc] using f3)
  exact this

/-- `a ≤ 4 A qᵢ` when `A ≤ bᵢ < 2A`. -/
lemma a_le_four {A i : ℕ} (hba : b < a) (h : i + 1 < P a b) (hi : orb a b i < 2 * A) :
    a ≤ 4 * A * qq a b i := by
  have hlt : orb a b (i + 1) < orb a b i := by
    rw [orb_succ_of_ne (orb_ne_zero_of_lt (by omega : i < P a b))]
    exact Nat.mod_lt _ (orb_pos_of_lt (by omega))
  exact le_four_mul (orb_div (by omega)) hlt hi (qq_pos hba (by omega))

end State

section GoodStarts

variable {a b : ℕ}

/-- Telescoping: `∑_{m ∈ [s, s+n)} kₘ = q_{s+n} - q_s`. -/
lemma sum_kq (s n : ℕ) : ∑ m ∈ Ico s (s + n), kq a b m = (qq a b (s + n) : ℤ) - qq a b s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, sum_Ico_succ_top (by omega), ih]
    simp [kq]

/-- **Most starts are good.** In a run of `T ≥ 36` terms in `[A, 2A)`, at least `T/2` starts
`i` have `i + 9 ≤ s + T` and `k_{i}, …, k_{i+6} ≤ H`, where `H = ⌊28a/(AT)⌋ + 1`. -/
theorem good_card (hba : b < a) {s T A : ℕ}
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) (hsT : s + T ≤ P a b)
    (hT : 36 ≤ T) :
    T ≤ 2 * ((Ico s (s + T)).filter fun i => i + 9 ≤ s + T ∧
      ∀ m ∈ range 7, kq a b (i + m) ≤ (28 * a / (A * T) + 1 : ℕ)).card := by
  have hA : 1 ≤ A := by have := (hmem 0 (by omega)).2; omega
  set H : ℕ := 28 * a / (A * T) + 1 with hH
  set G := (Ico s (s + T)).filter fun i => i + 9 ≤ s + T ∧ ∀ m ∈ range 7, kq a b (i + m) ≤ (H : ℤ)
  set Big := (Ico s (s + (T - 1))).filter fun m => (H : ℤ) < kq a b m
  set I := Ico s (s + (T - 9))
  set Bad := I.filter fun i => ∃ m ∈ range 7, (H : ℤ) < kq a b (i + m)
  have ha : 0 < a := by omega
  -- the large increments are few: `28 #Big ≤ T`
  have hsum : (Big.card : ℤ) * (H + 1) ≤ a / A := by
    have h1 : (Big.card : ℤ) * (H + 1) ≤ ∑ m ∈ Big, kq a b m := by
      rw [card_eq_sum_ones, Nat.cast_sum, sum_mul]
      refine sum_le_sum fun m hm => ?_
      have := (mem_filter.mp hm).2
      push_cast; linarith
    have h2 : ∑ m ∈ Big, kq a b m ≤ ∑ m ∈ Ico s (s + (T - 1)), kq a b m := by
      refine sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun m hm _ => ?_
      have := mem_Ico.mp hm
      have := kq_pos (a := a) (b := b) (i := m) (by omega)
      linarith
    have h3 : ∑ m ∈ Ico s (s + (T - 1)), kq a b m ≤ (a / A : ℕ) := by
      rw [sum_kq]
      have hle : qq a b (s + (T - 1)) ≤ a / A := by
        unfold qq
        exact Nat.div_le_div_left (hmem (T - 1) (by omega)).1 (by omega)
      have : (0 : ℤ) ≤ qq a b s := by positivity
      have : ((qq a b (s + (T - 1)) : ℕ) : ℤ) ≤ ((a / A : ℕ) : ℤ) := by exact_mod_cast hle
      linarith
    have := h1.trans (h2.trans h3)
    exact_mod_cast this
  have hBig : 28 * Big.card ≤ T := by
    have h1 : Big.card * (H + 1) ≤ a / A := by exact_mod_cast hsum
    have h2 : Big.card * (H + 1) * A ≤ a :=
      (Nat.mul_le_mul_right A h1).trans (Nat.div_mul_le_self a A)
    have hAT : 0 < A * T := by positivity
    have h3 : 28 * a < H * (A * T) := by
      simp only [hH]
      have := Nat.lt_div_mul_add (a := 28 * a) hAT
      nlinarith
    have h4 : Big.card * (28 * a) ≤ Big.card * (H * (A * T)) := Nat.mul_le_mul_left _ h3.le
    have h5 : Big.card * (H * (A * T)) ≤ a * T := by
      calc Big.card * (H * (A * T)) ≤ Big.card * (H + 1) * A * T := by
            rw [show Big.card * (H + 1) * A * T = Big.card * ((H + 1) * (A * T)) by ring]
            exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
        _ ≤ a * T := Nat.mul_le_mul_right _ h2
    have : (28 * Big.card) * a ≤ T * a := by nlinarith
    exact Nat.le_of_mul_le_mul_right this ha
  -- the bad starts are covered by the large increments
  have hBad : Bad.card ≤ 7 * Big.card := by
    have hsub : Bad ⊆ (Big ×ˢ range 7).image fun p => p.1 - p.2 := by
      intro i hi
      obtain ⟨hiI, m, hm, hlt⟩ := mem_filter.mp hi
      have := mem_Ico.mp hiI
      have := mem_range.mp hm
      refine mem_image.mpr ⟨(i + m, m), mem_product.mpr ⟨mem_filter.mpr ⟨mem_Ico.mpr
        ⟨by omega, by omega⟩, hlt⟩, hm⟩, by simp⟩
    calc Bad.card ≤ ((Big ×ˢ range 7).image fun p => p.1 - p.2).card := card_le_card hsub
      _ ≤ (Big ×ˢ range 7).card := card_image_le
      _ = 7 * Big.card := by rw [card_product, card_range]; ring
  -- the good starts contain `I \ Bad`
  have hG : I \ Bad ⊆ G := by
    intro i hi
    obtain ⟨hiI, hnb⟩ := mem_sdiff.mp hi
    have := mem_Ico.mp hiI
    refine mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, by omega, fun m hm => ?_⟩
    by_contra hc
    exact hnb (mem_filter.mpr ⟨hiI, m, hm, by push Not at hc; exact hc⟩)
  have hI : I.card = T - 9 := by simp [I]
  have h1 : I.card - Bad.card ≤ G.card := by
    have := card_le_card hG
    have := le_card_sdiff Bad I
    omega
  omega

/-- `|z| n ≤ C` gives `|z| ≤ ⌊C / n⌋`. -/
lemma abs_le_div {z : ℤ} {C n : ℕ} (hn : 0 < n) (h : |z| * n ≤ C) : |z| ≤ ((C / n : ℕ) : ℤ) := by
  rw [Int.natCast_div, Int.le_ediv_iff_mul_le (by exact_mod_cast hn)]
  exact h

/-- The good starts of a window run `s, …, s + T - 1` (`good_card`): `i + 9 ≤ s + T` and
`kᵢ, …, k_{i+6} ≤ H`. -/
def goodStarts (a b s T H : ℕ) : Finset ℕ :=
  (Ico s (s + T)).filter fun i => i + 9 ≤ s + T ∧ ∀ m ∈ range 7, kq a b (i + m) ≤ (H : ℤ)

/-- The facts at a good start. -/
lemma mem_goodStarts {s T A H i : ℕ}
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) (hsT : s + T ≤ P a b)
    (hi : i ∈ goodStarts a b s T H) :
    i + 8 < P a b ∧ (∀ m, m < 7 → 1 ≤ kq a b (i + m) ∧ kq a b (i + m) ≤ H) ∧
      orb a b i < 2 * A ∧ orb a b (i + 1) < 2 * A ∧ orb a b (i + 2) < 2 * A := by
  obtain ⟨hiI, h9, hk⟩ := mem_filter.mp hi
  have := mem_Ico.mp hiI
  refine ⟨by omega, fun m hm => ⟨kq_pos (by omega), hk m (mem_range.mpr hm)⟩, ?_, ?_, ?_⟩
  · have := (hmem (i - s) (by omega)).2; rwa [show s + (i - s) = i by omega] at this
  · have := (hmem (i + 1 - s) (by omega)).2; rwa [show s + (i + 1 - s) = i + 1 by omega] at this
  · have := (hmem (i + 2 - s) (by omega)).2; rwa [show s + (i + 2 - s) = i + 2 by omega] at this

/-- The hypotheses shared by the pattern counts (`pattern_count`, `pattern_count_slice`,
`pattern_count_lattice`) for states `G`, patterns `θ`, gaps `κ` and quotients `Q`. -/
structure PatternHyps (G : Finset ℕ) (θ : ℕ → Fin 7 → ℤ) (κ : ℕ → Fin 5 → ℤ) (Q : ℕ → ℤ)
    (a : ℤ) (H : ℕ) : Prop where
  inj : Set.InjOn Q G
  gaps : ∀ i ∈ G, ∀ t, 1 ≤ κ i t ∧ κ i t ≤ H
  pos0 : ∀ i ∈ G, 1 ≤ θ i 0
  pos1 : ∀ i ∈ G, 1 ≤ θ i 1
  e0 : ∀ i ∈ G, -θ i 1 * κ i 0 + θ i 3 * κ i 1 + θ i 4 * κ i 2 + θ i 0 * κ i 3 = 0
  e4 : ∀ i ∈ G, -θ i 2 * κ i 1 + θ i 5 * κ i 2 + θ i 6 * κ i 3 + θ i 1 * κ i 4 = 0
  e3 : ∀ i ∈ G, -θ i 1 * (κ i 0 ^ 2 + κ i 1) + θ i 3 * (κ i 1 * (2 * κ i 0 + κ i 1) + κ i 2) +
    θ i 4 * (κ i 2 * (2 * κ i 0 + 2 * κ i 1 + κ i 2) + κ i 3) +
    θ i 0 * (κ i 3 * (2 * κ i 0 + 2 * κ i 1 + 2 * κ i 2 + κ i 3) + κ i 4) = 0
  mult : ∀ i ∈ G, quart (-θ i 1) (θ i 3) (θ i 4) (θ i 0) (κ i 0) (κ i 1) (κ i 2) (Q i) =
    a * muH4 (κ i 0) (κ i 1) (κ i 2) (κ i 3) (κ i 4)

/-- **The good starts satisfy the pattern hypotheses.** -/
theorem goodStarts_patternHyps (hba : b < a) {s T A H : ℕ}
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) (hsT : s + T ≤ P a b) :
    PatternHyps (goodStarts a b s T H) (theta a b) (kap a b) (fun i => (qq a b i : ℤ)) a H where
  inj i hi i' hi' h := by
    have hP := (mem_goodStarts hmem hsT hi).1
    have hP' := (mem_goodStarts hmem hsT hi').1
    simp only [Nat.cast_inj] at h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (qq_strictMono (a := a) (b := b) hlt (by omega)).ne h
    · exact (qq_strictMono (a := a) (b := b) hlt (by omega)).ne h.symm
  gaps i hi t := by
    obtain ⟨-, hk, -⟩ := mem_goodStarts hmem hsT hi
    fin_cases t
    · simpa [kap] using hk 0 (by norm_num)
    · simpa [kap] using hk 1 (by norm_num)
    · simpa [kap] using hk 2 (by norm_num)
    · simpa [kap] using hk 3 (by norm_num)
    · simpa [kap] using hk 4 (by norm_num)
  pos0 i hi := by
    simpa [theta] using Lz_pos hba (i := i) (by have := (mem_goodStarts hmem hsT hi).1; omega)
  pos1 i hi := by
    simpa [theta] using Lz_pos hba (i := i + 1) (by have := (mem_goodStarts hmem hsT hi).1; omega)
  e0 i _ := by simpa [theta, kap] using e0_at (a := a) (b := b) i
  e4 i _ := by simpa [theta, kap, add_assoc] using e0_at (a := a) (b := b) (i + 1)
  e3 i _ := by simpa [theta, kap] using e3_at (a := a) (b := b) i
  mult i hi := by
    simpa [theta, kap] using mult_at (a := a) (b := b) (i := i)
      (by have := (mem_goodStarts hmem hsT hi).1; omega)

end GoodStarts

/-! ### The matrix `𝓜ᵢ` and the pattern as signed minors -/

section Matrix

variable (a b : ℕ)

/-- `sⱼ = q_{i+j} - qᵢ`. -/
def sq (i j : ℕ) : ℤ := (qq a b (i + j) : ℤ) - qq a b i

/-- `rⱼ = kⱼ (sⱼ + sⱼ₊₁) + kⱼ₊₁`. -/
def rq (i j : ℕ) : ℤ := kq a b (i + j) * (sq a b i j + sq a b i (j + 1)) + kq a b (i + j + 1)

/-- The `3 × 5` matrix `𝓜ᵢ`. -/
def Mi (i : ℕ) : Fin 3 → Fin 5 → ℤ :=
  ![fun j => dq a b (i + j), fun j => kq a b (i + j), fun j => rq a b i j]

end Matrix

section Minors

variable {a b : ℕ}

/-- The pattern as signed minors: the coordinates of the minor vector forming `θ`. -/
def projθ (p : Fin 10 → ℤ) : Fin 7 → ℤ := ![p 0, p 6, p 9, p 3, -p 1, p 8, -p 7]

/-- The pattern `θ(i)` is the projection `projθ` of the `3 × 3` minors of `𝓜ᵢ`. -/
theorem theta_eq (i : ℕ) : theta a b i = projθ (plk (Mi a b i)) := by
  funext t
  fin_cases t <;>
  simp [theta, projθ, plk, Mi, trip, minor3, Lz, U1z, U2z, sixL, pU1, pU2, rq, sq, kq, dq,
    Nat.add_assoc] <;> ring

/-- Starts with the same pattern have the same projected invariants. -/
lemma theta_eq_of_plk_eq {i : ℕ} {G : Finset ℕ} (hpat : ∀ l ∈ G, plk (Mi a b l) = plk (Mi a b i))
    (l : ℕ) (hl : l ∈ G) : theta a b i = theta a b l := by
  rw [theta_eq, theta_eq, hpat l hl]

/-- An orbit's pattern has a nonzero first minor `Lz`. -/
lemma orbit_pattern_first {l : ℕ} (hba : b < a) (hl : l + 5 < P a b) :
    plk (Mi a b l) 0 ≠ 0 := by
  have h := congrFun (theta_eq (a := a) (b := b) l) 0
  simp only [theta, projθ, Matrix.cons_val_zero] at h
  have := Lz_pos hba (i := l) hl
  omega

end Minors

end PierceLengthBound
