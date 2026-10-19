/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceBound.PatternBound
public import PierceBound.PatternCount
public import PierceBound.Main
public import PierceBound.RisesMain

/-!
# `P(a, b) ≪_ε a^{23/77 + ε}`

For an orbit state `i` put `kᵢ = q_{i+1} - qᵢ`, `dᵢ = bᵢ - b_{i+1}` (`kq`, `dq`), the six-step
integer `L(i)` (`Lz`, equal to `I₄(i)`), and the cofactors `U₁(i)`, `U₂(i)`. The *pattern* of `i`
is `θ(i) = (L(i), L(i+1), L(i+2), U₁(i), U₂(i), U₁(i+1), U₂(i+1)) ∈ ℤ⁷` and its gaps are
`κ(i) = (kᵢ, …, k_{i+4})`.

In a window run of `T ≥ 36` terms in `[A, 2A)` take `H = ⌊28a/(AT)⌋ + 1`. At least `T/2`
starts have their next seven increments `≤ H` (`good_card`). If `237568 A⁴ H⁵ ≤ a³`, their
patterns are bounded by `M = ⌊172032 A⁴ H⁶ / a³⌋` (`state_bound`), so the counting lemma gives
`T ≤ 16 (2M+1)⁷ H²` (`two_state_window_77`). Combined with the six-step bound and the drop bound,
every window has `T⁷⁷ ≤ C₇₇ Δ²² a²³` (`window_77`), and the dyadic decomposition gives the
theorem (`P_le_23_77`).
-/

@[expose] public section

namespace PierceBound

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

lemma qq_strictMono {i i' : ℕ} (hii : i < i') (hi' : i' < P a b) : qq a b i < qq a b i' := by
  induction i', hii using Nat.le_induction with
  | base => exact qq_lt hi'
  | succ i' hii ih => exact (ih (by omega)).trans (qq_lt hi')

lemma Lz_pos (hba : b < a) {i : ℕ} (h : i + 5 < P a b) : 1 ≤ Lz a b i := by
  have h4 := hankelInv_four hba h
  have hp := hankelInv_pos hba (i := i) (r := 4) (by omega) (by omega)
  rw [h4] at hp
  have : (0 : ℤ) < Lz a b i := by
    unfold Lz kq dq; exact_mod_cast hp
  omega

lemma e0_at (i : ℕ) : -Lz a b (i + 1) * kq a b i + U1z a b i * kq a b (i + 1) +
    U2z a b i * kq a b (i + 2) + Lz a b i * kq a b (i + 3) = 0 :=
  null_k _ _ _ _ _ _ _ _ _

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
  have e := orb_div (a := a) (b := b) (i := i) (by omega)
  have hq := qq_pos hba (i := i) (by omega)
  have hlt : orb a b (i + 1) < orb a b i := by
    rw [orb_succ_of_ne (orb_ne_zero_of_lt (by omega : i < P a b))]
    exact Nat.mod_lt _ (orb_pos_of_lt (by omega))
  nlinarith

/-- **The label bound in window form.** `L(i) a³ ≤ 256 A⁴ gramP`. -/
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

lemma abs_le_div {z : ℤ} {C n : ℕ} (hn : 0 < n) (h : |z| * n ≤ C) : |z| ≤ ((C / n : ℕ) : ℤ) := by
  rw [Int.natCast_div, Int.le_ediv_iff_mul_le (by exact_mod_cast hn)]
  exact h

/-- **The window theorem.** Under the scale condition `237568 A⁴ H⁵ ≤ a³`,
`T ≤ 16 (2M + 1)⁷ H²` with `M = ⌊172032 A⁴ H⁶ / a³⌋`. -/
theorem two_state_window_77 (hba : b < a) {s T A : ℕ}
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A) (hsT : s + T ≤ P a b)
    (hT : 36 ≤ T)
    (hc : 237568 * A ^ 4 * (28 * a / (A * T) + 1) ^ 5 ≤ a ^ 3) :
    T ≤ 16 * (2 * (172032 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3) + 1) ^ 7 *
      (28 * a / (A * T) + 1) ^ 2 := by
  have hA : 1 ≤ A := by have := (hmem 0 (by omega)).2; omega
  set H : ℕ := 28 * a / (A * T) + 1 with hH
  set M : ℕ := 172032 * A ^ 4 * H ^ 6 / a ^ 3 with hM
  set G := (Ico s (s + T)).filter fun i => i + 9 ≤ s + T ∧
    ∀ m ∈ range 7, kq a b (i + m) ≤ (H : ℤ)
  have hgood := good_card hba hmem hsT hT
  have ha : 0 < a := by omega
  have ha3 : 0 < a ^ 3 := by positivity
  have hcZ : (237568 : ℤ) * (A : ℤ) ^ 4 * (H : ℤ) ^ 5 ≤ (a : ℤ) ^ 3 := by exact_mod_cast hc
  have hAZ : (1 : ℤ) ≤ A := by exact_mod_cast hA
  -- facts at a good start
  have facts : ∀ i ∈ G, i + 8 < P a b ∧ (∀ m, m < 7 → 1 ≤ kq a b (i + m) ∧ kq a b (i + m) ≤ H) ∧
      orb a b i < 2 * A ∧ orb a b (i + 1) < 2 * A ∧ orb a b (i + 2) < 2 * A := by
    intro i hi
    obtain ⟨hiI, h9, hk⟩ := mem_filter.mp hi
    have := mem_Ico.mp hiI
    refine ⟨by omega, fun m hm => ⟨kq_pos (by omega), hk m (mem_range.mpr hm)⟩, ?_, ?_, ?_⟩
    · have := (hmem (i - s) (by omega)).2; rwa [show s + (i - s) = i by omega] at this
    · have := (hmem (i + 1 - s) (by omega)).2; rwa [show s + (i + 1 - s) = i + 1 by omega] at this
    · have := (hmem (i + 2 - s) (by omega)).2; rwa [show s + (i + 2 - s) = i + 2 by omega] at this
  have hcount := pattern_count (G := G) (θ := theta a b) (κ := kap a b)
    (Q := fun i => (qq a b i : ℤ)) (a := (a : ℤ)) (M := M) (H := H) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have hg2 : T ≤ 2 * G.card := hgood
    calc T ≤ 2 * G.card := hg2
      _ ≤ 2 * (8 * (2 * M + 1) ^ 7 * H ^ 2) := Nat.mul_le_mul_left _ hcount
      _ = 16 * (2 * M + 1) ^ 7 * H ^ 2 := by ring
  -- injectivity of the quotient
  · intro i hi i' hi' h
    have hP := (facts i hi).1
    have hP' := (facts i' hi').1
    simp only [Nat.cast_inj] at h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (qq_strictMono (a := a) (b := b) hlt (by omega)).ne h
    · exact (qq_strictMono (a := a) (b := b) hlt (by omega)).ne h.symm
  -- the pattern bound
  · intro i hi t
    obtain ⟨hP, hk, hb0, hb1, hb2⟩ := facts i hi
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
    have cv : ∀ z : ℤ, |z| * (a : ℤ) ^ 3 ≤ 172032 * (A : ℤ) ^ 4 * (H : ℤ) ^ 6 → |z| ≤ M := by
      intro z hz
      refine abs_le_div ha3 ?_
      exact_mod_cast hz
    have cvL : ∀ z : ℤ, 1 ≤ z → z * (a : ℤ) ^ 3 ≤ 172032 * (A : ℤ) ^ 4 * (H : ℤ) ^ 6 →
        |z| ≤ M := fun z hz h => cv z (by rwa [abs_of_pos (by omega)])
    fin_cases t
    · exact cvL _ P0 SB0.2.2.1
    · exact cvL _ P1 SB0.2.2.2
    · exact cvL _ P2 SB1.2.2.2
    · exact cv _ SB0.1
    · exact cv _ SB0.2.1
    · exact cv _ SB1.1
    · exact cv _ SB1.2.1
  -- the gaps
  · intro i hi t
    obtain ⟨-, hk, -⟩ := facts i hi
    fin_cases t
    · simpa [kap] using hk 0 (by norm_num)
    · simpa [kap] using hk 1 (by norm_num)
    · simpa [kap] using hk 2 (by norm_num)
    · simpa [kap] using hk 3 (by norm_num)
    · simpa [kap] using hk 4 (by norm_num)
  · intro i hi; simpa [theta] using Lz_pos hba (i := i) (by have := (facts i hi).1; omega)
  · intro i hi; simpa [theta] using Lz_pos hba (i := i + 1) (by have := (facts i hi).1; omega)
  · intro i _; simpa [theta, kap] using e0_at (a := a) (b := b) i
  · intro i _; simpa [theta, kap, add_assoc] using e0_at (a := a) (b := b) (i + 1)
  · intro i _; simpa [theta, kap] using e3_at (a := a) (b := b) i
  · intro i hi; simpa [theta, kap] using mult_at (a := a) (b := b) (i := i)
      (by have := (facts i hi).1; omega)

end Window

section Exponent

/-- The constant in `window_77`. -/
def C77 : ℕ := 122449 ^ 20 + (8 * 237568 * 56 ^ 5) ^ 11 + (64 * 50176) ^ 11 +
  8 ^ 16 * (16 * 3 ^ 7 * 172032 ^ 7) * 56 ^ 44

/-- **The exponent arithmetic.** Every window run satisfies `T⁷⁷ ≤ C₇₇ Δ²² a²³`. -/
theorem window_77 {a A T Δ : ℕ} (hT : 36 ≤ T)
    (hsix : T ^ 6 * A ^ 2 ≤ 96000000 * a ^ 3) (hdrop : T * (T - 1) ≤ 4 * A * Δ)
    (hwin : 237568 * A ^ 4 * (28 * a / (A * T) + 1) ^ 5 ≤ a ^ 3 →
      T ≤ 16 * (2 * (172032 * A ^ 4 * (28 * a / (A * T) + 1) ^ 6 / a ^ 3) + 1) ^ 7 *
        (28 * a / (A * T) + 1) ^ 2) :
    T ^ 77 ≤ C77 * Δ ^ 22 * a ^ 23 := by
  have hA : 1 ≤ A := Nat.pos_of_ne_zero fun h => by simp [h] at hdrop; omega
  have hΔ : 1 ≤ Δ := Nat.pos_of_ne_zero fun h => by simp [h] at hdrop; omega
  have ha : 1 ≤ a := Nat.pos_of_ne_zero fun h => by simp [h] at hsix; omega
  set H := 28 * a / (A * T) + 1 with hH
  set M := 172032 * A ^ 4 * H ^ 6 / a ^ 3 with hM
  have ha0 : 0 < a := by omega
  have hT1 : 1 ≤ T := by omega
  have hT2 : T ^ 2 ≤ 8 * A * Δ := by
    have : T ^ 2 ≤ 2 * (T * (T - 1)) := by
      have : T ≤ 2 * (T - 1) := by omega
      calc T ^ 2 = T * T := sq T
        _ ≤ T * (2 * (T - 1)) := Nat.mul_le_mul_left _ this
        _ = 2 * (T * (T - 1)) := by ring
    calc T ^ 2 ≤ 2 * (T * (T - 1)) := this
      _ ≤ 2 * (4 * A * Δ) := Nat.mul_le_mul_left _ hdrop
      _ = 8 * A * Δ := by ring
  have hΔa : Δ ^ 22 * a ^ 23 ≥ 1 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hC : ∀ c : ℕ, c ≤ C77 → ∀ x : ℕ, x ≤ c * Δ ^ 22 * a ^ 23 →
      x ≤ C77 * Δ ^ 22 * a ^ 23 := fun c hc x hx =>
    hx.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc))
  by_cases hbig : 28 * a < A * T
  · -- `T⁴ ≤ 122449 a`
    have h1 : (28 * a) ^ 2 * T ^ 4 ≤ 96000000 * a ^ 3 := by
      calc (28 * a) ^ 2 * T ^ 4 ≤ (A * T) ^ 2 * T ^ 4 :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hbig.le 2)
        _ = T ^ 6 * A ^ 2 := by ring
        _ ≤ _ := hsix
    have h2 : T ^ 4 ≤ 122449 * a := by
      have : (784 * T ^ 4) * a ^ 2 ≤ (784 * (122449 * a)) * a ^ 2 := by
        calc (784 * T ^ 4) * a ^ 2 = (28 * a) ^ 2 * T ^ 4 := by ring
          _ ≤ 96000000 * a ^ 3 := h1
          _ ≤ (784 * (122449 * a)) * a ^ 2 := by ring_nf; omega
      have := Nat.le_of_mul_le_mul_right this (by positivity)
      omega
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
  have hHAT : H * (A * T) ≤ 56 * a := by
    have := Nat.div_mul_le_self (28 * a) (A * T)
    calc H * (A * T) = 28 * a / (A * T) * (A * T) + A * T := by rw [hH]; ring
      _ ≤ 56 * a := by omega
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
  by_cases hT : (visits a b k).card ≤ 35
  · exact Or.inl hT
  right
  set T := (visits a b k).card
  have hne : (visits a b k).Nonempty := by rw [← card_pos]; omega
  have W := visits_window hba.le hne
  set s := (visits a b k).min' hne
  have hmem : ∀ j < T, 2 ^ k ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * 2 ^ k := W.mem
  have hsT : s + T ≤ P a b := by
    have h := (hmem (T - 1) (by omega)).1
    have := lt_P_of_orb_pos (a := a) (b := b) (i := s + (T - 1))
      (lt_of_lt_of_le (Nat.two_pow_pos k) h)
    omega
  exact window_77 (by omega) (six_step_bound W (by omega))
    (drop_bound W hΔ (by omega))
    (fun hc => two_state_window_77 hba hmem hsT (by omega) hc)

/-- **Theorem.** `P(a, b) ≪_ε a^{23/77 + ε}` uniformly in `0 < b < a`. -/
theorem P_le_23_77 : ∀ ε > (0 : ℝ), ∃ C > 0, ∀ a b : ℕ, 0 < b → b < a →
    (P a b : ℝ) ≤ C * (a : ℝ) ^ ((23 : ℝ) / 77 + ε) := by
  have h := P_le_of_visits (N := 77) (r := 23) (K := C77) (by norm_num)
    ((tauMax_slow 32 7).pow 22) fun a b k _ hba =>
      visits_77 (k := k) hba (tauMax_divBound a)
  intro ε hε
  obtain ⟨C, hC, hP⟩ := h ε hε
  refine ⟨C, hC, fun a b hb hba => ?_⟩
  have := hP a b hb hba
  norm_num at this ⊢
  exact this

end Exponent

end PierceBound
