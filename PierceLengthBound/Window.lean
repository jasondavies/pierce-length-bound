/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.Fiber
public import PierceLengthBound.Block

/-!
# Counting the visits to a dyadic window

A *window run* is a run `g 0, g 1, …, g (T-1)` of consecutive terms of an orbit of
`x ↦ a mod x`, all lying in `[A, 2A)`. We prove, with `Δ` a bound for the divisor function on
`[1, 32 a⁷]`:

* `drop_bound`: `T (T - 1) ≤ 4 A Δ` (the Erdős–Shallit divisor argument);
* `curvature_bound`: `T⁶ A² ≤ 995328 a³ Δ` for `T ≥ 12` (the curvature argument,
  Proposition 4.3);
* `window_bound`: hence `T¹⁰ ≤ 63700992 a³ Δ³` for `T ≥ 12` (Corollary 4.4).

The file also holds the window vocabulary shared by the later window bounds:

* the structure `Window` with its monotonicity lemmas and the telescoping identities
  `Window.sum_drops`, `Window.sum_triple_drops`, `Window.sum_five_drops`;
* the divisor-bound predicate `DivBound`;
* the quotient increments `incr` and drops `drop` of a run, with `Window.quot_lt`,
  `Window.one_le_incr`, `Window.one_le_drop`, the size bound `Window.incr_mul_le` and the
  quotient telescoping `Window.sum_incr`, `Window.sum_incr_le`;
* the inequalities `le_four_mul`, `lt_three_mul` (from one division equation),
  `drop_bound_sq` (`T² ≤ 8 A Δ`) and `gap_height_mul_le` (for the gap height
  `H = ⌊28a/(AT)⌋ + 1` of the good-start lemmas).
-/

@[expose] public section

namespace PierceLengthBound

open Finset

/-- A run of `T` consecutive terms of the orbit of `x ↦ a mod x`, all in `[A, 2A)`, `A ≥ 1`. -/
structure Window (a A T : ℕ) (g : ℕ → ℕ) : Prop where
  one_le : 1 ≤ A
  mem : ∀ j < T, A ≤ g j ∧ g j < 2 * A
  le_a : ∀ j < T, g j ≤ a
  step : ∀ j, j + 1 < T → g (j + 1) = a % g j

/-- `Δ` bounds the divisor function on `[1, 32 a⁷]`. -/
def DivBound (a Δ : ℕ) : Prop := ∀ n : ℕ, 0 < n → n ≤ 32 * a ^ 7 → n.divisors.card ≤ Δ

namespace Window

variable {a A T : ℕ} {g : ℕ → ℕ}

lemma pos (W : Window a A T g) {j : ℕ} (hj : j < T) : 0 < g j :=
  lt_of_lt_of_le W.one_le (W.mem j hj).1

lemma succ_lt (W : Window a A T g) {j : ℕ} (hj : j + 1 < T) : g (j + 1) < g j := by
  rw [W.step j hj]; exact Nat.mod_lt _ (W.pos (by omega))

lemma lt_of_lt (W : Window a A T g) {i j : ℕ} (hij : i < j) (hj : j < T) : g j < g i := by
  induction j, hij using Nat.le_induction with
  | base => exact W.succ_lt hj
  | succ j hij ih => exact (W.succ_lt hj).trans (ih (by omega))

lemma injOn (W : Window a A T g) : Set.InjOn g (range T : Set ℕ) := by
  intro i hi j hj h
  simp only [coe_range, Set.mem_Iio] at hi hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact (W.lt_of_lt hlt hj).ne' h
  · exact (W.lt_of_lt hlt hi).ne h

lemma one_le_a (W : Window a A T g) (hT : 1 ≤ T) : 1 ≤ a :=
  (W.pos (by omega : 0 < T)).trans_le (W.le_a 0 (by omega))

/-- Telescoping for single drops. -/
lemma sum_drops (W : Window a A T g) :
    ∀ m, m + 1 ≤ T → ∑ j ∈ range m, (g j - g (j + 1)) + g m = g 0 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro hm
    rw [sum_range_succ]
    have := ih (by omega)
    have := (W.succ_lt (j := m) (by omega)).le
    omega

/-- Telescoping for triple drops. -/
lemma sum_triple_drops (W : Window a A T g) :
    ∀ m, m + 3 ≤ T → ∑ j ∈ range m, (g j - g (j + 3)) + g m + g (m + 1) + g (m + 2) =
      g 0 + g 1 + g 2 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro hm
    rw [sum_range_succ, show m + 1 + 1 = m + 2 by ring, show m + 1 + 2 = m + 3 by ring]
    have := ih (by omega)
    have := (W.lt_of_lt (i := m) (j := m + 3) (by omega) (by omega)).le
    omega

lemma le_of_le (W : Window a A T g) {i j : ℕ} (hij : i ≤ j) (hj : j < T) : g j ≤ g i := by
  rcases hij.lt_or_eq with h | rfl
  · exact (W.lt_of_lt h hj).le
  · exact le_rfl

/-- Telescoping for five-step drops. -/
lemma sum_five_drops (W : Window a A T g) :
    ∀ m, m + 5 ≤ T → ∑ j ∈ range m, (g j - g (j + 5)) + g m + g (m + 1) + g (m + 2) + g (m + 3) +
      g (m + 4) = g 0 + g 1 + g 2 + g 3 + g 4 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro hm
    rw [sum_range_succ, show m + 1 + 1 = m + 2 by ring, show m + 1 + 2 = m + 3 by ring,
      show m + 1 + 3 = m + 4 by ring, show m + 1 + 4 = m + 5 by ring]
    have := ih (by omega)
    have := (W.lt_of_lt (i := m) (j := m + 5) (by omega) (by omega)).le
    omega

end Window

/-! ### Quotient increments and drops -/

/-- The quotient increment `kⱼ = ⌊a/g(j+1)⌋ - ⌊a/g(j)⌋`. -/
def incr (a : ℕ) (g : ℕ → ℕ) (j : ℕ) : ℕ := a / g (j + 1) - a / g j

/-- The drop `dⱼ = g(j) - g(j+1)`. -/
def drop (g : ℕ → ℕ) (j : ℕ) : ℕ := g j - g (j + 1)

/-- `a ≤ 4 A q` from `a = x q + y` with `y < x < 2A` and `q ≥ 1`. -/
lemma le_four_mul {a x y q A : ℕ} (h0 : x * q + y = a) (hyx : y < x) (hx : x < 2 * A)
    (hq : 1 ≤ q) : a ≤ 4 * A * q := by
  nlinarith

/-- `a < 3 A q` from `a = x q + y` with `y < x < 2A` and `6A ≤ a`. -/
lemma lt_three_mul {a A q x y : ℕ} (e : x * q + y = a) (hyx : y < x) (hx : x < 2 * A)
    (h6 : 6 * A ≤ a) : a < 3 * A * q := by
  nlinarith

namespace Window

variable {a A T : ℕ} {g : ℕ → ℕ}

lemma quot_lt (W : Window a A T g) {j : ℕ} (hj : j + 1 < T) : a / g j < a / g (j + 1) := by
  have e : a % g j = g (j + 1) := (W.step j hj).symm
  have := div_lt_div_mod (a := a) (W.pos (j := j) (by omega))
    (by rw [e]; exact (W.pos hj).ne')
  rwa [e] at this

lemma one_le_incr (W : Window a A T g) {j : ℕ} (hj : j + 1 < T) : 1 ≤ incr a g j := by
  have := W.quot_lt hj; unfold incr; omega

lemma one_le_drop (W : Window a A T g) {j : ℕ} (hj : j + 1 < T) : 1 ≤ drop g j := by
  have := W.succ_lt hj; unfold drop; omega

/-- The size of an increment: `kⱼ g(j+1) g(j) ≤ a (g(j) - g(j+2))`. -/
lemma incr_mul_le (W : Window a A T g) {j : ℕ} (hj : j + 2 < T) :
    incr a g j * (g (j + 1) * g j) ≤ a * (g j - g (j + 2)) := by
  have e1 : a % g j = g (j + 1) := (W.step j (by omega)).symm
  have e2 : a % (a % g j) = g (j + 2) := by rw [e1]; exact (W.step (j + 1) (by omega)).symm
  have hb := bu_mul_le (W.pos (j := j) (by omega)) (by rw [e1]; exact (W.pos (by omega)).ne')
    (by rw [e2]; exact (W.pos hj).ne') (W.le_a j (by omega))
  unfold bu at hb
  rwa [e2, e1] at hb

/-- Telescoping for the quotients. -/
lemma sum_incr (W : Window a A T g) :
    ∀ m, m + 1 ≤ T → ∑ j ∈ range m, incr a g j + a / g 0 = a / g m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro hm
    have hih := ih (by omega)
    have hle := (W.quot_lt (j := m) (by omega)).le
    calc ∑ j ∈ range (m + 1), incr a g j + a / g 0
        = (∑ j ∈ range m, incr a g j + a / g 0) + incr a g m := by rw [sum_range_succ]; ring
      _ = a / g m + (a / g (m + 1) - a / g m) := by rw [hih]; rfl
      _ = a / g (m + 1) := Nat.add_sub_cancel' hle

lemma sum_incr_le (W : Window a A T g) (hT : 1 ≤ T) :
    ∑ j ∈ range (T - 1), incr a g j ≤ a / A := by
  have := W.sum_incr (T - 1) (by omega)
  have hA : a / g (T - 1) ≤ a / A := Nat.div_le_div_left (W.mem (T - 1) (by omega)).1 W.one_le
  calc ∑ j ∈ range (T - 1), incr a g j ≤ ∑ j ∈ range (T - 1), incr a g j + a / g 0 :=
        Nat.le_add_right _ _
    _ = a / g (T - 1) := this
    _ ≤ a / A := hA

end Window

/-- **The drop bound** (Erdős–Shallit). `T (T - 1) ≤ 4 A Δ`. -/
theorem drop_bound {a A T Δ : ℕ} {g : ℕ → ℕ} (W : Window a A T g) (hΔ : DivBound a Δ)
    (hT : 2 ≤ T) : T * (T - 1) ≤ 4 * A * Δ := by
  classical
  set J := range (T - 1)
  set h : ℕ → ℕ := fun j => g j - g (j + 1) with hh
  have ha := W.one_le_a (by omega)
  have hsum : ∑ j ∈ J, h j ≤ A - 1 := by
    have := W.sum_drops (T - 1) (by omega)
    have h0 := W.mem 0 (by omega)
    have h1 := W.mem (T - 1) (by omega)
    simp only [J, hh]
    omega
  set Sel := J.filter fun j => h j * (T - 1) ≤ 2 * A
  set Bad := J.filter fun j => ¬ (h j * (T - 1) ≤ 2 * A)
  have hsplit : Sel.card + Bad.card = T - 1 := by
    rw [card_filter_add_card_filter_not, card_range]
  have hbad : 2 * Bad.card < T - 1 := by
    have h1 : Bad.card * (2 * A + 1) ≤ ∑ j ∈ Bad, h j * (T - 1) := by
      rw [← smul_eq_mul]
      exact card_nsmul_le_sum _ _ _ fun j hj => by
        have := (mem_filter.mp hj).2; omega
    have h2 : ∑ j ∈ Bad, h j * (T - 1) ≤ ∑ j ∈ J, h j * (T - 1) :=
      sum_le_sum_of_subset (filter_subset _ _)
    have h3 : ∑ j ∈ J, h j * (T - 1) ≤ (A - 1) * (T - 1) := by
      rw [← sum_mul]; exact Nat.mul_le_mul_right _ hsum
    have h4 := h1.trans (h2.trans h3)
    have hA := W.one_le
    by_contra hcon
    push Not at hcon
    have : (T - 1) * (2 * A + 1) ≤ 2 * Bad.card * (2 * A + 1) := Nat.mul_le_mul_right _ hcon
    have : 2 * (A - 1) * (T - 1) < (T - 1) * (2 * A + 1) := by
      have : 2 * (A - 1) < 2 * A + 1 := by omega
      calc 2 * (A - 1) * (T - 1) < (2 * A + 1) * (T - 1) :=
            Nat.mul_lt_mul_of_pos_right this (by omega)
        _ = _ := by ring
    nlinarith
  have hsel : T ≤ 2 * Sel.card := by omega
  set H := 2 * A / (T - 1)
  have himg : ∀ j ∈ Sel, h j ∈ Icc 1 H := by
    intro j hj
    obtain ⟨hjJ, hjs⟩ := mem_filter.mp hj
    have hjT := mem_range.mp hjJ
    have := W.succ_lt (j := j) (by omega)
    exact mem_Icc.mpr ⟨by simp only [hh]; omega,
      (Nat.le_div_iff_mul_le (by omega)).mpr hjs⟩
  have hfib : ∀ b ∈ Icc 1 H, (Sel.filter fun j => h j = b).card ≤ Δ := by
    intro b hb
    obtain ⟨hb1, -⟩ := mem_Icc.mp hb
    -- each `j` in the fiber has `g j ∣ a + b`
    have hdvd : ∀ j ∈ Sel.filter (fun j => h j = b), g j ∈ (a + b).divisors := by
      intro j hj
      obtain ⟨hjS, hjb⟩ := mem_filter.mp hj
      have hjT := mem_range.mp (mem_filter.mp hjS).1
      have hstep := W.step j (by omega)
      have hlt := W.succ_lt (j := j) (by omega)
      have hdecomp := Nat.div_add_mod a (g j)
      refine Nat.mem_divisors.mpr ⟨⟨a / g j + 1, ?_⟩, by omega⟩
      simp only [hh] at hjb
      rw [← hstep] at hdecomp
      rw [← hjb]
      have : g (j + 1) ≤ g j := hlt.le
      zify [this] at hdecomp ⊢
      linarith
    rcases (Sel.filter fun j => h j = b).eq_empty_or_nonempty with he | ⟨j0, hj0⟩
    · rw [he]; simp
    have hb_le : b ≤ a := by
      obtain ⟨hjS, hjb⟩ := mem_filter.mp hj0
      have hjT := mem_range.mp (mem_filter.mp hjS).1
      have := W.le_a j0 (by omega)
      simp only [hh] at hjb
      omega
    calc (Sel.filter fun j => h j = b).card ≤ (a + b).divisors.card := by
          apply card_le_card_of_injOn g (fun j hj => hdvd j hj)
          intro i hi j hj hij
          have hi' := mem_range.mp (mem_filter.mp (mem_filter.mp (Finset.mem_coe.mp hi)).1).1
          have hj' := mem_range.mp (mem_filter.mp (mem_filter.mp (Finset.mem_coe.mp hj)).1).1
          exact W.injOn (by simp; omega) (by simp; omega) hij
      _ ≤ Δ := by
          apply hΔ _ (by omega)
          have : a ≤ a ^ 7 := by
            calc a = a ^ 1 := (pow_one a).symm
              _ ≤ a ^ 7 := Nat.pow_le_pow_right ha (by norm_num)
          omega
  have hcard : Sel.card ≤ Δ * H := by
    have := card_le_mul_card_image_of_maps_to himg Δ hfib
    simpa using this
  have hH : H * (T - 1) ≤ 2 * A := Nat.div_mul_le_self _ _
  calc T * (T - 1) ≤ (2 * (Δ * H)) * (T - 1) := Nat.mul_le_mul_right _ (hsel.trans (by omega))
    _ = 2 * Δ * (H * (T - 1)) := by ring
    _ ≤ 2 * Δ * (2 * A) := Nat.mul_le_mul_left _ hH
    _ = 4 * A * Δ := by ring

/-- The drop bound as used by the exponent arithmetic: `A, Δ ≥ 1` and `T² ≤ 8 A Δ`. -/
lemma drop_bound_sq {A T Δ : ℕ} (hT : 2 ≤ T) (hdrop : T * (T - 1) ≤ 4 * A * Δ) :
    1 ≤ A ∧ 1 ≤ Δ ∧ T ^ 2 ≤ 8 * A * Δ := by
  refine ⟨Nat.pos_of_ne_zero fun h => by simp [h] at hdrop; omega,
    Nat.pos_of_ne_zero fun h => by simp [h] at hdrop; omega, ?_⟩
  have : T ≤ 2 * (T - 1) := by omega
  nlinarith

/-- The gap height `H = ⌊28a/(AT)⌋ + 1` satisfies `H A T ≤ 56 a` once `A T ≤ 28 a`. -/
lemma gap_height_mul_le {a A T : ℕ} (h : A * T ≤ 28 * a) :
    (28 * a / (A * T) + 1) * (A * T) ≤ 56 * a := by
  have := Nat.div_mul_le_self (28 * a) (A * T)
  rw [add_mul, one_mul]
  omega

/-- The three successors of a term of a window run with `j + 3 < T`. -/
private lemma Window.succ3 {a A T : ℕ} {g : ℕ → ℕ} (W : Window a A T g) {j : ℕ} (hj : j + 3 < T) :
    a % g j = g (j + 1) ∧ a % (a % g j) = g (j + 2) ∧ a % (a % (a % g j)) = g (j + 3) := by
  have e1 : a % g j = g (j + 1) := (W.step j (by omega)).symm
  have e2 : a % (a % g j) = g (j + 2) := by rw [e1]; exact (W.step (j + 1) (by omega)).symm
  have e3 : a % (a % (a % g j)) = g (j + 3) := by rw [e2]; exact (W.step (j + 2) (by omega)).symm
  exact ⟨e1, e2, e3⟩

/-- **The block parameters are small.** For a block of drop `s` with `s T ≤ 12 A`:
`u A T ≤ 12 a`, `v A T ≤ 12 a` and `D T³ ≤ 3456 a`. -/
private lemma block_small {a A T : ℕ} {g : ℕ → ℕ} (W : Window a A T g) {j : ℕ} (hj : j + 3 < T)
    (hsT : (g j - g (j + 3)) * T ≤ 12 * A) :
    1 ≤ bu a (g j) ∧ 1 ≤ bv a (g j) ∧ 1 ≤ bD a (g j) ∧
    bu a (g j) * (A * T) ≤ 12 * a ∧ bv a (g j) * (A * T) ≤ 12 * a ∧
    bD a (g j) * T ^ 3 ≤ 3456 * a := by
  obtain ⟨e1, e2, e3⟩ := W.succ3 hj
  have hA := W.one_le
  have m0 := W.mem j (by omega)
  have m1 := W.mem (j + 1) (by omega)
  have m2 := W.mem (j + 2) (by omega)
  have m3 := W.mem (j + 3) (by omega)
  have hx : 0 < g j := by omega
  have hy : a % g j ≠ 0 := by rw [e1]; omega
  have hz : a % (a % g j) ≠ 0 := by rw [e2]; omega
  have hw : a % (a % (a % g j)) ≠ 0 := by rw [e3]; omega
  have l32 := (W.lt_of_lt (i := j + 2) (j := j + 3) (by omega) hj).le
  have l21 := (W.lt_of_lt (i := j + 1) (j := j + 2) (by omega) (by omega)).le
  have l10 := (W.lt_of_lt (i := j) (j := j + 1) (by omega) (by omega)).le
  set sj := g j - g (j + 3) with hsj
  have hu1 := one_le_bu hx hy
  have hv1 := one_le_bv hy hz
  have hD1 := one_le_bD hx hy hz
  have hu := bu_mul_le hx hy hz (W.le_a j (by omega))
  have hv := bv_mul_le hy hz hw
  have hD := bD_mul_le hx hy hz
  rw [e2, e1] at hu
  rw [e3, e2, e1] at hv
  rw [e3, e2] at hD
  rw [← hsj] at hD
  set u := bu a (g j)
  set v := bv a (g j)
  set D := bD a (g j)
  have hAA : A * A ≤ g (j + 1) * g j := Nat.mul_le_mul m1.1 m0.1
  have hAA' : A * A ≤ g (j + 2) * g (j + 1) := Nat.mul_le_mul m2.1 m1.1
  -- `u A² ≤ a s` and `v A² ≤ a s`
  have hu2 : u * (A * A) ≤ a * sj :=
    (Nat.mul_le_mul_left u hAA).trans (hu.trans (Nat.mul_le_mul_left a (by omega)))
  have hv2 : v * (A * A) ≤ a * sj :=
    (Nat.mul_le_mul_left v hAA').trans (hv.trans (Nat.mul_le_mul_left a (by omega)))
  have cancel : ∀ w : ℕ, w * (A * A) ≤ a * sj → w * (A * T) ≤ 12 * a := by
    intro w hw'
    have : w * (A * T) * A ≤ 12 * a * A := by
      calc w * (A * T) * A = w * (A * A) * T := by ring
        _ ≤ a * sj * T := Nat.mul_le_mul_right _ hw'
        _ = a * (sj * T) := by ring
        _ ≤ a * (12 * A) := Nat.mul_le_mul_left _ hsT
        _ = 12 * a * A := by ring
    exact Nat.le_of_mul_le_mul_right this (by omega)
  have huAT := cancel u hu2
  refine ⟨hu1, hv1, hD1, huAT, cancel v hv2, ?_⟩
  -- `D A ≤ 2 u s²`
  have hDA : D * A ≤ 2 * u * sj ^ 2 :=
    (Nat.mul_le_mul_left D m2.1).trans (hD.trans (Nat.mul_le_mul_right _ (by omega)))
  have h1 : D * T ^ 2 * A ≤ 288 * u * A * A := by
    calc D * T ^ 2 * A = D * A * T ^ 2 := by ring
      _ ≤ 2 * u * sj ^ 2 * T ^ 2 := Nat.mul_le_mul_right _ hDA
      _ = 2 * u * (sj * T) ^ 2 := by ring
      _ ≤ 2 * u * (12 * A) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsT 2)
      _ = 288 * u * A * A := by ring
  have h2 : D * T ^ 2 ≤ 288 * u * A := Nat.le_of_mul_le_mul_right h1 (by omega)
  calc D * T ^ 3 = D * T ^ 2 * T := by ring
    _ ≤ 288 * u * A * T := Nat.mul_le_mul_right _ h2
    _ = 288 * (u * (A * T)) := by ring
    _ ≤ 288 * (12 * a) := Nat.mul_le_mul_left _ huAT
    _ = 3456 * a := by ring

/-- **The curvature bound.** `T⁶ A² ≤ 995328 a³ Δ` for `T ≥ 12`. -/
theorem curvature_bound {a A T Δ : ℕ} {g : ℕ → ℕ} (W : Window a A T g) (hΔ : DivBound a Δ)
    (hT : 12 ≤ T) : T ^ 6 * A ^ 2 ≤ 995328 * a ^ 3 * Δ := by
  classical
  set J := range (T - 3)
  set s : ℕ → ℕ := fun j => g j - g (j + 3) with hs
  have ha := W.one_le_a (by omega)
  have hA := W.one_le
  have hsum : ∑ j ∈ J, s j ≤ 3 * A - 3 := by
    have := W.sum_triple_drops (T - 3) (by omega)
    have := W.mem 0 (by omega); have := W.mem 1 (by omega); have := W.mem 2 (by omega)
    have := W.mem (T - 3) (by omega); have := W.mem (T - 3 + 1) (by omega)
    have := W.mem (T - 3 + 2) (by omega)
    simp only [J, hs]
    omega
  set Sel := J.filter fun j => s j * T ≤ 12 * A
  set Bad := J.filter fun j => ¬ (s j * T ≤ 12 * A)
  have hsplit : Sel.card + Bad.card = T - 3 := by
    rw [card_filter_add_card_filter_not, card_range]
  have hbad : 4 * Bad.card < T := by
    have h1 : Bad.card * (12 * A + 1) ≤ ∑ j ∈ Bad, s j * T := by
      rw [← smul_eq_mul]
      exact card_nsmul_le_sum _ _ _ fun j hj => by
        have := (mem_filter.mp hj).2; omega
    have h2 : ∑ j ∈ Bad, s j * T ≤ ∑ j ∈ J, s j * T :=
      sum_le_sum_of_subset (filter_subset _ _)
    have h3 : ∑ j ∈ J, s j * T ≤ (3 * A - 3) * T := by
      rw [← sum_mul]; exact Nat.mul_le_mul_right _ hsum
    have h4 := h1.trans (h2.trans h3)
    by_contra hcon
    push Not at hcon
    have : T * (12 * A + 1) ≤ 4 * Bad.card * (12 * A + 1) := Nat.mul_le_mul_right _ hcon
    have : 4 * (3 * A - 3) * T < T * (12 * A + 1) := by
      have : 4 * (3 * A - 3) < 12 * A + 1 := by omega
      calc 4 * (3 * A - 3) * T < (12 * A + 1) * T :=
            Nat.mul_lt_mul_of_pos_right this (by omega)
        _ = _ := by ring
    nlinarith
  have hsel : T ≤ 2 * Sel.card := by omega
  set U := 12 * a / (A * T) with hU
  set Dm := 3456 * a / T ^ 3 with hDm
  have hAT : 12 ≤ A * T := by nlinarith
  have hUa : U ≤ a := by
    calc U ≤ 12 * a / 12 := Nat.div_le_div_left hAT (by norm_num)
      _ = a := by omega
  have hT3 : 1728 ≤ T ^ 3 := by
    calc 1728 = 12 ^ 3 := by norm_num
      _ ≤ T ^ 3 := Nat.pow_le_pow_left hT 3
  have hDma : Dm ≤ 2 * a := by
    calc Dm ≤ 3456 * a / 1728 := Nat.div_le_div_left hT3 (by norm_num)
      _ = 2 * a := by omega
  set φ : ℕ → ℕ × ℕ × ℕ := fun j => (bu a (g j), bv a (g j), bD a (g j)) with hφ
  set box := Icc 1 U ×ˢ (Icc 1 U ×ˢ Icc 1 Dm)
  have hmaps : ∀ j ∈ Sel, φ j ∈ box := by
    intro j hj
    obtain ⟨hjJ, hjs⟩ := mem_filter.mp hj
    have hjT := mem_range.mp hjJ
    obtain ⟨hu1, hv1, hD1, hu, hv, hD⟩ := block_small W (j := j) (by omega) hjs
    simp only [box, φ, mem_product, mem_Icc]
    refine ⟨⟨hu1, (Nat.le_div_iff_mul_le (by omega)).mpr hu⟩,
      ⟨hv1, (Nat.le_div_iff_mul_le (by omega)).mpr hv⟩,
      ⟨hD1, (Nat.le_div_iff_mul_le (by positivity)).mpr hD⟩⟩
  have hfib : ∀ t ∈ box, (Sel.filter fun j => φ j = t).card ≤ Δ := by
    rintro ⟨u, v, D⟩ ht
    simp only [box, mem_product, mem_Icc] at ht
    obtain ⟨⟨hu1, huU⟩, ⟨hv1, hvU⟩, ⟨hD1, hDD⟩⟩ := ht
    set F := Sel.filter fun j => φ j = (u, v, D)
    have hFj : ∀ j ∈ F, j + 3 < T ∧ bu a (g j) = u ∧ bv a (g j) = v ∧ bD a (g j) = D := by
      intro j hj
      obtain ⟨hjS, hjt⟩ := mem_filter.mp hj
      have hjT := mem_range.mp (mem_filter.mp hjS).1
      simp only [φ, Prod.mk.injEq] at hjt
      exact ⟨by omega, hjt.1, hjt.2.1, hjt.2.2⟩
    have hfeq : ∀ j ∈ F, g j * (u * (a / g j) ^ 2 + (u ^ 2 + u + v) * (a / g j) + v) =
        a * u * (a / g j) + (a * (u ^ 2 + v) + D) := by
      intro j hj
      obtain ⟨hjT, rfl, rfl, rfl⟩ := hFj j hj
      obtain ⟨e1, e2, -⟩ := W.succ3 hjT
      have m1 := W.mem (j + 1) (by omega)
      have m2 := W.mem (j + 2) (by omega)
      exact block_fiber_eq (W.pos (by omega)) (by rw [e1]; omega) (by rw [e2]; omega)
    have hinj : Set.InjOn (fun j => a / g j) (F : Set ℕ) := by
      intro i hi j hj hij
      simp only at hij
      have hi' := hfeq i hi
      have hj' := hfeq j hj
      rw [hij] at hi'
      have hMpos : 0 < u * (a / g j) ^ 2 + (u ^ 2 + u + v) * (a / g j) + v := by positivity
      have hg : g i = g j := Nat.eq_of_mul_eq_mul_right hMpos (hi'.trans hj'.symm)
      exact W.injOn (by simp; have := (hFj i hi).1; omega)
        (by simp; have := (hFj j hj).1; omega) hg
    rw [← card_image_of_injOn hinj]
    apply fiber_card_le a u v D Δ ha hu1 (huU.trans hUa) hv1 (hvU.trans hUa)
      (hDD.trans hDma) hΔ
    intro q hq
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hq
    exact ⟨g j, W.pos (by have := (hFj j hj).1; omega), hfeq j hj⟩
  have hcard : Sel.card ≤ Δ * (U * (U * Dm)) := by
    have := card_le_mul_card_image_of_maps_to hmaps Δ hfib
    simpa [box, card_product] using this
  have hUAT : U * (A * T) ≤ 12 * a := Nat.div_mul_le_self _ _
  have hDmT : Dm * T ^ 3 ≤ 3456 * a := Nat.div_mul_le_self _ _
  calc T ^ 6 * A ^ 2 = T * ((A * T) * (A * T) * T ^ 3) := by ring
    _ ≤ (2 * (Δ * (U * (U * Dm)))) * ((A * T) * (A * T) * T ^ 3) :=
        Nat.mul_le_mul_right _ (hsel.trans (by omega))
    _ = 2 * Δ * ((U * (A * T)) * (U * (A * T)) * (Dm * T ^ 3)) := by ring
    _ ≤ 2 * Δ * ((12 * a) * (12 * a) * (3456 * a)) := by gcongr
    _ = 995328 * a ^ 3 * Δ := by ring

/-- **The window bound.** `T¹⁰ ≤ 63700992 a³ Δ³` for `T ≥ 12`. -/
theorem window_bound {a A T Δ : ℕ} {g : ℕ → ℕ} (W : Window a A T g) (hΔ : DivBound a Δ)
    (hT : 12 ≤ T) : T ^ 10 ≤ 63700992 * a ^ 3 * Δ ^ 3 := by
  have h1 := drop_bound W hΔ (by omega)
  have h2 := curvature_bound W hΔ hT
  have hA := W.one_le
  have h3 : T ≤ 2 * (T - 1) := by omega
  have key : T ^ 10 * A ^ 2 ≤ 63700992 * a ^ 3 * Δ ^ 3 * A ^ 2 := by
    calc T ^ 10 * A ^ 2 = T ^ 6 * A ^ 2 * T ^ 2 * T ^ 2 := by ring
      _ ≤ T ^ 6 * A ^ 2 * T ^ 2 * (2 * (T - 1)) ^ 2 := by gcongr
      _ = 4 * (T ^ 6 * A ^ 2) * (T * (T - 1)) ^ 2 := by ring
      _ ≤ 4 * (995328 * a ^ 3 * Δ) * (4 * A * Δ) ^ 2 := by gcongr
      _ = 63700992 * a ^ 3 * Δ ^ 3 * A ^ 2 := by ring
  exact Nat.le_of_mul_le_mul_right key (by positivity)

end PierceLengthBound
