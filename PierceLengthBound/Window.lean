/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.Block

/-!
# Counting the visits to a dyadic window

A *window run* is a run `g 0, g 1, …, g (T-1)` of consecutive terms of an orbit of
`x ↦ a mod x`, all lying in `[A, 2A)`. We prove, with `Δ` a bound for the divisor function on
`[1, 2a]`:

* `drop_bound`: `T (T - 1) ≤ 4 A Δ` (the Erdős–Shallit divisor argument, Proposition 5.1).

Combined with the six-step bound it gives the `3/10` window bound (`window_bound` in
`SixStep`). The file also holds the window vocabulary shared by the later window bounds:

* the structure `Window` with its monotonicity lemmas and the telescoping identities
  `Window.sum_drops`, `Window.sum_five_drops`;
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

/-- `Δ` bounds the divisor function on `[1, 2a]`. -/
def DivBound (a Δ : ℕ) : Prop := ∀ n : ℕ, 0 < n → n ≤ 2 * a → n.divisors.card ≤ Δ

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
      _ ≤ Δ := hΔ _ (by omega) (by omega)
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

end PierceLengthBound
