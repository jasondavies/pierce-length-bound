/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.Conditional

/-!
# Trajectories with few rises in the quotient increments

Let `kᵢ = q_{i+1} - qᵢ` be the quotient increments and `R = 1 + #{i : k_{i+1} > kᵢ}`.
This file proves the window bounds; `RisesMain.lean` deduces `P(a, b) ≪ a^{1/4} √R` (`P_le_rises`).

* `ap_bound`: six quotients in arithmetic progression `q, q+h, …, q+5h` force
  `q⁴ ≤ 324 h³ a`. The key is the exact identity `q h U = (3h-1) E + F` for the integer
  third difference `U = d₀ - 2d₁ + d₂`, so `U ≥ 1`.
* `drop_lt_of_not_rise`: if `k_{i+1} ≤ kᵢ` then `d_{i+1} < dᵢ` (from the curvature `D ≥ 1`).
* window bounds: `T - 1 ≤ √(2R'A)`, `T - 1 ≤ √(8R'a/A) + (26244 A)^{1/3}` and `T - 1 ≤ a/A`.
-/

@[expose] public section

namespace PierceLengthBound

open Finset

/-- The arithmetic-progression identity `q h U = (3h - 1) E + F`. -/
theorem ap_identity (a q h x0 x1 x2 x3 x4 : ℤ)
    (e0 : x0 * q + x1 = a) (e1 : x1 * (q + h) + x2 = a) (e2 : x2 * (q + 2 * h) + x3 = a)
    (e3 : x3 * (q + 3 * h) + x4 = a) :
    q * h * ((x0 - x1) - 2 * (x1 - x2) + (x2 - x3)) =
      (3 * h - 1) * ((x1 - x2) * h - (x2 - x3) * h) + ((x2 - x3) * h - (x3 - x4) * h) := by
  linear_combination h * e0 - 3 * h * e1 + 3 * h * e2 - h * e3

/-- `q (x - y) ≤ h y` for two consecutive division equations with increment `h`. -/
lemma mul_drop_le {a q h x y z : ℕ} (e1 : x * q + y = a) (e2 : y * (q + h) + z = a)
    (hzy : z ≤ y) (hyx : y ≤ x) : q * (x - y) ≤ h * y := by
  have : ((q * (x - y) : ℕ) : ℤ) ≤ ((h * y : ℕ) : ℤ) := by
    push_cast [hyx]
    have e1' : (x : ℤ) * q + y = a := by exact_mod_cast e1
    have e2' : (y : ℤ) * (q + h) + z = a := by exact_mod_cast e2
    have : (z : ℤ) ≤ y := by exact_mod_cast hzy
    nlinarith
  exact_mod_cast this

private lemma aux_h3 (q h : ℕ) (hh : 1 ≤ h) :
    (3 * h - 1) * (q + 3 * h + 1) + (q + 4 * h + 1) ≤ 3 * h * (q + 4 * h + 1) := by
  have : 1 ≤ 3 * h := by omega
  zify [this]; nlinarith

private lemma aux_pos {E F h : ℤ} (hE : 1 ≤ E) (hF : 0 ≤ F) (hh : 1 ≤ h) :
    0 < (3 * h - 1) * E + F := by
  have h2 : (2 : ℤ) ≤ 3 * h - 1 := by linarith
  have : (2 : ℤ) * 1 ≤ (3 * h - 1) * E := mul_le_mul h2 hE (by norm_num) (by linarith)
  linarith

/-- **Six quotients in arithmetic progression.** If `xⱼ (q + j h) + x_{j+1} = a` for
`j = 0, …, 5` with `x₀ > x₁ > ⋯ > x₆`, then `q⁴ ≤ 324 h³ a`. -/
theorem ap_bound {a q h x0 x1 x2 x3 x4 x5 x6 : ℕ} (hq : 1 ≤ q) (hh : 1 ≤ h)
    (e0 : x0 * q + x1 = a) (e1 : x1 * (q + h) + x2 = a) (e2 : x2 * (q + 2 * h) + x3 = a)
    (e3 : x3 * (q + 3 * h) + x4 = a) (e4 : x4 * (q + 4 * h) + x5 = a)
    (e5 : x5 * (q + 5 * h) + x6 = a)
    (_h01 : x1 < x0) (h12 : x2 < x1) (h23 : x3 < x2) (h34 : x4 < x3) (h45 : x5 < x4)
    (h56 : x6 < x5) :
    q ^ 4 ≤ 324 * h ^ 3 * a := by
  -- the curvatures `E` (block at `x₁`) and `F` (block at `x₂`)
  have bE := block_core a x4 (x3 - x4) (x2 - x3) (x1 - x2) (q + h) h h (by omega) (by omega) hh
    (by rw [show x4 + (x3 - x4) + (x2 - x3) + (x1 - x2) = x1 by omega,
      show x4 + (x3 - x4) + (x2 - x3) = x2 by omega]; exact e1)
    (by rw [show x4 + (x3 - x4) + (x2 - x3) = x2 by omega, show x4 + (x3 - x4) = x3 by omega,
      show q + h + h = q + 2 * h by ring]; exact e2)
    (by rw [show x4 + (x3 - x4) = x3 by omega, show q + h + h + h = q + 3 * h by ring]; exact e3)
  have bF := block_core a x5 (x4 - x5) (x3 - x4) (x2 - x3) (q + 2 * h) h h (by omega) (by omega)
    hh
    (by rw [show x5 + (x4 - x5) + (x3 - x4) + (x2 - x3) = x2 by omega,
      show x5 + (x4 - x5) + (x3 - x4) = x3 by omega]; exact e2)
    (by rw [show x5 + (x4 - x5) + (x3 - x4) = x3 by omega, show x5 + (x4 - x5) = x4 by omega,
      show q + 2 * h + h = q + 3 * h by ring]; exact e3)
    (by rw [show x5 + (x4 - x5) = x4 by omega, show q + 2 * h + h + h = q + 4 * h by ring]
        exact e4)
  obtain ⟨hEpos, hEle, -⟩ := bE
  obtain ⟨hFpos, hFle, -⟩ := bF
  rw [show x4 + (x3 - x4) = x3 by omega,
    show x1 - x2 + (x2 - x3) + (x3 - x4) = x1 - x4 by omega] at hEle
  rw [show x5 + (x4 - x5) = x4 by omega,
    show x2 - x3 + (x3 - x4) + (x4 - x5) = x2 - x5 by omega] at hFle
  set E := (x1 - x2) * h - (x2 - x3) * h with hE
  set F := (x2 - x3) * h - (x3 - x4) * h with hF
  -- `U ≥ 1` from the identity
  have hid := ap_identity a q h x0 x1 x2 x3 x4 (by exact_mod_cast e0) (by exact_mod_cast e1)
    (by exact_mod_cast e2) (by exact_mod_cast e3)
  have cE : (E : ℤ) = ((x1 : ℤ) - x2) * h - ((x2 : ℤ) - x3) * h := by
    rw [hE, Nat.cast_sub hEpos.le]; push_cast [h12.le, h23.le]; ring
  have cF : (F : ℤ) = ((x2 : ℤ) - x3) * h - ((x3 : ℤ) - x4) * h := by
    rw [hF, Nat.cast_sub hFpos.le]; push_cast [h23.le, h34.le]; ring
  rw [← cE, ← cF] at hid
  set U : ℤ := ((x0 : ℤ) - x1) - 2 * ((x1 : ℤ) - x2) + ((x2 : ℤ) - x3) with hU
  have hE1 : 1 ≤ E := by omega
  have hU1 : 1 ≤ U := by
    have h3 : (0 : ℤ) < (3 * h - 1) * (E : ℤ) + F :=
      aux_pos (by exact_mod_cast hE1) (by positivity) (by exact_mod_cast hh)
    have : 0 < (q : ℤ) * h * U := by rw [hid]; exact h3
    have hqh : (0 : ℤ) < (q : ℤ) * h := by
      have : (1 : ℤ) ≤ q := by exact_mod_cast hq
      have : (1 : ℤ) ≤ h := by exact_mod_cast hh
      positivity
    have := pos_of_mul_pos_right this hqh.le
    omega
  -- the drops are `≤ h a / q²`
  have d1 := mul_drop_le e1 (by rw [show q + h + h = q + 2 * h by ring]; exact e2) h23.le h12.le
  have d2 := mul_drop_le e2 (by rw [show q + 2 * h + h = q + 3 * h by ring]; exact e3) h34.le
    h23.le
  have d3 := mul_drop_le e3 (by rw [show q + 3 * h + h = q + 4 * h by ring]; exact e4) h45.le
    h34.le
  have d4 := mul_drop_le e4 (by rw [show q + 4 * h + h = q + 5 * h by ring]; exact e5) h56.le
    h45.le
  have b2 : x2 * (q + 2 * h) ≤ a := by omega
  have b3 : x3 * (q + 3 * h) ≤ a := by omega
  have b4 : x4 * (q + 4 * h) ≤ a := by omega
  have b5 : x5 * (q + 5 * h) ≤ a := by omega
  -- `q² fⱼ ≤ h a` for `j = 1, …, 4`
  have sq : ∀ {f x qj qj' : ℕ}, q ≤ qj → q ≤ qj' → qj * f ≤ h * x → x * qj' ≤ a →
      q ^ 2 * f ≤ h * a := by
    intro f x qj qj' hq1 hq2 hf hx
    calc q ^ 2 * f = q * (q * f) := by ring
      _ ≤ qj' * (qj * f) := Nat.mul_le_mul hq2 (Nat.mul_le_mul_right _ hq1)
      _ ≤ qj' * (h * x) := Nat.mul_le_mul_left _ hf
      _ = h * (x * qj') := by ring
      _ ≤ h * a := Nat.mul_le_mul_left _ hx
  have f1 := sq (by omega) (by omega) d1 b2
  have f2 := sq (by omega) (by omega) d2 b3
  have f3 := sq (by omega) (by omega) d3 b4
  have f4 := sq (by omega) (by omega) d4 b5
  -- `E q⁴ ≤ 9 h² (h+1) (q + 3h + 1) a`, `F q⁴ ≤ 9 h² (h+1) (q + 4h + 1) a`
  have ha3 : a < x3 * (q + 3 * h + 1) := by rw [mul_add, mul_one]; omega
  have ha4 : a < x4 * (q + 4 * h + 1) := by rw [mul_add, mul_one]; omega
  have ha0 : 0 < a := by omega
  have hEq : E * q ^ 4 ≤ 9 * h ^ 2 * (h + 1) * (q + 3 * h + 1) * a := by
    have hsum : q ^ 2 * (x1 - x4) ≤ 3 * (h * a) := by
      rw [show x1 - x4 = (x1 - x2) + (x2 - x3) + (x3 - x4) by omega, mul_add, mul_add]; omega
    have : E * x3 * q ^ 4 ≤ 9 * h ^ 2 * (h + 1) * a * a := by
      calc E * x3 * q ^ 4 ≤ (h + 1) * (x1 - x4) ^ 2 * q ^ 4 := Nat.mul_le_mul_right _ hEle
        _ = (h + 1) * (q ^ 2 * (x1 - x4)) ^ 2 := by ring
        _ ≤ (h + 1) * (3 * (h * a)) ^ 2 := by gcongr
        _ = 9 * h ^ 2 * (h + 1) * a * a := by ring
    have : E * q ^ 4 * a ≤ 9 * h ^ 2 * (h + 1) * (q + 3 * h + 1) * a * a := by
      calc E * q ^ 4 * a ≤ E * q ^ 4 * (x3 * (q + 3 * h + 1)) := Nat.mul_le_mul_left _ ha3.le
        _ = E * x3 * q ^ 4 * (q + 3 * h + 1) := by ring
        _ ≤ 9 * h ^ 2 * (h + 1) * a * a * (q + 3 * h + 1) := Nat.mul_le_mul_right _ this
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right this ha0
  have hFq : F * q ^ 4 ≤ 9 * h ^ 2 * (h + 1) * (q + 4 * h + 1) * a := by
    have hsum : q ^ 2 * (x2 - x5) ≤ 3 * (h * a) := by
      rw [show x2 - x5 = (x2 - x3) + (x3 - x4) + (x4 - x5) by omega, mul_add, mul_add]; omega
    have : F * x4 * q ^ 4 ≤ 9 * h ^ 2 * (h + 1) * a * a := by
      calc F * x4 * q ^ 4 ≤ (h + 1) * (x2 - x5) ^ 2 * q ^ 4 := Nat.mul_le_mul_right _ hFle
        _ = (h + 1) * (q ^ 2 * (x2 - x5)) ^ 2 := by ring
        _ ≤ (h + 1) * (3 * (h * a)) ^ 2 := by gcongr
        _ = 9 * h ^ 2 * (h + 1) * a * a := by ring
    have : F * q ^ 4 * a ≤ 9 * h ^ 2 * (h + 1) * (q + 4 * h + 1) * a * a := by
      calc F * q ^ 4 * a ≤ F * q ^ 4 * (x4 * (q + 4 * h + 1)) := Nat.mul_le_mul_left _ ha4.le
        _ = F * x4 * q ^ 4 * (q + 4 * h + 1) := by ring
        _ ≤ 9 * h ^ 2 * (h + 1) * a * a * (q + 4 * h + 1) := Nat.mul_le_mul_right _ this
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right this ha0
  -- `q h ≤ q h U = (3h-1) E + F`, so `q⁵ h ≤ 27 h³ (h+1) (q + 4h + 1) a`
  have hqhU : q * h ≤ (3 * h - 1) * E + F := by
    have : ((q * h : ℕ) : ℤ) ≤ (((3 * h - 1) * E + F : ℕ) : ℤ) := by
      push_cast [show 1 ≤ 3 * h by omega]
      calc (q : ℤ) * h = q * h * 1 := by ring
        _ ≤ q * h * U := by gcongr
        _ = _ := hid
    exact_mod_cast this
  have key : q ^ 5 * h ≤ 27 * h ^ 3 * (h + 1) * (q + 4 * h + 1) * a := by
    calc q ^ 5 * h = q * h * q ^ 4 := by ring
      _ ≤ ((3 * h - 1) * E + F) * q ^ 4 := Nat.mul_le_mul_right _ hqhU
      _ = (3 * h - 1) * (E * q ^ 4) + F * q ^ 4 := by ring
      _ ≤ (3 * h - 1) * (9 * h ^ 2 * (h + 1) * (q + 3 * h + 1) * a) +
            9 * h ^ 2 * (h + 1) * (q + 4 * h + 1) * a := by gcongr
      _ ≤ 27 * h ^ 3 * (h + 1) * (q + 4 * h + 1) * a := by
          have h3 := aux_h3 q h hh
          calc (3 * h - 1) * (9 * h ^ 2 * (h + 1) * (q + 3 * h + 1) * a) +
                9 * h ^ 2 * (h + 1) * (q + 4 * h + 1) * a
              = 9 * h ^ 2 * (h + 1) * a * ((3 * h - 1) * (q + 3 * h + 1) + (q + 4 * h + 1)) := by
                ring
            _ ≤ 9 * h ^ 2 * (h + 1) * a * (3 * h * (q + 4 * h + 1)) := Nat.mul_le_mul_left _ h3
            _ = _ := by ring
  have key' : q ^ 5 ≤ 27 * h ^ 2 * (h + 1) * (q + 4 * h + 1) * a := by
    have : q ^ 5 * h ≤ 27 * h ^ 2 * (h + 1) * (q + 4 * h + 1) * a * h := by
      calc q ^ 5 * h ≤ _ := key
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right this (by omega)
  rcases le_or_gt h q with hqh | hqh
  · -- `q + 4h + 1 ≤ 6q` and `h + 1 ≤ 2h`
    have : q ^ 5 ≤ 324 * h ^ 3 * a * q := by
      calc q ^ 5 ≤ 27 * h ^ 2 * (h + 1) * (q + 4 * h + 1) * a := key'
        _ ≤ 27 * h ^ 2 * (2 * h) * (6 * q) * a := by gcongr <;> omega
        _ = 324 * h ^ 3 * a * q := by ring
    have : q ^ 4 * q ≤ 324 * h ^ 3 * a * q := by rw [← pow_succ]; exact this
    exact Nat.le_of_mul_le_mul_right this (by omega)
  · -- `q < h ≤ a`
    have hha : h ≤ a := by
      have : q + h ≤ x1 * (q + h) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    calc q ^ 4 ≤ h ^ 4 := Nat.pow_le_pow_left hqh.le 4
      _ = h ^ 3 * h := by ring
      _ ≤ h ^ 3 * a := Nat.mul_le_mul_left _ hha
      _ ≤ 324 * (h ^ 3 * a) := Nat.le_mul_of_pos_left _ (by norm_num)
      _ = 324 * h ^ 3 * a := by ring

/-! ### Runs and multiplicities -/

/-- If every value occurs at most `M` times among the positive numbers `c j`, `j ∈ J`, then
`|J|² ≤ 2 M ∑_{j ∈ J} c j`. -/
theorem sq_card_le_of_fiber (c : ℕ → ℕ) (M : ℕ) :
    ∀ J : Finset ℕ, (∀ j ∈ J, 1 ≤ c j) → (∀ v, (J.filter (c · = v)).card ≤ M) →
      J.card ^ 2 ≤ 2 * M * ∑ j ∈ J, c j := by
  classical
  intro J
  induction J using Finset.strongInduction with
  | H J ih =>
    intro hc hM
    rcases J.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨j0, hj0, hmax⟩ := J.exists_max_image c hne
    -- `|J| ≤ M · c j0`
    have hcard : J.card ≤ M * c j0 := by
      have := card_le_mul_card_image_of_maps_to (f := c) (t := Icc 1 (c j0))
        (fun j hj => mem_Icc.mpr ⟨hc j hj, hmax j hj⟩) M (fun v _ => hM v)
      simpa using this
    have hsub : J.erase j0 ⊂ J := erase_ssubset hj0
    have ih' := ih _ hsub (fun j hj => hc j (mem_of_mem_erase hj))
      (fun v => (card_le_card (filter_subset_filter _ (erase_subset _ _))).trans (hM v))
    have hsum := add_sum_erase J c hj0
    have hJ : J.card = (J.erase j0).card + 1 := (card_erase_add_one hj0).symm
    rw [← hsum, hJ]
    rw [hJ] at hcard
    nlinarith

/-- The end of the run containing `j`: the first `e ≥ j` with a rise at `e`, or `n - 1`. -/
noncomputable def runEnd (n : ℕ) (rise : ℕ → Prop) [DecidablePred rise] (j : ℕ) : ℕ :=
  Nat.find (⟨j + n, by omega, Or.inl (by omega)⟩ : ∃ e, j ≤ e ∧ (n ≤ e + 1 ∨ rise e))

section Runs

variable {n : ℕ} {rise : ℕ → Prop} [DecidablePred rise]

lemma le_runEnd (j : ℕ) : j ≤ runEnd n rise j := (Nat.find_spec (⟨j + n, by omega,
  Or.inl (by omega)⟩ : ∃ e, j ≤ e ∧ (n ≤ e + 1 ∨ rise e))).1

lemma runEnd_spec (j : ℕ) : n ≤ runEnd n rise j + 1 ∨ rise (runEnd n rise j) :=
  (Nat.find_spec (⟨j + n, by omega, Or.inl (by omega)⟩ : ∃ e, j ≤ e ∧ (n ≤ e + 1 ∨ rise e))).2

lemma runEnd_le {j : ℕ} (hj : j < n) : runEnd n rise j ≤ n - 1 :=
  Nat.find_min' _ ⟨by omega, Or.inl (by omega)⟩

/-- Before the end of its run there is no rise, and we are not at the last index. -/
lemma not_rise_of_lt_runEnd {j m : ℕ} (hjm : j ≤ m) (hm : m < runEnd n rise j) :
    ¬ rise m ∧ m + 1 < n := by
  have := Nat.find_min (⟨j + n, by omega, Or.inl (by omega)⟩ :
    ∃ e, j ≤ e ∧ (n ≤ e + 1 ∨ rise e)) hm
  push Not at this
  obtain ⟨h1, h2⟩ := this hjm
  exact ⟨h2, by omega⟩

/-- There are at most `1 + #rises` run ends. -/
lemma card_image_runEnd_le :
    ((range n).image (runEnd n rise)).card ≤ ((range (n - 1)).filter rise).card + 1 := by
  classical
  calc ((range n).image (runEnd n rise)).card
      ≤ (insert (n - 1) ((range (n - 1)).filter rise)).card := by
        apply card_le_card
        intro e he
        obtain ⟨j, hj, rfl⟩ := mem_image.mp he
        have hjn := mem_range.mp hj
        have hle := runEnd_le (rise := rise) hjn
        rcases runEnd_spec (n := n) (rise := rise) j with h | h
        · exact mem_insert.mpr (Or.inl (by omega))
        · rcases eq_or_lt_of_le hle with h' | h'
          · exact mem_insert.mpr (Or.inl h')
          · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_range.mpr h', h⟩)
    _ ≤ _ := card_insert_le _ _

end Runs

/-- A strictly decreasing stretch: `c (m+1) < c m` on `[j, j')` gives `c j' < c j`. -/
lemma lt_of_chain {c : ℕ → ℕ} {j j' : ℕ} (h : ∀ m, j ≤ m → m < j' → c (m + 1) < c m)
    (hjj : j < j') : c j' < c j := by
  induction j', hjj using Nat.le_induction with
  | base => exact h j le_rfl (by omega)
  | succ j' hjj ih =>
    exact (h j' (by omega) (by omega)).trans (ih fun m h1 h2 => h m h1 (by omega))

/-- A nonincreasing stretch: `c (m+1) ≤ c m` on `[j, j')` gives `c j' ≤ c m ≤ c j` on it. -/
lemma le_of_chain {c : ℕ → ℕ} {j j' : ℕ} (h : ∀ m, j ≤ m → m < j' → c (m + 1) ≤ c m) :
    ∀ m, j ≤ m → m ≤ j' → c j' ≤ c m ∧ c m ≤ c j := by
  have up : ∀ t m, j ≤ m → m + t = j' → c j' ≤ c m := by
    intro t
    induction t with
    | zero => intro m _ hm; rw [← hm]; simp
    | succ t ih =>
      intro m hjm hm
      exact (ih (m + 1) (by omega) (by omega)).trans (h m hjm (by omega))
  have down : ∀ t, j + t ≤ j' → c (j + t) ≤ c j := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      exact (h (j + t) (by omega) (by omega)).trans (ih (by omega))
  intro m hjm hmj
  refine ⟨up (j' - m) m hjm (by omega), ?_⟩
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hjm
  exact down t hmj

/-! ### Increments and drops of a window run -/

/-- The quotient increment `kⱼ = ⌊a/g(j+1)⌋ - ⌊a/g(j)⌋`. -/
def incr (a : ℕ) (g : ℕ → ℕ) (j : ℕ) : ℕ := a / g (j + 1) - a / g j

/-- The drop `dⱼ = g(j) - g(j+1)`. -/
def drop (g : ℕ → ℕ) (j : ℕ) : ℕ := g j - g (j + 1)

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

/-- The curvature `D ≥ 1` as `d_{j+1} k_j < d_j k_{j+1}`. -/
lemma ratio_lt (W : Window a A T g) {j : ℕ} (hj : j + 2 < T) :
    drop g (j + 1) * incr a g j < drop g j * incr a g (j + 1) := by
  have e1 : a % g j = g (j + 1) := (W.step j (by omega)).symm
  have e2 : a % g (j + 1) = g (j + 2) := (W.step (j + 1) (by omega)).symm
  have hx := W.pos (j := j) (by omega)
  have hy : a % g j ≠ 0 := by rw [e1]; exact (W.pos (j := j + 1) (by omega)).ne'
  have hz : a % (a % g j) ≠ 0 := by rw [e1, e2]; exact (W.pos (j := j + 2) (by omega)).ne'
  have h := one_le_bD hx hy hz
  unfold bD bv bu at h
  rw [e1, e2] at h
  unfold drop incr
  rw [show j + 1 + 1 = j + 2 from rfl]
  omega

/-- **No rise means a falling drop.** -/
lemma drop_lt_of_not_rise (W : Window a A T g) {j : ℕ} (hj : j + 2 < T)
    (h : incr a g (j + 1) ≤ incr a g j) : drop g (j + 1) < drop g j := by
  have hr := W.ratio_lt hj
  have hk := W.one_le_incr (j := j + 1) (by omega)
  by_contra hcon
  push Not at hcon
  have : drop g j * incr a g (j + 1) ≤ drop g (j + 1) * incr a g j :=
    Nat.mul_le_mul hcon h
  omega

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

/-- The number of rises `k_j < k_{j+1}` inside a window run. -/
noncomputable def windowRises (a : ℕ) (g : ℕ → ℕ) (T : ℕ) : ℕ :=
  ((range (T - 2)).filter fun j => incr a g j < incr a g (j + 1)).card

/-! ### The three window bounds -/

private lemma lt_three_mul {a A q x y : ℕ} (e : x * q + y = a) (hyx : y < x) (hx : x < 2 * A)
    (h6 : 6 * A ≤ a) : a < 3 * A * q := by
  nlinarith

private lemma low_contra {a A q h : ℕ} (hq4 : q ^ 4 ≤ 324 * h ^ 3 * a) (h3 : a < 3 * A * q)
    (hlow : 26244 * h ^ 3 * A ^ 4 < a ^ 3) : False := by
  have h1 : a ^ 4 < (3 * A * q) ^ 4 := Nat.pow_lt_pow_left h3 (by norm_num)
  have h2 : (3 * A * q) ^ 4 ≤ 81 * A ^ 4 * (324 * h ^ 3 * a) := by
    calc (3 * A * q) ^ 4 = 81 * A ^ 4 * q ^ 4 := by ring
      _ ≤ 81 * A ^ 4 * (324 * h ^ 3 * a) := Nat.mul_le_mul_left _ hq4
  have h3' : 81 * A ^ 4 * (324 * h ^ 3 * a) = 26244 * h ^ 3 * A ^ 4 * a := by ring
  have h4 : 26244 * h ^ 3 * A ^ 4 * a < a ^ 3 * a :=
    Nat.mul_lt_mul_of_pos_right hlow (by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · subst h0; simp at hlow
      · exact h0)
  have h5 : a ^ 4 < a ^ 3 * a := (lt_of_lt_of_le h1 (h2.trans h3'.le)).trans h4
  rw [← pow_succ] at h5
  exact lt_irrefl _ h5

private lemma high_cube {s k Q A a : ℕ} (h1 : s * k ≤ Q) (h2 : a ^ 3 ≤ 26244 * k ^ 3 * A ^ 4)
    (hQ : A * Q ≤ a) (ha : 0 < a) : s ^ 3 ≤ 26244 * A := by
  have : s ^ 3 * a ^ 3 ≤ 26244 * A * a ^ 3 := by
    calc s ^ 3 * a ^ 3 ≤ s ^ 3 * (26244 * k ^ 3 * A ^ 4) := Nat.mul_le_mul_left _ h2
      _ = 26244 * A * (A * (s * k)) ^ 3 := by ring
      _ ≤ 26244 * A * (A * Q) ^ 3 := by gcongr
      _ ≤ 26244 * A * a ^ 3 := by gcongr
  exact Nat.le_of_mul_le_mul_right this (by positivity)

namespace Window

variable {a A T : ℕ} {g : ℕ → ℕ}

/-- The run ends of a window run, for its `T - 1` increments. -/
private noncomputable abbrev wEnd (a : ℕ) (g : ℕ → ℕ) (T : ℕ) : ℕ → ℕ :=
  runEnd (T - 1) (fun j => incr a g j < incr a g (j + 1))

private lemma card_wEnd (a : ℕ) (g : ℕ → ℕ) (T : ℕ) :
    ((range (T - 1)).image (wEnd a g T)).card ≤ windowRises a g T + 1 := by
  have := card_image_runEnd_le (n := T - 1) (rise := fun j => incr a g j < incr a g (j + 1))
  rw [show T - 1 - 1 = T - 2 by omega] at this
  exact this

/-- No rise strictly before the end of the run. -/
private lemma incr_le_of_lt_wEnd {j m : ℕ} (hjm : j ≤ m) (hm : m < wEnd a g T j) :
    incr a g (m + 1) ≤ incr a g m ∧ m + 2 < T := by
  have := not_rise_of_lt_runEnd (n := T - 1) (rise := fun j => incr a g j < incr a g (j + 1))
    hjm hm
  exact ⟨not_lt.mp this.1, by omega⟩

/-- **Proposition 9.5(1).** `(T - 1)² ≤ 2 (ρ + 1)(A - 1)`. -/
theorem rises_drop_bound (W : Window a A T g) (hT : 2 ≤ T) :
    (T - 1) ^ 2 ≤ 2 * (windowRises a g T + 1) * (A - 1) := by
  classical
  set M := ((range (T - 1)).image (wEnd a g T)).card
  have hM : M ≤ windowRises a g T + 1 := card_wEnd a g T
  have hfib : ∀ v, ((range (T - 1)).filter (drop g · = v)).card ≤ M := by
    intro v
    apply card_le_card_of_injOn (wEnd a g T)
    · intro j hj
      exact mem_image_of_mem _ (mem_filter.mp (Finset.mem_coe.mp hj)).1
    · intro j hj j' hj' heq
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, mem_range] at hj hj'
      by_contra hne
      have key : ∀ {i i' : ℕ}, i < i' → wEnd a g T i = wEnd a g T i' →
          drop g i' < drop g i := by
        intro i i' hii heq'
        apply lt_of_chain _ hii
        intro m h1 h2
        have hle' : i' ≤ wEnd a g T i' := le_runEnd i'
        have hm : m < wEnd a g T i := by rw [heq']; omega
        obtain ⟨hle, hmT⟩ := incr_le_of_lt_wEnd h1 hm
        exact W.drop_lt_of_not_rise hmT hle
      rcases lt_or_gt_of_ne hne with h | h
      · have := key h heq; omega
      · have := key h heq.symm; omega
  have hsq := sq_card_le_of_fiber (drop g) M (range (T - 1))
    (fun j hj => W.one_le_drop (by have := mem_range.mp hj; omega)) hfib
  rw [card_range] at hsq
  have hsum : ∑ j ∈ range (T - 1), drop g j ≤ A - 1 := by
    have := W.sum_drops (T - 1) (by omega)
    have h0 := W.mem 0 (by omega)
    have h1 := W.mem (T - 1) (by omega)
    unfold drop
    omega
  calc (T - 1) ^ 2 ≤ 2 * M * ∑ j ∈ range (T - 1), drop g j := hsq
    _ ≤ 2 * (windowRises a g T + 1) * (A - 1) := by gcongr

/-- **Proposition 9.5(2).** `T - 1 ≤ a / A`. -/
theorem rises_quot_bound (W : Window a A T g) (hT : 1 ≤ T) : T - 1 ≤ a / A := by
  have h1 : (range (T - 1)).card • 1 ≤ ∑ j ∈ range (T - 1), incr a g j :=
    card_nsmul_le_sum _ _ _ fun j hj => W.one_le_incr (by have := mem_range.mp hj; omega)
  rw [card_range, smul_eq_mul, mul_one] at h1
  exact h1.trans (W.sum_incr_le hT)

/-- Five consecutive equal increments `h` force `h` to be large. -/
private lemma not_low_of_five (W : Window a A T g) (h6 : 6 * A ≤ a) {j h : ℕ}
    (hj : j + 5 < T) (hk : ∀ t, t < 5 → incr a g (j + t) = h) :
    a ^ 3 ≤ 26244 * h ^ 3 * A ^ 4 := by
  by_contra hlow
  push Not at hlow
  set q := a / g j
  have hq : ∀ t, t ≤ 5 → a / g (j + t) = q + t * h := by
    intro t ht
    induction t with
    | zero => simp [q]
    | succ t ih =>
      have := ih (by omega)
      have hlt := W.quot_lt (j := j + t) (by omega)
      have hkt := hk t (by omega)
      have e : a / g (j + t + 1) = a / g (j + t) + incr a g (j + t) := by
        unfold incr; exact (Nat.add_sub_cancel' hlt.le).symm
      rw [show j + (t + 1) = j + t + 1 by ring, e, this, hkt]
      ring
  have hdiv : ∀ t, t ≤ 4 → g (j + t) * (q + t * h) + g (j + t + 1) = a := by
    intro t ht
    rw [← hq t (by omega), W.step (j + t) (by omega)]
    exact Nat.div_add_mod a _
  have hh : 1 ≤ h := by rw [← hk 0 (by omega)]; exact W.one_le_incr (by omega)
  have hq1 : 1 ≤ q := (Nat.le_div_iff_mul_le (W.pos (by omega))).mpr (by
    simpa using W.le_a j (by omega))
  have e0 := hdiv 0 (by norm_num)
  have e1 := hdiv 1 (by norm_num)
  have e2 := hdiv 2 (by norm_num)
  have e3 := hdiv 3 (by norm_num)
  have e4 := hdiv 4 (by norm_num)
  have e5 : g (j + 5) * (q + 5 * h) + a % g (j + 5) = a := by
    rw [← hq 5 le_rfl]; exact Nat.div_add_mod a _
  simp only [add_zero, zero_mul, one_mul] at e0 e1
  have l : ∀ t, t ≤ 4 → g (j + t + 1) < g (j + t) := fun t ht => W.succ_lt (by omega)
  have l0 := l 0 (by norm_num); have l1 := l 1 (by norm_num); have l2 := l 2 (by norm_num)
  have l3 := l 3 (by norm_num); have l4 := l 4 (by norm_num)
  have l5 : a % g (j + 5) < g (j + 5) := Nat.mod_lt _ (W.pos (by omega))
  simp only [add_zero] at l0
  have hq4 := ap_bound (x0 := g j) (x1 := g (j + 1)) (x2 := g (j + 2)) (x3 := g (j + 3))
    (x4 := g (j + 4)) (x5 := g (j + 5)) (x6 := a % g (j + 5)) hq1 hh e0 e1 e2 e3 e4 e5
    l0 l1 l2 l3 l4 l5
  have h3 := lt_three_mul e0 l0 (W.mem j (by omega)).2 h6
  exact low_contra hq4 h3 hlow

/-- **Proposition 9.5(3).** If `6A ≤ a` then `T - 1 = ℓ + s` with `ℓ² ≤ 8(ρ+1)(a/A)` and
`s³ ≤ 26244 A`. -/
theorem rises_incr_bound (W : Window a A T g) (hT : 2 ≤ T) (h6 : 6 * A ≤ a) :
    ∃ l s : ℕ, T - 1 = l + s ∧ l ^ 2 ≤ 8 * (windowRises a g T + 1) * (a / A) ∧
      s ^ 3 ≤ 26244 * A := by
  classical
  set low : ℕ → Prop := fun j => 26244 * incr a g j ^ 3 * A ^ 4 < a ^ 3
  set JL := (range (T - 1)).filter low
  set JH := (range (T - 1)).filter fun j => ¬ low j
  have hsplit : JL.card + JH.card = T - 1 := by
    rw [card_filter_add_card_filter_not, card_range]
  set M := ((range (T - 1)).image (wEnd a g T)).card
  have hM : M ≤ windowRises a g T + 1 := card_wEnd a g T
  have hA := W.one_le
  have ha : 0 < a := by omega
  have hsumall := W.sum_incr_le (by omega)
  refine ⟨JL.card, JH.card, hsplit.symm, ?_, ?_⟩
  · -- low values occur at most `4M` times
    have hfib : ∀ v, (JL.filter (incr a g · = v)).card ≤ 4 * M := by
      intro v
      have := card_le_mul_card_image_of_maps_to (f := wEnd a g T)
        (s := JL.filter (incr a g · = v)) (t := (range (T - 1)).image (wEnd a g T))
        (fun j hj => mem_image_of_mem _ (mem_filter.mp (mem_filter.mp hj).1).1) 4 ?_
      · exact this
      intro e _
      by_contra hcon
      push Not at hcon
      set G := (JL.filter (incr a g · = v)).filter (wEnd a g T · = e)
      have hGne : G.Nonempty := by rw [← card_pos]; omega
      obtain ⟨j1, hj1d⟩ : ∃ j1, j1 = G.min' hGne := ⟨_, rfl⟩
      obtain ⟨j5, hj5d⟩ : ∃ j5, j5 = G.max' hGne := ⟨_, rfl⟩
      have hj1 : j1 ∈ G := hj1d ▸ G.min'_mem hGne
      have hj5 : j5 ∈ G := hj5d ▸ G.max'_mem hGne
      have hsub : G ⊆ Icc j1 j5 := fun j hj => mem_Icc.mpr
        ⟨hj1d ▸ G.min'_le j hj, hj5d ▸ G.le_max' j hj⟩
      have hgap : j1 + 4 ≤ j5 := by
        have := card_le_card hsub; simp at this; omega
      have mem : ∀ {j}, j ∈ G → j < T - 1 ∧ low j ∧ incr a g j = v ∧ wEnd a g T j = e := by
        intro j hj
        simp only [G, JL, mem_filter, mem_range] at hj; tauto
      obtain ⟨hj1T, hj1low, hj1v, hj1e⟩ := mem hj1
      obtain ⟨hj5T, -, hj5v, hj5e⟩ := mem hj5
      -- nonincreasing on `[j1, j5]`
      have hchain : ∀ m, j1 ≤ m → m < j5 → incr a g (m + 1) ≤ incr a g m := by
        intro m h1 h2
        have hle5 : j5 ≤ wEnd a g T j5 := le_runEnd j5
        have : m < wEnd a g T j1 := by rw [hj1e]; rw [hj5e] at hle5; omega
        exact (incr_le_of_lt_wEnd h1 this).1
      have hconst : ∀ t, t < 5 → incr a g (j1 + t) = v := by
        intro t ht
        have := le_of_chain hchain (j1 + t) (by omega) (by omega)
        omega
      have hnl := W.not_low_of_five h6 (j := j1) (h := v) (by omega) hconst
      change 26244 * incr a g j1 ^ 3 * A ^ 4 < a ^ 3 at hj1low
      rw [hj1v] at hj1low
      exact absurd hnl (not_le.mpr hj1low)
    have hsq := sq_card_le_of_fiber (incr a g) (4 * M) JL
      (fun j hj => W.one_le_incr (by have := mem_range.mp (mem_filter.mp hj).1; omega)) hfib
    have hsumL : ∑ j ∈ JL, incr a g j ≤ a / A :=
      (sum_le_sum_of_subset (filter_subset _ _)).trans hsumall
    calc JL.card ^ 2 ≤ 2 * (4 * M) * ∑ j ∈ JL, incr a g j := hsq
      _ ≤ 2 * (4 * (windowRises a g T + 1)) * (a / A) := by gcongr
      _ = 8 * (windowRises a g T + 1) * (a / A) := by ring
  · -- high values: `s · k_min ≤ a/A` and `a³ ≤ 26244 k_min³ A⁴`
    rcases JH.eq_empty_or_nonempty with he | hne
    · rw [he]; simp
    obtain ⟨j0, hj0, hmin⟩ := JH.exists_min_image (incr a g) hne
    have h1 : JH.card * incr a g j0 ≤ a / A := by
      have := card_nsmul_le_sum JH (incr a g) (incr a g j0) hmin
      rw [smul_eq_mul] at this
      exact this.trans ((sum_le_sum_of_subset (filter_subset _ _)).trans hsumall)
    have h2 : a ^ 3 ≤ 26244 * incr a g j0 ^ 3 * A ^ 4 := by
      have := (mem_filter.mp hj0).2
      simp only [low, not_lt] at this
      exact this
    exact high_cube h1 h2 (Nat.mul_div_le a A) ha

end Window

end PierceLengthBound
