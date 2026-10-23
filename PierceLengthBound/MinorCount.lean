/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib

/-!
# Counting minor vectors of `3 × 5` integer matrices

The ten `3 × 3` minors `p` of an integer `3 × 5` matrix satisfy the Plücker relations. Fix a
pivot minor `m = p_τ` of maximal absolute value. The six minors with one pivot column replaced
form two vectors `u, v ∈ ℤ³` (Cramer's rule), and the remaining three minors are
`±(u × v)/m` (`plucker`). So `p` is determined by `(τ, m, u, v)`, where `|u|, |v| ≤ |m|` and
`m ∣ u × v`. For fixed `m` and `u` there are at most `27 m g²` such `v` in the box, where
`g = gcd(m, u)` (`card_cross_fiber`): `v` is a multiple of `u/g` modulo `m/g`. Summing,
`#{(u, v)} ≤ 729 m⁴ τ(m)` (`card_crossSet`), and there are at most
`1 + 20 ∑_{m ≤ Y} 729 m⁴ τ(m)` minor vectors of height `≤ Y` (`minor_vector_count`).
-/

@[expose] public section

namespace PierceLengthBound

open Finset

def trip : Fin 10 → Fin 5 × Fin 5 × Fin 5 := ![(0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 2, 3),
    (0, 2, 4), (0, 3, 4), (1, 2, 3), (1, 2, 4), (1, 3, 4), (2, 3, 4)]

def puX : Fin 10 → Fin 3 → Fin 10 := ![![6, 3, 1], ![6, 3, 0], ![7, 4, 0], ![6, 1, 0], ![7, 2, 0],
    ![8, 2, 1], ![3, 1, 0], ![4, 2, 0], ![5, 2, 1], ![5, 4, 3]]

def puS : Fin 10 → Fin 3 → ℤ := ![![1, -1, 1], ![-1, 1, 1], ![-1, 1, 1], ![1, 1, -1], ![1, 1, -1],
    ![1, 1, -1], ![1, -1, 1], ![1, -1, 1], ![1, -1, 1], ![1, -1, 1]]

def pvX : Fin 10 → Fin 3 → Fin 10 := ![![7, 4, 2], ![8, 5, 2], ![8, 5, 1], ![9, 5, 4], ![9, 5, 3],
    ![9, 4, 3], ![9, 8, 7], ![9, 8, 6], ![9, 7, 6], ![8, 7, 6]]

def pvS : Fin 10 → Fin 3 → ℤ := ![![1, -1, 1], ![1, -1, 1], ![-1, 1, 1], ![1, -1, 1], ![-1, 1, 1],
    ![1, 1, -1], ![1, -1, 1], ![-1, 1, 1], ![1, 1, -1], ![1, -1, 1]]

def pwX : Fin 10 → Fin 3 → Fin 10 := ![![5, 8, 9], ![4, 7, 9], ![3, 6, 9], ![2, 7, 8], ![1, 6, 8],
    ![0, 6, 7], ![2, 4, 5], ![1, 3, 5], ![0, 3, 4], ![0, 1, 2]]

def pwS : Fin 10 → Fin 3 → ℤ := ![![1, 1, 1], ![1, 1, -1], ![1, 1, 1], ![1, -1, -1], ![1, -1, 1],
    ![1, 1, 1], ![-1, -1, -1], ![-1, -1, 1], ![-1, 1, 1], ![1, 1, 1]]

/-- The `3 × 3` minor on columns `c₁, c₂, c₃`. -/
def minor3 (M : Fin 3 → Fin 5 → ℤ) (c1 c2 c3 : Fin 5) : ℤ :=
  M 0 c1 * (M 1 c2 * M 2 c3 - M 1 c3 * M 2 c2) - M 0 c2 * (M 1 c1 * M 2 c3 - M 1 c3 * M 2 c1) +
    M 0 c3 * (M 1 c1 * M 2 c2 - M 1 c2 * M 2 c1)

/-- The vector of the ten minors. -/
def plk (M : Fin 3 → Fin 5 → ℤ) (t : Fin 10) : ℤ := minor3 M (trip t).1 (trip t).2.1 (trip t).2.2

/-- The `u`-coordinates attached to a pivot. -/
def uVec (p : Fin 10 → ℤ) (t : Fin 10) (a : Fin 3) : ℤ := puS t a * p (puX t a)

/-- The `v`-coordinates attached to a pivot. -/
def vVec (p : Fin 10 → ℤ) (t : Fin 10) (a : Fin 3) : ℤ := pvS t a * p (pvX t a)

/-- The cross product. -/
def cross3 (u v : Fin 3 → ℤ) (a : Fin 3) : ℤ := u (a + 1) * v (a + 2) - u (a + 2) * v (a + 1)

/-- The Plücker relations: `p_τ · p_{w_a} = ± (u × v)_a`. -/
def PluckerRel (p : Fin 10 → ℤ) : Prop :=
  ∀ t a, p t * p (pwX t a) = pwS t a * cross3 (uVec p t) (vVec p t) a

theorem plucker (M : Fin 3 → Fin 5 → ℤ) : PluckerRel (plk M) := by
  intro t a
  fin_cases t <;> fin_cases a <;>
    simp [plk, trip, minor3, uVec, vVec, cross3, puX, puS, pvX, pvS, pwX, pwS] <;> ring

/-- Every index is the pivot or one of its nine companions. -/
lemma cover (t s : Fin 10) : s = t ∨ (∃ a, s = puX t a) ∨ (∃ a, s = pvX t a) ∨
    ∃ a, s = pwX t a := by
  fin_cases t <;> fin_cases s <;> decide

lemma sign_sq (t : Fin 10) (a : Fin 3) : puS t a * puS t a = 1 ∧ pvS t a * pvS t a = 1 ∧
    pwS t a * pwS t a = 1 := by
  fin_cases t <;> fin_cases a <;> decide

/-! ### The congruence count -/

/-- Integers in `[-m, m]` in a fixed class modulo `n` number at most `2m/n + 1`. -/
lemma card_Icc_dvd_le {m n : ℕ} (hn : 0 < n) (c : ℤ) :
    ((Icc (-(m : ℤ)) m).filter fun x => (n : ℤ) ∣ x - c).card ≤ 2 * m / n + 1 := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  refine (card_le_card_of_injOn (fun x : ℤ => ((x + (m : ℤ)) / (n : ℤ)).toNat)
    (t := range (2 * m / n + 1))
    (fun x hx => ?_) (fun x hx x' hx' h => ?_)).trans (by simp)
  · obtain ⟨hx1, -⟩ := mem_filter.mp (mem_coe.mp hx)
    obtain ⟨hl, hu⟩ := mem_Icc.mp hx1
    refine mem_range.mpr (Nat.lt_succ_of_le ?_)
    change ((x + (m : ℤ)) / (n : ℤ)).toNat ≤ 2 * m / n
    have h1 : (x + m) / n ≤ (((2 * m : ℕ) : ℤ)) / n := Int.ediv_le_ediv hn' (by push_cast; linarith)
    have h2 : ((2 * m / n : ℕ) : ℤ) = ((2 * m : ℕ) : ℤ) / n := Int.natCast_div _ _
    have h3 : 0 ≤ (x + m) / n := Int.ediv_nonneg (by linarith) hn'.le
    omega
  · obtain ⟨hx1, hxc⟩ := mem_filter.mp (mem_coe.mp hx)
    obtain ⟨hx1', hxc'⟩ := mem_filter.mp (mem_coe.mp hx')
    obtain ⟨hl, -⟩ := mem_Icc.mp hx1
    obtain ⟨hl', -⟩ := mem_Icc.mp hx1'
    have h3 : 0 ≤ (x + m) / n := Int.ediv_nonneg (by linarith) hn'.le
    have h3' : 0 ≤ (x' + m) / n := Int.ediv_nonneg (by linarith) hn'.le
    have hq : (x + m) / n = (x' + m) / n := by
      have := congrArg (fun k : ℕ => (k : ℤ)) h
      simp only [Int.toNat_of_nonneg h3, Int.toNat_of_nonneg h3'] at this
      exact this
    have hr : (x + m) % n = (x' + m) % n := by
      have : (n : ℤ) ∣ (x + m) - (x' + m) := by
        have := dvd_sub hxc hxc'; rwa [show x - c - (x' - c) = x + m - (x' + m) by ring] at this
      exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd this)
    have e1 := Int.mul_ediv_add_emod (x + m) n
    have e2 := Int.mul_ediv_add_emod (x' + m) n
    rw [hq, hr] at e1
    linarith

/-- The box `[-m, m]³`. -/
def ibox3 (m : ℕ) : Finset (Fin 3 → ℤ) := Fintype.piFinset fun _ => Icc (-(m : ℤ)) m

/-- `gcd(m, u₀, u₁, u₂)`. -/
def gcd4 (m : ℕ) (u : Fin 3 → ℤ) : ℕ := Int.gcd m (Int.gcd (u 0) (Int.gcd (u 1) (u 2)))

lemma cross3_zero (u v : Fin 3 → ℤ) : cross3 u v 0 = u 1 * v 2 - u 2 * v 1 := rfl
lemma cross3_one (u v : Fin 3 → ℤ) : cross3 u v 1 = u 2 * v 0 - u 0 * v 2 := rfl
lemma cross3_two (u v : Fin 3 → ℤ) : cross3 u v 2 = u 0 * v 1 - u 1 * v 0 := rfl

lemma gcd4_dvd (m : ℕ) (u : Fin 3 → ℤ) (a : Fin 3) : (gcd4 m u : ℤ) ∣ u a := by
  have h1 : (gcd4 m u : ℤ) ∣ (Int.gcd (u 0) (Int.gcd (u 1) (u 2)) : ℤ) := Int.gcd_dvd_right _ _
  have h2 : ((Int.gcd (u 0) (Int.gcd (u 1) (u 2)) : ℕ) : ℤ) ∣ u 0 := Int.gcd_dvd_left _ _
  have h3 : ((Int.gcd (u 0) (Int.gcd (u 1) (u 2)) : ℕ) : ℤ) ∣ (Int.gcd (u 1) (u 2) : ℤ) :=
    Int.gcd_dvd_right _ _
  have h4 : ((Int.gcd (u 1) (u 2) : ℕ) : ℤ) ∣ u 1 := Int.gcd_dvd_left _ _
  have h5 : ((Int.gcd (u 1) (u 2) : ℕ) : ℤ) ∣ u 2 := Int.gcd_dvd_right _ _
  match a with
  | 0 => exact h1.trans h2
  | 1 => exact h1.trans (h3.trans h4)
  | 2 => exact h1.trans (h3.trans h5)

lemma gcd4_dvd_m (m : ℕ) (u : Fin 3 → ℤ) : gcd4 m u ∣ m := by
  have : (gcd4 m u : ℤ) ∣ (m : ℤ) := Int.gcd_dvd_left _ _
  exact_mod_cast this

/-- Bézout for `gcd(m, u₀, u₁, u₂)`. -/
lemma gcd4_bezout (m : ℕ) (u : Fin 3 → ℤ) :
    ∃ x c0 c1 c2 : ℤ, (m : ℤ) * x + u 0 * c0 + u 1 * c1 + u 2 * c2 = gcd4 m u := by
  have e1 := Int.gcd_eq_gcd_ab (m : ℤ) (Int.gcd (u 0) (Int.gcd (u 1) (u 2)))
  have e2 := Int.gcd_eq_gcd_ab (u 0) (Int.gcd (u 1) (u 2))
  have e3 := Int.gcd_eq_gcd_ab (u 1) (u 2)
  set y := Int.gcdB (m : ℤ) (Int.gcd (u 0) (Int.gcd (u 1) (u 2)))
  set y0 := Int.gcdB (u 0) (Int.gcd (u 1) (u 2))
  refine ⟨Int.gcdA (m : ℤ) (Int.gcd (u 0) (Int.gcd (u 1) (u 2))), y * Int.gcdA (u 0)
    (Int.gcd (u 1) (u 2)), y * y0 * Int.gcdA (u 1) (u 2), y * y0 * Int.gcdB (u 1) (u 2), ?_⟩
  simp only [gcd4]
  rw [e1]
  have e2' : ((Int.gcd (u 0) (Int.gcd (u 1) (u 2)) : ℕ) : ℤ) = u 0 * Int.gcdA (u 0)
      (Int.gcd (u 1) (u 2)) + (Int.gcd (u 1) (u 2) : ℤ) * y0 := e2
  rw [e2', e3]
  ring

lemma gcd4_pos {m : ℕ} (hm : 0 < m) (u : Fin 3 → ℤ) : 0 < gcd4 m u :=
  Int.gcd_pos_of_ne_zero_left _ (by exact_mod_cast hm.ne')

/-- **The cross congruence**: `m ∣ u × v` forces `v ≡ λ u' (mod m/g)`. -/
lemma cross_cong {m : ℕ} (hm : 0 < m) {u v : Fin 3 → ℤ} (hd : ∀ a, (m : ℤ) ∣ cross3 u v a) :
    ∃ n : ℤ, ∃ u' : Fin 3 → ℤ, ∃ lam : ℤ, 0 < n ∧ (m : ℤ) = gcd4 m u * n ∧
      (∀ a, u a = gcd4 m u * u' a) ∧ ∀ a, n ∣ v a - lam * u' a := by
  set g := gcd4 m u
  have hg0 : 0 < g := gcd4_pos hm u
  obtain ⟨x, c0, c1, c2, hb⟩ := gcd4_bezout m u
  obtain ⟨n, hn⟩ : (g : ℤ) ∣ m := Int.gcd_dvd_left _ _
  obtain ⟨w0, hw0⟩ := gcd4_dvd m u 0
  obtain ⟨w1, hw1⟩ := gcd4_dvd m u 1
  obtain ⟨w2, hw2⟩ := gcd4_dvd m u 2
  set u' : Fin 3 → ℤ := ![w0, w1, w2]
  have hu' : ∀ a, u a = g * u' a := by
    intro a; fin_cases a <;> simp [u', hw0, hw1, hw2, g]
  have hg0' : (g : ℤ) ≠ 0 := by exact_mod_cast hg0.ne'
  have hn1 : n * x + w0 * c0 + w1 * c1 + w2 * c2 = 1 := by
    apply mul_left_cancel₀ hg0'
    rw [hn, hw0, hw1, hw2] at hb
    linear_combination hb
  have hnpos : 0 < n := by
    have : (0 : ℤ) < m := by exact_mod_cast hm
    rw [hn] at this
    exact pos_of_mul_pos_right this (by positivity)
  refine ⟨n, u', c0 * v 0 + c1 * v 1 + c2 * v 2, hnpos, hn, hu', ?_⟩
  have hd' : ∀ a, n ∣ cross3 u' v a := by
    intro a
    have h := hd a
    have e : cross3 u v a = g * cross3 u' v a := by
      simp only [cross3, hu']; ring
    rw [e, hn] at h
    exact (mul_dvd_mul_iff_left hg0').mp h
  obtain ⟨z0, hz0⟩ := hd' 0
  obtain ⟨z1, hz1⟩ := hd' 1
  obtain ⟨z2, hz2⟩ := hd' 2
  rw [cross3_zero] at hz0
  rw [cross3_one] at hz1
  rw [cross3_two] at hz2
  simp only [u', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hz0 hz1 hz2
  intro a
  match a with
  | 0 => exact ⟨v 0 * x - c1 * z2 + c2 * z1, by
      simp [u']
      linear_combination -v 0 * hn1 - c1 * hz2 + c2 * hz1⟩
  | 1 => exact ⟨v 1 * x + c0 * z2 - c2 * z0, by
      simp [u']
      linear_combination -v 1 * hn1 + c0 * hz2 - c2 * hz0⟩
  | 2 => exact ⟨v 2 * x - c0 * z1 + c1 * z0, by
      simp [u']
      linear_combination -v 2 * hn1 - c0 * hz1 + c1 * hz0⟩

/-- **For fixed `u`, at most `27 m g²` vectors `v` have `m ∣ u × v`.** -/
theorem card_cross_fiber {m : ℕ} (hm : 0 < m) (u : Fin 3 → ℤ) :
    ((ibox3 m).filter fun v => ∀ a, (m : ℤ) ∣ cross3 u v a).card ≤ 27 * m * gcd4 m u ^ 2 := by
  obtain ⟨nn, hmg⟩ := gcd4_dvd_m m u
  set g := gcd4 m u
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast (gcd4_pos hm u).ne'
  have hnn0 : 0 < nn := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hnn : (0 : ℤ) < nn := by exact_mod_cast hnn0
  -- the congruence `v ≡ λ_v u' (mod m/g)`, with `u = g u'`
  have hcong : ∀ v ∈ (ibox3 m).filter (fun v => ∀ a, (m : ℤ) ∣ cross3 u v a),
      ∃ lam : ℤ, ∀ a, (nn : ℤ) ∣ v a - lam * (u a / g) := by
    intro v hv
    obtain ⟨n, u', lam, -, hn, hu, hv⟩ := cross_cong hm (mem_filter.mp hv).2
    have hn' : n = nn := mul_left_cancel₀ hg0 (hn.symm.trans (by exact_mod_cast hmg))
    refine ⟨lam, fun a => ?_⟩
    rw [hu a, Int.mul_ediv_cancel_left _ hg0, ← hn']
    exact hv a
  choose! lam hlam using hcong
  -- count by the residue of `λ`
  refine (card_le_mul_card_image_of_maps_to (f := fun v => (lam v % nn).toNat) (t := range nn)
    (fun v _ => mem_range.mpr (by
      have := Int.emod_nonneg (lam v) hnn.ne'
      have := Int.emod_lt_of_pos (lam v) hnn
      omega)) (27 * g ^ 3) fun l _ => ?_).trans ?_
  · -- a fixed residue `l`
    have hsub : ((ibox3 m).filter (fun v => ∀ a, (m : ℤ) ∣ cross3 u v a)).filter
        (fun v => (lam v % nn).toNat = l) ⊆ Fintype.piFinset fun a =>
          (Icc (-(m : ℤ)) m).filter fun y => (nn : ℤ) ∣ y - l * (u a / g) := by
      intro v hv
      obtain ⟨hv1, hvl⟩ := mem_filter.mp hv
      have hvb := (mem_filter.mp hv1).1
      refine Fintype.mem_piFinset.mpr fun a => mem_filter.mpr ⟨Fintype.mem_piFinset.mp hvb a, ?_⟩
      have h2 : (nn : ℤ) ∣ lam v - l := by
        have e : ((l : ℕ) : ℤ) = lam v % nn := by
          rw [← hvl, Int.toNat_of_nonneg (Int.emod_nonneg _ hnn.ne')]
        rw [e]; exact Int.dvd_self_sub_emod ..
      have := dvd_add (hlam v hv1 a) (dvd_mul_of_dvd_left h2 (u a / g))
      rwa [show v a - lam v * (u a / g) + (lam v - l) * (u a / g) = v a - l * (u a / g) by ring]
        at this
    refine (card_le_card hsub).trans ?_
    rw [Fintype.card_piFinset, Fin.prod_univ_three]
    have hb : ∀ c : ℤ, ((Icc (-(m : ℤ)) m).filter fun y => (nn : ℤ) ∣ y - c).card ≤ 3 * g := by
      intro c
      refine (card_Icc_dvd_le hnn0 c).trans ?_
      rw [hmg, show 2 * (g * nn) / nn = 2 * g by
        rw [show 2 * (g * nn) = 2 * g * nn by ring, Nat.mul_div_cancel _ hnn0]]
      omega
    calc _ ≤ (3 * g) * (3 * g) * (3 * g) := Nat.mul_le_mul (Nat.mul_le_mul (hb _) (hb _)) (hb _)
      _ = 27 * g ^ 3 := by ring
  · rw [card_range, hmg]; ring_nf; exact le_rfl

/-- `∑_{u ∈ [-m,m]³} gcd(m, u)² ≤ 27 m³ τ(m)`. -/
lemma sum_gcd4_sq_le {m : ℕ} (hm : 0 < m) :
    ∑ u ∈ ibox3 m, gcd4 m u ^ 2 ≤ 27 * m ^ 3 * m.divisors.card := by
  rw [← sum_fiberwise_of_maps_to (g := fun u => gcd4 m u) (t := m.divisors)
    (fun u _ => Nat.mem_divisors.mpr ⟨gcd4_dvd_m m u, hm.ne'⟩)]
  calc ∑ d ∈ m.divisors, ∑ u ∈ (ibox3 m).filter (fun u => gcd4 m u = d), gcd4 m u ^ 2
      ≤ ∑ _d ∈ m.divisors, 27 * m ^ 3 := by
        refine sum_le_sum fun d hd => ?_
        obtain ⟨hdm, -⟩ := Nat.mem_divisors.mp hd
        have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdm hm
        obtain ⟨e, he⟩ := hdm
        have he0 : 0 < e := by
          rcases Nat.eq_zero_or_pos e with h | h
          · rw [h, mul_zero] at he; omega
          · exact h
        have hsub : (ibox3 m).filter (fun u => gcd4 m u = d) ⊆
            Fintype.piFinset fun _ => (Icc (-(m : ℤ)) m).filter fun y => (d : ℤ) ∣ y - 0 := by
          intro u hu
          obtain ⟨hub, hud⟩ := mem_filter.mp hu
          refine Fintype.mem_piFinset.mpr fun a => mem_filter.mpr
            ⟨Fintype.mem_piFinset.mp hub a, ?_⟩
          rw [sub_zero, ← hud]; exact gcd4_dvd m u a
        have hb : ((Icc (-(m : ℤ)) m).filter fun y => (d : ℤ) ∣ y - 0).card ≤ 3 * e := by
          refine (card_Icc_dvd_le hd0 0).trans ?_
          rw [he, show 2 * (d * e) / d = 2 * e by
            rw [show 2 * (d * e) = 2 * e * d by ring, Nat.mul_div_cancel _ hd0]]
          omega
        calc ∑ u ∈ (ibox3 m).filter (fun u => gcd4 m u = d), gcd4 m u ^ 2
            = ∑ u ∈ (ibox3 m).filter (fun u => gcd4 m u = d), d ^ 2 :=
              sum_congr rfl fun u hu => by rw [(mem_filter.mp hu).2]
          _ = ((ibox3 m).filter (fun u => gcd4 m u = d)).card * d ^ 2 := by
              rw [sum_const, smul_eq_mul]
          _ ≤ (3 * e) ^ 3 * d ^ 2 := by
              refine Nat.mul_le_mul_right _ ((card_le_card hsub).trans ?_)
              rw [Fintype.card_piFinset, Fin.prod_univ_three]
              calc _ ≤ (3 * e) * (3 * e) * (3 * e) := Nat.mul_le_mul (Nat.mul_le_mul hb hb) hb
                _ = (3 * e) ^ 3 := by ring
          _ ≤ 27 * m ^ 3 := by
              rw [he]
              have : e ^ 3 * d ^ 2 ≤ e ^ 3 * d ^ 3 := Nat.mul_le_mul_left _
                (Nat.pow_le_pow_right hd0 (by norm_num))
              nlinarith
    _ = 27 * m ^ 3 * m.divisors.card := by rw [sum_const, smul_eq_mul]; ring

/-- The admissible `(u, v)` for a pivot of size `m`. -/
def crossSet (m : ℕ) : Finset ((Fin 3 → ℤ) × (Fin 3 → ℤ)) :=
  (ibox3 m ×ˢ ibox3 m).filter fun uv => ∀ a, (m : ℤ) ∣ cross3 uv.1 uv.2 a

/-- **`#{(u, v)} ≤ 729 m⁴ τ(m)`.** -/
theorem card_crossSet {m : ℕ} (hm : 0 < m) :
    (crossSet m).card ≤ 729 * m ^ 4 * m.divisors.card := by
  rw [card_eq_sum_card_fiberwise (s := crossSet m) (f := Prod.fst) (t := ibox3 m)
    (fun uv huv => (mem_product.mp (mem_filter.mp huv).1).1)]
  calc ∑ u ∈ ibox3 m, ((crossSet m).filter fun uv => uv.1 = u).card
      ≤ ∑ u ∈ ibox3 m, 27 * m * gcd4 m u ^ 2 := by
        refine sum_le_sum fun u _ => le_trans (card_le_card_of_injOn Prod.snd
          (t := (ibox3 m).filter fun v => ∀ a, (m : ℤ) ∣ cross3 u v a) (fun uv huv => ?_)
          (fun uv huv uv' huv' h => ?_)) (card_cross_fiber hm u)
        · obtain ⟨h1, h2⟩ := mem_filter.mp (mem_coe.mp huv)
          obtain ⟨h3, h4⟩ := mem_filter.mp h1
          rw [← h2]
          exact mem_filter.mpr ⟨(mem_product.mp h3).2, h4⟩
        · have e1 := (mem_filter.mp (mem_coe.mp huv)).2
          have e2 := (mem_filter.mp (mem_coe.mp huv')).2
          exact Prod.ext (e1.trans e2.symm) h
    _ = 27 * m * ∑ u ∈ ibox3 m, gcd4 m u ^ 2 := by rw [mul_sum]
    _ ≤ 27 * m * (27 * m ^ 3 * m.divisors.card) := Nat.mul_le_mul_left _ (sum_gcd4_sq_le hm)
    _ = 729 * m ^ 4 * m.divisors.card := by ring

/-- A pivot: an index of maximal absolute value. -/
noncomputable def piv (p : Fin 10 → ℤ) : Fin 10 :=
  Classical.choose (exists_max_image univ (fun t => |p t|) univ_nonempty)

lemma piv_max (p : Fin 10 → ℤ) (t : Fin 10) : |p t| ≤ |p (piv p)| :=
  (Classical.choose_spec (exists_max_image univ (fun t => |p t|) univ_nonempty)).2 t (mem_univ t)

/-- The pivot entry is nonzero as soon as some entry is. -/
lemma piv_ne_zero {p : Fin 10 → ℤ} {t : Fin 10} (h0 : p t ≠ 0) : p (piv p) ≠ 0 := by
  intro hz
  have := piv_max p t
  rw [hz, abs_zero] at this
  exact h0 (abs_eq_zero.mp (le_antisymm this (abs_nonneg _)))

/-- The pivot entry of a nonzero vector is nonzero. -/
lemma piv_ne_zero_of_ne_zero {p : Fin 10 → ℤ} (hp : p ≠ 0) : p (piv p) ≠ 0 :=
  piv_ne_zero (Function.ne_iff.mp hp).choose_spec

/-- Discarding the zero vector loses at most one element. -/
lemma card_le_one_add_card_filter_ne_zero (S : Finset (Fin 10 → ℤ)) :
    S.card ≤ 1 + (S.filter fun p => p ≠ 0).card := by
  rw [filter_ne']
  have := pred_card_le_card_erase (s := S) (a := 0)
  omega

/-- The pivot divides the cross product. -/
lemma piv_cross {p : Fin 10 → ℤ} (hpl : PluckerRel p) (a : Fin 3) :
    p (piv p) ∣ cross3 (uVec p (piv p)) (vVec p (piv p)) a := by
  set τ := piv p
  refine ⟨pwS τ a * p (pwX τ a), ?_⟩
  have h1 := hpl τ a
  have h2 := (sign_sq τ a).2.2
  linear_combination (-pwS τ a) * h1 - cross3 (uVec p τ) (vVec p τ) a * h2

/-- **The minor-vector count, refined.** Vectors of height `≤ Y` satisfying the Plücker relations,
with nonzero pivot `m` and `P |m| u` for the first row `u` of the pivot, number at most
`20 ∑_{m ≤ Y} #{(u, v) ∈ crossSet m : P m u}`. -/
theorem minor_vector_count_of (P : ℕ → (Fin 3 → ℤ) → Prop) [∀ m u, Decidable (P m u)]
    {S : Finset (Fin 10 → ℤ)} {Y : ℕ}
    (hS : ∀ p ∈ S, (∀ t, |p t| ≤ Y) ∧ PluckerRel p ∧ p (piv p) ≠ 0 ∧
      P (p (piv p)).natAbs (uVec p (piv p))) :
    S.card ≤ 20 * ∑ m ∈ Icc 1 Y, ((crossSet m).filter fun uv => P m uv.1).card := by
  classical
  set key : (Fin 10 → ℤ) → Fin 10 × Bool × ℕ × (Fin 3 → ℤ) × (Fin 3 → ℤ) := fun p =>
    (piv p, decide (0 < p (piv p)), (p (piv p)).natAbs, uVec p (piv p), vVec p (piv p))
  set Bm : Finset (ℕ × (Fin 3 → ℤ) × (Fin 3 → ℤ)) :=
    (Icc 1 Y).biUnion fun m => ((crossSet m).filter fun uv => P m uv.1).image
      fun uv => (m, uv.1, uv.2)
  set KS : Finset (Fin 10 × Bool × ℕ × (Fin 3 → ℤ) × (Fin 3 → ℤ)) := univ ×ˢ univ ×ˢ Bm
  have hKS : KS.card ≤ 20 * ∑ m ∈ Icc 1 Y, ((crossSet m).filter fun uv => P m uv.1).card := by
    have h1 : Bm.card ≤ ∑ m ∈ Icc 1 Y, ((crossSet m).filter fun uv => P m uv.1).card :=
      card_biUnion_le.trans (sum_le_sum fun m _ => card_image_le)
    have e : KS.card = 10 * (2 * Bm.card) := by
      simp only [KS, card_product, card_univ, Fintype.card_fin, Fintype.card_bool]
    rw [e]; omega
  have hmaps : ∀ p ∈ S, key p ∈ KS := by
    intro p hp
    obtain ⟨hb, hpl, hm, hP⟩ := hS p hp
    set τ := piv p
    set m := p τ
    have hmY : m.natAbs ≤ Y := by
      have h1 : ((m.natAbs : ℕ) : ℤ) ≤ Y := by rw [Int.natCast_natAbs]; exact hb τ
      exact_mod_cast h1
    have hm1 : 1 ≤ m.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hm)
    refine mem_product.mpr ⟨mem_univ _, mem_product.mpr ⟨mem_univ _, mem_biUnion.mpr
      ⟨m.natAbs, mem_Icc.mpr ⟨hm1, hmY⟩, mem_image.mpr ⟨(uVec p τ, vVec p τ), ?_, rfl⟩⟩⟩⟩
    have hcast : ((m.natAbs : ℕ) : ℤ) = |m| := Int.natCast_natAbs m
    have hu : ∀ a, |uVec p τ a| ≤ |m| := fun a => by
      have hs := (sign_sq τ a).1
      have : |puS τ a| = 1 := by
        rcases Int.eq_one_or_neg_one_of_mul_eq_one hs with h | h <;> simp [h]
      simp only [uVec, abs_mul, this, one_mul]; exact piv_max p _
    have hv : ∀ a, |vVec p τ a| ≤ |m| := fun a => by
      have hs := (sign_sq τ a).2.1
      have : |pvS τ a| = 1 := by
        rcases Int.eq_one_or_neg_one_of_mul_eq_one hs with h | h <;> simp [h]
      simp only [vVec, abs_mul, this, one_mul]; exact piv_max p _
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun a =>
      mem_Icc.mpr (by rw [hcast]; exact abs_le.mp (hu a)), Fintype.mem_piFinset.mpr fun a =>
      mem_Icc.mpr (by rw [hcast]; exact abs_le.mp (hv a))⟩, fun a => ?_⟩, hP⟩
    rw [Int.natCast_natAbs]
    exact (abs_dvd m _).mpr (piv_cross hpl a)
  have hinj : Set.InjOn key S := by
    intro p hp p' hp' h
    simp only [key, Prod.mk.injEq] at h
    obtain ⟨hτ, hsg, hab, hu, hv⟩ := h
    have hp1 := mem_coe.mp hp
    have hp1' := mem_coe.mp hp'
    have hm := (hS p hp1).2.2.1
    have hm' := (hS p' hp1').2.2.1
    rw [← hτ] at hsg hab hu hv hm'
    set τ := piv p
    have hmm : p τ = p' τ := by
      by_cases hpos : 0 < p τ
      · have : 0 < p' τ := by simpa [hpos] using hsg
        omega
      · have : ¬ 0 < p' τ := by simpa [hpos] using hsg
        omega
    have hpl := (hS p hp1).2.1
    have hpl' := (hS p' hp1').2.1
    funext s
    rcases cover τ s with h | ⟨a, h⟩ | ⟨a, h⟩ | ⟨a, h⟩
    · rw [h, hmm]
    · have e := congrFun hu a
      simp only [uVec] at e
      have hs := (sign_sq τ a).1
      rw [h]
      linear_combination puS τ a * e + (p' (puX τ a) - p (puX τ a)) * hs
    · have e := congrFun hv a
      simp only [vVec] at e
      have hs := (sign_sq τ a).2.1
      rw [h]
      linear_combination pvS τ a * e + (p' (pvX τ a) - p (pvX τ a)) * hs
    · have e1 := hpl τ a
      have e2 := hpl' τ a
      rw [← hmm, ← hu, ← hv] at e2
      rw [h]
      exact mul_left_cancel₀ hm (e1.trans e2.symm)
  exact (card_le_card_of_injOn key hmaps hinj).trans hKS

/-- **The minor-vector lemma.** Vectors of height `≤ Y` satisfying the Plücker relations number
at most `1 + 20 ∑_{m ≤ Y} 729 m⁴ τ(m)`. -/
theorem minor_vector_count {S : Finset (Fin 10 → ℤ)} {Y : ℕ}
    (hS : ∀ p ∈ S, (∀ t, |p t| ≤ Y) ∧ PluckerRel p) :
    S.card ≤ 1 + 20 * ∑ m ∈ Icc 1 Y, 729 * m ^ 4 * m.divisors.card := by
  refine (card_le_one_add_card_filter_ne_zero S).trans (Nat.add_le_add_left
    ((minor_vector_count_of (fun _ _ => True) fun p hp => ⟨(hS p (mem_filter.mp hp).1).1,
      (hS p (mem_filter.mp hp).1).2, piv_ne_zero_of_ne_zero (mem_filter.mp hp).2, trivial⟩).trans
    ?_) 1)
  exact Nat.mul_le_mul_left _ (sum_le_sum fun m hm => (card_filter_le _ _).trans
    (card_crossSet (by have := (mem_Icc.mp hm).1; omega)))

end PierceLengthBound
