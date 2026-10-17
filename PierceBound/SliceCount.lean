/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
import PierceBound.NormCount
import PierceBound.DefiniteNorm
import PierceBound.TwoState

/-!
# Counting a ternary quadratic by binary slices

Let `F(x,y,z) = αx² + βxy + γy² + d(z)x + e(z)y + f(z)` with `d(z) = d₁z + d₀`,
`e(z) = e₁z + e₀`, `f(z) = f₂z² + f₁z + f₀`, `α > 0` and `Δ = β² - 4αγ ≠ 0`. Put
`U = 2αx + βy + d(z)`, `Λ(z) = βd(z) - 2αe(z)`, `V = Δy + Λ(z)` and
`N(z) = Λ(z)² + Δ(4αf(z) - d(z)²)`. Then `V² - ΔU² = N(z) - 4αΔF` (`slice_identity`).

So a zero of `F` in a slice with `N(z) ≠ 0` is a solution of a norm equation, counted by
`norm_count` if `Δ > 0` and by `norm_count_def` if `Δ < 0`. If the `z²` coefficient of `N` is
nonzero, at most two slices have `N(z) = 0`, and in those `V² = ΔU²` leaves at most two `x` for
each `y`. Hence (`slice_count_ne`, and `slice_count` for `Δ > 0`) `#{F = 0} ≤ (2H+1)(W + 4)` in
the box `[-H, H]³`, where `W` bounds the norm counts.
-/

namespace PierceBound

open Finset

/-- The ternary quadratic. -/
def tern (α β γ d1 d0 e1 e0 f2 f1 f0 x y z : ℤ) : ℤ :=
  α * x ^ 2 + β * x * y + γ * y ^ 2 + (d1 * z + d0) * x + (e1 * z + e0) * y +
    (f2 * z ^ 2 + f1 * z + f0)

/-- The right side `N(z)` of the norm equation. -/
def ternN (α β γ d1 d0 e1 e0 f2 f1 f0 z : ℤ) : ℤ :=
  (β * (d1 * z + d0) - 2 * α * (e1 * z + e0)) ^ 2 +
    (β ^ 2 - 4 * α * γ) * (4 * α * (f2 * z ^ 2 + f1 * z + f0) - (d1 * z + d0) ^ 2)

lemma slice_identity (α β γ d1 d0 e1 e0 f2 f1 f0 x y z : ℤ) :
    ((β ^ 2 - 4 * α * γ) * y + (β * (d1 * z + d0) - 2 * α * (e1 * z + e0))) ^ 2 -
      (β ^ 2 - 4 * α * γ) * (2 * α * x + β * y + (d1 * z + d0)) ^ 2 =
    ternN α β γ d1 d0 e1 e0 f2 f1 f0 z -
      4 * α * (β ^ 2 - 4 * α * γ) * tern α β γ d1 d0 e1 e0 f2 f1 f0 x y z := by
  unfold ternN tern; ring

lemma ternN_eq (α β γ d1 d0 e1 e0 f2 f1 f0 z : ℤ) :
    ternN α β γ d1 d0 e1 e0 f2 f1 f0 z =
      ((β * d1 - 2 * α * e1) ^ 2 + (β ^ 2 - 4 * α * γ) * (4 * α * f2 - d1 ^ 2)) * z ^ 2 +
      (2 * (β * d1 - 2 * α * e1) * (β * d0 - 2 * α * e0) +
        (β ^ 2 - 4 * α * γ) * (4 * α * f1 - 2 * d1 * d0)) * z +
      ((β * d0 - 2 * α * e0) ^ 2 + (β ^ 2 - 4 * α * γ) * (4 * α * f0 - d0 ^ 2)) := by
  unfold ternN; ring

/-- The integer box `[-H, H]`. -/
def ibox (H : ℕ) : Finset ℤ := Icc (-(H : ℤ)) H

lemma card_ibox (H : ℕ) : (ibox H).card = 2 * H + 1 := by
  simp [ibox, Int.card_Icc]; omega

lemma abs_le_of_mem_ibox {H : ℕ} {x : ℤ} (h : x ∈ ibox H) : |x| ≤ H := abs_le.mpr (mem_Icc.mp h)

/-- `|β² - 4αγ| ≤ 5K²`. -/
lemma disc_bound {α β γ : ℤ} {K : ℕ} (kα : |α| ≤ K) (kβ : |β| ≤ K) (kγ : |γ| ≤ K) :
    |β ^ 2 - 4 * α * γ| ≤ 5 * (K : ℤ) ^ 2 := by
  have h1 : |β * β| ≤ K * K := by
    rw [abs_mul]; exact mul_le_mul kβ kβ (abs_nonneg _) (by linarith [abs_nonneg β])
  have h2 : |α * γ| ≤ K * K := by
    rw [abs_mul]; exact mul_le_mul kα kγ (abs_nonneg _) (by linarith [abs_nonneg α])
  calc |β ^ 2 - 4 * α * γ| = |β * β - 4 * (α * γ)| := by ring_nf
    _ ≤ |β * β| + |4 * (α * γ)| := abs_sub _ _
    _ = |β * β| + 4 * |α * γ| := by rw [abs_mul (4 : ℤ)]; norm_num
    _ ≤ K * K + 4 * (K * K) := by linarith
    _ = 5 * K ^ 2 := by ring

/-- The norm-equation variables are `O(K²H)` on the box. -/
lemma slice_bnd {α β γ d1 d0 e1 e0 : ℤ} {K H : ℕ} (hH : 1 ≤ H) (hK1 : (1 : ℤ) ≤ K) (kα : |α| ≤ K)
    (kβ : |β| ≤ K)
    (kγ : |γ| ≤ K) (kd1 : |d1| ≤ K) (kd0 : |d0| ≤ K) (ke1 : |e1| ≤ K) (ke0 : |e0| ≤ K)
    {x y z : ℤ} (hx : x ∈ ibox H) (hy : y ∈ ibox H) (hz : z ∈ ibox H) :
    |2 * α * x + β * y + (d1 * z + d0)| ≤ ((11 * K ^ 2 * H : ℕ) : ℤ) ∧
      |(β ^ 2 - 4 * α * γ) * y + (β * (d1 * z + d0) - 2 * α * (e1 * z + e0))| ≤
        ((11 * K ^ 2 * H : ℕ) : ℤ) := by
  set Δ := β ^ 2 - 4 * α * γ
  have ax := abs_le_of_mem_ibox hx
  have ay := abs_le_of_mem_ibox hy
  have az := abs_le_of_mem_ibox hz
  have hH1 : (1 : ℤ) ≤ H := by exact_mod_cast hH
  have hKH : (K : ℤ) ≤ K * H := by nlinarith
  have m2 : ∀ a b : ℤ, ∀ A Bb : ℤ, |a| ≤ A → |b| ≤ Bb → |a * b| ≤ A * Bb := fun a b A Bb ha hb => by
    rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
  have hd : |d1 * z + d0| ≤ 2 * K * H := by
    have := m2 _ _ _ _ kd1 az
    calc |d1 * z + d0| ≤ |d1 * z| + |d0| := abs_add_le _ _
      _ ≤ K * H + K := add_le_add this kd0
      _ ≤ 2 * K * H := by linarith
  have he : |e1 * z + e0| ≤ 2 * K * H := by
    have := m2 _ _ _ _ ke1 az
    calc |e1 * z + e0| ≤ |e1 * z| + |e0| := abs_add_le _ _
      _ ≤ K * H + K := add_le_add this ke0
      _ ≤ 2 * K * H := by linarith
  have hDl : |Δ| ≤ 5 * K ^ 2 := disc_bound kα kβ kγ
  push_cast
  constructor
  · have t1 := m2 _ _ _ _ (show |2 * α| ≤ 2 * K by rw [abs_mul]; norm_num; linarith) ax
    have t2 := m2 _ _ _ _ kβ ay
    calc |2 * α * x + β * y + (d1 * z + d0)| ≤ |2 * α * x| + |β * y| + |d1 * z + d0| :=
          abs_add_three _ _ _
      _ ≤ 2 * K * H + K * H + 2 * K * H := by linarith
      _ ≤ 11 * K ^ 2 * H := by nlinarith
  · have t1 := m2 _ _ _ _ hDl ay
    have t2 := m2 _ _ _ _ kβ hd
    have t3 := m2 _ _ _ _ (show |2 * α| ≤ 2 * K by rw [abs_mul]; norm_num; linarith) he
    have s1 := abs_add_le (Δ * y) (β * (d1 * z + d0) - 2 * α * (e1 * z + e0))
    have s2 := abs_sub (β * (d1 * z + d0)) (2 * α * (e1 * z + e0))
    have : 5 * (K : ℤ) ^ 2 * H + (K * (2 * K * H) + 2 * K * (2 * K * H)) = 11 * K ^ 2 * H := by
      ring
    linarith

/-- `|N(z)| ≤ 116 K⁴ H²` on the box. -/
lemma ternN_bound {α β γ d1 d0 e1 e0 f2 f1 f0 : ℤ} {K H : ℕ} (hH : 1 ≤ H) (kα : |α| ≤ K)
    (kβ : |β| ≤ K) (kγ : |γ| ≤ K) (kd1 : |d1| ≤ K) (kd0 : |d0| ≤ K) (ke1 : |e1| ≤ K)
    (ke0 : |e0| ≤ K) (kf2 : |f2| ≤ K) (kf1 : |f1| ≤ K) (kf0 : |f0| ≤ K) {z : ℤ} (hz : z ∈ ibox H) :
    |ternN α β γ d1 d0 e1 e0 f2 f1 f0 z| ≤ 116 * K ^ 4 * H ^ 2 := by
  set Δ := β ^ 2 - 4 * α * γ with hΔdef
  have hH1 : (1 : ℤ) ≤ H := by exact_mod_cast hH
  have hK1 : (0 : ℤ) ≤ K := by exact_mod_cast Nat.zero_le K
  have hKH : (K : ℤ) ≤ K * H := by nlinarith
  have m2 : ∀ a b : ℤ, ∀ A Bb : ℤ, |a| ≤ A → |b| ≤ Bb → |a * b| ≤ A * Bb := fun a b A Bb ha hb => by
    rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
  have hDl : |Δ| ≤ 5 * K ^ 2 := disc_bound kα kβ kγ
  have az := abs_le_of_mem_ibox hz
  have hd : |d1 * z + d0| ≤ 2 * K * H := by
    have := m2 _ _ _ _ kd1 az
    calc |d1 * z + d0| ≤ |d1 * z| + |d0| := abs_add_le _ _
      _ ≤ K * H + K := add_le_add this kd0
      _ ≤ 2 * K * H := by linarith
  have he : |e1 * z + e0| ≤ 2 * K * H := by
    have := m2 _ _ _ _ ke1 az
    calc |e1 * z + e0| ≤ |e1 * z| + |e0| := abs_add_le _ _
      _ ≤ K * H + K := add_le_add this ke0
      _ ≤ 2 * K * H := by linarith
  have hf : |f2 * z ^ 2 + f1 * z + f0| ≤ 3 * (K : ℤ) * (H : ℤ) ^ 2 := by
    have t1 := m2 _ _ _ _ kf2
        (show |z ^ 2| ≤ (H : ℤ) ^ 2 by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) az 2)
    have t2 := m2 _ _ _ _ kf1 az
    have s1 := abs_add_three (f2 * z ^ 2) (f1 * z) f0
    have : (K : ℤ) * H ≤ K * H ^ 2 := by nlinarith
    have : (K : ℤ) ≤ K * H ^ 2 := by nlinarith
    linarith
  have hΛ : |β * (d1 * z + d0) - 2 * α * (e1 * z + e0)| ≤ 6 * (K : ℤ) ^ 2 * H := by
    have t1 := m2 _ _ _ _ kβ hd
    have t2 := m2 _ _ _ _ (show |2 * α| ≤ 2 * K by rw [abs_mul]; norm_num; linarith) he
    have := abs_sub (β * (d1 * z + d0)) (2 * α * (e1 * z + e0))
    nlinarith
  have hQ : |4 * α * (f2 * z ^ 2 + f1 * z + f0) - (d1 * z + d0) ^ 2| ≤ 16 * (K : ℤ) ^ 2
      * (H : ℤ) ^ 2 := by
    have t1 := m2 _ _ _ _ (show |4 * α| ≤ 4 * K by rw [abs_mul]; norm_num; linarith) hf
    have t2 : |(d1 * z + d0) ^ 2| ≤ (2 * (K : ℤ) * H) ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
    have := abs_sub (4 * α * (f2 * z ^ 2 + f1 * z + f0)) ((d1 * z + d0) ^ 2)
    nlinarith
  have t1 : |(β * (d1 * z + d0) - 2 * α * (e1 * z + e0)) ^ 2| ≤ (6 * (K : ℤ) ^ 2 * H) ^ 2 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hΛ 2
  have t2 := m2 _ _ _ _ hDl hQ
  have e : ternN α β γ d1 d0 e1 e0 f2 f1 f0 z =
      (β * (d1 * z + d0) - 2 * α * (e1 * z + e0)) ^ 2 +
        Δ * (4 * α * (f2 * z ^ 2 + f1 * z + f0) - (d1 * z + d0) ^ 2) := by
    simp only [ternN, hΔdef]
  rw [e]
  calc _ ≤ |(β * (d1 * z + d0) - 2 * α * (e1 * z + e0)) ^ 2| +
        |Δ * (4 * α * (f2 * z ^ 2 + f1 * z + f0) - (d1 * z + d0) ^ 2)| := abs_add_le _ _
    _ ≤ (6 * (K : ℤ) ^ 2 * H) ^ 2 + 5 * (K : ℤ) ^ 2 * (16 * (K : ℤ) ^ 2 * (H : ℤ) ^ 2) :=
        add_le_add t1 t2
    _ = 116 * (K : ℤ) ^ 4 * (H : ℤ) ^ 2 := by ring

/-- **The slice count** for either sign of the binary discriminant `Δ`. -/
theorem slice_count_ne {α β γ d1 d0 e1 e0 f2 f1 f0 : ℤ} {K H W : ℕ} (hH : 1 ≤ H)
    (hα : 0 < α) (hΔ : β ^ 2 - 4 * α * γ ≠ 0)
    (hlead : (β * d1 - 2 * α * e1) ^ 2 + (β ^ 2 - 4 * α * γ) * (4 * α * f2 - d1 ^ 2) ≠ 0)
    (hK : |α| ≤ K ∧ |β| ≤ K ∧ |γ| ≤ K ∧ |d1| ≤ K ∧ |d0| ≤ K ∧ |e1| ≤ K ∧ |e0| ≤ K ∧
      |f2| ≤ K ∧ |f1| ≤ K ∧ |f0| ≤ K)
    (hW : ∀ M : ℤ, M ≠ 0 → |M| ≤ 116 * K ^ 4 * H ^ 2 →
      2 * M.natAbs.divisors.card ^ 3 * (Nat.log 3 ((11 * K ^ 2 * H * (3 * K + 2)) ^ 2) + 1) ≤ W) :
    ((ibox H ×ˢ ibox H ×ˢ ibox H).filter fun p =>
      tern α β γ d1 d0 e1 e0 f2 f1 f0 p.1 p.2.1 p.2.2 = 0).card ≤ (2 * H + 1) * (W + 4) := by
  classical
  set Δ := β ^ 2 - 4 * α * γ with hΔdef
  set S := (ibox H ×ˢ ibox H ×ˢ ibox H).filter fun p =>
    tern α β γ d1 d0 e1 e0 f2 f1 f0 p.1 p.2.1 p.2.2 = 0
  obtain ⟨kα, kβ, kγ, kd1, kd0, ke1, ke0, kf2, kf1, kf0⟩ := hK
  have hK1 : (1 : ℤ) ≤ K := by
    have : (1 : ℤ) ≤ |α| := by rw [abs_of_pos hα]; omega
    linarith
  -- the slice of a fixed `z`
  set slice : ℤ → Finset (ℤ × ℤ) := fun z => (ibox H ×ˢ ibox H).filter fun q =>
    tern α β γ d1 d0 e1 e0 f2 f1 f0 q.1 q.2 z = 0
  have hsplit : S.card = ∑ z ∈ ibox H, (slice z).card := by
    rw [card_eq_sum_card_fiberwise (f := fun p => p.2.2) (t := ibox H)
      (fun p hp => (mem_product.mp (mem_product.mp (mem_filter.mp hp).1).2).2)]
    refine sum_congr rfl fun z hz => ?_
    refine card_bij (fun p _ => (p.1, p.2.1)) (fun p hp => ?_) (fun p hp p' hp' h => ?_)
      (fun q hq => ?_)
    · obtain ⟨hp1, hp2⟩ := mem_filter.mp hp
      obtain ⟨hpb, hpF⟩ := mem_filter.mp hp1
      obtain ⟨hx, hyz⟩ := mem_product.mp hpb
      obtain ⟨hy, -⟩ := mem_product.mp hyz
      refine mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, ?_⟩
      rw [← hp2]; exact hpF
    · have e1 := (mem_filter.mp hp).2
      have e2 := (mem_filter.mp hp').2
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 (Prod.ext h.2 (e1.trans e2.symm))
    · obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
      obtain ⟨hx, hy⟩ := mem_product.mp hq1
      refine ⟨(q.1, q.2, z), mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hx,
        mem_product.mpr ⟨hy, hz⟩⟩, hq2⟩, rfl⟩, rfl⟩
  have hΔ0 : Δ ≠ 0 := hΔ
  have hα0 : α ≠ 0 := hα.ne'
  -- size bounds on the box
  have bnd : ∀ x y z : ℤ, x ∈ ibox H → y ∈ ibox H → z ∈ ibox H →
      |2 * α * x + β * y + (d1 * z + d0)| ≤ ((11 * K ^ 2 * H : ℕ) : ℤ) ∧
      |Δ * y + (β * (d1 * z + d0) - 2 * α * (e1 * z + e0))| ≤ ((11 * K ^ 2 * H : ℕ) : ℤ) :=
    fun _ _ _ hx hy hz => slice_bnd hH hK1 kα kβ kγ kd1 kd0 ke1 ke0 hx hy hz
  have hH1 : (1 : ℤ) ≤ H := by exact_mod_cast hH
  have hKH : (K : ℤ) ≤ K * H := by nlinarith
  have hDl : |Δ| ≤ 5 * K ^ 2 := disc_bound kα kβ kγ
  have hNb : ∀ z ∈ ibox H, |ternN α β γ d1 d0 e1 e0 f2 f1 f0 z| ≤ 116 * K ^ 4 * H ^ 2 :=
    fun _ hz => ternN_bound hH kα kβ kγ kd1 kd0 ke1 ke0 kf2 kf1 kf0 hz
  -- a slice with `N(z) ≠ 0`
  have hgood : ∀ z ∈ ibox H, ternN α β γ d1 d0 e1 e0 f2 f1 f0 z ≠ 0 → (slice z).card ≤ W := by
    intro z hz hN
    have hinj : Set.InjOn (fun q : ℤ × ℤ => (Δ * q.2 + (β * (d1 * z + d0) -
        2 * α * (e1 * z + e0)), 2 * α * q.1 + β * q.2 + (d1 * z + d0))) (slice z) := by
      intro q hq q' hq' h
      simp only [Prod.mk.injEq] at h
      have hy : q.2 = q'.2 := by
        have : Δ * q.2 = Δ * q'.2 := by linarith
        exact mul_left_cancel₀ hΔ0 this
      have hx : q.1 = q'.1 := by
        have : (2 * α) * q.1 = (2 * α) * q'.1 := by rw [hy] at h; linarith
        exact mul_left_cancel₀ (by positivity) this
      exact Prod.ext hx hy
    have hbox : ∀ q ∈ slice z,
        |Δ * q.2 + (β * (d1 * z + d0) - 2 * α * (e1 * z + e0))| ≤ ((11 * K ^ 2 * H : ℕ) : ℤ) ∧
        |2 * α * q.1 + β * q.2 + (d1 * z + d0)| ≤ ((11 * K ^ 2 * H : ℕ) : ℤ) ∧
        (Δ * q.2 + (β * (d1 * z + d0) - 2 * α * (e1 * z + e0))) ^ 2 -
          Δ * (2 * α * q.1 + β * q.2 + (d1 * z + d0)) ^ 2 =
          ternN α β γ d1 d0 e1 e0 f2 f1 f0 z := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
      obtain ⟨hx, hy⟩ := mem_product.mp hq1
      obtain ⟨b1, b2⟩ := bnd q.1 q.2 z hx hy hz
      refine ⟨b2, b1, ?_⟩
      have := slice_identity α β γ d1 d0 e1 e0 f2 f1 f0 q.1 q.2 z
      rw [hq2, mul_zero, sub_zero] at this
      exact this
    rcases lt_or_gt_of_ne hΔ0 with hneg | hpos
    · -- definite: `V² + |Δ| U² = N`
      have hDcast : (((-Δ).toNat : ℕ) : ℤ) = -Δ := Int.toNat_of_nonneg (by linarith)
      refine le_trans (card_le_card_of_injOn _ (t := defSols (-Δ).toNat
        (ternN α β γ d1 d0 e1 e0 f2 f1 f0 z) (11 * K ^ 2 * H)) (fun q hq => ?_) hinj)
        ((norm_count_def _ (by omega) hN).trans (le_trans ?_ (hW _ hN (hNb z hz))))
      · obtain ⟨b2, b1, hid⟩ := hbox q (mem_coe.mp hq)
        refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr (abs_le.mp b2),
          mem_Icc.mpr (abs_le.mp b1)⟩, ?_⟩
        simp only
        rw [hDcast]
        linear_combination hid
      have hKH : 1 ≤ K ^ 2 * H := Nat.mul_pos (pow_pos (by exact_mod_cast hK1) 2) hH
      have hl : 1 ≤ Nat.log 3 ((11 * K ^ 2 * H * (3 * K + 2)) ^ 2) :=
        Nat.le_log_of_pow_le (by norm_num) (by
          have h55 : 1 ≤ 11 * K ^ 2 * H * (3 * K + 2) := by
            have := Nat.mul_le_mul_left 11 hKH
            calc 1 ≤ 11 * (K ^ 2 * H) * 1 := by omega
              _ ≤ _ := by rw [← mul_assoc]; exact Nat.mul_le_mul_left _ (by omega)
          calc 3 ^ 1 ≤ (11 * K ^ 2 * H * (3 * K + 2)) ^ 1 := by
                rw [pow_one, pow_one]
                calc 3 ≤ 1 * (3 * K + 2) := by omega
                  _ ≤ _ := Nat.mul_le_mul_right _ (by nlinarith)
            _ ≤ _ := Nat.pow_le_pow_right h55 (by norm_num))
      calc 4 * _ = 2 * _ * 2 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
    · have hsqrt : Nat.sqrt Δ.toNat ≤ 3 * K := by
        have : Δ ≤ 5 * K ^ 2 := le_trans (le_abs_self _) hDl
        have h2 : (Δ.toNat : ℤ) ≤ (((3 * K) ^ 2 : ℕ) : ℤ) := by
          rw [Int.toNat_of_nonneg hpos.le]; push_cast
          linarith [show ((3 : ℤ) * K) ^ 2 = 9 * (K : ℤ) ^ 2 by ring, sq_nonneg (K : ℤ)]
        have h3 : Δ.toNat ≤ (3 * K) ^ 2 := by exact_mod_cast h2
        calc Nat.sqrt Δ.toNat ≤ Nat.sqrt ((3 * K) ^ 2) := Nat.sqrt_le_sqrt h3
          _ = 3 * K := Nat.sqrt_eq' _
      have hD1 : 1 ≤ Δ.toNat := by omega
      have hDcast : ((Δ.toNat : ℕ) : ℤ) = Δ := Int.toNat_of_nonneg hpos.le
      refine le_trans (card_le_card_of_injOn _
        (t := normSols Δ.toNat (ternN α β γ d1 d0 e1 e0 f2 f1 f0 z) (11 * K ^ 2 * H))
        (fun q hq => ?_) hinj)
        ((norm_count _ hD1 hN).trans (le_trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ
          (Nat.log_mono_right (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (by omega)) 2))))
          (hW _ hN (hNb z hz))))
      obtain ⟨b2, b1, hid⟩ := hbox q (mem_coe.mp hq)
      refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr (abs_le.mp b2),
        mem_Icc.mpr (abs_le.mp b1)⟩, ?_⟩
      simp only
      rw [hDcast]
      exact hid
  -- a slice with `N(z) = 0`
  have hbad : ∀ z ∈ ibox H, ternN α β γ d1 d0 e1 e0 f2 f1 f0 z = 0 →
      (slice z).card ≤ 2 * (2 * H + 1) := by
    intro z hz hN
    refine (card_le_mul_card_image_of_maps_to (f := fun q => q.2) (t := ibox H)
      (fun q hq => (mem_product.mp (mem_filter.mp hq).1).2) 2 fun y _ => ?_).trans
      (by rw [card_ibox])
    set Fy := (slice z).filter fun q => q.2 = y
    rw [← card_image_of_injOn (f := fun q => q.1) (s := Fy) (fun q hq q' hq' h => Prod.ext h
      ((mem_filter.mp (mem_coe.mp hq)).2.trans (mem_filter.mp (mem_coe.mp hq')).2.symm))]
    refine card_le_two_of_quad (α := 4 * α ^ 2 * Δ) (β := 4 * α * Δ * (β * y + (d1 * z + d0)))
      (γ := Δ * (β * y + (d1 * z + d0)) ^ 2 - (Δ * y + (β * (d1 * z + d0) -
        2 * α * (e1 * z + e0))) ^ 2) (mul_ne_zero (by positivity) hΔ0) fun x hx => ?_
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hx
    obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
    have hF := (mem_filter.mp hq1).2
    have := slice_identity α β γ d1 d0 e1 e0 f2 f1 f0 q.1 q.2 z
    rw [hF, hN, mul_zero, sub_zero, hq2, ← hΔdef] at this
    linear_combination -this
  -- at most two bad slices
  have hbadz : ((ibox H).filter fun z => ternN α β γ d1 d0 e1 e0 f2 f1 f0 z = 0).card ≤ 2 :=
    card_le_two_of_quad hlead fun z hz => by
      have := (mem_filter.mp hz).2
      rw [ternN_eq] at this
      exact this
  rw [hsplit]
  calc ∑ z ∈ ibox H, (slice z).card
      ≤ ∑ z ∈ ibox H, (W + if ternN α β γ d1 d0 e1 e0 f2 f1 f0 z = 0 then 2 * (2 * H
          + 1) else 0) := by
        refine sum_le_sum fun z hz => ?_
        by_cases hN : ternN α β γ d1 d0 e1 e0 f2 f1 f0 z = 0
        · rw [ite_eq_left hN]; exact (hbad z hz hN).trans (Nat.le_add_left _ _)
        · rw [ite_eq_right hN, add_zero]; exact hgood z hz hN
    _ = (2 * H + 1) * W + ((ibox H).filter fun z => ternN α β γ d1 d0 e1 e0 f2 f1 f0 z = 0).card *
          (2 * (2 * H + 1)) := by
        rw [sum_add_distrib, sum_const, card_ibox, smul_eq_mul, ← sum_filter, sum_const,
          smul_eq_mul]
    _ ≤ (2 * H + 1) * W + 2 * (2 * (2 * H + 1)) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hbadz) _
    _ = (2 * H + 1) * (W + 4) := by ring

/-- **The slice count** for `Δ > 0`. -/
theorem slice_count {α β γ d1 d0 e1 e0 f2 f1 f0 : ℤ} {K H W : ℕ} (hH : 1 ≤ H)
    (hα : 0 < α) (hΔ : 0 < β ^ 2 - 4 * α * γ)
    (hlead : (β * d1 - 2 * α * e1) ^ 2 + (β ^ 2 - 4 * α * γ) * (4 * α * f2 - d1 ^ 2) ≠ 0)
    (hK : |α| ≤ K ∧ |β| ≤ K ∧ |γ| ≤ K ∧ |d1| ≤ K ∧ |d0| ≤ K ∧ |e1| ≤ K ∧ |e0| ≤ K ∧
      |f2| ≤ K ∧ |f1| ≤ K ∧ |f0| ≤ K)
    (hW : ∀ M : ℤ, M ≠ 0 → |M| ≤ 116 * K ^ 4 * H ^ 2 →
      2 * M.natAbs.divisors.card ^ 3 * (Nat.log 3 ((11 * K ^ 2 * H * (3 * K + 2)) ^ 2) + 1) ≤ W) :
    ((ibox H ×ˢ ibox H ×ˢ ibox H).filter fun p =>
      tern α β γ d1 d0 e1 e0 f2 f1 f0 p.1 p.2.1 p.2.2 = 0).card ≤ (2 * H + 1) * (W + 4) :=
  slice_count_ne hH hα hΔ.ne' hlead hK hW

end PierceBound
