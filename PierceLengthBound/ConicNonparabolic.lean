/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ConicArithmetic
public import PierceLengthBound.SliceCount

/-! Uniform arithmetic counting for nonparabolic conics. The existing cubic
divisor loss suffices for an arbitrary epsilon, so no stronger norm-counting
claim is needed. Nonzero discriminant and norm are explicit hypotheses. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Finset

/-- Combine the definite and indefinite norm bounds for either sign of the discriminant. -/
theorem signed_norm_count (S : Finset (ℤ × ℤ)) {D N : ℤ} {B : ℕ}
    (hD : D ≠ 0) (hN : N ≠ 0)
    (hS : ∀ p ∈ S, |p.1| ≤ B ∧ |p.2| ≤ B ∧ p.1 ^ 2 - D * p.2 ^ 2 = N) :
    S.card ≤ 4 * N.natAbs.divisors.card ^ 3 *
      (Nat.log 3 ((B * (Nat.sqrt D.natAbs + 2)) ^ 2) + 1) := by
  rcases lt_or_gt_of_ne hD with hneg | hpos
  · have hDcast : (D.natAbs : ℤ) = -D := by rw [Int.natCast_natAbs, abs_of_nonpos hneg.le]
    have hsub : S ⊆ defSols D.natAbs N B := by
      intro p hp
      obtain ⟨h1, h2, he⟩ := hS p hp
      refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr (abs_le.mp h1),
        mem_Icc.mpr (abs_le.mp h2)⟩, ?_⟩
      rw [hDcast]
      linear_combination he
    calc S.card ≤ (defSols D.natAbs N B).card := card_le_card hsub
      _ ≤ 4 * N.natAbs.divisors.card ^ 3 := norm_count_def B (by omega) hN
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  · have hDcast : (D.natAbs : ℤ) = D := by rw [Int.natCast_natAbs, abs_of_nonneg hpos.le]
    have hsub : S ⊆ normSols D.natAbs N B := by
      intro p hp
      obtain ⟨h1, h2, he⟩ := hS p hp
      refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr (abs_le.mp h1),
        mem_Icc.mpr (abs_le.mp h2)⟩, ?_⟩
      simpa only [hDcast] using he
    calc S.card ≤ (normSols D.natAbs N B).card := card_le_card hsub
      _ ≤ 2 * N.natAbs.divisors.card ^ 3 *
          (Nat.log 3 ((B * (Nat.sqrt D.natAbs + 2)) ^ 2) + 1) := norm_count B (by omega) hN
      _ ≤ _ := by gcongr; norm_num

/-- A nonparabolic conic injects into the corresponding norm equation. -/
theorem nonparabolic_conic_count (S : Finset (ℤ × ℤ)) {α β γ d e f : ℤ} {B : ℕ}
    (hα : α ≠ 0) (hD : β ^ 2 - 4 * α * γ ≠ 0)
    (hN : (β * d - 2 * α * e) ^ 2 + (β ^ 2 - 4 * α * γ) * (4 * α * f - d ^ 2) ≠ 0)
    (hS : ∀ p ∈ S, conicValue α β γ d e f p.1 p.2 = 0 ∧
      |(β ^ 2 - 4 * α * γ) * p.2 + (β * d - 2 * α * e)| ≤ (B : ℤ) ∧
      |2 * α * p.1 + β * p.2 + d| ≤ (B : ℤ)) :
    S.card ≤ 4 *
      ((β * d - 2 * α * e) ^ 2 + (β ^ 2 - 4 * α * γ) *
        (4 * α * f - d ^ 2)).natAbs.divisors.card ^ 3 *
      (Nat.log 3 ((B * (Nat.sqrt (β ^ 2 - 4 * α * γ).natAbs + 2)) ^ 2) + 1) := by
  classical
  let Φ : ℤ × ℤ → ℤ × ℤ := fun p =>
    ((β ^ 2 - 4 * α * γ) * p.2 + (β * d - 2 * α * e),
      2 * α * p.1 + β * p.2 + d)
  have hinj : Function.Injective Φ := conic_norm_coordinates_injective hα hD
  rw [← card_image_of_injective S hinj]
  apply signed_norm_count _ hD hN
  intro p hp
  obtain ⟨z, hz, rfl⟩ := mem_image.mp hp
  obtain ⟨he, h1, h2⟩ := hS z hz
  refine ⟨h1, h2, ?_⟩
  have hid := conic_norm_identity α β γ d e f z.1 z.2
  rw [he] at hid
  dsimp [Φ]
  linear_combination hid

/-- The norm integer has fourth-power coefficient height, independently of the
coordinate box. -/
theorem conic_norm_height {α β γ d e f : ℤ} {K : ℕ}
    (hK : |α| ≤ K ∧ |β| ≤ K ∧ |γ| ≤ K ∧ |d| ≤ K ∧ |e| ≤ K ∧ |f| ≤ K) :
    |(β * d - 2 * α * e) ^ 2 + (β ^ 2 - 4 * α * γ) * (4 * α * f - d ^ 2)| ≤
      116 * (K : ℤ) ^ 4 := by
  obtain ⟨hα, hβ, hγ, hd, he, hf⟩ := hK
  have hz : (0 : ℤ) ∈ ibox 1 := by simp [ibox]
  have hn := ternN_bound (H := 1) (by norm_num) hα hβ hγ
    (show |(0 : ℤ)| ≤ K by simp) hd (show |(0 : ℤ)| ≤ K by simp) he
    (show |(0 : ℤ)| ≤ K by simp) (show |(0 : ℤ)| ≤ K by simp) hf hz
  simpa [ternN] using hn

/-- Polynomial bounds for both transformed norm coordinates. -/
theorem conic_norm_box {α β γ d e x y : ℤ} {K H : ℕ}
    (hH : 1 ≤ H) (hK1 : 1 ≤ K)
    (hK : |α| ≤ K ∧ |β| ≤ K ∧ |γ| ≤ K ∧ |d| ≤ K ∧ |e| ≤ K)
    (hx : |x| ≤ (H : ℤ)) (hy : |y| ≤ (H : ℤ)) :
    |(β ^ 2 - 4 * α * γ) * y + (β * d - 2 * α * e)| ≤ ((11 * K ^ 2 * H : ℕ) : ℤ) ∧
      |2 * α * x + β * y + d| ≤ ((11 * K ^ 2 * H : ℕ) : ℤ) := by
  obtain ⟨hα, hβ, hγ, hd, he⟩ := hK
  have hz : (0 : ℤ) ∈ ibox H := by simp [ibox]
  have hb := slice_bnd hH (by exact_mod_cast hK1) hα hβ hγ
    (show |(0 : ℤ)| ≤ K by simp) hd (show |(0 : ℤ)| ≤ K by simp) he
    (show x ∈ ibox H from mem_Icc.mpr (abs_le.mp hx))
    (show y ∈ ibox H from mem_Icc.mpr (abs_le.mp hy)) hz
  simpa using hb.symm

/-- Uniform count stated directly with the original coefficient and coordinate
bounds, with no unspecified transformation-height assumption. -/
theorem nonparabolic_conic_box_count (S : Finset (ℤ × ℤ)) {α β γ d e f : ℤ} {K H : ℕ}
    (hH : 1 ≤ H) (hK1 : 1 ≤ K)
    (hK : |α| ≤ K ∧ |β| ≤ K ∧ |γ| ≤ K ∧ |d| ≤ K ∧ |e| ≤ K)
    (hα : α ≠ 0) (hD : β ^ 2 - 4 * α * γ ≠ 0)
    (hN : (β * d - 2 * α * e) ^ 2 + (β ^ 2 - 4 * α * γ) * (4 * α * f - d ^ 2) ≠ 0)
    (hS : ∀ p ∈ S, conicValue α β γ d e f p.1 p.2 = 0 ∧
      |p.1| ≤ (H : ℤ) ∧ |p.2| ≤ (H : ℤ)) :
    S.card ≤ 4 *
      ((β * d - 2 * α * e) ^ 2 + (β ^ 2 - 4 * α * γ) *
        (4 * α * f - d ^ 2)).natAbs.divisors.card ^ 3 *
      (Nat.log 3 ((11 * K ^ 2 * H * (Nat.sqrt (β ^ 2 - 4 * α * γ).natAbs + 2)) ^ 2) + 1) := by
  apply nonparabolic_conic_count S hα hD hN
  intro p hp
  obtain ⟨he, hx, hy⟩ := hS p hp
  exact ⟨he, conic_norm_box hH hK1 hK hx hy⟩

end PierceLengthBound.FixedDividend
