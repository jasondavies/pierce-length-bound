/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.MinorCount

/-! Completion of a first-four-column minor vertex in an independently sized
box. The common divisor is retained explicitly. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset

/-- A rectangular version of the existing cross-congruence fiber count. -/
theorem branch_completion_count_nat {m : ℕ} (hm : 0 < m) (X : ℕ) (u : Fin 3 → ℤ) :
    ((ibox3 X).filter fun v => ∀ j, (m : ℤ) ∣ cross3 u v j).card ≤
      (2 * X / m + 1) ^ 3 * (27 * m * gcd4 m u ^ 2) := by
  classical
  let S := (ibox3 X).filter fun v => ∀ j, (m : ℤ) ∣ cross3 u v j
  let T := (ibox3 m).filter fun v => ∀ j, (m : ℤ) ∣ cross3 u v j
  let key (v : Fin 3 → ℤ) : Fin 3 → ℤ := fun j => v j % (m : ℤ)
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  have hmaps : ∀ v ∈ S, key v ∈ T := by
    intro v hv
    refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun j => ?_), fun j => ?_⟩
    · exact mem_Icc.mpr ⟨by dsimp [key]; have := Int.emod_nonneg (v j) hmZ.ne'; omega,
        by dsimp [key]; exact (Int.emod_lt_of_pos _ hmZ).le⟩
    · have h := (mem_filter.mp hv).2 j
      apply Int.dvd_of_emod_eq_zero
      rw [← Int.emod_eq_zero_of_dvd h]
      simp [cross3, key, Int.sub_emod, Int.mul_emod]
  have hfiber : ∀ w ∈ T, (S.filter fun v => key v = w).card ≤ (2 * X / m + 1) ^ 3 := by
    intro w _
    let V := Fintype.piFinset fun j : Fin 3 =>
      (Icc (-(X : ℤ)) X).filter fun z => (m : ℤ) ∣ z - w j
    have hsub : S.filter (fun v => key v = w) ⊆ V := by
      intro v hv
      obtain ⟨hvS, hvw⟩ := mem_filter.mp hv
      apply Fintype.mem_piFinset.mpr
      intro j
      refine mem_filter.mpr ⟨Fintype.mem_piFinset.mp (mem_filter.mp hvS).1 j, ?_⟩
      have hj : v j % (m : ℤ) = w j := congrFun hvw j
      rw [← hj]
      apply Int.dvd_of_emod_eq_zero
      simp [Int.sub_emod]
    apply (card_le_card hsub).trans
    calc V.card = ∏ j : Fin 3,
          ((Icc (-(X : ℤ)) X).filter fun z => (m : ℤ) ∣ z - w j).card := by
            simp [V]
      _ ≤ ∏ _j : Fin 3, (2 * X / m + 1) := prod_le_prod fun j _ => card_Icc_dvd_le hm _
      _ = _ := by simp
  exact (card_le_mul_card_image_of_maps_to hmaps _ hfiber).trans
    (Nat.mul_le_mul_left _ (card_cross_fiber hm u))

/-- In a box of radius `X ≥ m`, the completion count is `O(X³g²/m²)`. -/
theorem branch_completion_count {m X : ℕ} (hm : 0 < m) (hmX : m ≤ X)
    (u : Fin 3 → ℤ) :
    (((ibox3 X).filter fun v => ∀ j, (m : ℤ) ∣ cross3 u v j).card : ℝ) ≤
      729 * (X : ℝ) ^ 3 * (gcd4 m u : ℝ) ^ 2 / (m : ℝ) ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hq : ((2 * X / m : ℕ) : ℝ) ≤ 2 * (X : ℝ) / m := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_div_le :
      ((2 * X / m : ℕ) : ℝ) ≤ (2 * X : ℕ) / (m : ℝ))
  have hmXR : (m : ℝ) ≤ X := by exact_mod_cast hmX
  have hq' : ((2 * X / m + 1 : ℕ) : ℝ) ≤ 3 * (X : ℝ) / m := by
    push_cast
    have hone : (1 : ℝ) ≤ X / (m : ℝ) := (le_div_iff₀ hmR).mpr (by simpa using hmXR)
    linarith only [hq, hone, show 3 * (X : ℝ) / m = 2 * X / m + X / m by ring]
  calc
    _ ≤ ((2 * X / m + 1 : ℕ) : ℝ) ^ 3 * (27 * m * (gcd4 m u : ℝ) ^ 2) := by
      exact_mod_cast (branch_completion_count_nat hm X u)
    _ ≤ (3 * (X : ℝ) / m) ^ 3 * (27 * m * (gcd4 m u : ℝ) ^ 2) := by gcongr
    _ = _ := by field_simp; ring

end
end PierceLengthBound.FixedDividend
