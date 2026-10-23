/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ExceptionalParameterCount
public import PierceLengthBound.ExceptionalDirection

/-! Counting rank-one pairs with an orthogonal third vector, including every
common divisor. This is the zero-Plücker-coordinate counting problem. -/

@[expose] public section
namespace PierceLengthBound
open Finset
open scoped Matrix
open Matrix (vec3_dotProduct)
noncomputable section

/-- Decode a primitive direction, its two scalar multiples and an orthogonal vector. -/
def exceptionalDecode (p : (Fin 3 → ℤ) × (ℤ × ℤ) × (Fin 3 → ℤ)) :
    (Fin 3 → ℤ) × (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
  (fun j => p.2.1.1 * p.1 j, fun j => p.2.1.2 * p.1 j, p.2.2)

/-- Every nonzero rank-one pair occurs in a bounded dyadic parameter set. -/
theorem rank_one_parameter_cover {a b t : Fin 3 → ℤ} {X : ℕ}
    (hne : a ≠ 0 ∨ b ≠ 0) (hcross : ∀ j, (a ⨯₃ b) j = 0)
    (haX : ∀ j, |a j| ≤ X) (hbX : ∀ j, |b j| ≤ X) (htX : ∀ j, |t j| ≤ X)
    (hat : a ⬝ᵥ t = 0) (hbt : b ⬝ᵥ t = 0) :
    ∃ k ≤ Nat.log 2 X, (a, b, t) ∈
      (exceptionalParameters X (2 ^ k)).image exceptionalDecode := by
  classical
  obtain ⟨z, c, r, s, hc, ha, hb, hrs⟩ := exists_common_primitive_direction hne hcross
  obtain ⟨j, _, hj⟩ := exists_max_image univ (fun j => (z j).natAbs) univ_nonempty
  let N := (z j).natAbs
  have hn : 0 < N := by
    by_contra hn
    have hzero : ∀ k, z k = 0 := by
      intro k
      have := hj k (mem_univ k)
      have : (z k).natAbs = 0 := by dsimp [N] at hn; omega
      exact Int.natAbs_eq_zero.mp this
    simp [vec3_dotProduct, hzero] at hc
  have hr : r.natAbs * N ≤ X := by
    have h := haX j
    rw [ha j, abs_mul, ← Int.natCast_natAbs, ← Int.natCast_natAbs] at h
    exact_mod_cast h
  have hs : s.natAbs * N ≤ X := by
    have h := hbX j
    rw [hb j, abs_mul, ← Int.natCast_natAbs, ← Int.natCast_natAbs] at h
    exact_mod_cast h
  have hNX : N ≤ X := by
    rcases hrs with hr0 | hs0
    · have : 1 ≤ r.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hr0)
      nlinarith
    · have : 1 ≤ s.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hs0)
      nlinarith
  let k := Nat.log 2 N
  let Z := 2 ^ k
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hZN : Z ≤ N := Nat.pow_log_le_self 2 hn.ne'
  have hN2Z : N < 2 * Z := by
    have := Nat.lt_pow_succ_log_self (by decide : 1 < 2) N
    simpa [Z, k, pow_succ, mul_comm] using this
  have hkb : k ≤ Nat.log 2 X := Nat.log_mono_right hNX
  refine ⟨k, hkb, mem_image.mpr ⟨(z, (r, s), t), ?_, ?_⟩⟩
  · apply mem_biUnion.mpr
    refine ⟨z, ?_, mem_image.mpr ⟨((r, s), t), ?_, rfl⟩⟩
    · apply mem_filter.mpr
      refine ⟨Fintype.mem_piFinset.mpr ?_, ⟨c, hc⟩, j, hZN, hNX⟩
      intro l
      apply mem_Icc.mpr
      apply abs_le.mp
      have h := hj l (mem_univ l)
      have : (z l).natAbs ≤ 2 * Z := by omega
      have : ((z l).natAbs : ℤ) ≤ (2 * Z : ℕ) := by exact_mod_cast this
      simpa [Z, Int.natCast_natAbs] using this
    · apply mem_product.mpr
      constructor
      · have hrr : r.natAbs ≤ X / Z := (Nat.le_div_iff_mul_le hZ).mpr
          ((Nat.mul_le_mul_left r.natAbs hZN).trans hr)
        have hss : s.natAbs ≤ X / Z := (Nat.le_div_iff_mul_le hZ).mpr
          ((Nat.mul_le_mul_left s.natAbs hZN).trans hs)
        apply mem_product.mpr
        constructor
        · apply mem_Icc.mpr; apply abs_le.mp
          have : ((r.natAbs : ℕ) : ℤ) ≤ (X / Z : ℕ) := by exact_mod_cast hrr
          simpa [Z, Int.natCast_natAbs] using this
        · apply mem_Icc.mpr; apply abs_le.mp
          have : ((s.natAbs : ℕ) : ℤ) ≤ (X / Z : ℕ) := by exact_mod_cast hss
          simpa [Z, Int.natCast_natAbs] using this
      · exact mem_filter.mpr ⟨Fintype.mem_piFinset.mpr
          (fun l => mem_Icc.mpr (abs_le.mp (htX l))),
          common_direction_orthogonal ha hb hrs hat hbt⟩
  · apply Prod.ext
    · funext l; exact (ha l).symm
    · apply Prod.ext
      · funext l; exact (hb l).symm
      · rfl

/-- Uniform `O(X⁴ log(2X))` count for the rank-one/orthogonality equations. -/
theorem rank_one_orthogonal_count
    {S : Finset ((Fin 3 → ℤ) × (Fin 3 → ℤ) × (Fin 3 → ℤ))} {X : ℕ} (hX : 1 ≤ X)
    (hS : ∀ p ∈ S,
      (∀ j, |p.1 j| ≤ X) ∧ (∀ j, |p.2.1 j| ≤ X) ∧ (∀ j, |p.2.2 j| ≤ X) ∧
      (∀ j, (p.1 ⨯₃ p.2.1) j = 0) ∧ p.1 ⬝ᵥ p.2.2 = 0 ∧ p.2.1 ⬝ᵥ p.2.2 = 0) :
    S.card ≤ (2 * X + 1) ^ 3 + (Nat.log 2 X + 1) * (273375 * X ^ 4) := by
  classical
  let zeroSet := (ibox3 X).image fun t => ((0 : Fin 3 → ℤ), (0 : Fin 3 → ℤ), t)
  let otherSet := (range (Nat.log 2 X + 1)).biUnion fun k =>
    (exceptionalParameters X (2 ^ k)).image exceptionalDecode
  have hsub : S ⊆ zeroSet ∪ otherSet := by
    intro p hp
    obtain ⟨haX, hbX, htX, hab, hat, hbt⟩ := hS p hp
    by_cases ha : p.1 = 0
    · by_cases hb : p.2.1 = 0
      · apply mem_union_left
        exact mem_image.mpr ⟨p.2.2, Fintype.mem_piFinset.mpr
          (fun j => mem_Icc.mpr (abs_le.mp (htX j))),
          Prod.ext ha.symm (Prod.ext hb.symm rfl)⟩
      · obtain ⟨k, hk, hmem⟩ := rank_one_parameter_cover (Or.inr hb) hab haX hbX htX hat hbt
        exact mem_union_right _ (mem_biUnion.mpr ⟨k, mem_range.mpr (by omega), hmem⟩)
    · obtain ⟨k, hk, hmem⟩ := rank_one_parameter_cover (Or.inl ha) hab haX hbX htX hat hbt
      exact mem_union_right _ (mem_biUnion.mpr ⟨k, mem_range.mpr (by omega), hmem⟩)
  have hz : zeroSet.card ≤ (2 * X + 1) ^ 3 := card_image_le.trans_eq (ibox3_card X)
  have ho : otherSet.card ≤ (Nat.log 2 X + 1) * (273375 * X ^ 4) := by
    calc otherSet.card ≤ ∑ k ∈ range (Nat.log 2 X + 1),
        ((exceptionalParameters X (2 ^ k)).image exceptionalDecode).card := card_biUnion_le
      _ ≤ ∑ _k ∈ range (Nat.log 2 X + 1), 273375 * X ^ 4 := by
        apply sum_le_sum
        intro k hk
        apply card_image_le.trans
        exact exceptional_parameters_count (Nat.one_le_pow _ _ (by decide))
          (Nat.pow_le_of_le_log (by omega : X ≠ 0) (by simpa using mem_range.mp hk))
      _ = _ := by rw [sum_const, card_range, smul_eq_mul]
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add hz ho))

end
end PierceLengthBound
