/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchPoleEnvelope

/-! Integer powers multiply pole orders and coordinate pole envelopes. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

lemma discretePoleOrder_pow {F : Type*} [Field F]
    (ν : AddValuation F (WithTop ℤ)) (x : F) (n : ℕ) :
    discretePoleOrder ν (x ^ n) = n * discretePoleOrder ν x := by
  cases h : ν x with
  | top =>
    cases n with
    | zero => simp [discretePoleOrder]
    | succ n => simp [discretePoleOrder, ν.map_pow, h, succ_nsmul]
  | coe z =>
    have hh : ν (x ^ n) = (((n : ℤ) * z : ℤ) : WithTop ℤ) := by
      rw [ν.map_pow, h, ← WithTop.coe_nsmul]
      congr 1
    rw [discretePoleOrder_eq ν hh, discretePoleOrder_eq ν h, ← mul_neg]
    by_cases hz : 0 ≤ -z
    · rw [Int.toNat_mul (Int.natCast_nonneg n) hz]
      simp
    · have hz' : -z ≤ 0 := (lt_of_not_ge hz).le
      rw [Int.toNat_eq_zero.mpr (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg n) hz'),
        Int.toNat_eq_zero.mpr hz', mul_zero]

lemma branchPoleEnvelope_pow {F ι : Type*} [Field F] [Fintype ι]
    (ν : AddValuation F (WithTop ℤ)) (W : ι → F) (n : ℕ) :
    branchPoleEnvelope ν (fun j => W j ^ n) = n * branchPoleEnvelope ν W := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro j _
    rw [discretePoleOrder_pow]
    exact Nat.mul_le_mul_left n (pole_order_le_envelope ν W j)
  · by_cases h : branchPoleEnvelope ν W = 0
    · simp [h]
    · obtain ⟨j, hj⟩ := branchPoleEnvelope_attained ν W (Nat.pos_of_ne_zero h)
      have he := (discretePoleOrder_eq_iff_of_pos ν (W j) (Nat.pos_of_ne_zero h)).mpr hj
      rw [← he, ← discretePoleOrder_pow]
      exact pole_order_le_envelope ν (fun j => W j ^ n) j

end
end PierceLengthBound.FixedDividend
