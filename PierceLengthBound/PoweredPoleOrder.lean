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

end
end PierceLengthBound.FixedDividend
