/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.OrbitPattern

/-! The integral rank-three Hankel invariant `I₃(i) = d_i k_{i+1} - d_{i+1} k_i`, the
coordinate added by the integral lift: it equals `hankelInv a b i 3` and is a positive
integer. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset Polynomial Matrix

/-- The integral rank-three Hankel invariant, written in drops and gaps. -/
def integralLiftCoordinate (a b i : ℕ) : ℤ :=
  dq a b i * kq a b (i + 1) - dq a b (i + 1) * kq a b i

/-- The integral lift coordinate is the Hankel invariant `I₃(i)`. -/
lemma integralLiftCoordinate_eq {a b i : ℕ} (hba : b < a) (hi : i + 3 < P a b) :
    (integralLiftCoordinate a b i : ℝ) = hankelInv a b i 3 := by
  rw [hankelInv_three hba hi]
  simp [integralLiftCoordinate, dq, kq, kv, kk]

/-- The integral lift coordinate is at least `1`. -/
lemma integralLiftCoordinate_pos {a b i : ℕ} (hba : b < a) (hi : i + 3 < P a b) :
    1 ≤ integralLiftCoordinate a b i := by
  have h := hankelInv_pos hba (i := i) (r := 3) (by omega) (by omega)
  rw [← integralLiftCoordinate_eq hba hi] at h
  have : (0 : ℤ) < integralLiftCoordinate a b i := by exact_mod_cast h
  omega

end
end PierceLengthBound.FixedDividend
