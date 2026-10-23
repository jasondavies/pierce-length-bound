/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendSelection
public import PierceLengthBound.Gram

/-! The added coordinate is a positive integer with the required small box bound
at actual selected orbit starts. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset Polynomial Matrix

/-- The integral rank-three Hankel invariant, written in actual drops and gaps. -/
def integralLiftCoordinate (a b i : ℕ) : ℤ :=
  dq a b i * kq a b (i + 1) - dq a b (i + 1) * kq a b i

lemma integralLiftCoordinate_eq {a b i : ℕ} (hba : b < a) (hi : i + 3 < P a b) :
    (integralLiftCoordinate a b i : ℝ) = hankelInv a b i 3 := by
  rw [hankelInv_three hba hi]
  simp [integralLiftCoordinate, dq, kq, kv, kk]

lemma integralLiftCoordinate_pos {a b i : ℕ} (hba : b < a) (hi : i + 3 < P a b) :
    1 ≤ integralLiftCoordinate a b i := by
  have h := hankelInv_pos hba (i := i) (r := 3) (by omega) (by omega)
  rw [← integralLiftCoordinate_eq hba hi] at h
  have : (0 : ℤ) < integralLiftCoordinate a b i := by exact_mod_cast h
  omega

end
end PierceLengthBound.FixedDividend
