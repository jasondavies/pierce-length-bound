/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveResultantGeneric

/-! Generic unnormalized first-minor vertices recover the normalized branch
coefficients. They provide a coefficient map for proving generic irreducibility
of the monic integer family. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial
open scoped RatFunc
attribute [local instance] Polynomial.algebra
open scoped BranchLocationFields

/-- Generic vertices in order `(A,D,C,B)`, inverse to the normalized location
coefficients `c₁=−(B+C)/A`, `c₂=(C+D)/A`, `c₃=−(D+A)/A`. -/
def branchGenericVertex : Fin 4 → RatFunc BranchLocationField :=
  ![RatFunc.X, -RatFunc.X * (branchResultantGenericCoefficient 2 + 1),
    RatFunc.X * (branchResultantGenericCoefficient 1 + branchResultantGenericCoefficient 2 + 1),
    -RatFunc.X * (branchResultantGenericCoefficient 0 + branchResultantGenericCoefficient 1 +
      branchResultantGenericCoefficient 2 + 1)]

lemma branchGenericVertex_zero :
    branchGenericVertex 0 = (RatFunc.X : RatFunc BranchLocationField) := rfl

lemma branchGenericVertex_normalized :
    (-branchGenericVertex 3 - branchGenericVertex 2) / branchGenericVertex 0 =
        branchResultantGenericCoefficient 0 ∧
      (branchGenericVertex 2 + branchGenericVertex 1) / branchGenericVertex 0 =
        branchResultantGenericCoefficient 1 ∧
      (-branchGenericVertex 1 - branchGenericVertex 0) / branchGenericVertex 0 =
        branchResultantGenericCoefficient 2 := by
  dsimp [branchGenericVertex]
  constructor <;> (try constructor) <;> field_simp [RatFunc.X_ne_zero] <;> ring

end
end PierceLengthBound.FixedDividend
