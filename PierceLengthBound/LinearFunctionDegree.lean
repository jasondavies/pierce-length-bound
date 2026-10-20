/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendFilteredIntersection
public import AffineCurveCounting.CurveFunctionField
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! The function-field degree of a transcendental linear coordinate is bounded
by the affine Hilbert degree. This reuses the proved rank comparison from the
external curve-counting development with the Pierce coordinate filtration. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open scoped IntermediateField

theorem linear_function_degree_le_hilbert {K F σ : Type*}
    [Field K] [Field F] [Algebra K F] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    [Algebra (MvPolynomial σ K ⧸ I) F] [IsScalarTower K (MvPolynomial σ K ⧸ I) F]
    [IsFractionRing (MvPolynomial σ K ⧸ I) F]
    {d : ℕ} (hdegree : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c)
    (l : MvPolynomial σ K) (hl : l.totalDegree ≤ 1)
    (x : F) (hx : Transcendental K x)
    (he : algebraMap (MvPolynomial σ K ⧸ I) F (Ideal.Quotient.mk I l) = x) :
    Module.Finite K⟮x⟯ F ∧ Module.finrank K⟮x⟯ F ≤ d := by
  let : Fintype σ := Fintype.ofFinite σ
  let u : K⟮x⟯ := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
  have hu : Transcendental K u :=
    (transcendental_algebraMap_iff (R := K) (S := K⟮x⟯)
      (A := F) (algebraMap K⟮x⟯ F).injective).mp hx
  exact AffineCurveCounting.curve_functionField_finite_rank_le I d hdegree l hl u hu he

end
end PierceLengthBound.FixedDividend
