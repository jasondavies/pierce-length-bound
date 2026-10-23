/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveUniformRootBound
public import PierceLengthBound.BranchSieveRationalization
import Mathlib.Tactic

/-! The uniform integral-root estimate in nested-polynomial notation. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

theorem branch_uniform_nested_root_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Type*) [Field F] [Algebra ℤ[X] F]
      [IsFractionRing ℤ[X] F], ∀ (p : ℤ[X][X]), p.Monic →
      Irreducible (p.map (algebraMap ℤ[X] F)) →
      CCDN.bivariateTotalDegree p ≤ d → 2 ≤ p.natDegree →
      ∀ H B : ℕ, (∀ i j, |(p.coeff i).coeff j| ≤ (H : ℤ)) → 1 ≤ B →
      ∀ S : Finset ℤ,
      (∀ t ∈ S, |t| ≤ (B : ℤ) ∧ ∃ y : ℤ,
        (p.map (Polynomial.evalRingHom t)).eval y = 0) →
      (S.card : ℝ) ≤ C * (1 + Real.log (H + 1 : ℕ)) ^ 4 *
        (B : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log B) := by
  obtain ⟨C, hC, hroot⟩ := branch_uniform_integral_root_bound d
  refine ⟨C, hC, ?_⟩
  intro F _ _ _ p hp hir hd hn H B hH hB S hS
  apply hroot (branchNestedCoordinates ℤ p)
  · unfold branchRationalPolynomial
    rw [branchNestedCoordinates_map]
    exact (MulEquiv.irreducible_iff (f := branchNestedCoordinates ℚ)).mpr
      (branch_rational_nested_irreducible p hp hir)
  · rwa [branchNestedCoordinates_totalDegree]
  · rwa [branchNestedCoordinates_degreeOf]
  · intro s
    rw [branchNestedCoordinates_coeff]
    exact hH _ _
  · exact hB
  · intro t ht
    obtain ⟨htB, y, hy⟩ := hS t ht
    exact ⟨htB, y, by rwa [branchNestedCoordinates_eval]⟩

end
end PierceLengthBound.FixedDividend
