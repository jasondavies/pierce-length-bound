/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveIntegralFactorWitness
public import PierceLengthBound.BranchSieveReductionMap
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.Tactic

/-! The integral closure contains every root of a monic polynomial. This
supplies the splitting algebra used in the specialization argument. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

theorem branch_monic_splits_integralClosure {R L : Type*}
    [CommRing R] [IsDomain R] [Field L] [Algebra R L]
    (p : R[X]) (hp : p.Monic) (hsplit : (p.map (algebraMap R L)).Splits) :
    (p.map (algebraMap R (integralClosure R L))).Splits := by
  let S := integralClosure R L
  have hmap : (p.map (algebraMap R S)).map (algebraMap S L) = p.map (algebraMap R L) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  apply Polynomial.Splits.of_splits_map_of_injective
    (i := algebraMap S L) (FaithfulSMul.algebraMap_injective S L)
  · rwa [hmap]
  · intro x hx
    rw [hmap] at hx
    have hxroot := (Polynomial.mem_roots (hp.map (algebraMap R L)).ne_zero).mp hx
    have hint : IsIntegral R x := ⟨p, hp, by
      simpa only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def] using hxroot⟩
    exact ⟨⟨x, hint⟩, rfl⟩

end
end PierceLengthBound.FixedDividend
