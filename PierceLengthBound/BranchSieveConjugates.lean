/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveQuadratic
import Mathlib.Tactic

/-! Distinctness of the twelve branch labels after introducing the reciprocal
square-root scale. This supplies the elementary distinctness step in the
construction of the twelve embeddings over the original coefficient field. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

variable {K : Type*} [Field K]

/-- Constants and the independent scale have independent coefficients. -/
lemma branch_linear_function_eq_iff (t b t' b' : K) :
    RatFunc.C t + RatFunc.C b * RatFunc.X = RatFunc.C t' + RatFunc.C b' * RatFunc.X ↔
      t = t' ∧ b = b' := by
  constructor
  · intro h
    have hp : (Polynomial.C t + Polynomial.C b * Polynomial.X : Polynomial K) =
        Polynomial.C t' + Polynomial.C b' * Polynomial.X := by
      apply IsFractionRing.injective (Polynomial K) (RatFunc K)
      simpa only [map_add, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X] using h
    exact ⟨by simpa using congrArg (fun p : Polynomial K => p.coeff 0) hp,
      by simpa using congrArg (fun p : Polynomial K => p.coeff 1) hp⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The sign distinguishes the two branch labels above each location. -/
def branchConjugateLabel (t b : K) (ε : Fin 2) : RatFunc K :=
  RatFunc.C t + RatFunc.C (if ε = 0 then b else -b) * RatFunc.X

/-- Six distinct constant locations and nonzero sign coefficients give twelve distinct
functions of the reciprocal square-root scale. -/
theorem branchConjugateLabels_injective [CharZero K]
    (t b : Fin 6 → K) (ht : Function.Injective t) (hb : ∀ j, b j ≠ 0) :
    Function.Injective (fun p : Fin 6 × Fin 2 => branchConjugateLabel (t p.1) (b p.1) p.2) := by
  rintro ⟨i, ε⟩ ⟨j, δ⟩ he
  have h := (branch_linear_function_eq_iff _ _ _ _).mp he
  have hij : i = j := ht h.1
  subst j
  apply Prod.ext
  · rfl
  · fin_cases ε <;> fin_cases δ <;> simp [CharZero.eq_neg_self_iff,
      CharZero.neg_eq_self_iff, hb] at h ⊢

/-- The label set has exactly twelve elements. This counts functions, before specialization
of the independent scale. -/
theorem branchConjugateLabels_card [CharZero K]
    (t b : Fin 6 → K) (ht : Function.Injective t) (hb : ∀ j, b j ≠ 0) :
    Nat.card (Set.range
      (fun p : Fin 6 × Fin 2 => branchConjugateLabel (t p.1) (b p.1) p.2)) = 12 := by
  rw [Nat.card_range_of_injective (branchConjugateLabels_injective t b ht hb)]
  simp

end
end PierceLengthBound.FixedDividend
