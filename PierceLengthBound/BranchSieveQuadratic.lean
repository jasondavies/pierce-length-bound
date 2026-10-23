/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic

/-! The quadratic extension which distinguishes the two branches above an infinity location.
The absolute scale is an independent variable. Its odd rational-function degree proves that
`a Δ / A` is not a square, for every nonzero dividend and every nonzero location invariant.
These are unconditional algebraic statements; no specialization-counting estimate is assumed. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

variable {K : Type*} [Field K]

/-- The squared branch sign, with the absolute scale represented by `RatFunc.X`. -/
def branchSignSquare (a Δ : K) : RatFunc K := RatFunc.C (a * Δ) / RatFunc.X

lemma branchSignSquare_ne_zero {a Δ : K} (ha : a ≠ 0) (hΔ : Δ ≠ 0) :
    branchSignSquare a Δ ≠ 0 := by
  apply div_ne_zero
  · simpa only [map_zero] using RatFunc.C_injective.ne (mul_ne_zero ha hΔ)
  · exact RatFunc.X_ne_zero

/-- Odd degree in the absolute scale prevents a square, independently of the dividend. -/
theorem branchSignSquare_not_square {a Δ : K} (ha : a ≠ 0) (hΔ : Δ ≠ 0)
    (β : RatFunc K) : β ^ 2 ≠ branchSignSquare a Δ := by
  intro he
  have hβ : β ≠ 0 := by
    intro h
    apply branchSignSquare_ne_zero ha hΔ
    rw [← he, h, zero_pow (by decide : 2 ≠ 0)]
  have hdeg := congrArg RatFunc.intDegree he
  rw [pow_two, RatFunc.intDegree_mul hβ hβ] at hdeg
  have hc : RatFunc.C (a * Δ) ≠ 0 := by
    simpa only [map_zero] using RatFunc.C_injective.ne (mul_ne_zero ha hΔ)
  rw [branchSignSquare, RatFunc.intDegree_div hc RatFunc.X_ne_zero,
    RatFunc.intDegree_C, RatFunc.intDegree_X] at hdeg
  omega

/-- The quadratic equation for the two local branch signs. -/
def branchSignPolynomial (a Δ : K) : Polynomial (RatFunc K) :=
  Polynomial.X ^ 2 - Polynomial.C (branchSignSquare a Δ)

/-- The branch-sign polynomial is irreducible for every nonzero dividend. -/
theorem branchSignPolynomial_irreducible {a Δ : K} (ha : a ≠ 0) (hΔ : Δ ≠ 0) :
    Irreducible (branchSignPolynomial a Δ) :=
  X_pow_sub_C_irreducible_of_prime (by norm_num : Nat.Prime 2)
    (branchSignSquare_not_square ha hΔ)

lemma branchSignPolynomial_natDegree (a Δ : K) :
    (branchSignPolynomial a Δ).natDegree = 2 := by
  exact Polynomial.natDegree_X_pow_sub_C

/-- Adjoining a branch sign has dimension two over the location field with the scale added. -/
theorem branchSignExtension_finrank (a Δ : K) :
    Module.finrank (RatFunc K) (AdjoinRoot (branchSignPolynomial a Δ)) = 2 := by
  have hp : branchSignPolynomial a Δ ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero (by decide : 0 < 2) _
  simpa only [AdjoinRoot.powerBasis_dim, branchSignPolynomial_natDegree] using
    (AdjoinRoot.powerBasis hp).finrank

/-- Translation by the location preserves the irreducible quadratic equation.
This is the degree-two part of the primitive element `t + β`. -/
theorem branchTranslatedSignPolynomial_irreducible {a Δ : K}
    (ha : a ≠ 0) (hΔ : Δ ≠ 0) (t : K) :
    Irreducible ((Polynomial.X - Polynomial.C (RatFunc.C t)) ^ 2 -
      Polynomial.C (branchSignSquare a Δ)) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hd : (((Polynomial.X - Polynomial.C (RatFunc.C t)) ^ 2 -
        Polynomial.C (branchSignSquare a Δ)) : Polynomial (RatFunc K)).natDegree = 2 := by
      compute_degree
      simp
    simp [hd]
  · intro z hz
    exact branchSignSquare_not_square ha hΔ (z - RatFunc.C t)
      (by simpa [Polynomial.IsRoot, Polynomial.eval_sub, sub_eq_zero] using hz)

/-- For nonzero dividend and invariant, the branch-sign algebra is a field. -/
theorem branchSignExtension_isField {a Δ : K} (ha : a ≠ 0) (hΔ : Δ ≠ 0) :
    IsField (AdjoinRoot (branchSignPolynomial a Δ)) := by
  let : Fact (Irreducible (branchSignPolynomial a Δ)) :=
    ⟨branchSignPolynomial_irreducible ha hΔ⟩
  exact Field.toIsField _

open scoped RatFunc
attribute [local instance] Polynomial.algebra

/-- A sextic location extension and the quadratic branch equation give an algebra of
dimension twelve after adjoining the independent absolute scale. -/
theorem branchSignTower_finrank
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
    (hL : Module.finrank F L = 6) (a Δ : L) :
    Module.finrank (RatFunc F) (AdjoinRoot (branchSignPolynomial a Δ)) = 12 := by
  rw [← Module.finrank_mul_finrank (RatFunc F) (RatFunc L)
    (AdjoinRoot (branchSignPolynomial a Δ)), RatFunc.finrank_ratFunc_ratFunc,
    hL, branchSignExtension_finrank]

end
end PierceLengthBound.FixedDividend
