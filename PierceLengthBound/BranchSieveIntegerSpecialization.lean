/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveIntegralFactorWitness
public import PierceLengthBound.BranchSieveReductionMap
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.Tactic

/-! A reducible integer specialization supplies an integral coefficient root.
The integral closure of `ℤ[X]` in a splitting field serves as the splitting
algebra, and the reduction map over `X = t` comes from lying-over
(`branch_exists_integer_reduction`). -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

/-- A monic polynomial that splits over `L` splits over the integral
closure of `R` in `L`. -/
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

open scoped Polynomial.Bivariate

variable {F L : Type*} [Field F] [Algebra ℤ[X] F] [IsFractionRing ℤ[X] F]
  [Field L] [Algebra ℤ[X] L] [Algebra F L] [IsScalarTower ℤ[X] F L]
  [FaithfulSMul ℤ[X] L]

/-- If `p(t, Y)` has a monic factor `q` of degree strictly between zero and
`deg p`, then some coefficient of a monic factor `q₀` of `p` over the integral
closure has a monic minimal polynomial over `ℤ[X]`, irreducible over the
fraction field and of degree at least two, which vanishes at `(t, q.coeff j)`. -/
theorem branch_integer_specialization_witness (p : ℤ[X][Y])
    (hp : p.Monic) (hir : Irreducible (p.map (algebraMap ℤ[X] F)))
    (hsplit : (p.map (algebraMap ℤ[X] L)).Splits)
    (t : ℤ) (q : ℤ[X]) (hq : q.Monic) (hdiv : q ∣ p.map (evalRingHom t))
    (hqpos : 0 < q.natDegree) (hqlt : q.natDegree < p.natDegree) :
    ∃ q₀ : Polynomial (integralClosure ℤ[X] L),
      q₀.Monic ∧ q₀ ∣ p.map (algebraMap ℤ[X] (integralClosure ℤ[X] L)) ∧
      ∃ j : ℕ, (minpoly ℤ[X] (q₀.coeff j)).Monic ∧
        Irreducible ((minpoly ℤ[X] (q₀.coeff j)).map (algebraMap ℤ[X] F)) ∧
        2 ≤ (minpoly ℤ[X] (q₀.coeff j)).natDegree ∧
        (minpoly ℤ[X] (q₀.coeff j)).evalEval t (q.coeff j) = 0 := by
  let S := integralClosure ℤ[X] L
  let : FaithfulSMul ℤ[X] S := (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
    intro a b hab
    apply FaithfulSMul.algebraMap_injective ℤ[X] L
    exact congrArg Subtype.val hab)
  obtain ⟨Q, hQ, hchar, hφ⟩ := branch_exists_integer_reduction S t
  let : Q.IsPrime := hQ
  let : CharZero (S ⧸ Q) := hchar
  let φ := Ideal.Quotient.mk Q
  let qK := q.map (Int.castRingHom (S ⧸ Q))
  have hpsplit := branch_monic_splits_integralClosure p hp hsplit
  have hqK : qK.Monic := hq.map _
  have hqKdiv : qK ∣ (p.map (algebraMap ℤ[X] S)).map φ := by
    have hh := Polynomial.map_dvd (Int.castRingHom (S ⧸ Q)) hdiv
    simpa only [qK, φ, Polynomial.map_map, hφ] using hh
  obtain ⟨q₀, hq₀, hq₀div, hq₀map, j, hfmonic, hfir, hfdeg, hfroot⟩ :=
    branch_integral_factor_witness (L := L) φ hp hir hpsplit hqK hqKdiv
      (by simpa only [qK, hq.natDegree_map] using hqpos)
      (by simpa only [qK, hq.natDegree_map] using hqlt)
  refine ⟨q₀, hq₀, hq₀div, j, hfmonic, hfir, hfdeg, ?_⟩
  have hroot : ((minpoly ℤ[X] (q₀.coeff j)).map (evalRingHom t)).eval (q.coeff j) = 0 := by
    have hzero := hfroot
    simp only [qK, Polynomial.coeff_map, φ, hφ] at hzero
    rw [← Polynomial.eval₂_map, Polynomial.eval₂_at_apply] at hzero
    exact (Int.castRingHom (S ⧸ Q)).injective_int (by simpa only [map_zero] using hzero)
  simpa only [Polynomial.eval_map, Polynomial.eval₂_evalRingHom] using hroot

end
end PierceLengthBound.FixedDividend
