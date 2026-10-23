/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Norm
public import Mathlib.RingTheory.Adjoin.Polynomial.Transcendental
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! A domain `S` finite over `K[w]`, `w` transcendental, has `dim_K S/(w)` equal to its rank
over `K[w]`. The integral closure of `S` in its fraction field has the same rank over `K[w]`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial Module

/-- A polynomial parameter fiber in a finite torsion-free algebra has dimension
equal to the rank over the parameter algebra. -/
theorem polynomial_parameter_fiber_finrank {K T S : Type*}
    [Field K] [CommRing T] [IsDomain T] [Algebra K T]
    [CommRing S] [IsDomain S] [Algebra K S] [Algebra T S] [IsScalarTower K T S]
    [FaithfulSMul T S] [Module.Finite T S] (e : K[X] ≃ₐ[K] T) :
    Module.finrank K (S ⧸ Ideal.span {algebraMap T S (e X)}) = Module.finrank T S := by
  let : Algebra K[X] T := e.toRingHom.toAlgebra
  let : Algebra K[X] S := ((algebraMap T S).comp e.toRingHom).toAlgebra
  let : IsScalarTower K[X] T S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower K K[X] S := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap K S c = algebraMap T S (e (Polynomial.C c))
    rw [show e (Polynomial.C c) = algebraMap K T c from e.commutes c]
    exact IsScalarTower.algebraMap_apply K T S c)
  let : Module.Finite K[X] T := e.toRingEquiv.finite
  let : Module.Finite K[X] S := Module.Finite.trans T S
  let : IsTorsionFree K[X] S := isTorsionFree_iff_algebraMap_injective.mpr
    ((FaithfulSMul.algebraMap_injective T S).comp e.injective)
  have hX : algebraMap K[X] S X = algebraMap T S (e X) := rfl
  have hX0 : algebraMap K[X] S X ≠ 0 := by
    change algebraMap T S (e X) ≠ 0
    simpa only [Function.comp_apply, map_zero] using
      ((FaithfulSMul.algebraMap_injective T S).comp e.injective).ne Polynomial.X_ne_zero
  calc
    Module.finrank K (S ⧸ Ideal.span {algebraMap T S (e X)}) = Module.finrank K[X] S := by
      rw [← hX, finrank_quotient_span_eq_natDegree_norm (Module.Free.chooseBasis K[X] S)
        hX0, Algebra.norm_algebraMap, natDegree_X_pow]
    _ = Module.finrank T S :=
      Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl S) rfl

/-- `dim_K S/(w) = rank_{K[w]} S` for a domain `S` finite over `K[w]`, `w` transcendental. -/
theorem parameter_fiber_finrank {K S : Type*} [Field K] [CommRing S] [IsDomain S]
    [Algebra K S] (w : S) (hw : Transcendental K w)
    [Module.Finite (Algebra.adjoin K {w}) S] :
    Module.finrank K (S ⧸ Ideal.span {w}) = Module.finrank (Algebra.adjoin K {w}) S := by
  have hh := polynomial_parameter_fiber_finrank (S := S)
    (Polynomial.algEquivOfTranscendental K w hw)
  have he : algebraMap (Algebra.adjoin K {w}) S
      (Polynomial.algEquivOfTranscendental K w hw X) = w := by
    change ((Polynomial.algEquivOfTranscendental K w hw X : Algebra.adjoin K {w}) : S) = w
    rw [Polynomial.algEquivOfTranscendental_apply_X]
  rwa [he] at hh

/-- The integral closure of `S` in its fraction field has the same rank over `K[w]` as `S`,
since it has rank one over `S`. -/
theorem normalization_parameter_rank {K S L : Type*}
    [Field K] [CommRing S] [IsDomain S] [Algebra K S]
    [Field L] [Algebra S L] [IsFractionRing S L] (w : S) :
    Module.finrank (Algebra.adjoin K {w}) (integralClosure S L) =
      Module.finrank (Algebra.adjoin K {w}) S := by
  let T := Algebra.adjoin K {w}
  let C := integralClosure S L
  let : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension S L L C
  have hr : Module.finrank S C = 1 := by
    rw [← IsFractionRing.finrank_eq S L C L, Module.finrank_self]
  rw [← Module.finrank_mul_finrank' (R := T) (S := S) C, hr, mul_one]

end
end PierceLengthBound.FixedDividend
