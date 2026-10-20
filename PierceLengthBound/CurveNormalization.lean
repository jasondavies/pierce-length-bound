/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.Adjoin.Polynomial.Transcendental
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.CharP.Algebra

/-! Finite normalization for rational curve charts finite over a transcendental
parameter. The normalization is the integral closure in the chart's own
fraction field, with no assumed normality or smoothness of the original chart. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

attribute [local instance] FractionRing.liftAlgebra

/-- A finite rational curve algebra over a transcendental parameter has finite
Dedekind normalization in its own fraction field. -/
theorem finite_parameter_normalization {S : Type*} [CommRing S] [IsDomain S] [Algebra ℚ S]
    (w : S) (hw : Transcendental ℚ w) [Module.Finite (Algebra.adjoin ℚ {w}) S]
    (L : Type*) [Field L] [Algebra S L] [IsFractionRing S L] :
    IsDedekindDomain (integralClosure S L) ∧ Module.Finite S (integralClosure S L) := by
  let T := Algebra.adjoin ℚ ({w} : Set S)
  let C := integralClosure S L
  let : Fact (Transcendental ℚ w) := ⟨hw⟩
  let : IsIntegralClosure C T L :=
    ⟨Subtype.val_injective, fun {x} => ⟨fun hx => ⟨⟨x, hx.tower_top⟩, rfl⟩,
      fun ⟨y, hy⟩ => hy ▸ isIntegral_trans (R := T) (y : L) y.property⟩⟩
  let : FiniteDimensional (FractionRing T) (FractionRing S) := inferInstance
  let e₀ := (FractionRing.algEquiv S L).toLinearEquiv.restrictScalars T
  let e := e₀.extendScalarsOfIsLocalization (nonZeroDivisors T) (FractionRing T)
  let : FiniteDimensional (FractionRing T) L := Module.Finite.equiv e
  let : CharZero (FractionRing T) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (FractionRing T)).injective
  have hD : IsDedekindDomain C :=
    IsIntegralClosure.isDedekindDomain T (FractionRing T) L C
  let : Module.Finite T C :=
    IsIntegralClosure.finite T (FractionRing T) L C
  exact ⟨hD, Module.Finite.of_restrictScalars_finite T S C⟩

end
end PierceLengthBound.FixedDividend
