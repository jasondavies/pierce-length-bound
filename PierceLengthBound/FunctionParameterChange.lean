/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FunctionParameterNormalization
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! Changing the parameter of a one-variable function field. A finite extension
of K(t) is finite over K(x) for every transcendental x in that extension. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin

/-- Finiteness over any transcendental parameter follows from one known finite
parameter; it need not be supplied separately for each rational function. -/
theorem finite_over_parameter_of_trdeg_le_one {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] (hdim : Algebra.trdeg K L ≤ 1)
    (x : L) (hx : Transcendental K x) : FiniteDimensional K⟮x⟯ L := by
  let : Algebra.EssFiniteType K⟮x⟯ L := Algebra.EssFiniteType.of_comp K K⟮x⟯ L
  have hind : AlgebraicIndependent K (fun _ : Unit => x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  have hb : IsTranscendenceBasis K (fun _ : Unit => x) :=
    hind.isTranscendenceBasis_of_lift_trdeg_le_of_finite (by
      simpa using hdim)
  let : Algebra.IsAlgebraic K⟮x⟯ L := by
    have hh := hb.isAlgebraic_field
    change Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range (fun _ : Unit => x))) L at hh
    rw [Set.range_const] at hh
    exact hh
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

/-- The fraction field of an affine domain finite over K[t] is finite over
K(x) for every transcendental rational function x. -/
theorem finite_fraction_field_over_function {K S L : Type*} [Field K]
    [CommRing S] [IsDomain S] [Algebra K S]
    [Field L] [Algebra K L] [Algebra S L] [IsScalarTower K S L] [IsFractionRing S L]
    (t : S) (ht : Transcendental K t) [Module.Finite (Algebra.adjoin K {t}) S]
    (x : L) (hx : Transcendental K x) : FiniteDimensional K⟮x⟯ L := by
  let T := Algebra.adjoin K {t}
  let : Algebra.IsAlgebraic S L := IsLocalization.isAlgebraic L (nonZeroDivisors S)
  let : Algebra.IsAlgebraic T L := Algebra.IsAlgebraic.trans T S L
  have hT : Algebra.trdeg K T = 1 := by
    simpa using (Polynomial.algEquivOfTranscendental K t ht).lift_trdeg_eq.symm
  have hL : Algebra.trdeg K L = 1 := by
    have hh := lift_trdeg_add_eq K T L
    simpa [hT, trdeg_eq_zero (R := T) (A := L)] using hh.symm
  let : Algebra.FiniteType K S := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType K T) (inferInstance : Algebra.FiniteType T S)
  let : Algebra.EssFiniteType S L := .of_isLocalization L (nonZeroDivisors S)
  let : Algebra.EssFiniteType K L := Algebra.EssFiniteType.comp K S L
  exact finite_over_parameter_of_trdeg_le_one hL.le x hx

/-- A nonzero function that vanishes under a ground-field point evaluation is
transcendental. This applies to the curvature combination chosen at an actual
orbit point. -/
theorem transcendental_of_nonzero_point_zero {K R : Type*} [Field K]
    [CommRing R] [IsDomain R] [Algebra K R]
    (φ : R →ₐ[K] K) {x : R} (hx : x ≠ 0) (hzero : φ x = 0) :
    Transcendental K x := by
  intro h
  have hu := (h.isIntegral.isUnit hx).map φ.toRingHom
  change IsUnit (φ x) at hu
  rw [hzero] at hu
  exact not_isUnit_zero hu

end
end PierceLengthBound.FixedDividend
