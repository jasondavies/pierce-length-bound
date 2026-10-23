/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import PierceLengthBound.PolarProjectionLocalCenter
public import PierceLengthBound.AffineNormalization
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-! Finite normalization persists on the local ring of an affine component. -/
@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- Localizing an affine ring with finite Dedekind normalization gives
finite Dedekind normalization in the same fraction field. -/
theorem finite_normalization_localization {A R L : Type*}
    [CommRing A] [IsDomain A] [CommRing R] [IsDomain R]
    [Field L] [Algebra A R] [Algebra A L] [IsFractionRing A L]
    [Algebra R L] [IsScalarTower A R L]
    (M : Submonoid A) (hM : M ≤ nonZeroDivisors A) [IsLocalization M R]
    [IsDedekindDomain (integralClosure A L)]
    [Module.Finite A (integralClosure A L)] :
    IsDedekindDomain (integralClosure R L) ∧ Module.Finite R (integralClosure R L) := by
  let C := integralClosure A L
  let S := integralClosure R L
  let φ : C →+* S :=
    { toFun := fun x => ⟨x, x.property.tower_top⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let : Algebra C S := φ.toAlgebra
  let : IsScalarTower C S L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower A C S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hL : Algebra.algebraMapSubmonoid L M ≤ IsUnit.submonoid L := by
    rintro _ ⟨a, ha, rfl⟩
    exact isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff (algebraMap A L) (IsFractionRing.injective A L)).mpr
        (nonZeroDivisors.ne_zero (hM ha)))
  let : IsLocalization (Algebra.algebraMapSubmonoid L M) L :=
    IsLocalization.of_le_isUnit hL
  let : IsLocalization (Algebra.algebraMapSubmonoid C M) S :=
    IsLocalization.integralClosure (S := L) (Rf := R) (Sf := L) M
  have hC : Algebra.algebraMapSubmonoid C M ≤ nonZeroDivisors C := by
    rintro _ ⟨a, ha, rfl⟩
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro h
    have he := congrArg (algebraMap C L) h
    rw [← IsScalarTower.algebraMap_apply A C L, map_zero] at he
    exact nonZeroDivisors.ne_zero (hM ha) ((IsFractionRing.injective A L)
      (he.trans (map_zero _).symm))
  exact ⟨IsLocalization.isDedekindDomain C hC S,
    Module.Finite.of_isLocalization A C M⟩

/-- The local component ring has dimension at most one whenever the
affine ring is finite over one transcendental coordinate. -/
theorem finite_parameter_local_dimension {A R : Type*}
    [CommRing A] [IsDomain A] [Algebra ℚ A]
    (w : A) (hw : Transcendental ℚ w) [Module.Finite (Algebra.adjoin ℚ {w}) A]
    [CommRing R] [Algebra A R]
    (M : Submonoid A) (hM : M ≤ nonZeroDivisors A) [IsLocalization M R] :
    Ring.KrullDimLE 1 R := by
  let : Fact (Transcendental ℚ w) := ⟨hw⟩
  let : Ring.DimensionLEOne A := Ring.DimensionLEOne.of_isIntegral (Algebra.adjoin ℚ {w}) A
  let : Ring.DimensionLEOne R := Ring.DimensionLEOne.localization R hM
  infer_instance

end
end PierceLengthBound.FixedDividend
