/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Ideal.Nonunits

/-!
# Units detected by finite-dimensional residue points

For a finite-dimensional algebra over an algebraically closed field, an element
is a unit exactly when it does not vanish at any algebra homomorphism to the
base field. Nilpotents in the finite algebra are allowed.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- All closed points of a finite algebra over an algebraically closed field
are rational; nonvanishing at these points detects units. -/
theorem finite_algebra_isUnit_of_points {K R : Type*} [Field K] [IsAlgClosed K]
    [CommRing R] [Algebra K R] [Module.Finite K R] (r : R)
    (hr : ∀ φ : R →ₐ[K] K, φ r ≠ 0) : IsUnit r := by
  by_contra h
  obtain ⟨J, hJ, hrJ⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr h)
  let : J.IsMaximal := hJ
  let : Field (R ⧸ J) := Ideal.Quotient.field J
  have : Module.Finite K (R ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K J).toLinearMap
      Ideal.Quotient.mk_surjective
  let φ : (R ⧸ J) →ₐ[K] K := IsAlgClosed.lift
  apply hr (φ.comp (Ideal.Quotient.mkₐ K J))
  change φ (Ideal.Quotient.mk J r) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hrJ, map_zero]

end
end PierceLengthBound.FixedDividend
