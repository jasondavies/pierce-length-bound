/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveNestedCoordinates
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic

/-! Passing the generic irreducibility of an integral parameter polynomial
to its rational bivariate equation. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial
open scoped nonZeroDivisors
attribute [local instance] Polynomial.algebra

instance branchIntegerPolynomial_ratFunc_fractionRing :
    IsFractionRing ℤ[X] (RatFunc ℚ) := by
  let : IsLocalization ((nonZeroDivisors ℤ).map Polynomial.C) ℚ[X] :=
    Polynomial.isLocalization _ _
  have h := IsLocalization.localization_localization_isLocalization_of_has_all_units
    ((nonZeroDivisors ℤ).map Polynomial.C) (nonZeroDivisors ℚ[X]) (RatFunc ℚ)
    (fun _ hx => hx.mem_nonZeroDivisors)
  convert h using 1
  ext x
  simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  change x ≠ 0 ↔ x.map (algebraMap ℤ ℚ) ≠ 0
  simpa only [Polynomial.map_zero] using
    ((Polynomial.map_injective (algebraMap ℤ ℚ)
      (IsFractionRing.injective _ _)).ne_iff (x := x) (y := 0)).symm

theorem branch_rational_nested_irreducible {F : Type*} [Field F]
    [Algebra ℤ[X] F] [IsFractionRing ℤ[X] F]
    (p : ℤ[X][X]) (hp : p.Monic)
    (hir : Irreducible (p.map (algebraMap ℤ[X] F))) :
    Irreducible (CCDN.bivariateMap (Int.castRingHom ℚ) p) := by
  let e := IsLocalization.algEquiv (nonZeroDivisors ℤ[X]) F (RatFunc ℚ)
  have he : e.toRingHom.comp (algebraMap ℤ[X] F) = algebraMap ℤ[X] (RatFunc ℚ) :=
    e.toAlgHom.comp_algebraMap
  have hr : Irreducible (p.map (algebraMap ℤ[X] (RatFunc ℚ))) := by
    rw [← he, ← Polynomial.map_map]
    exact (MulEquiv.irreducible_iff (f := Polynomial.mapEquiv e.toRingEquiv)).mpr hir
  have hmonic := hp.map (Polynomial.mapRingHom (Int.castRingHom ℚ))
  apply (hmonic.irreducible_iff_irreducible_map_fraction_map (K := RatFunc ℚ)).mpr
  rw [Polynomial.map_map]
  change Irreducible (p.map ((algebraMap ℚ[X] (RatFunc ℚ)).comp (algebraMap ℤ[X] ℚ[X])))
  rwa [← IsScalarTower.algebraMap_eq]

end
end PierceLengthBound.FixedDividend
