/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendFiniteSectionParity
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Parity after inverting a unit on the infinity section

Localizing at an element invertible on a finite section preserves that
section. Thus the square/fourth-power parity argument needs the resultant to be
invertible only modulo the infinity equation.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- Localization at an element invertible modulo an ideal preserves the quotient. -/
def quotientEquivAwayOfUnit {K R S : Type*} [Field K] [CommRing R] [CommRing S]
    [Algebra K R] [Algebra R S] [Algebra K S] [IsScalarTower K R S]
    (J : Ideal R) (r : R) [IsLocalization.Away r S]
    (hr : IsUnit (Ideal.Quotient.mk J r)) :
    (R ⧸ J) ≃ₐ[K] (S ⧸ J.map (algebraMap R S)) := by
  have hunit : Algebra.algebraMapSubmonoid (R ⧸ J) (Submonoid.powers r) ≤
      IsUnit.submonoid (R ⧸ J) := by
    rintro x ⟨y, ⟨n, rfl⟩, rfl⟩
    change IsUnit (Ideal.Quotient.mk J (r ^ n))
    simpa only [map_pow] using hr.pow n
  let e := IsLocalization.atUnits (R ⧸ J) _
    (S := S ⧸ J.map (algebraMap R S)) hunit
  exact AlgEquiv.ofBijective
    (Ideal.quotientMapₐ (J.map (algebraMap R S))
      (IsScalarTower.toAlgHom K R S) Ideal.le_comap_map) e.bijective

/-- If `A h² r = a δ⁴` with `A`, `a` units and `r` nonzero and a unit modulo `h`, the
finite section cut out by `h` has even dimension. -/
theorem finite_infinity_section_even_of_unit_modulo {K R : Type*}
    [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    {A a r h δ : R} (hA : IsUnit A) (ha : IsUnit a)
    (hr : IsUnit (Ideal.Quotient.mk (Ideal.span {h}) r)) (hr0 : r ≠ 0)
    (hh : h ≠ 0) [Module.Finite K (R ⧸ Ideal.span {h})]
    (heq : A * h ^ 2 * r = a * δ ^ 4) :
    Even (Module.finrank K (R ⧸ Ideal.span {h})) := by
  let S := Localization (Submonoid.powers r)
  have hregular : Submonoid.powers r ≤ nonZeroDivisors R := by
    rintro x ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hr0)
  let : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hregular
  let f := algebraMap R S
  have hf : Function.Injective f := IsLocalization.injective S hregular
  let e := quotientEquivAwayOfUnit (K := K) (S := S) (Ideal.span {h}) r hr
  have hi : (Ideal.span {h} : Ideal R).map f = Ideal.span {f h} := by
    rw [Ideal.map_span, Set.image_singleton]
  let : Module.Finite K (S ⧸ (Ideal.span {h} : Ideal R).map f) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  have hfin : Module.Finite K (S ⧸ Ideal.span {f h}) := hi ▸ inferInstance
  have hp : Even (Module.finrank K (S ⧸ Ideal.span {f h})) := by
    apply finite_infinity_section_even (hA.map f) (ha.map f)
      (IsLocalization.Away.algebraMap_isUnit r)
      (fun hz => hh (hf (by simpa [f] using hz)))
    simpa only [map_mul, map_pow] using congrArg f heq
  rw [← hi] at hp
  rw [e.toLinearEquiv.finrank_eq]
  exact hp

end
end PierceLengthBound.FixedDividend
