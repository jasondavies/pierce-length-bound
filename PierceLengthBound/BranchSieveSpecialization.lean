/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic

/-! Degree-preserving irreducible specialization proves generic irreducibility.
This algebraic criterion is used for the sextic location polynomial. It is separate from,
and does not imply, the arithmetic theorem counting reducible specializations. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

variable {R F : Type*} [CommRing R] [IsDomain R] [Field F]

/-- A primitive polynomial is irreducible if one specialization preserves its degree and
is irreducible. The specialization homomorphism need not be injective. -/
theorem primitive_irreducible_of_degree_preserving_specialization
    (φ : R →+* F) {p : R[X]} (hp : p.IsPrimitive)
    (hdegree : (p.map φ).natDegree = p.natDegree)
    (hirr : Irreducible (p.map φ)) : Irreducible p := by
  refine ⟨hirr.not_isUnit ∘ IsUnit.map (mapRingHom φ), fun a b hab ↦ ?_⟩
  have hm : p.map φ = a.map φ * b.map φ := by rw [hab, Polynomial.map_mul]
  have hma0 : a.map φ ≠ 0 := (mul_ne_zero_iff.mp (hm ▸ hirr.ne_zero)).1
  have hmb0 : b.map φ ≠ 0 := (mul_ne_zero_iff.mp (hm ▸ hirr.ne_zero)).2
  have ha0 : a ≠ 0 := by intro h; simp [h] at hma0
  have hb0 : b ≠ 0 := by intro h; simp [h] at hmb0
  have hsum : (a.map φ).natDegree + (b.map φ).natDegree = a.natDegree + b.natDegree := by
    rw [← natDegree_mul hma0 hmb0, ← hm, hdegree, hab, natDegree_mul ha0 hb0]
  have ha_le : (a.map φ).natDegree ≤ a.natDegree := natDegree_map_le
  have hb_le : (b.map φ).natDegree ≤ b.natDegree := natDegree_map_le
  have hunit : ∀ q : R[X], q.natDegree = 0 → q ∣ p → IsUnit q := by
    intro q hq hqp
    have hqC := eq_C_of_natDegree_eq_zero hq
    rw [hqC] at hqp ⊢
    exact isUnit_C.mpr (hp _ hqp)
  rcases hirr.isUnit_or_isUnit hm with hma | hmb
  · left
    apply hunit a _ ⟨b, hab⟩
    have := natDegree_eq_zero_of_isUnit hma
    omega
  · right
    apply hunit b _ ⟨a, hab.trans (mul_comm a b)⟩
    have := natDegree_eq_zero_of_isUnit hmb
    omega

/-- Even without primitivity, an irreducible specialization of full degree proves
irreducibility over the fraction field of the coefficient ring. -/
theorem fraction_irreducible_of_degree_preserving_specialization
    [NormalizedGCDMonoid R] (φ : R →+* F) {p : R[X]}
    (hdegree : (p.map φ).natDegree = p.natDegree)
    (hirr : Irreducible (p.map φ)) :
    Irreducible (p.map (algebraMap R (FractionRing R))) := by
  have he : p.map φ = C (φ p.content) * p.primPart.map φ := by
    conv_lhs => rw [p.eq_C_content_mul_primPart]
    simp only [Polynomial.map_mul, Polynomial.map_C]
  have hc : φ p.content ≠ 0 := by
    intro h
    apply hirr.ne_zero
    rw [he, h, C_0, zero_mul]
  have hu : IsUnit (C (φ p.content)) := isUnit_C.mpr (IsUnit.mk0 _ hc)
  have hprim_map : Irreducible (p.primPart.map φ) :=
    (irreducible_isUnit_mul hu).mp (he ▸ hirr)
  have hprim_degree : (p.primPart.map φ).natDegree = p.primPart.natDegree := by
    rw [natDegree_primPart]
    rw [he, natDegree_C_mul hc] at hdegree
    exact hdegree
  have hprim := primitive_irreducible_of_degree_preserving_specialization φ
    p.isPrimitive_primPart hprim_degree hprim_map
  have hprim_fraction : Irreducible (p.primPart.map (algebraMap R (FractionRing R))) :=
    p.isPrimitive_primPart.irreducible_iff_irreducible_map_fraction_map.mp hprim
  have hc0 : p.content ≠ 0 := by intro h; exact hc (by rw [h, map_zero])
  have hcF : algebraMap R (FractionRing R) p.content ≠ 0 :=
    by simpa only [map_zero] using (IsFractionRing.injective R (FractionRing R)).ne hc0
  have heF : p.map (algebraMap R (FractionRing R)) =
      C (algebraMap R (FractionRing R) p.content) *
        p.primPart.map (algebraMap R (FractionRing R)) := by
    conv_lhs => rw [p.eq_C_content_mul_primPart]
    simp only [Polynomial.map_mul, Polynomial.map_C]
  rw [heF]
  exact (irreducible_isUnit_mul (isUnit_C.mpr (IsUnit.mk0 _ hcF))).mpr hprim_fraction

end
end PierceLengthBound.FixedDividend
