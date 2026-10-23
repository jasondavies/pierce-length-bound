/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendChartHomogenization
public import PierceLengthBound.FixedDividendLocalizationParity
public import PierceLengthBound.FixedDividendLocalParity
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The norm residue along a degree-two infinity section

The square/fourth-power identity makes the norm a nonzero nilpotent residue
modulo the infinity coordinate.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- The norm has a nonzero nilpotent residue along infinity. It supplies the
nilpotent basis vector in every degree-two section. -/
theorem square_fourth_norm_residue {K R : Type*}
    [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    {A a r h δ : R} (hA : IsUnit A) (ha : IsUnit a) (hh : h ≠ 0)
    [Nontrivial (R ⧸ Ideal.span {h})]
    (hr : IsUnit (Ideal.Quotient.mk (Ideal.span {h}) r))
    (heq : A * h ^ 2 * r = a * δ ^ 4) :
    Ideal.Quotient.mk (Ideal.span {h}) δ ≠ 0 ∧
      IsNilpotent (Ideal.Quotient.mk (Ideal.span {h}) δ) := by
  let q := Ideal.Quotient.mk (Ideal.span {h})
  have hq : q h = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_singleton _))
  constructor
  · intro hz
    have hmem : δ ∈ (Ideal.span {h} : Ideal R) := Ideal.Quotient.eq_zero_iff_mem.mp hz
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hmem
    have he : h ^ 2 * (A * r) = h ^ 2 * (a * h ^ 2 * t ^ 4) := by
      rw [ht] at heq
      convert heq using 1 <;> ring
    have hc := mul_left_cancel₀ (pow_ne_zero 2 hh) he
    have hcq := congrArg q hc
    simp only [map_mul, map_pow, hq, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul] at hcq
    exact ((hA.map q).mul hr).ne_zero hcq
  · refine ⟨4, ?_⟩
    have ht := congrArg q heq
    simp only [map_mul, map_pow, hq, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul] at ht
    exact (ha.map q).mul_right_eq_zero.mp ht.symm

end
end PierceLengthBound.FixedDividend
