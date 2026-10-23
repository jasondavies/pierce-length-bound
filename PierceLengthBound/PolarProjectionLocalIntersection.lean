/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
public import Mathlib.RingTheory.AdjoinRoot

/-! Colength of a completed one-dimensional section from its first nonzero
coefficient. Applying this to the polar curve still requires constructing its
smooth local section and comparing its normalization branches. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- A nonzero formal power series over a field generates the same ideal as
the power of the parameter given by its order. -/
theorem formal_section_ideal_eq_parameter_power {K : Type*} [Field K]
    (f : PowerSeries K) (hf : f ≠ 0) :
    Ideal.span {f} = Ideal.span {PowerSeries.X ^ f.order.toNat} := by
  conv_lhs => rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := f)]
  exact Ideal.span_singleton_mul_right_unit
    (PowerSeries.isUnit_divided_by_X_pow_order hf) _

/-- The colength of a nonzero principal ideal in a formal disk is exactly
the order of its generator. This is the local intersection calculation after
one smooth local parameter has been eliminated. -/
theorem formal_section_colength {K : Type*} [Field K]
    (f : PowerSeries K) (hf : f ≠ 0) :
    Module.finrank K (PowerSeries K ⧸ Ideal.span {f}) = f.order.toNat := by
  let n := f.order.toNat
  have hd : (Polynomial.X ^ n : Polynomial K).IsDistinguishedAt (⊥ : Ideal K) := by
    constructor
    · constructor
      intro i hi
      have hin : i ≠ n := by simpa only [Polynomial.natDegree_X_pow] using ne_of_lt hi
      simp [Polynomial.coeff_X_pow, hin]
    · exact Polynomial.monic_X_pow n
  have he := hd.algEquivQuotient.toLinearEquiv.finrank_eq
  have hs : ((Polynomial.X ^ n : Polynomial K) : PowerSeries K) = PowerSeries.X ^ n := by
    simp
  rw [hs] at he
  rw [formal_section_ideal_eq_parameter_power f hf, ← he,
    finrank_quotient_span_eq_natDegree, Polynomial.natDegree_X_pow]

/-- A checked first nonzero coefficient determines the completed section's
colength, without an assumed multiplicity or normalization statement. -/
theorem formal_section_colength_of_coefficients {K : Type*} [Field K]
    (f : PowerSeries K) (n : ℕ)
    (hlower : ∀ j < n, PowerSeries.coeff j f = 0)
    (hfirst : PowerSeries.coeff n f ≠ 0) :
    Module.finrank K (PowerSeries K ⧸ Ideal.span {f}) = n := by
  have hf : f ≠ 0 := by intro h; simp [h] at hfirst
  have ho : f.order = n := PowerSeries.order_eq_nat.mpr ⟨hfirst, hlower⟩
  rw [formal_section_colength f hf, ho, ENat.toNat_natCast]

end
end PierceLengthBound.FixedDividend
