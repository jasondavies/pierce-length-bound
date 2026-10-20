/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchResidueComparison

/-! A nontrivial normalized order regular on a model has a nonzero prime center
on that model. Regularity extends to normalization. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- A normalized order regular on a fraction-field model has a center there.
The numerator of a uniformizer supplies a nonzero element of that center. -/
theorem regular_branch_center {R L : Type*} [CommRing R] [IsDomain R] [Field L] [Algebra R L]
    [IsFractionRing R L] (ν : AddValuation L (WithTop ℤ))
    (hR : ∀ r : R, 0 ≤ ν (algebraMap R L r)) (hπ : ∃ π : L, ν π = 1) :
    ∃ p : IsDedekindDomain.HeightOneSpectrum R,
      ∀ r : R, r ∈ p.asIdeal ↔ 0 < ν (algebraMap R L r) := by
  obtain ⟨π, hπ⟩ := hπ
  have hπ0 : π ≠ 0 := by intro h; simp [h] at hπ
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R π
  have ha : a ≠ 0 := by
    intro h
    rw [h, map_zero, zero_div] at hab
    exact hπ0 hab.symm
  have hb0 : algebraMap R L b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hmul := (div_eq_iff hb0).mp hab
  apply branch_center_exists ν hR ha
  rw [hmul, ν.map_mul, hπ]
  exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (hR b))

theorem regular_branch_realized {R L : Type*} [CommRing R] [IsDedekindDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (ν : AddValuation L (WithTop ℤ)) (hR : ∀ r : R, 0 ≤ ν (algebraMap R L r))
    (hπ : ∃ π : L, ν π = 1) :
    ∃ p : IsDedekindDomain.HeightOneSpectrum R, normalizedBranchOrder p L = ν := by
  obtain ⟨p, hp⟩ := regular_branch_center ν hR hπ
  exact ⟨p, centered_branch_order_eq p ν hR hp hπ⟩

theorem regular_normalization_branch_center {R L : Type*} [CommRing R] [IsDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (ν : AddValuation L (WithTop ℤ)) (hR : ∀ r : R, 0 ≤ ν (algebraMap R L r))
    (hπ : ∃ π : L, ν π = 1) :
    ∃ p : IsDedekindDomain.HeightOneSpectrum (integralClosure R L),
      ∀ r : integralClosure R L, r ∈ p.asIdeal ↔ 0 < ν (r : L) := by
  let C := integralClosure R L
  let : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension R L L C
  exact regular_branch_center ν (branch_order_nonnegative_on_normalization ν hR) hπ

end
end PierceLengthBound.FixedDividend
