/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FunctionParameterNormalization
public import Mathlib.RingTheory.Valuation.Integral

/-! Extending regular branch orders to integral closures and constructing their
centers. This is the first step in identifying branches on different normalizations. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- Integrality cannot introduce a pole at a branch where all base-ring
elements are regular. -/
theorem branch_order_nonnegative_of_integral {R L : Type*} [CommRing R]
    [Field L] [Algebra R L] (ν : AddValuation L (WithTop ℤ))
    (hR : ∀ r : R, 0 ≤ ν (algebraMap R L r)) {x : L} (hx : IsIntegral R x) :
    0 ≤ ν x := by
  let v := ν.toValuation
  let f : R →+* v.integer := (algebraMap R L).codRestrict v.integer hR
  let : Algebra R v.integer := f.toAlgebra
  let : IsScalarTower R v.integer L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact (Valuation.integer.integers v).isIntegral_iff_v_le_one.mp hx.tower_top

theorem branch_order_nonnegative_on_normalization {R L : Type*} [CommRing R]
    [Field L] [Algebra R L] (ν : AddValuation L (WithTop ℤ))
    (hR : ∀ r : R, 0 ≤ ν (algebraMap R L r)) (x : integralClosure R L) :
    0 ≤ ν (x : L) :=
  branch_order_nonnegative_of_integral ν hR x.property

/-- A regular branch order defines a map into its valuation ring. -/
def branchValuationMap {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (ν : AddValuation L (WithTop ℤ)) (hR : ∀ r : R, 0 ≤ ν (algebraMap R L r)) :
    R →+* ν.toValuation.valuationSubring :=
  (algebraMap R L).codRestrict ν.toValuation.valuationSubring.toSubring hR

/-- The center consists exactly of the base-ring elements with positive order. -/
def branchCenterIdeal {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (ν : AddValuation L (WithTop ℤ)) (hR : ∀ r : R, 0 ≤ ν (algebraMap R L r)) : Ideal R :=
  (IsLocalRing.maximalIdeal ν.toValuation.valuationSubring).comap (branchValuationMap ν hR)

theorem mem_branchCenterIdeal {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (ν : AddValuation L (WithTop ℤ)) (hR : ∀ r : R, 0 ≤ ν (algebraMap R L r)) (r : R) :
    r ∈ branchCenterIdeal ν hR ↔ 0 < ν (algebraMap R L r) := by
  change branchValuationMap ν hR r ∈ IsLocalRing.maximalIdeal ν.toValuation.valuationSubring ↔ _
  exact ν.toValuation.mem_maximalIdeal_iff

theorem branchCenterIdeal_isPrime {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (ν : AddValuation L (WithTop ℤ)) (hR : ∀ r : R, 0 ≤ ν (algebraMap R L r)) :
    (branchCenterIdeal ν hR).IsPrime :=
  Ideal.IsPrime.comap (branchValuationMap ν hR)

theorem branch_center_exists {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (ν : AddValuation L (WithTop ℤ)) (hR : ∀ r : R, 0 ≤ ν (algebraMap R L r))
    {x : R} (hx : x ≠ 0) (hpos : 0 < ν (algebraMap R L x)) :
    ∃ p : IsDedekindDomain.HeightOneSpectrum R,
      ∀ r : R, r ∈ p.asIdeal ↔ 0 < ν (algebraMap R L r) := by
  have hp0 : branchCenterIdeal ν hR ≠ ⊥ := by
    intro h
    have hm := (mem_branchCenterIdeal ν hR x).mpr hpos
    rw [h, Ideal.mem_bot] at hm
    exact hx hm
  exact ⟨⟨branchCenterIdeal ν hR, branchCenterIdeal_isPrime ν hR, hp0⟩,
    mem_branchCenterIdeal ν hR⟩

theorem branch_order_nonnegative_on_parameter_algebra {K L : Type*} [Field K] [CommRing L]
    [Algebra K L] (ν : AddValuation L (WithTop ℤ))
    (hK : ∀ c : K, 0 ≤ ν (algebraMap K L c)) {x : L} (hx : 0 ≤ ν x)
    (r : Algebra.adjoin K {x}) : 0 ≤ ν (r : L) := by
  apply Algebra.adjoin_induction (p := fun y _ => 0 ≤ ν y) _ _ _ _ r.property
  · intro y hy
    have he : y = x := hy
    simpa only [he] using hx
  · exact hK
  · intro a b _ _ ha hb
    exact (le_min ha hb).trans (ν.map_add a b)
  · intro a b _ _ ha hb
    rw [ν.map_mul]
    exact add_nonneg ha hb

/-- On a finite parameter algebra, regularity of the parameter forces
regularity of every element. This applies to both affine and infinity charts. -/
theorem branch_order_nonnegative_of_finite_parameter {K R L : Type*}
    [Field K] [CommRing R] [Algebra K R] [Field L]
    [Algebra K L] [Algebra R L] [IsScalarTower K R L]
    (t : R) [Module.Finite (Algebra.adjoin K {t}) R]
    (ν : AddValuation L (WithTop ℤ))
    (hK : ∀ c : K, 0 ≤ ν (algebraMap K L c))
    (ht : 0 ≤ ν (algebraMap R L t)) (r : R) : 0 ≤ ν (algebraMap R L r) := by
  let T := Algebra.adjoin K {t}
  let μ := ν.comap (algebraMap R L)
  have hT (a : T) : 0 ≤ ν (algebraMap T L a) := by
    have hK' (c : K) : 0 ≤ μ (algebraMap K R c) := by
      change 0 ≤ ν (algebraMap R L (algebraMap K R c))
      rw [← IsScalarTower.algebraMap_apply K R L]
      exact hK c
    exact branch_order_nonnegative_on_parameter_algebra μ hK' ht a
  apply branch_order_nonnegative_of_integral ν hT
  exact (Algebra.IsIntegral.isIntegral (R := T) r).algebraMap

/-- Any branch where the function has a zero has a center on the function's
parameter normalization, and that center lies in its zero fiber. -/
theorem function_parameter_center {L : Type*} [Field L] [Algebra ℚ L]
    (ν : AddValuation L (WithTop ℤ)) (hQ : ∀ c : ℚ, 0 ≤ ν (algebraMap ℚ L c))
    {x : L} (hx : x ≠ 0) (hpos : 0 < ν x) :
    ∃ q : IsDedekindDomain.HeightOneSpectrum (functionParameterNormalization x),
      (∀ r : functionParameterNormalization x, r ∈ q.asIdeal ↔ 0 < ν (r : L)) ∧
      functionParameterElement x ∈ q.asIdeal := by
  let C := functionParameterNormalization x
  have hC (r : C) : 0 ≤ ν (r : L) :=
    branch_order_nonnegative_on_normalization ν
      (branch_order_nonnegative_on_parameter_algebra ν hQ hpos.le) r
  have hw : functionParameterElement x ≠ 0 := fun h =>
    hx (congrArg (fun r : C => (r : L)) h)
  obtain ⟨q, hq⟩ := branch_center_exists ν hC hw hpos
  exact ⟨q, hq, (hq _).mpr hpos⟩

end
end PierceLengthBound.FixedDividend
