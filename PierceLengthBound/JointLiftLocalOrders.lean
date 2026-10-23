/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import PierceLengthBound.IntegralLiftResolvent

/-! Discrete valuation calculations for the joint lift. These lemmas use actual
additive valuations, with infinity for the zero function. Constructing the
valuations on normalized components and summing their degrees is separate. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

variable {K : Type*} [Field K]

lemma discrete_order_mul_ge (v : AddValuation K (WithTop ℤ)) {x y : K} {r s : ℤ}
    (hx : (r : WithTop ℤ) ≤ v x) (hy : (s : WithTop ℤ) ≤ v y) :
    ((r + s : ℤ) : WithTop ℤ) ≤ v (x * y) := by
  rw [v.map_mul, WithTop.coe_add]
  exact add_le_add hx hy

lemma discrete_order_div_ge (v : AddValuation K (WithTop ℤ)) {x y : K} {r s : ℤ}
    (hx : (r : WithTop ℤ) ≤ v x) (hy : v y = (s : WithTop ℤ)) :
    ((r - s : ℤ) : WithTop ℤ) ≤ v (x / y) := by
  rw [div_eq_mul_inv]
  have hv : v y⁻¹ = ((-s : ℤ) : WithTop ℤ) := by
    rw [v.map_inv, hy, WithTop.LinearOrderedAddCommGroup.coe_neg]
  simpa only [sub_eq_add_neg] using discrete_order_mul_ge v hx hv.ge

/-- Noncollision of the leading nodes makes the cubic term dominate the
quadratic remainder in the raw rank-three Hankel determinant. -/
theorem rawHankelThree_discrete_order (v : AddValuation K (WithTop ℤ))
    {k0 k1 k2 : K} {e : ℤ} (he : 0 < e)
    (h0 : v k0 = ((-e : ℤ) : WithTop ℤ))
    (h1 : v k1 = ((-e : ℤ) : WithTop ℤ))
    (h01 : v (k0 + k1) = ((-e : ℤ) : WithTop ℤ))
    (h2 : ((-e : ℤ) : WithTop ℤ) ≤ v k2) :
    v (rawHankelThree k0 k1 k2) = ((-3 * e : ℤ) : WithTop ℤ) := by
  have hlead : v (k0 * k1 * (k0 + k1)) = ((-3 * e : ℤ) : WithTop ℤ) := by
    rw [v.map_mul, v.map_mul, h0, h1, h01]
    norm_cast
    omega
  have hlow : ((-2 * e : ℤ) : WithTop ℤ) ≤ v (k0 * k2 - k1 ^ 2) := by
    apply v.map_le_sub
    · convert discrete_order_mul_ge v h0.ge h2 using 1; norm_cast; omega
    · rw [pow_two, v.map_mul, h1]
      norm_cast
      omega
  have hlt : v (k0 * k1 * (k0 + k1)) < v (k0 * k2 - k1 ^ 2) := by
    rw [hlead]
    exact lt_of_lt_of_le (by exact_mod_cast (show -3 * e < -2 * e by omega)) hlow
  rw [rawHankelThree_leading, show
    k0 * k1 * (k0 + k1) + k0 * k2 - k1 ^ 2 =
      k0 * k1 * (k0 + k1) + (k0 * k2 - k1 ^ 2) by ring,
    v.map_add_eq_of_lt_left hlt, hlead]

/-- The resolvent numerator has a unique lowest-order term. For old infinity
multiplicity `e = 2t`, the reconstructed I3 has exact zero order `3t`. -/
theorem resolvent_discrete_order (v : AddValuation K (WithTop ℤ))
    {a q p3 H3 M P : K} {t : ℤ} (ht : 0 < t)
    (ha : v a = 0) (hq : v q = ((-3 * t : ℤ) : WithTop ℤ))
    (hp3 : ((-2 * t : ℤ) : WithTop ℤ) ≤ v p3)
    (hH3 : v H3 = ((-6 * t : ℤ) : WithTop ℤ))
    (hM : ((-8 * t : ℤ) : WithTop ℤ) ≤ v M)
    (hP : v P = ((-12 * t : ℤ) : WithTop ℤ)) :
    v (a * ((q - p3) * H3 - M) / P) = ((3 * t : ℤ) : WithTop ℤ) := by
  have hqp : v (q - p3) = ((-3 * t : ℤ) : WithTop ℤ) := by
    rw [v.map_sub_eq_of_lt_left, hq]
    rw [hq]
    exact lt_of_lt_of_le (by exact_mod_cast (show -3 * t < -2 * t by omega)) hp3
  have hprod : v ((q - p3) * H3) = ((-9 * t : ℤ) : WithTop ℤ) := by
    rw [v.map_mul, hqp, hH3]
    norm_cast
    omega
  have hnum : v ((q - p3) * H3 - M) = ((-9 * t : ℤ) : WithTop ℤ) := by
    rw [v.map_sub_eq_of_lt_left, hprod]
    rw [hprod]
    exact lt_of_lt_of_le (by exact_mod_cast (show -9 * t < -8 * t by omega)) hM
  rw [v.map_div, v.map_mul, ha, zero_add, hnum, hP]
  norm_cast
  omega

/-- Both leading curvature coordinates have zero order `3t`; cancellation in
the middle coordinate can only increase its order. -/
theorem curvature_discrete_orders (v : AddValuation K (WithTop ℤ))
    {A B0 B1 E0 k0 k1 k2 : K} {t : ℤ} (ht : 0 < t)
    (hA : v A = 0) (hB0 : v B0 = ((-6 * t : ℤ) : WithTop ℤ))
    (hB1 : v B1 = ((-6 * t : ℤ) : WithTop ℤ))
    (hE0 : v E0 = ((3 * t : ℤ) : WithTop ℤ))
    (hk0 : ((-2 * t : ℤ) : WithTop ℤ) ≤ v k0)
    (hk1 : v k1 = ((-2 * t : ℤ) : WithTop ℤ))
    (hk2 : ((-2 * t : ℤ) : WithTop ℤ) ≤ v k2) :
    let E12 := (B1 * E0 - A * k1) / B0
    let E02 := (k0 * E12 + k2 * E0) / k1
    v E12 = ((3 * t : ℤ) : WithTop ℤ) ∧
      ((3 * t : ℤ) : WithTop ℤ) ≤ v (-E02) ∧
      v E0 = ((3 * t : ℤ) : WithTop ℤ) := by
  dsimp only
  have hBE : v (B1 * E0) = ((-3 * t : ℤ) : WithTop ℤ) := by
    rw [v.map_mul, hB1, hE0]
    norm_cast
    omega
  have hAk : v (A * k1) = ((-2 * t : ℤ) : WithTop ℤ) := by
    rw [v.map_mul, hA, zero_add, hk1]
  have hnum : v (B1 * E0 - A * k1) = ((-3 * t : ℤ) : WithTop ℤ) := by
    rw [v.map_sub_eq_of_lt_left, hBE]
    rw [hBE, hAk]
    exact_mod_cast (show -3 * t < -2 * t by omega)
  have hE12 : v ((B1 * E0 - A * k1) / B0) = ((3 * t : ℤ) : WithTop ℤ) := by
    rw [v.map_div, hnum, hB0]
    norm_cast
    omega
  refine ⟨hE12, ?_, hE0⟩
  rw [v.map_neg]
  have hsum : (t : WithTop ℤ) ≤ v (k0 * ((B1 * E0 - A * k1) / B0) + k2 * E0) := by
    apply v.map_le_add
    · convert discrete_order_mul_ge v hk0 hE12.ge using 1; norm_cast; omega
    · convert discrete_order_mul_ge v hk2 hE0.ge using 1; norm_cast; omega
  convert discrete_order_div_ge v hsum hk1 using 1; norm_cast; omega

end
end PierceLengthBound.FixedDividend
