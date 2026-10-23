/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftResolvent

/-! Degree calculations for the resolvent of the integral lift along a quadratic
parametrization: the mixed raw minor has degree at most eight, the raw rank-three determinant
has degree six when the leading gap coefficients are suitably nonzero, and the resolvent
numerator `(q - p₃) H₃ - J` has degree nine when `q` is cubic. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Polynomial

/-- Quadratic gap coordinates bound the mixed raw minor's parameter degree by eight. -/
theorem rawHankelMixed_parabola_degree {K : Type*} [Field K]
    (k0 k1 k2 k3 : K[X]) (h0 : k0.natDegree ≤ 2) (h1 : k1.natDegree ≤ 2)
    (h2 : k2.natDegree ≤ 2) (h3 : k3.natDegree ≤ 2) :
    (rawHankelMixed k0 k1 k2 k3).natDegree ≤ 8 := by
  unfold rawHankelMixed
  compute_degree
  omega

/-- If `k₀`, `k₁` and `k₀ + k₁` have degree two and `k₂` degree at most two, the raw rank-three
determinant has degree six; its terms other than `k₀k₁(k₀ + k₁)` have degree at most four. -/
theorem rawHankelThree_parabola_degree {K : Type*} [Field K]
    (k0 k1 k2 : K[X]) (h0 : k0.natDegree = 2) (h1 : k1.natDegree = 2)
    (h2 : k2.natDegree ≤ 2) (hs : (k0 + k1).natDegree = 2) :
    (rawHankelThree k0 k1 k2).natDegree = 6 := by
  have hn0 : k0 ≠ 0 := ne_zero_of_natDegree_gt (show 0 < k0.natDegree by omega)
  have hn1 : k1 ≠ 0 := ne_zero_of_natDegree_gt (show 0 < k1.natDegree by omega)
  have hns : k0 + k1 ≠ 0 := ne_zero_of_natDegree_gt (show 0 < (k0 + k1).natDegree by omega)
  have hlead : (k0 * k1 * (k0 + k1)).natDegree = 6 := by
    rw [natDegree_mul (mul_ne_zero hn0 hn1) hns, natDegree_mul hn0 hn1, h0, h1, hs]
  have hlow : (k0 * k2 - k1 ^ 2).natDegree ≤ 4 := by
    compute_degree
    omega
  have he : rawHankelThree k0 k1 k2 = k0 * k1 * (k0 + k1) +
      (k0 * k2 - k1 ^ 2) := by rw [rawHankelThree_leading]; ring
  rw [he, natDegree_add_eq_left_of_natDegree_lt (by omega), hlead]

/-- For cubic `q`, `deg p₃ ≤ 2`, `deg H₃ = 6` and `deg J ≤ 8`, the resolvent numerator
`(q - p₃) H₃ - J` has degree nine. -/
theorem integralLift_parabola_numerator_degree {K : Type*} [Field K]
    (q p3 H3 J : K[X]) (hq : q.natDegree = 3) (hp : p3.natDegree ≤ 2)
    (hH : H3.natDegree = 6) (hJ : J.natDegree ≤ 8) :
    ((q - p3) * H3 - J).natDegree = 9 := by
  have hqp : (q - p3).natDegree = 3 := by
    rw [natDegree_sub_eq_left_of_natDegree_lt (by omega), hq]
  have hprod : ((q - p3) * H3).natDegree = 9 := by
    rw [natDegree_mul (ne_zero_of_natDegree_gt (show 0 < (q - p3).natDegree by omega))
      (ne_zero_of_natDegree_gt (show 0 < H3.natDegree by omega)), hqp, hH]
  rw [natDegree_sub_eq_left_of_natDegree_lt (by omega), hprod]

end PierceLengthBound.FixedDividend
