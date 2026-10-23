/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib

/-! The rank-three resolvent identity for the integral Hankel coordinate `I₃` added by the
integral lift, and the raw rank-three and mixed Hankel minors as polynomials in three or four
consecutive gaps. All identities are polynomial and hold over arbitrary commutative rings. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Matrix

/-- Rank-three Hankel determinant of a moment sequence. -/
def hankelThree {R : Type*} [CommRing R] (v : ℕ → R) : R :=
  (!![v 0, v 1, v 2; v 1, v 2, v 3; v 2, v 3, v 4]).det

/-- The mixed minor with column indices `0,1,3`. -/
def hankelMixed {R : Type*} [CommRing R] (v : ℕ → R) : R :=
  (!![v 0, v 1, v 3; v 1, v 2, v 4; v 2, v 3, v 5]).det

/-- The resolvent formula with its denominator cleared: if `v` satisfies the quartic
recurrence with coefficients `p₀, …, p₃`, then
`H₃(v) (q⁴ - p₃q³ + p₂q² - p₁q + p₀) = (q - p₃) H₃(w) - H_mixed(w)` with
`w_j = q v_j + v_{j+1}`. -/
theorem hankel_three_resolvent {R : Type*} [CommRing R]
    (p0 p1 p2 p3 q : R) (v : ℕ → R)
    (hrec : ∀ j < 3, p0 * v j + p1 * v (j + 1) + p2 * v (j + 2) +
      p3 * v (j + 3) + v (j + 4) = 0) :
    hankelThree v * (q ^ 4 - p3 * q ^ 3 + p2 * q ^ 2 - p1 * q + p0) =
      (q - p3) * hankelThree (fun j => q * v j + v (j + 1)) -
        hankelMixed (fun j => q * v j + v (j + 1)) := by
  have h4 : v 4 = -(p0 * v 0 + p1 * v 1 + p2 * v 2 + p3 * v 3) := by
    linear_combination hrec 0 (by decide)
  have h5 : v 5 = -(p0 * v 1 + p1 * v 2 + p2 * v 3 + p3 * v 4) := by
    linear_combination hrec 1 (by decide)
  have h6 : v 6 = -(p0 * v 2 + p1 * v 3 + p2 * v 4 + p3 * v 5) := by
    linear_combination hrec 2 (by decide)
  norm_num [hankelThree, hankelMixed, Matrix.det_fin_three]
  rw [h6, h5, h4]
  ring

/-- The raw rank-three determinant in the three consecutive gaps. -/
def rawHankelThree {R : Type*} [CommRing R] (k0 k1 k2 : R) : R :=
  k0 ^ 2 * k1 + (k0 - 1) * k1 ^ 2 + k0 * k2

/-- Its leading form is the three-node Vandermonde. -/
lemma rawHankelThree_leading {R : Type*} [CommRing R] (k0 k1 k2 : R) :
    rawHankelThree k0 k1 k2 = k0 * k1 * (k0 + k1) + k0 * k2 - k1 ^ 2 := by
  unfold rawHankelThree
  ring

/-- The mixed raw minor, separated into its quartic leading form and lower terms. -/
def rawHankelMixed {R : Type*} [CommRing R] (k0 k1 k2 k3 : R) : R :=
  (2 * k0 + k1) * k0 * k1 * (k0 + k1) +
    (k0 ^ 2 * k1 + 3 * k0 ^ 2 * k2 - k0 * k1 ^ 2 + 3 * k0 * k1 * k2 +
      k0 * k2 ^ 2 + k0 * k2 + k0 * k3 - k1 ^ 3 - k1 ^ 2 - k1 * k2)

/-- Exact mixed determinant from the first six raw moments. -/
theorem hankelMixed_raw_identity {R : Type*} [CommRing R] (k0 k1 k2 k3 : R) :
    (!![1, 1, k0 ^ 2 + 2 * k0 + k1 + 1;
      1, k0 + 1, k0 ^ 3 + 3 * k0 ^ 2 + 3 * k0 * (k1 + 1) +
        k1 ^ 2 + 2 * k1 + k2 + 1;
      k0 + 1, k0 ^ 2 + 2 * k0 + k1 + 1,
        k0 ^ 4 + 4 * k0 ^ 3 + 6 * k0 ^ 2 * (k1 + 1) +
          4 * k0 * (k1 ^ 2 + 2 * k1 + k2 + 1) +
          k1 ^ 3 + 3 * k1 ^ 2 + 3 * k1 * (k2 + 1) +
          k2 ^ 2 + 2 * k2 + k3 + 1]).det = rawHankelMixed k0 k1 k2 k3 := by
  norm_num [Matrix.det_fin_three, rawHankelMixed]
  ring

/-- Exact raw determinant from the first five moments. -/
theorem hankelThree_raw_identity {R : Type*} [CommRing R] (k0 k1 k2 : R) :
    (!![1, 1, k0 + 1;
      1, k0 + 1, k0 ^ 2 + 2 * k0 + k1 + 1;
      k0 + 1, k0 ^ 2 + 2 * k0 + k1 + 1,
        k0 ^ 3 + 3 * k0 ^ 2 + 3 * k0 * (k1 + 1) + k1 ^ 2 + 2 * k1 + k2 + 1]).det =
      rawHankelThree k0 k1 k2 := by
  norm_num [Matrix.det_fin_three, rawHankelThree]
  ring

end PierceLengthBound.FixedDividend
