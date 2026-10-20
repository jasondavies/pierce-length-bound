/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ConicRawDeterminant
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-! Polynomial degree calculations for the generic parabolic branch.
The geometric parametrization and its coefficient-height estimates are not
assumed to have been constructed by this file. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Polynomial

/-- A rational-function solution of a monic polynomial equation is polynomial. -/
theorem rational_monic_root_polynomial {K : Type*} [Field K]
    {P : Polynomial (Polynomial K)} (hP : P.Monic) {q : RatFunc K}
    (hq : aeval q P = 0) : ∃ Q : Polynomial K, algebraMap (Polynomial K) (RatFunc K) Q = q :=
  IsIntegrallyClosed.algebraMap_eq_of_integral ⟨P, hP, hq⟩

/-- Coefficient of the initial remainder after four recurrence steps. -/
noncomputable def parabolaV {K : Type*} [Field K] (c : Fin 4 → K) (v : Fin 4 → K[X]) : K[X] :=
  C (c 0) - C (c 1) * v 0 + C (c 2) * (v 0 * v 1) -
    C (c 3) * (v 0 * v 1 * v 2) + v 0 * v 1 * v 2 * v 3

/-- Coefficient of the fixed dividend after four recurrence steps. -/
noncomputable def parabolaW {K : Type*} [Field K] (c : Fin 4 → K) (v : Fin 4 → K[X]) : K[X] :=
  C (c 1) + C (c 2) * (1 - v 1) + C (c 3) * (1 - v 2 + v 2 * v 1) +
    (1 - v 3 + v 3 * v 2 - v 3 * v 2 * v 1)

/-- The quartic has degree four times the common positive quotient degree. -/
theorem parabolaV_degree {K : Type*} [Field K] (c : Fin 4 → K) (v : Fin 4 → K[X])
    {m : ℕ} (hm : 0 < m) (hv : ∀ j, (v j).natDegree = m) :
    (parabolaV c v).natDegree = 4 * m := by
  have hne : ∀ j, v j ≠ 0 := fun j => ne_zero_of_natDegree_gt (by rw [hv j]; exact hm)
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  have hl : (C (c 0) - C (c 1) * v 0 + C (c 2) * (v 0 * v 1) -
      C (c 3) * (v 0 * v 1 * v 2)).natDegree ≤ 3 * m := by
    compute_degree
    omega
  have hh : (v 0 * v 1 * v 2 * v 3).natDegree = 4 * m := by
    rw [natDegree_mul (mul_ne_zero (mul_ne_zero (hne 0) (hne 1)) (hne 2)) (hne 3),
      natDegree_mul (mul_ne_zero (hne 0) (hne 1)) (hne 2), natDegree_mul (hne 0) (hne 1)]
    omega
  unfold parabolaV
  rw [natDegree_add_eq_right_of_natDegree_lt (by rw [hh]; omega), hh]

/-- The dividend coefficient has degree three times the positive quotient degree. -/
theorem parabolaW_degree {K : Type*} [Field K] (c : Fin 4 → K) (v : Fin 4 → K[X])
    {m : ℕ} (hm : 0 < m) (hv : ∀ j, (v j).natDegree = m) :
    (parabolaW c v).natDegree = 3 * m := by
  have hne : ∀ j, v j ≠ 0 := fun j => ne_zero_of_natDegree_gt (by rw [hv j]; exact hm)
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  have hl : (C (c 1) + C (c 2) * (1 - v 1) + C (c 3) * (1 - v 2 + v 2 * v 1) +
      (1 - v 3 + v 3 * v 2)).natDegree ≤ 2 * m := by
    compute_degree
    omega
  have hh : (v 3 * v 2 * v 1).natDegree = 3 * m := by
    rw [natDegree_mul (mul_ne_zero (hne 3) (hne 2)) (hne 1), natDegree_mul (hne 3) (hne 2)]
    omega
  have he : parabolaW c v =
      (C (c 1) + C (c 2) * (1 - v 1) + C (c 3) * (1 - v 2 + v 2 * v 1) +
        (1 - v 3 + v 3 * v 2)) - v 3 * v 2 * v 1 := by unfold parabolaW; ring
  rw [he, natDegree_sub_eq_right_of_natDegree_lt (by rw [hh]; omega), hh]

/-- If all quotient shifts have degree at most two, the quartic has degree at most eight. -/
theorem parabolaV_degree_le_eight {K : Type*} [Field K] (c : Fin 4 → K)
    (v : Fin 4 → K[X]) (hv : ∀ j, (v j).natDegree ≤ 2) :
    (parabolaV c v).natDegree ≤ 8 := by
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  unfold parabolaV
  compute_degree
  omega

/-- A quartic of parameter degree twelve forces a cubic quotient. -/
theorem parabola_quotient_degree_three {K : Type*} [Field K] (c : Fin 4 → K)
    (s : Fin 4 → K[X]) (hs : ∀ j, (s j).natDegree ≤ 2) (q : K[X])
    (hdegree : (parabolaV c (fun j => q + s j)).natDegree = 12) : q.natDegree = 3 := by
  have hq : 2 < q.natDegree := by
    by_contra h
    have hb := parabolaV_degree_le_eight c (fun j => q + s j) fun j =>
      natDegree_add_le_of_degree_le (by omega) (hs j)
    omega
  have hv : ∀ j, (q + s j).natDegree = q.natDegree := fun j =>
    natDegree_add_eq_left_of_natDegree_lt (lt_of_le_of_lt (hs j) hq)
  have hd := parabolaV_degree c (fun j => q + s j) (by omega : 0 < q.natDegree) hv
  omega

/-- The resulting remainder numerator has degree nine and denominator degree twelve. -/
theorem parabola_remainder_degrees {K : Type*} [Field K] (c : Fin 4 → K)
    (s : Fin 4 → K[X]) (hs : ∀ j, (s j).natDegree ≤ 2) (q : K[X])
    (hdegree : (parabolaV c (fun j => q + s j)).natDegree = 12) :
    (parabolaW c (fun j => q + s j)).natDegree = 9 ∧
      (parabolaW c (fun j => q + s j)).natDegree <
        (parabolaV c (fun j => q + s j)).natDegree := by
  have hq := parabola_quotient_degree_three c s hs q hdegree
  have hv : ∀ j, (q + s j).natDegree = 3 := fun j => by
    rw [natDegree_add_eq_left_of_natDegree_lt
      (by rw [hq]; exact lt_of_le_of_lt (hs j) (by norm_num)), hq]
  have hw := parabolaW_degree c (fun j => q + s j) (by norm_num : 0 < 3) hv
  constructor <;> omega

/-- The actual normalization identity transfers degree twelve from the raw
multiplicity polynomial to the quartic. -/
theorem parabola_normalization_degree {K : Type*} [Field K] (c : Fin 4 → K)
    (v : Fin 4 → K[X]) (k : Fin 5 → K[X]) {A a : K} (hA : A ≠ 0) (ha : a ≠ 0)
    (hdegree : (muH4 (k 0) (k 1) (k 2) (k 3) (k 4)).natDegree = 12)
    (hid : C A * parabolaV c v = C a * muH4 (k 0) (k 1) (k 2) (k 3) (k 4)) :
    (parabolaV c v).natDegree = 12 := by
  have hd := congrArg Polynomial.natDegree hid
  rwa [natDegree_C_mul hA, natDegree_C_mul ha, hdegree] at hd

/-- Explicit four-step recurrence expansion, valid in any commutative ring. -/
theorem quartic_remainder_expansion {R : Type*} [CommRing R]
    (a b c0 c1 c2 c3 v0 v1 v2 v3 : R) :
    c0 * b + c1 * (a - v0 * b) + c2 * (a - v1 * (a - v0 * b)) +
      c3 * (a - v2 * (a - v1 * (a - v0 * b))) +
      (a - v3 * (a - v2 * (a - v1 * (a - v0 * b)))) =
    (c0 - c1 * v0 + c2 * (v0 * v1) - c3 * (v0 * v1 * v2) +
      v0 * v1 * v2 * v3) * b +
    a * (c1 + c2 * (1 - v1) + c3 * (1 - v2 + v2 * v1) +
      (1 - v3 + v3 * v2 - v3 * v2 * v1)) := by ring

/-- Cancellation preserves the degree difference, so the reduced denominator
of a degree-nine over degree-twelve rational function is nonconstant. -/
theorem proper_remainder_denominator {K : Type*} [Field K] {F G : K[X]}
    (hF : F.natDegree = 9) (hG : G.natDegree = 12) :
    let b := algebraMap K[X] (RatFunc K) F / algebraMap K[X] (RatFunc K) G
    b.num.natDegree + 3 = b.denom.natDegree ∧ 0 < b.denom.natDegree := by
  have hFn : F ≠ 0 := ne_zero_of_natDegree_gt (show 0 < F.natDegree by omega)
  have hGn : G ≠ 0 := ne_zero_of_natDegree_gt (show 0 < G.natDegree by omega)
  have hi := IsFractionRing.injective K[X] (RatFunc K)
  have hFm : algebraMap K[X] (RatFunc K) F ≠ 0 := by
    simpa only [map_zero] using hi.ne hFn
  have hGm : algebraMap K[X] (RatFunc K) G ≠ 0 := by
    simpa only [map_zero] using hi.ne hGn
  have hd := RatFunc.intDegree_div hFm hGm
  rw [RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial, hF, hG] at hd
  rw [RatFunc.intDegree] at hd
  dsimp only
  constructor <;> omega

end PierceLengthBound.FixedDividend
