/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.TwoState
public import Mathlib.Tactic.ComputeDegree

/-! The leading Vandermonde term of the multiplicity polynomial `muH4`:
`muH4 = k₀k₁k₂(k₀+k₁)(k₁+k₂)(k₀+k₁+k₂) + rawDetLower`, with `rawDetLower` of total gap degree at
most five. Under a quadratic parametrization of the gaps, `muH4` has degree at most twelve with
an explicit coefficient of `t¹²`, and degree exactly twelve when that coefficient is nonzero. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend

/-- Terms of total gap degree at most five. -/
def rawDetLower {R : Type*} [CommRing R] (k0 k1 k2 k3 k4 : R) : R :=
    k0^3*k1*k3
    - k0^3*k2^2
    + 3*k0^2*k1^2*k3
    - 2*k0^2*k1*k2^2
    + 3*k0^2*k1*k2*k3
    + k0^2*k1*k3^2
    + k0^2*k1*k4
    - k0^2*k2^3
    - k0^2*k2*k3
    - k0*k1^3*k2
    + 2*k0*k1^3*k3
    - 3*k0*k1^2*k2^2
    + 3*k0*k1^2*k2*k3
    + k0*k1^2*k3^2
    - k0*k1^2*k3
    + k0*k1^2*k4
    - 2*k0*k1*k2^3
    + k0*k1*k2^2
    - 2*k0*k1*k2*k3
    + k0*k2^3
    + k0*k2^2*k3
    + k0*k2*k3^2
    + k0*k2*k4
    - k0*k3^2
    - k1^4*k2
    - 2*k1^3*k2^2
    - 2*k1^3*k3
    - k1^2*k2^3
    + 2*k1^2*k2^2
    - 3*k1^2*k2*k3
    - k1^2*k3^2
    - k1^2*k4
    + 2*k1*k2^3
    + 2*k1*k2*k3
    - k2^3

/-- Exact leading Vandermonde term, over an arbitrary commutative ring. -/
theorem muH4_leading_decomposition {R : Type*} [CommRing R] (k0 k1 k2 k3 k4 : R) :
    muH4 k0 k1 k2 k3 k4 =
      k0 * k1 * k2 * (k0 + k1) * (k1 + k2) * (k0 + k1 + k2) +
        rawDetLower k0 k1 k2 k3 k4 := by
  unfold muH4 rawDetLower
  ring

set_option maxHeartbeats 2000000 in
-- Expanding the 35 lower-degree monomials requires a larger tactic budget.
/-- Under a quadratic parametrization, the lower terms have parameter degree at most ten. -/
theorem rawDetLower_degree_le {K : Type*} [Field K] (k : Fin 5 → Polynomial K)
    (hk : ∀ j, (k j).natDegree ≤ 2) :
    (rawDetLower (k 0) (k 1) (k 2) (k 3) (k 4)).natDegree ≤ 10 := by
  have h0 := hk 0
  have h1 := hk 1
  have h2 := hk 2
  have h3 := hk 3
  have h4 := hk 4
  unfold rawDetLower
  compute_degree
  simp only [max_le_iff]
  omega

open Polynomial

/-- The coefficient of `t¹²` in the Vandermonde product of quadratic gaps is the same product
of their leading coefficients. -/
lemma vandermonde_six_coeff {K : Type*} [Field K] (k : Fin 5 → Polynomial K)
    (hk : ∀ j, (k j).natDegree ≤ 2) :
    (k 0 * k 1 * k 2 * (k 0 + k 1) * (k 1 + k 2) * (k 0 + k 1 + k 2)).coeff 12 =
      (k 0).coeff 2 * (k 1).coeff 2 * (k 2).coeff 2 *
        ((k 0).coeff 2 + (k 1).coeff 2) * ((k 1).coeff 2 + (k 2).coeff 2) *
        ((k 0).coeff 2 + (k 1).coeff 2 + (k 2).coeff 2) := by
  have h0 := hk 0
  have h1 := hk 1
  have h2 := hk 2
  have hl : ∀ p ∈ [k 0, k 1, k 2, k 0 + k 1, k 1 + k 2, k 0 + k 1 + k 2],
      p.natDegree ≤ 2 := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      compute_degree
      try simp only [max_le_iff]
      omega
  have hc := coeff_list_prod_of_natDegree_le _ 2 hl
  simpa only [List.length_cons, List.length_nil, List.prod_cons, List.prod_nil,
    List.map_cons, List.map_nil, mul_one, coeff_add, mul_assoc] using hc

/-- The parameter degree is at most twelve for any quadratic gap parametrization. -/
theorem muH4_quadratic_degree_le {K : Type*} [Field K] (k : Fin 5 → Polynomial K)
    (hk : ∀ j, (k j).natDegree ≤ 2) :
    (muH4 (k 0) (k 1) (k 2) (k 3) (k 4)).natDegree ≤ 12 := by
  rw [muH4_leading_decomposition]
  have h0 := hk 0
  have h1 := hk 1
  have h2 := hk 2
  apply (natDegree_add_le _ _).trans
  apply max_le
  · compute_degree
    omega
  · exact (rawDetLower_degree_le k hk).trans (by omega)

/-- Under a quadratic gap parametrization, the coefficient of `t¹²` in `muH4` is the
Vandermonde product of the leading gap coefficients. -/
theorem muH4_quadratic_coeff_twelve {K : Type*} [Field K] (k : Fin 5 → Polynomial K)
    (hk : ∀ j, (k j).natDegree ≤ 2) :
    (muH4 (k 0) (k 1) (k 2) (k 3) (k 4)).coeff 12 =
      (k 0).coeff 2 * (k 1).coeff 2 * (k 2).coeff 2 *
        ((k 0).coeff 2 + (k 1).coeff 2) * ((k 1).coeff 2 + (k 2).coeff 2) *
        ((k 0).coeff 2 + (k 1).coeff 2 + (k 2).coeff 2) := by
  rw [muH4_leading_decomposition, coeff_add,
    coeff_eq_zero_of_natDegree_lt ((rawDetLower_degree_le k hk).trans_lt (by norm_num)),
    add_zero, vandermonde_six_coeff k hk]

/-- Nonzero Vandermonde coefficient forces exact parameter degree twelve. -/
theorem muH4_quadratic_degree_eq {K : Type*} [Field K] (k : Fin 5 → Polynomial K)
    (hk : ∀ j, (k j).natDegree ≤ 2)
    (hv : (k 0).coeff 2 * (k 1).coeff 2 * (k 2).coeff 2 *
      ((k 0).coeff 2 + (k 1).coeff 2) * ((k 1).coeff 2 + (k 2).coeff 2) *
      ((k 0).coeff 2 + (k 1).coeff 2 + (k 2).coeff 2) ≠ 0) :
    (muH4 (k 0) (k 1) (k 2) (k 3) (k 4)).natDegree = 12 :=
  natDegree_eq_of_le_of_coeff_ne_zero (muH4_quadratic_degree_le k hk)
    (by rwa [muH4_quadratic_coeff_twelve k hk])

end PierceLengthBound.FixedDividend
