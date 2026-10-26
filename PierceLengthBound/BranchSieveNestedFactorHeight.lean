/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveBivariateFactorHeight
public import CCDN.Noether.BivariateTotalDegree
import Mathlib.Tactic

/-! Total degree and height bounds for factors in the nested bivariate
integer polynomial ring. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

theorem branch_nested_totalDegree_le_of_dvd {R : Type*} [CommRing R] [IsDomain R]
    {p q : R[X][X]} (hp : p ≠ 0) (hdiv : q ∣ p) :
    CCDN.bivariateTotalDegree q ≤ CCDN.bivariateTotalDegree p := by
  obtain ⟨r, rfl⟩ := hdiv
  have hne {f : R[X][X]} (hf : f ≠ 0) : (CCDN.bivariatePolynomialEquiv R).symm f ≠ 0 :=
    (map_ne_zero_iff _ (CCDN.bivariatePolynomialEquiv R).symm.injective).mpr hf
  unfold CCDN.bivariateTotalDegree
  rw [map_mul, MvPolynomial.totalDegree_mul_of_isDomain (hne (left_ne_zero_of_mul hp))
    (hne (right_ne_zero_of_mul hp))]
  omega

/-- A factor of a nonzero nested integer polynomial of total degree at most
`d` and coefficient height at most `H` has coefficient height at most
`2^((d+1)d) ((d+1)d + 1) (d+1)^2 H`. -/
theorem branch_nested_factor_coeff_height (p : ℤ[X][X]) (hp : p ≠ 0) {d H : ℕ}
    (hd : CCDN.bivariateTotalDegree p ≤ d)
    (hH : ∀ i j, |(p.coeff i).coeff j| ≤ (H : ℤ))
    (q : ℤ[X][X]) (hdiv : q ∣ p) (i j : ℕ) :
    |(q.coeff i).coeff j| ≤
      (2 ^ ((d + 1) * d) * ((d + 1) * d + 1) * ((d + 1) ^ 2 * H) : ℕ) := by
  let e := (CCDN.bivariatePolynomialEquiv ℤ).symm
  have hp' : e p ≠ 0 := (map_ne_zero_iff _ e.injective).mpr hp
  have hH' (s) : |(e p).coeff s| ≤ (H : ℤ) := by
    have h := hH (s 0) (s 1)
    have he := CCDN.bivariatePolynomialEquiv_coeff (e p) (s 0) (s 1)
    rw [AlgEquiv.apply_symm_apply, ← CCDN.bivariate_exponent_eq s] at he
    rwa [← he]
  have hh := branch_bivariate_factor_coeff_height (e p) hp' hd hH' (e q)
    (map_dvd e.toRingHom hdiv) (Finsupp.cons i (Finsupp.single 0 j))
  have he := CCDN.bivariatePolynomialEquiv_coeff (e q) i j
  rw [AlgEquiv.apply_symm_apply] at he
  rwa [← he] at hh

end
end PierceLengthBound.FixedDividend
