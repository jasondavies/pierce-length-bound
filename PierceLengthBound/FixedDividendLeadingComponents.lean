/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendHomogenization

/-!
# Leading homogeneous components and degree drops

These lemmas connect the already checked radial coefficients with the ordinary
homogeneous components of the multivariate coordinate equations. They allow
homogeneous ideal certificates to be lifted to the affine degree filtration.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

lemma radialMap_monomial {K : Type*} [CommRing K] (d : Fin 3 →₀ ℕ) (c : K) :
    radialMap (monomial d c) =
      Polynomial.C (monomial d c) * Polynomial.X ^ d.degree := by
  classical
  rw [monomial_eq, map_mul, radialMap_C, map_finsuppProd]
  simp only [map_pow, radialMap_X, mul_pow]
  rw [Finsupp.prod_mul]
  simp only [← map_pow, Finsupp.prod]
  rw [← map_prod, Finset.prod_pow_eq_pow_sum]
  rw [← mul_assoc, ← Polynomial.C_mul]
  rfl


/-- Radial coefficients are exactly the ordinary homogeneous components. -/
theorem radialMap_coeff_eq_homogeneousComponent {K : Type*} [CommRing K]
    (f : MvPolynomial (Fin 3) K) (n : ℕ) :
    (radialMap f).coeff n = homogeneousComponent n f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add, Polynomial.coeff_add, hf, hg]
  | monomial d c =>
    rw [radialMap_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [homogeneousComponent_of_mem (isHomogeneous_monomial c rfl)]
    split_ifs <;> simp_all

lemma homogeneousComponent_mul_of_homogeneous_left {K σ : Type*} [CommRing K]
    {f : MvPolynomial σ K} {i : ℕ} (hf : f.IsHomogeneous i)
    (g : MvPolynomial σ K) (j : ℕ) :
    homogeneousComponent (i + j) (f * g) = f * homogeneousComponent j g := by
  let := MvPolynomial.gradedAlgebra (σ := σ) (R := K)
  have ht := DirectSum.coe_decompose_mul_add_of_left_mem
    (homogeneousSubmodule σ K) (j := j) hf (b := g)
  simpa only [← DirectSum.Decomposition.decompose'_eq,
    MvPolynomial.decomposition.decompose'_apply] using ht

/-- Subtracting the top homogeneous component strictly lowers a positive degree cutoff. -/
theorem totalDegree_sub_homogeneousComponent_le {K σ : Type*} [CommRing K]
    (f : MvPolynomial σ K) {n : ℕ} (hn : 0 < n) (hf : f.totalDegree ≤ n) :
    (f - homogeneousComponent n f).totalDegree ≤ n - 1 := by
  classical
  rw [totalDegree, Finset.sup_le_iff]
  intro d hd
  have hc : (f - homogeneousComponent n f).coeff d ≠ 0 := mem_support_iff.mp hd
  rw [coeff_sub, coeff_homogeneousComponent] at hc
  by_cases he : d.degree = n
  · simp [he] at hc
  have hdn : d.degree ≤ n := by
    by_contra hh
    have hz : f.coeff d = 0 := coeff_eq_zero_of_totalDegree_lt (by
      change f.totalDegree < d.sum (fun _ e => e)
      change f.totalDegree < d.degree
      omega)
    simp [he, hz] at hc
  change d.degree ≤ n - 1
  omega

lemma curveQuadratic_top_component {K : Type*} [CommRing K] (ρ u v ρ' u' v' : K) :
    homogeneousComponent 2 (curveQuadratic ρ u v ρ' u' v') =
      leadingQuadratic (-ρ - u) (u - v) (v - 1) := by
  rw [← radialMap_coeff_eq_homogeneousComponent, radialMap_quadratic_coeff]

lemma curveNorm_top_component {K : Type*} [CommRing K] (ρ u v ρ' u' v' : K) :
    homogeneousComponent 3 (curveNorm ρ u v ρ' u' v') =
      leadingCubic (-ρ - u) (u - v) (v - 1) := by
  rw [← radialMap_coeff_eq_homogeneousComponent, radialMap_norm_coeff]

/-- The degree-twelve leading equation is exactly minus the dividend times D₃⁴. -/
lemma curveEquation_top_component {K : Type*} [Field K] (ρ u v ρ' u' v' A a : K) :
    homogeneousComponent 12 (curveEquation ρ u v ρ' u' v' A a) =
      -C a * leadingCubic (-ρ - u) (u - v) (v - 1) ^ 4 := by
  rw [← radialMap_coeff_eq_homogeneousComponent]
  have he := congrArg (fun p : Polynomial (MvPolynomial (Fin 3) K) => p.eval 0)
    (curveEquation_homogenize ρ u v ρ' u' v' A a)
  rw [curveHomogenize_at_infinity] at he
  simpa only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_mul, zero_sub, curveNorm_at_infinity, neg_mul] using he

end
end PierceLengthBound.FixedDividend
