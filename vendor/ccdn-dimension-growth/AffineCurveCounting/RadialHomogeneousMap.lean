/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import AffineCurveCounting.InfinitySection

/-! Radial scaling records the homogeneous components as coefficients of a
single polynomial. Generalized from the radial-map lemmas in pierce-length-bound. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- Replace every coordinate by itself times the same scalar parameter. -/
def radialMap {K σ : Type*} [CommRing K] :
    MvPolynomial σ K →+* Polynomial (MvPolynomial σ K) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun j => Polynomial.C (MvPolynomial.X j) * Polynomial.X)

@[simp] lemma radialMap_C {K σ : Type*} [CommRing K] (c : K) :
    radialMap (MvPolynomial.C c : MvPolynomial σ K) = Polynomial.C (MvPolynomial.C c) := by
  simp [radialMap]

@[simp] lemma radialMap_X {K σ : Type*} [CommRing K] (j : σ) :
    radialMap (MvPolynomial.X j : MvPolynomial σ K) =
      Polynomial.C (MvPolynomial.X j) * Polynomial.X := by simp [radialMap]

lemma radialMap_monomial {K σ : Type*} [CommRing K] (e : σ →₀ ℕ) (c : K) :
    radialMap (monomial e c) = Polynomial.C (monomial e c) * Polynomial.X ^ e.degree := by
  classical
  rw [monomial_eq, map_mul, radialMap_C, map_finsuppProd]
  simp only [map_pow, radialMap_X, mul_pow]
  rw [Finsupp.prod_mul]
  simp only [← map_pow, Finsupp.prod]
  rw [← map_prod, Finset.prod_pow_eq_pow_sum]
  rw [← mul_assoc, ← Polynomial.C_mul]
  rfl

lemma radialMap_coeff {K σ : Type*} [CommRing K] (f : MvPolynomial σ K) (n : ℕ) :
    (radialMap f).coeff n = homogeneousComponent n f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add, Polynomial.coeff_add, hf, hg]
  | monomial e c =>
    rw [radialMap_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [homogeneousComponent_of_mem (isHomogeneous_monomial c rfl)]
    split_ifs <;> simp_all

/-- Radial scaling lands in the actual homogeneous coordinate algebra of I. -/
def quotientRadialMap {K σ : Type*} [Field K] (I : Ideal (MvPolynomial σ K)) :
    MvPolynomial σ K →ₐ[K] projectiveCoordinateAlgebra I where
  toFun f := ⟨Polynomial.map (Ideal.Quotient.mk I) (radialMap f), by
    intro n
    rw [Polynomial.coeff_map, radialMap_coeff]
    exact ⟨homogeneousComponent n f,
      (mem_restrictTotalDegree _ _ _).mpr (homogeneousComponent_isHomogeneous n f).totalDegree_le, rfl⟩⟩
  map_zero' := by apply Subtype.ext; simp
  map_one' := by apply Subtype.ext; simp
  map_add' f g := by apply Subtype.ext; simp
  map_mul' f g := by apply Subtype.ext; simp
  commutes' c := by
    apply Subtype.ext
    simp
    exact (Ideal.Quotient.mkₐ K I).commutes c

lemma quotientRadialMap_coeff {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (f : MvPolynomial σ K) (n : ℕ) :
    ((quotientRadialMap I f : projectiveCoordinateAlgebra I) :
      Polynomial (MvPolynomial σ K ⧸ I)).coeff n = (Ideal.Quotient.mk I) (homogeneousComponent n f) := by
  change (Polynomial.map (Ideal.Quotient.mk I) (radialMap f)).coeff n = _
  rw [Polynomial.coeff_map, radialMap_coeff]

lemma quotientRadialMap_homogeneous {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (f : MvPolynomial σ K) (n : ℕ) (hf : f.IsHomogeneous n) :
    quotientRadialMap I f = projectiveMonomialMap I n
      ⟨(Ideal.Quotient.mk I) f, ⟨f, (mem_restrictTotalDegree _ _ _).mpr hf.totalDegree_le, rfl⟩⟩ := by
  apply Subtype.ext
  ext m
  rw [quotientRadialMap_coeff, projectiveMonomialMap_val, Polynomial.coeff_monomial,
    homogeneousComponent_of_mem hf]
  split_ifs <;> simp_all

end
end AffineCurveCounting
