/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveUniformRootBound
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Integral
public import CCDN.Plane.PlaneGridHeight
public import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic

/-! The uniform integral-root estimate in nested-polynomial notation.

`branchNestedCoordinates` converts a nested polynomial in `ℤ[T][Y]` to the
coordinate convention of the integral-root estimates (parameter first, label
second), and `branch_rational_nested_irreducible` passes irreducibility over
the fraction field of `ℤ[T]` to the rational bivariate equation. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

/-- Nested polynomials `R[T][Y]` as bivariate polynomials, with the parameter
`T` as variable `0` and the label `Y` as variable `1`. -/
def branchNestedCoordinates (R : Type*) [CommRing R] :
    R[X][X] ≃ₐ[R] MvPolynomial (Fin 2) R :=
  (CCDN.bivariatePolynomialEquiv R).symm.trans
    (MvPolynomial.renameEquiv R (Equiv.swap 0 1))

theorem branchNestedCoordinates_totalDegree {R : Type*} [CommRing R] (p : R[X][X]) :
    (branchNestedCoordinates R p).totalDegree = CCDN.bivariateTotalDegree p := by
  exact MvPolynomial.totalDegree_renameEquiv _ _

theorem branchNestedCoordinates_degreeOf {R : Type*} [CommRing R] (p : R[X][X]) :
    (branchNestedCoordinates R p).degreeOf 1 = p.natDegree := by
  have h := MvPolynomial.degreeOf_rename_of_injective (Equiv.swap 0 1).injective
    (p := (CCDN.bivariatePolynomialEquiv R).symm p) 0
  have hdegree (f : MvPolynomial (Fin 2) R) :
      (CCDN.bivariatePolynomialEquiv R f).natDegree = f.degreeOf 0 := by
    change (Polynomial.map (MvPolynomial.uniqueAlgEquiv R (Fin 1)).toRingHom
      (MvPolynomial.finSuccEquiv R 1 f)).natDegree = _
    rw [Polynomial.natDegree_map_eq_of_injective (MvPolynomial.uniqueAlgEquiv R (Fin 1)).injective,
      MvPolynomial.natDegree_finSuccEquiv]
  simpa only [branchNestedCoordinates, AlgEquiv.trans_apply, MvPolynomial.renameEquiv_apply,
    Equiv.swap_apply_left, ← hdegree, AlgEquiv.apply_symm_apply] using h

theorem branchNestedCoordinates_eval {R : Type*} [CommRing R] (p : R[X][X]) (t y : R) :
    MvPolynomial.eval ![t, y] (branchNestedCoordinates R p) =
      (p.map (Polynomial.evalRingHom t)).eval y := by
  change MvPolynomial.eval ![t, y]
    (MvPolynomial.rename (Equiv.swap 0 1) ((CCDN.bivariatePolynomialEquiv R).symm p)) = _
  rw [MvPolynomial.eval_rename]
  have hv : ![t, y] ∘ Equiv.swap (0 : Fin 2) 1 = ![y, t] := by
    funext i
    fin_cases i <;> simp
  rw [hv, ← CCDN.bivariatePolynomialEquiv_eval, AlgEquiv.apply_symm_apply]

theorem branchNestedCoordinates_coeff {R : Type*} [CommRing R]
    (p : R[X][X]) (s : Fin 2 →₀ ℕ) :
    (branchNestedCoordinates R p).coeff s = (p.coeff (s 1)).coeff (s 0) := by
  let e : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  let u := s.mapDomain e
  have hu : u.mapDomain e = s := by
    ext i
    dsimp only [u]
    simp only [Finsupp.mapDomain_equiv_apply]
    simp [e]
  have h := MvPolynomial.coeff_rename_mapDomain e e.injective
    ((CCDN.bivariatePolynomialEquiv R).symm p) u
  rw [hu] at h
  change (MvPolynomial.rename e ((CCDN.bivariatePolynomialEquiv R).symm p)).coeff s = _
  rw [h]
  have he := CCDN.bivariatePolynomialEquiv_coeff
    ((CCDN.bivariatePolynomialEquiv R).symm p) (u 0) (u 1)
  rw [AlgEquiv.apply_symm_apply, ← CCDN.bivariate_exponent_eq u] at he
  rw [← he]
  have hu0 : u 0 = s 1 := by
    dsimp only [u]
    rw [Finsupp.mapDomain_equiv_apply]
    simp [e]
  have hu1 : u 1 = s 0 := by
    dsimp only [u]
    rw [Finsupp.mapDomain_equiv_apply]
    simp [e]
  rw [hu0, hu1]

theorem branchNestedCoordinates_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (p : R[X][X]) :
    MvPolynomial.map φ (branchNestedCoordinates R p) =
      branchNestedCoordinates S (CCDN.bivariateMap φ p) := by
  change MvPolynomial.map φ
    (MvPolynomial.rename (Equiv.swap 0 1) ((CCDN.bivariatePolynomialEquiv R).symm p)) =
    MvPolynomial.rename (Equiv.swap 0 1)
      ((CCDN.bivariatePolynomialEquiv S).symm (CCDN.bivariateMap φ p))
  rw [MvPolynomial.map_rename]
  congr 1
  apply (CCDN.bivariatePolynomialEquiv S).injective
  rw [← CCDN.bivariatePolynomialEquiv_map,
    AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

section Rationalization
open scoped nonZeroDivisors
attribute [local instance] Polynomial.algebra

instance branchPolynomial_ratFunc_fractionRing {R K : Type*} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] : IsFractionRing R[X] (RatFunc K) := by
  let : IsLocalization ((nonZeroDivisors R).map Polynomial.C) K[X] :=
    Polynomial.isLocalization _ _
  have h := IsLocalization.localization_localization_isLocalization_of_has_all_units
    ((nonZeroDivisors R).map Polynomial.C) (nonZeroDivisors K[X]) (RatFunc K)
    (fun _ hx => hx.mem_nonZeroDivisors)
  convert h using 1
  ext x
  simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  change x ≠ 0 ↔ x.map (algebraMap R K) ≠ 0
  simpa only [Polynomial.map_zero] using
    ((Polynomial.map_injective (algebraMap R K)
      (IsFractionRing.injective _ _)).ne_iff (x := x) (y := 0)).symm

theorem branch_rational_nested_irreducible {F : Type*} [Field F]
    [Algebra ℤ[X] F] [IsFractionRing ℤ[X] F]
    (p : ℤ[X][X]) (hp : p.Monic)
    (hir : Irreducible (p.map (algebraMap ℤ[X] F))) :
    Irreducible (CCDN.bivariateMap (Int.castRingHom ℚ) p) := by
  let e := IsLocalization.algEquiv (nonZeroDivisors ℤ[X]) F (RatFunc ℚ)
  have he : e.toRingHom.comp (algebraMap ℤ[X] F) = algebraMap ℤ[X] (RatFunc ℚ) :=
    e.toAlgHom.comp_algebraMap
  have hr : Irreducible (p.map (algebraMap ℤ[X] (RatFunc ℚ))) := by
    rw [← he, ← Polynomial.map_map]
    exact (MulEquiv.irreducible_iff (f := Polynomial.mapEquiv e.toRingEquiv)).mpr hir
  have hmonic := hp.map (Polynomial.mapRingHom (Int.castRingHom ℚ))
  apply (hmonic.irreducible_iff_irreducible_map_fraction_map (K := RatFunc ℚ)).mpr
  rw [Polynomial.map_map]
  change Irreducible (p.map ((algebraMap ℚ[X] (RatFunc ℚ)).comp (algebraMap ℤ[X] ℚ[X])))
  rwa [← IsScalarTower.algebraMap_eq]

end Rationalization

/-- For a monic `p ∈ ℤ[T][Y]` of total degree at most `d` and `Y`-degree at
least two, irreducible over the fraction field of `ℤ[T]`, the integers
`|t| ≤ B` for which `p(t, Y)` has an integer root number
`O((1 + log (H+1))^4 √B (1 + log B))`, with constant depending only on `d`. -/
theorem branch_uniform_nested_root_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Type*) [Field F] [Algebra ℤ[X] F]
      [IsFractionRing ℤ[X] F], ∀ (p : ℤ[X][X]), p.Monic →
      Irreducible (p.map (algebraMap ℤ[X] F)) →
      CCDN.bivariateTotalDegree p ≤ d → 2 ≤ p.natDegree →
      ∀ H B : ℕ, (∀ i j, |(p.coeff i).coeff j| ≤ (H : ℤ)) → 1 ≤ B →
      ∀ S : Finset ℤ,
      (∀ t ∈ S, |t| ≤ (B : ℤ) ∧ ∃ y : ℤ,
        (p.map (Polynomial.evalRingHom t)).eval y = 0) →
      (S.card : ℝ) ≤ C * (1 + Real.log (H + 1 : ℕ)) ^ 4 *
        (B : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log B) := by
  obtain ⟨C, hC, hroot⟩ := branch_uniform_integral_root_bound d
  refine ⟨C, hC, ?_⟩
  intro F _ _ _ p hp hir hd hn H B hH hB S hS
  apply hroot (branchNestedCoordinates ℤ p)
  · unfold branchRationalPolynomial
    rw [branchNestedCoordinates_map]
    exact (MulEquiv.irreducible_iff (f := branchNestedCoordinates ℚ)).mpr
      (branch_rational_nested_irreducible p hp hir)
  · rwa [branchNestedCoordinates_totalDegree]
  · rwa [branchNestedCoordinates_degreeOf]
  · intro s
    rw [branchNestedCoordinates_coeff]
    exact hH _ _
  · exact hB
  · intro t ht
    obtain ⟨htB, y, hy⟩ := hS t ht
    exact ⟨htB, y, by rwa [branchNestedCoordinates_eval]⟩

end
end PierceLengthBound.FixedDividend
