/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Plane.PlaneGridHeight
public import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic

/-! Conversion between nested parameter/label polynomials and the coordinate
convention used by the integral-root estimates: parameter first, label second. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

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

end
end PierceLengthBound.FixedDividend
