/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveCoefficientResolvent
public import PierceLengthBound.BranchSieveIntegralClosure
import Mathlib.Tactic

/-! Integral coefficient minimal polynomials divide fixed universal
resolvents after substitution of the original polynomial coefficients.
This reduces their degree and height bounds to ordinary polynomial
substitution and integer factor-height estimates. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

variable {R L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field L] [Algebra R L] [FaithfulSMul R L]

theorem branch_integral_factor_universal_divisor (p : R[X]) (hp : p.Monic)
    (hsplit : (p.map (algebraMap R L)).Splits)
    (q : Polynomial (integralClosure R L)) (hq : q.Monic)
    (hdiv : q ∣ p.map (algebraMap R (integralClosure R L))) :
    ∃ s : Finset (Fin p.natDegree), ∀ j : ℕ,
      minpoly R (q.coeff j) ∣
        (branchUniversalResolvent (branchFactorCoefficientExpression s j)).map
          (MvPolynomial.aeval (branchSignedCoefficients p p.natDegree)).toRingHom := by
  let S := integralClosure R L
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
    intro a b hab
    apply FaithfulSMul.algebraMap_injective R L
    exact congrArg Subtype.val hab)
  change q ∣ p.map (algebraMap R S) at hdiv
  have hdivL : q.map (algebraMap S L) ∣ p.map (algebraMap R L) := by
    simpa only [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] using
      Polynomial.map_dvd (algebraMap S L) hdiv
  have heq : ∃ s : Finset (Fin p.natDegree), ∀ j : ℕ,
      (branchUniversalResolvent (branchFactorCoefficientExpression s j)).eval₂
        (MvPolynomial.aeval
          (branchSignedCoefficients (p.map (algebraMap R L)) p.natDegree)).toRingHom
        ((q.map (algebraMap S L)).coeff j) = 0 := by
    have hw := branch_monic_factor_universal_equation
      (p.map (algebraMap R L)) (hp.map _) hsplit (hq.map _) hdivL
    rw [hp.natDegree_map] at hw
    obtain ⟨s, _hs, hcoeff⟩ := hw
    exact ⟨s, hcoeff⟩
  obtain ⟨s, hs⟩ := heq
  refine ⟨s, ?_⟩
  intro j
  have hint := Polynomial.isIntegral_coeff_of_dvd p q hp hq hdiv j
  apply minpoly.isIntegrallyClosed_dvd hint
  have hc : (algebraMap R L).comp
      (MvPolynomial.aeval (R := ℤ) (branchSignedCoefficients p p.natDegree)).toRingHom =
      (MvPolynomial.aeval (R := ℤ)
        (branchSignedCoefficients (p.map (algebraMap R L)) p.natDegree)).toRingHom := by
    ext i
    · simp
    · simp [branchSignedCoefficients]
  apply (FaithfulSMul.algebraMap_injective S L)
  rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂,
    ← IsScalarTower.algebraMap_eq, Polynomial.eval₂_map, hc]
  simpa only [Polynomial.coeff_map] using hs j

end
end PierceLengthBound.FixedDividend
