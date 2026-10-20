/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendHomogenization
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Local intersection parity from the actual homogeneous equations

A local chart homomorphism satisfying the two homogeneous equations and reducing
to a nonzero infinity direction has even infinity intersection length. Singular
one-dimensional Noetherian domains are allowed. Constructing the projective
charts and identifying their length sum with the affine Hilbert slope is not
asserted here.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

/-- A local residue homomorphism detects units. -/
lemma isUnit_of_residue_ne_zero {R K : Type*} [CommRing R] [IsLocalRing R] [Field K]
    (ψ : R →+* K) (hker : RingHom.ker ψ = IsLocalRing.maximalIdeal R)
    {r : R} (hr : ψ r ≠ 0) : IsUnit r := by
  apply IsLocalRing.notMem_maximalIdeal.mp
  rw [← hker]
  exact hr

/-- The evaluated homogeneous equation yields the square/fourth-power identity
in every chart ring. -/
lemma map_curveEquation_homogenize {K R : Type*} [CommRing K] [Nontrivial K]
    [CommRing R] (φ : Polynomial (MvPolynomial (Fin 3) K) →+* R)
    (ρ u v ρ' u' v' A a : K)
    (he : φ (curveHomogenize 12 (curveEquation ρ u v ρ' u' v' A a)) = 0) :
    φ (C (MvPolynomial.C A)) * φ X ^ 2 *
      φ (curveHomogenize 10 (curveResultant ρ u v ρ' u' v')) =
    φ (C (MvPolynomial.C a)) * φ (curveHomogenize 3 (curveNorm ρ u v ρ' u' v')) ^ 4 := by
  rw [curveEquation_homogenize, map_sub, sub_eq_zero] at he
  simpa only [map_mul, map_pow] using he

/-- Actual homogeneous equations imply even local infinity length. The hypotheses
spell out the local chart and its residue map; no normalization or DVR is needed. -/
theorem nonexceptional_local_infinity_length_even {R : Type*}
    [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {ρ u v : ℝ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern ρ u v) (ρ' u' v' A a : ℂ)
    (hA : A ≠ 0) (ha : a ≠ 0) (z : Fin 3 → ℂ) (hz : ∃ j, z j ≠ 0)
    (φ : Polynomial (MvPolynomial (Fin 3) ℂ) →+* R) (ψ : R →+* ℂ)
    (hker : RingHom.ker ψ = IsLocalRing.maximalIdeal R)
    (hres : ∀ p, ψ (φ p) = MvPolynomial.eval z (p.eval 0))
    (hw : φ X ≠ 0)
    (hq : φ (curveHomogenize 2 (curveQuadratic (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v')) = 0)
    (he : φ (curveHomogenize 12 (curveEquation (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v' A a)) = 0) :
    ∃ n : ℕ, Module.length R (R ⧸ Ideal.span {φ X}) = (2 * n : ℕ) := by
  have hq0 : MvPolynomial.eval z
      ((curveHomogenize 2 (curveQuadratic (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v')).eval 0) = 0 := by
    rw [← hres, hq, map_zero]
  have he0 : MvPolynomial.eval z
      ((curveHomogenize 12 (curveEquation (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v' A a)).eval 0) = 0 := by
    rw [← hres, he, map_zero]
  have hr : IsUnit (φ (curveHomogenize 10
      (curveResultant (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v'))) := by
    apply isUnit_of_residue_ne_zero ψ hker
    rw [hres]
    exact nonexceptional_resultant_at_infinity_ne_zero hρ hu hv hne
      ρ' u' v' A a ha z hz hq0 he0
  have hunit (c : ℂ) (hc : c ≠ 0) : IsUnit (φ (C (MvPolynomial.C c))) := by
    apply isUnit_of_residue_ne_zero ψ hker
    simpa only [hres, eval_C, MvPolynomial.eval_C] using hc
  exact local_length_even_of_square_unit_eq_fourth (hunit A hA) (hunit a ha) hr hw
    (map_curveEquation_homogenize φ (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v' A a he)

end
end PierceLengthBound.FixedDividend
