/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendHomogenization
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# The square/fourth-power identity in a chart ring

The evaluated homogeneous curve equation yields the square/fourth-power identity
in every chart ring.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

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

end
end PierceLengthBound.FixedDividend
