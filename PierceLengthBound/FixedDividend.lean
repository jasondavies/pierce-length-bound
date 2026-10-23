/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendMoments
public import PierceLengthBound.FixedDividendResultant
public import PierceLengthBound.ElevenCount
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# Newton coefficients for the fixed-dividend refinement

The Newton coefficients of the normalized monic quartic and their vanishing sum.
-/

@[expose] public section

namespace PierceLengthBound.FixedDividend

/-- Newton coefficients of the normalized monic quartic. -/
def coeffs {R : Type*} [CommRing R] (ρ u v : R) : Fin 5 → R := ![ρ, -ρ - u, u - v, v - 1, 1]

lemma coeffs_sum (ρ u v : ℝ) : ∑ j, coeffs ρ u v j = 0 := by
  simp [coeffs, Fin.sum_univ_succ]

end PierceLengthBound.FixedDividend
