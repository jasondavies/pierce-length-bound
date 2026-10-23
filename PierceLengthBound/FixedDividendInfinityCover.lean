/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendHomogenization
public import Mathlib.RingTheory.Nullstellensatz

/-!
# The first-node chart covers the nonexceptional infinity section

The leading quadratic and fourth power of the leading norm have no nonzero
common zero with first node zero, so the corresponding homogeneous boundary ideal
has only the origin as complex zero.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- The leading equations together with the complement of the first-node chart. -/
def infinityBoundaryIdeal (ρ u v : ℂ) : Ideal (MvPolynomial (Fin 3) ℂ) :=
  Ideal.span {leadingQuadratic (-ρ - u) (u - v) (v - 1),
    leadingCubic (-ρ - u) (u - v) (v - 1) ^ 4, X 0}

/-- No nonzero infinity direction is missed by the first-node chart. -/
theorem nonexceptional_infinity_boundary_zero {ρ u v : ℝ}
    (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0) (hne : NonexceptionalPattern ρ u v)
    (z : Fin 3 → ℂ) (hz : z ∈ zeroLocus ℂ (infinityBoundaryIdeal (ρ : ℂ) u v)) :
    z = 0 := by
  have hq := hz (leadingQuadratic (-(ρ : ℂ) - u) ((u : ℂ) - v) ((v : ℂ) - 1))
    (Ideal.subset_span (by simp))
  have hd := hz (leadingCubic (-(ρ : ℂ) - u) ((u : ℂ) - v) ((v : ℂ) - 1) ^ 4)
    (Ideal.subset_span (by simp))
  have hz0 : z 0 = 0 := by
    simpa using hz (X 0) (Ideal.subset_span (by simp))
  change eval z (leadingQuadratic (-(ρ : ℂ) - u) ((u : ℂ) - v) ((v : ℂ) - 1)) = 0 at hq
  change eval z (leadingCubic (-(ρ : ℂ) - u) ((u : ℂ) - v) ((v : ℂ) - 1) ^ 4) = 0 at hd
  rw [map_pow, pow_eq_zero_iff (by decide : 4 ≠ 0), eval_leadingCubic_moment] at hd
  rw [eval_leadingQuadratic_moment] at hq
  by_contra hz'
  have hnon : ∃ j, z j ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hz' (funext hh)
  have hm : ∀ m < 4, ∑ j : Fin 5, coeffs (ρ : ℂ) (u : ℂ) (v : ℂ) j *
      completeDirection (ρ : ℂ) (u : ℂ) (v : ℂ) z j ^ m = 0 := by
    intro m hm
    interval_cases m
    · exact completeDirection_moment_zero _ _ _ _
    · exact completeDirection_moment_one _ _ _ _
    · exact hq
    · exact hd
  have hinj := nonexceptional_leading_nodes_injective hρ hu hv hne
    (completeDirection (ρ : ℂ) (u : ℂ) (v : ℂ) z)
    (completeDirection_not_constant _ _ _ z hnon) (by simp [completeDirection]) hm
  have he : completeDirection (ρ : ℂ) (u : ℂ) (v : ℂ) z 1 =
      completeDirection (ρ : ℂ) (u : ℂ) (v : ℂ) z 0 := by simpa [completeDirection] using hz0
  exact (by decide : (1 : Fin 5) ≠ 0) (hinj he)

end
end PierceLengthBound.FixedDividend
