/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import PierceLengthBound.FixedDividendInfinityCover

/-!
# Rational certificates for the nonexceptional infinity chart

The Nullstellensatz is applied over the rational coefficient field with complex
zeros. Thus the chart-cover certificates themselves are rational, and no
geometric component decomposition or degree descent is needed.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

lemma map_leadingQuadratic {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (a b c : K) :
    map f (leadingQuadratic a b c) = leadingQuadratic (f a) (f b) (f c) := by
  simp [leadingQuadratic, ternaryQuadratic]

lemma map_leadingCubic {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (a b c : K) :
    map f (leadingCubic a b c) = leadingCubic (f a) (f b) (f c) := by
  simp [leadingCubic]

/-- The first-chart complement ideal with rational coefficients. -/
def rationalInfinityBoundaryIdeal (ρ u v : ℚ) : Ideal (MvPolynomial (Fin 3) ℚ) :=
  Ideal.span {leadingQuadratic (-ρ - u) (u - v) (v - 1),
    leadingCubic (-ρ - u) (u - v) (v - 1) ^ 4, X 0}

lemma rational_infinity_boundary_zero {ρ u v : ℚ}
    (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ))
    (z : Fin 3 → ℂ) (hz : z ∈ zeroLocus ℂ (rationalInfinityBoundaryIdeal ρ u v)) :
    z = 0 := by
  apply nonexceptional_infinity_boundary_zero
    (by exact_mod_cast hρ) (by exact_mod_cast hu) (by exact_mod_cast hv) hne z
  rw [infinityBoundaryIdeal, zeroLocus_span]
  rw [rationalInfinityBoundaryIdeal, zeroLocus_span] at hz
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq] at hz ⊢
  have hev (p : MvPolynomial (Fin 3) ℚ) :
      aeval z p = eval z (map (algebraMap ℚ ℂ) p) := eval₂_eq_eval_map _ _ _
  simp only [hev, map_pow, map_leadingQuadratic, map_leadingCubic, map_X,
    map_sub, map_neg, map_one] at hz
  simpa [aeval_eq_eval] using hz

/-- Rational coordinate powers lie in the rational boundary ideal. -/
theorem nonexceptional_infinity_coordinate_powers {ρ u v : ℚ}
    (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) :
    ∃ N : ℕ, 0 < N ∧ ∀ j : Fin 3, (X j : MvPolynomial (Fin 3) ℚ) ^ N ∈
      rationalInfinityBoundaryIdeal ρ u v := by
  classical
  have hp (j : Fin 3) : ∃ n : ℕ, (X j : MvPolynomial (Fin 3) ℚ) ^ n ∈
      rationalInfinityBoundaryIdeal ρ u v := by
    have hm : (X j : MvPolynomial (Fin 3) ℚ) ∈
        vanishingIdeal ℚ (zeroLocus ℂ (rationalInfinityBoundaryIdeal ρ u v)) := by
      intro z hz
      rw [rational_infinity_boundary_zero hρ hu hv hne z hz]
      simp
    rw [vanishingIdeal_zeroLocus_eq_radical] at hm
    exact hm
  choose n hn using hp
  let N := Finset.univ.sup n + 1
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro j
  have hj : n j ≤ N := by
    have := Finset.le_sup (f := n) (Finset.mem_univ j)
    dsimp [N]
    omega
  have ht := (rationalInfinityBoundaryIdeal ρ u v).mul_mem_left
    ((X j : MvPolynomial (Fin 3) ℚ) ^ (N - n j)) (hn j)
  simpa only [← pow_add, Nat.sub_add_cancel hj] using ht

end
end PierceLengthBound.FixedDividend
