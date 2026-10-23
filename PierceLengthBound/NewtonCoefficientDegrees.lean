/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import all PierceLengthBound.FixedDividendTotalDegree
public import PierceLengthBound.FixedDividendLineResultant

/-! With linear node coordinates, the coefficient of `x^j` in the first Newton quartic has
total degree at most `4 - j`. These bounds give the coefficient orders at infinity in
`ChartNewtonOrders`, where the leading term dominates. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

lemma map_firstNewtonCoeffs {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (c s : Fin 4 → R) (j : Fin 4) :
    f (firstNewtonCoeffs c s j) =
      firstNewtonCoeffs (fun k => f (c k)) (fun k => f (s k)) j := by
  fin_cases j <;> simp [firstNewtonCoeffs]

/-- Sharp degree bound for each lower coefficient of the monic Newton quartic. -/
theorem firstNewtonCoeffs_totalDegree_sharp {K σ : Type*} [Field K]
    (c : Fin 4 → K) (s : Fin 4 → MvPolynomial σ K)
    (hs : ∀ j, (s j).totalDegree ≤ 1) (j : Fin 4) :
    (firstNewtonCoeffs (fun k => C (c k)) s j).totalDegree ≤ 4 - j.val := by
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  fin_cases j
  · simp [firstNewtonCoeffs]
  · change (C (c 1) - C (c 2) * s 0 + C (c 3) * s 0 * s 1 - s 0 * s 1 * s 2).totalDegree ≤ 3
    fixed_dividend_mv_degree
  · change (C (c 2) - C (c 3) * (s 0 + s 1) + s 0 * s 1 + s 0 * s 2 + s 1 * s 2).totalDegree ≤ 2
    fixed_dividend_mv_degree
  · change (C (c 3) - (s 0 + s 1 + s 2)).totalDegree ≤ 1
    fixed_dividend_mv_degree

/-- Evaluation of the first Newton quartic at `-q` in terms of its coefficient vector:
`q⁴ + ∑ⱼ cⱼ (-q)ʲ`, the form used in `ChartNewtonOrders`. -/
lemma firstNewtonQuartic_eval_neg {K : Type*} [CommRing K]
    (c s : Fin 4 → K) (q : K) :
    (firstNewtonQuartic c s).eval (-q) =
      q ^ 4 + ∑ j : Fin 4, firstNewtonCoeffs c s j * (-q) ^ j.val := by
  rw [firstNewtonQuartic_eq]
  simp [monicQuartic, Fin.sum_univ_four]
  ring

end
end PierceLengthBound.FixedDividend
