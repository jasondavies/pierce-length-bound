/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ConicRawDeterminant
public import PierceLengthBound.IntegralLiftQuotientNormalization
import all PierceLengthBound.FixedDividendTotalDegree

/-! Degree bounds for the lower terms of the raw fourth determinant, for use
on arbitrary curve components rather than only polynomial parametrizations. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

lemma map_rawDetLower {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (k0 k1 k2 k3 k4 : R) :
    f (rawDetLower k0 k1 k2 k3 k4) = rawDetLower (f k0) (f k1) (f k2) (f k3) (f k4) := by
  simp only [rawDetLower, map_add, map_sub, map_mul, map_pow, map_ofNat]

set_option maxHeartbeats 2000000 in
/-- The entire remainder after the degree-six Vandermonde term has degree at
most five in any linear polynomial gap coordinates. -/
theorem rawDetLower_totalDegree {K σ : Type*} [Field K]
    (k : Fin 5 → MvPolynomial σ K) (hk : ∀ j, (k j).totalDegree ≤ 1) :
    (rawDetLower (k 0) (k 1) (k 2) (k 3) (k 4)).totalDegree ≤ 5 := by
  have h0 := hk 0
  have h1 := hk 1
  have h2 := hk 2
  have h3 := hk 3
  have h4 := hk 4
  simp only [rawDetLower, ← map_ofNat (C : K →+* MvPolynomial σ K)]
  run_tac do
    let g ← Lean.Elab.Tactic.getMainGoal
    let t ← Lean.Elab.Tactic.getMainTarget
    let g' ← g.replaceTargetDefEq t.consumeMData
    Lean.Elab.Tactic.replaceMainGoal [g']
  fixed_dividend_mv_degree

/-- All five recovered gaps are linear in the three node coordinates. -/
lemma lineGaps_totalDegree {K : Type*} [Field K] (ρ u v ρ' u' v' : K) (j : Fin 5) :
    (lineGaps (C ρ) (C u) (C v) (C ρ') (C u') (C v')
      (X 0 : MvPolynomial (Fin 3) K) (X 1) (X 2) j).totalDegree ≤ 1 := by
  have h0 : (X 0 : MvPolynomial (Fin 3) K).totalDegree ≤ 1 := le_of_eq (totalDegree_X _)
  have h1 : (X 1 : MvPolynomial (Fin 3) K).totalDegree ≤ 1 := le_of_eq (totalDegree_X _)
  have h2 : (X 2 : MvPolynomial (Fin 3) K).totalDegree ≤ 1 := le_of_eq (totalDegree_X _)
  generalize hx0 : (X 0 : MvPolynomial (Fin 3) K) = x0 at *
  generalize hx1 : (X 1 : MvPolynomial (Fin 3) K) = x1 at *
  generalize hx2 : (X 2 : MvPolynomial (Fin 3) K) = x2 at *
  fin_cases j <;> simp [lineGaps, fourthNode, hx0, hx1, hx2]
  all_goals fixed_dividend_mv_degree

end
end PierceLengthBound.FixedDividend
