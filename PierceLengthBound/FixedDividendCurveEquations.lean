/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendCoprimality
public import PierceLengthBound.FixedDividendTotalDegree

/-!
# The fixed-dividend equations in the coordinate ring

The quadratic and the degree-twelve fixed-dividend equation `A R - a N⁴` in three
free node coordinates: their degree bounds, evaluations, and vanishing at orbit
points.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- The fixed-dividend equation in three free node coordinates. -/
def curveEquation {K : Type*} [CommRing K] (ρ u v ρ' u' v' A a : K) :
    MvPolynomial (Fin 3) K :=
  C A * curveResultant ρ u v ρ' u' v' - C a * curveNorm ρ u v ρ' u' v' ^ 4

lemma curveEquation_degree_le {K : Type*} [Field K] (ρ u v ρ' u' v' A a : K) :
    (curveEquation ρ u v ρ' u' v' A a).totalDegree ≤ 12 := by
  have hs : ∀ j : Fin 4, (completeNodes (C ρ) (C u) (C v) (fun j => X j) j).totalDegree ≤ 1 := by
    intro j
    fin_cases j
    all_goals simp only [completeNodes, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    all_goals try exact le_of_eq (totalDegree_X _)
    change (fourthNode (C ρ) (C u) (C v) (X 0) (X 1) (X 2)).totalDegree ≤ 1
    have he : (fourthNode (C ρ) (C u) (C v) (X 0) (X 1) (X 2) : MvPolynomial (Fin 3) K) =
        C (ρ + u) * X 0 + C (-(u - v)) * X 1 + C (-(v - 1)) * X 2 := by
      simp [fourthNode]
      ring
    rw [he]
    exact linear_form_degree_le _ _ _
  have hr : (curveResultant ρ u v ρ' u' v').totalDegree ≤ 10 :=
    fixed_dividend_resultant_totalDegree_le_ten _ _ _ hs
  have hd : (curveNorm ρ u v ρ' u' v').totalDegree ≤ 3 :=
    lineNorm_totalDegree_le_three _ _ _ _ _ _ _ (fun j => le_of_eq (totalDegree_X j))
  apply (totalDegree_sub _ _).trans
  apply max_le
  · calc
      _ ≤ (C A : MvPolynomial (Fin 3) K).totalDegree +
        (curveResultant ρ u v ρ' u' v').totalDegree := totalDegree_mul _ _
      _ ≤ 0 + 10 := add_le_add (le_of_eq (totalDegree_C _)) hr
      _ ≤ 12 := by norm_num
  · calc
      _ ≤ (C a : MvPolynomial (Fin 3) K).totalDegree +
        (curveNorm ρ u v ρ' u' v' ^ 4).totalDegree := totalDegree_mul _ _
      _ ≤ 0 + 4 * 3 := add_le_add (le_of_eq (totalDegree_C _))
        ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left 4 hd))
      _ = 12 := by norm_num

lemma eval_curveQuadratic {K : Type*} [CommRing K] (ρ u v ρ' u' v' : K) (x : Fin 3 → K) :
    eval x (curveQuadratic ρ u v ρ' u' v') =
      lineQuadratic ρ u v ρ' u' v' (x 0) (x 1) (x 2) := by
  rw [curveQuadratic, map_lineQuadratic]
  simp

lemma eval_curveNorm {K : Type*} [CommRing K] (ρ u v ρ' u' v' : K) (x : Fin 3 → K) :
    eval x (curveNorm ρ u v ρ' u' v') = lineNorm ρ u v ρ' u' v' (x 0) (x 1) (x 2) := by
  rw [curveNorm, map_lineNorm]
  simp

lemma eval_curveResultant {K : Type*} [CommRing K] (ρ u v ρ' u' v' : K) (x : Fin 3 → K) :
    eval x (curveResultant ρ u v ρ' u' v') =
      Polynomial.resultant (firstNewtonQuartic (fun j : Fin 4 => coeffs ρ u v j.castSucc)
        (completeNodes ρ u v x))
      (Polynomial.X * nextNewtonQuartic (fun j : Fin 4 => coeffs ρ' u' v' j.castSucc)
        (completeNodes ρ u v x)) 4 5 := by
  have hn : eval x ∘ completeNodes (C ρ) (C u) (C v) (fun j => X j) =
      completeNodes ρ u v x := by
    funext j
    fin_cases j <;> simp [completeNodes, fourthNode]
  have hc (r s w : K) : eval x ∘ (fun j : Fin 4 => C (coeffs r s w j.castSucc)) =
      (fun j : Fin 4 => coeffs r s w j.castSucc) := by funext j; simp
  unfold curveResultant
  rw [← Polynomial.resultant_map_map, Polynomial.map_mul, Polynomial.map_X,
    map_firstNewtonQuartic, map_nextNewtonQuartic, hn, hc, hc]

/-- The orbit point lies on the coordinate-ring quadratic. -/
theorem orbit_curveQuadratic_zero {a b i : ℕ} (hba : b < a) (hi : i + 6 < P a b) :
    eval (orbitFreeNodes a b i) (curveQuadratic (patternRho a b i)
      (patternU a b i) (patternV a b i) (patternRho a b (i + 1))
      (patternU a b (i + 1)) (patternV a b (i + 1))) = 0 := by
  rw [eval_curveQuadratic]
  exact orbit_lineQuadratic_zero hba hi

/-- The fixed-dividend coordinate-ring equation vanishes at the orbit point. -/
theorem orbit_curveEquation_zero {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b) :
    eval (orbitFreeNodes a b i) (curveEquation (patternRho a b i)
      (patternU a b i) (patternV a b i) (patternRho a b (i + 1))
      (patternU a b (i + 1)) (patternV a b (i + 1)) (Lz a b i : ℝ) (a : ℝ)) = 0 := by
  have hn : completeNodes (patternRho a b i) (patternU a b i) (patternV a b i)
      (orbitFreeNodes a b i) = (fun j : Fin 4 => pt a b i ((j : ℕ) + 1)) := by
    funext j
    fin_cases j <;> simp only [completeNodes, orbitFreeNodes, Fin.isValue, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Nat.reduceAdd, zero_add]
    exact orbit_fourthNode (i := i) hba (by omega)
  simp only [curveEquation, map_sub, map_mul, eval_C, map_pow,
    eval_curveResultant, eval_curveNorm]
  change (Lz a b i : ℝ) * Polynomial.resultant
    (firstNewtonQuartic (fun j : Fin 4 => orbitCoeffs a b i j.castSucc) _)
    (Polynomial.X * nextNewtonQuartic
      (fun j : Fin 4 => orbitCoeffs a b (i + 1) j.castSucc) _) 4 5 -
    (a : ℝ) * lineNorm _ _ _ _ _ _ (pt a b i 1) (pt a b i 2) (pt a b i 3) ^ 4 = 0
  rw [hn, ← orbitQuartic_newton, ← nextQuartic_newton, orbit_lineNorm_eq (i := i) hba (by omega)]
  exact sub_eq_zero.mpr (orbit_fixed_dividend_identity hba hi)

end
end PierceLengthBound.FixedDividend
