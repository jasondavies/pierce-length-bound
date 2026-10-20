/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendCoordinates

/-!
# Exclusion of the four normalized line directions

The input is containment in the quadratic and fixed-dividend equations, expressed
as polynomial identities along the line. The resultant degree is proved rather
than assumed.
-/

@[expose] public section

namespace PierceLengthBound.FixedDividend

open Polynomial

/-- The norm restricted to one of the four normalized exceptional directions. -/
noncomputable def exceptionalNorm (ρ u v ρ' u' v' a b c : ℝ) (d : Fin 4) : ℝ[X] :=
  let s := exceptionalNodes ![a, b, c, fourthNode ρ u v a b c] d
  lineNorm (C ρ) (C u) (C v) (C ρ') (C u') (C v') (s 0) (s 1) (s 2)

/-- The first quadratic restricted to the same line. -/
noncomputable def exceptionalQuadratic (ρ u v ρ' u' v' a b c : ℝ) (d : Fin 4) : ℝ[X] :=
  let s := exceptionalNodes ![a, b, c, fourthNode ρ u v a b c] d
  lineQuadratic (C ρ) (C u) (C v) (C ρ') (C u') (C v') (s 0) (s 1) (s 2)

/-- The exact resultant restricted to the line. -/
noncomputable def exceptionalResultant (ρ u v ρ' u' v' a b c : ℝ) (d : Fin 4) : ℝ[X] :=
  let s := exceptionalNodes ![a, b, c, fourthNode ρ u v a b c] d
  resultant
    (firstNewtonQuartic (fun j : Fin 4 => C (coeffs ρ u v j.castSucc)) s)
    (X * nextNewtonQuartic (fun j : Fin 4 => C (coeffs ρ' u' v' j.castSucc)) s) 4 5

lemma eval_lineNorm (t : ℝ) (ρ u v ρ' u' v' a b c : ℝ[X]) :
    (lineNorm ρ u v ρ' u' v' a b c).eval t =
      lineNorm (ρ.eval t) (u.eval t) (v.eval t) (ρ'.eval t) (u'.eval t) (v'.eval t)
        (a.eval t) (b.eval t) (c.eval t) := by
  simp [lineNorm, lineNodes, extendedLineGaps, lineGaps, fourthNode, coeffs,
    Fin.sum_univ_succ]

lemma eval_lineQuadratic (t : ℝ) (ρ u v ρ' u' v' a b c : ℝ[X]) :
    (lineQuadratic ρ u v ρ' u' v' a b c).eval t =
      lineQuadratic (ρ.eval t) (u.eval t) (v.eval t) (ρ'.eval t) (u'.eval t) (v'.eval t)
        (a.eval t) (b.eval t) (c.eval t) := by
  simp [lineQuadratic, lineNodes, lineGaps, fourthNode, coeffs, Fin.sum_univ_succ]

lemma affine_second_difference {p : ℝ[X]} (hd : p.natDegree ≤ 1) :
    p.eval 1 + p.eval (-1) = 2 * p.eval 0 := by
  rw [p.as_sum_range_C_mul_X_pow' (by omega : p.natDegree < 2)]
  simp [Finset.sum_range_succ]
  ring

/-- Containment in the fixed-dividend equation forces the restricted norm to be affine. -/
theorem exceptionalNorm_degree_le_one {A a : ℝ} (hA : A ≠ 0) (ha : a ≠ 0)
    (ρ u v ρ' u' v' x y z : ℝ) (d : Fin 4)
    (he : C A * exceptionalResultant ρ u v ρ' u' v' x y z d =
      C a * exceptionalNorm ρ u v ρ' u' v' x y z d ^ 4) :
    (exceptionalNorm ρ u v ρ' u' v' x y z d).natDegree ≤ 1 := by
  apply norm_degree_le_one hA ha _ he
  exact line_resultant_natDegree_le_six
    (fun j : Fin 4 => coeffs ρ u v j.castSucc)
    (fun j : Fin 4 => coeffs ρ' u' v' j.castSucc) _ d

/-- The four cases retain the corresponding coefficient relation. -/
def ExceptionalRelation (ρ u v : ℝ) (d : Fin 4) : Prop :=
  ![v = 1 - ρ, v = -ρ, u = 1, u = 1 - ρ] d

/-- A contained exceptional line forces one of the four concrete obstruction equations. -/
theorem exceptional_line_obstruction {A a ρ u v ρ' u' v' x y z : ℝ} {d : Fin 4}
    (hA : A ≠ 0) (ha : a ≠ 0) (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hr : ExceptionalRelation ρ u v d)
    (hq : exceptionalQuadratic ρ u v ρ' u' v' x y z d = 0)
    (he : C A * exceptionalResultant ρ u v ρ' u' v' x y z d =
      C a * exceptionalNorm ρ u v ρ' u' v' x y z d ^ 4) :
    z = 0 ∨ y - x = 1 ∨ z - y = 1 ∨ fourthNode ρ u v x y z - x = u - v := by
  have hD := affine_second_difference (exceptionalNorm_degree_le_one hA ha _ _ _ _ _ _ _ _ _ d he)
  have hp := congrArg (fun p : ℝ[X] => p.eval 1) hq
  have hm := congrArg (fun p : ℝ[X] => p.eval (-1)) hq
  fin_cases d
  all_goals simp [ExceptionalRelation] at hr
  all_goals simp [exceptionalNorm, exceptionalQuadratic, exceptionalNodes,
    nodes03, nodes12, nodes23, nodes14, eval_lineNorm, eval_lineQuadratic] at hD hp hm
  · rw [hr] at hD hp hm ⊢
    exact Or.inl (line_obstruction_03 hρ hp hm hD)
  · rw [hr] at hD hp hm ⊢
    exact Or.inr (Or.inl (line_obstruction_12 (by linarith) hp hm hD))
  · rw [hr] at hD hp hm ⊢
    exact Or.inr (Or.inr (Or.inl (line_obstruction_23 (by linarith) hp hm hD)))
  · rw [hr] at hD hp hm ⊢
    exact Or.inr (Or.inr (Or.inr (line_obstruction_14 hp hm hD)))

/-- The four normalized line directions cannot carry a contained line through a
large-scale actual orbit window. Both defining polynomial identities are explicit. -/
theorem orbit_no_exceptional_line {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    {H X : ℤ} (hX : 1 ≤ X) (hg : ∀ m < 5, kq a b (i + m) ≤ H)
    (hU : |U1z a b i| ≤ X) (hV : |U2z a b i| ≤ X)
    (hscale : (a : ℤ) * H ^ 5 * (24 * X + 464) < (qq a b i : ℤ) ^ 4)
    (d : Fin 4) (hr : ExceptionalRelation (patternRho a b i) (patternU a b i) (patternV a b i) d)
    (hq : exceptionalQuadratic (patternRho a b i) (patternU a b i) (patternV a b i)
      (patternRho a b (i + 1)) (patternU a b (i + 1)) (patternV a b (i + 1))
      (pt a b i 1) (pt a b i 2) (pt a b i 3) d = 0) :
    C (Lz a b i : ℝ) * exceptionalResultant
      (patternRho a b i) (patternU a b i) (patternV a b i)
      (patternRho a b (i + 1)) (patternU a b (i + 1)) (patternV a b (i + 1))
      (pt a b i 1) (pt a b i 2) (pt a b i 3) d ≠
    C (a : ℝ) * exceptionalNorm
      (patternRho a b i) (patternU a b i) (patternV a b i)
      (patternRho a b (i + 1)) (patternU a b (i + 1)) (patternV a b (i + 1))
      (pt a b i 1) (pt a b i 2) (pt a b i 3) d ^ 4 := by
  intro he
  have ha : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  obtain ⟨hρ, hu, hv⟩ := orbit_pattern_signs hba (by omega : i + 6 < P a b)
  have ho := exceptional_line_obstruction (orbit_label_ne_zero hba (by omega)) ha
    hρ hu hv hr hq he
  rw [orbit_fourthNode hba (by omega)] at ho
  exact orbit_line_obstructions_excluded hba (by omega) hX hg hU hV hscale ho

end PierceLengthBound.FixedDividend
