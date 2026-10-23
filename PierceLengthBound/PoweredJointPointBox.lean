/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PoweredJointGraph
public import PierceLengthBound.JointLiftPointBox

/-! Integer points on the powered joint graph: each selected start gives the point
`(nodes, Wᵐ, Jⁿ)` of the powered graph of its pattern, in the box with radii `3H`, `Sᵐ` and
`Yⁿ`. The powered graph depends on a start only through its pattern. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- The powered graph depends on the start only through its pattern. -/
lemma orbitPoweredJointGraph_congr {a b i l : ℕ} (h : theta a b i = theta a b l)
    (m n : ℕ) (I : Ideal (MvPolynomial (Fin 3) ℚ)) :
    orbitPoweredJointGraphIdeal a b i m n I = orbitPoweredJointGraphIdeal a b l m n I := by
  obtain ⟨hP, hD⟩ := orbitJoint_polynomials_congr h
  simp only [orbitPoweredJointGraphIdeal, orbitPoweredJointNumerators, hP, hD]

/-- The integer point `(nodes, Wᵐ, Jⁿ)` of a state, with rank-five integer `J`. -/
def orbitPoweredJointPoint (a b i J m n : ℕ) : Fin 3 ⊕ Fin 4 → ℤ :=
  Sum.elim (fun j => sq a b i (j.val + 1))
    (fun j => orbitJointPoint a b i J (Sum.inr j) ^ jointCoordinatePowers m n j)

lemma orbitFreeNodesQ_eq_of_poweredJointPoint_eq {a b i l J K m n : ℕ}
    (h : orbitPoweredJointPoint a b i J m n = orbitPoweredJointPoint a b l K m n) :
    orbitFreeNodesQ a b i = orbitFreeNodesQ a b l := by
  funext j
  have he := congrFun h (Sum.inl j)
  change sq a b i (j.val + 1) = sq a b l (j.val + 1) at he
  dsimp only [sq] at he
  dsimp only [orbitFreeNodesQ]
  exact_mod_cast he

/-- A state's powered point lies on the powered graph over any component containing its
nodes. -/
lemma orbitPoweredJointGraph_point {a b i J : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (m n : ℕ) (I : Ideal (MvPolynomial (Fin 3) ℚ))
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hJ : (Lz a b i : ℝ) * orbitNorm a b i = J) :
    (fun j => (orbitPoweredJointPoint a b i J m n j : ℚ)) ∈
      coordinateZeroLocus (orbitPoweredJointGraphIdeal a b i m n I) := by
  have hj : eval (orbitFreeNodesQ a b i) (jointRankFivePolynomial a b i) = (J : ℚ) := by
    apply (algebraMap ℚ ℝ).injective
    exact (jointRankFivePolynomial_eval_cast hba hi).trans hJ
  have hD := orbitJointDenominator_eval_ne_zero hba hi
  have hDN : eval (orbitFreeNodesQ a b i) (orbitJointDenominator a b i ^ (m + n)) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ hD
  have hh := jointGraph_point I (orbitPoweredJointNumerators a b i m n)
    (orbitJointDenominator a b i ^ (m + n)) _ hz hDN
  have he : Sum.elim (orbitFreeNodesQ a b i)
      (fun j => eval (orbitFreeNodesQ a b i) (orbitPoweredJointNumerators a b i m n j) /
        eval (orbitFreeNodesQ a b i) (orbitJointDenominator a b i ^ (m + n))) =
      (fun j => (orbitPoweredJointPoint a b i J m n j : ℚ)) := by
    funext j
    cases j with
    | inl j => simp [orbitPoweredJointPoint, orbitFreeNodesQ, sq]
    | inr j =>
      change eval (orbitFreeNodesQ a b i) (orbitPoweredJointNumerators a b i m n j) /
        eval (orbitFreeNodesQ a b i) (orbitJointDenominator a b i ^ (m + n)) = _
      simp only [orbitPoweredJointNumerators, poweredGraphNumerators, map_mul, map_pow]
      rw [powered_fraction _ _ hD (jointCoordinatePowers_le m n j)]
      change (_ / _) ^ jointCoordinatePowers m n j =
        ((orbitJointPoint a b i J (Sum.inr j) ^ jointCoordinatePowers m n j : ℤ) : ℚ)
      rw [Int.cast_pow]
      congr 1
      fin_cases j
      · exact orbitJoint_curvature_evaluation hba hi 0
      · exact orbitJoint_curvature_evaluation hba hi 1
      · exact orbitJoint_curvature_evaluation hba hi 2
      · exact (orbitJoint_rankFive_evaluation hba hi).trans hj
  rw [he] at hh
  exact hh

/-- The box `max(3H, Sᵐ, Yⁿ)` of the powered points of a window. -/
def poweredJointPointBoxHeight (a A T m n : ℕ) : ℕ :=
  max (3 * selectedGapHeight a A T)
    (max (selectedCurvatureHeight a A T ^ m) (selectedRankFiveHeight a A T ^ n))

/-- Each selected start `l` with the pattern of `i` gives, for a positive rank-five integer
`J`, an integer point of the powered graph of `i` in the box `poweredJointPointBoxHeight`. -/
theorem selected_poweredJointGraph_integerPoint {a b s T A i l : ℕ}
    (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hl : l ∈ selectedStarts a b s T A)
    (hθ : theta a b i = theta a b l) (m n : ℕ) (I : Ideal (MvPolynomial (Fin 3) ℚ))
    (hz : orbitFreeNodesQ a b l ∈ coordinateZeroLocus I) :
    ∃ J : ℕ, 0 < J ∧
      (fun j => (orbitPoweredJointPoint a b l J m n j : ℚ)) ∈
        coordinateZeroLocus (orbitPoweredJointGraphIdeal a b i m n I) ∧
      ∀ j, |orbitPoweredJointPoint a b l J m n j| ≤ (poweredJointPointBoxHeight a A T m n : ℤ) := by
  have hP := (selectedStart_spec hmem hsT hl).1
  obtain ⟨J, hpos, hJ, hheight⟩ := selected_rankFive_positive_integer hba hmem hsT hl
  refine ⟨J, hpos, ?_, ?_⟩
  · rw [orbitPoweredJointGraph_congr hθ]
    exact orbitPoweredJointGraph_point hba (by omega) m n I hz hJ
  · have hH : 3 * (selectedGapHeight a A T : ℤ) ≤
        (poweredJointPointBoxHeight a A T m n : ℤ) := by
      exact_mod_cast le_max_left (3 * selectedGapHeight a A T)
        (max (selectedCurvatureHeight a A T ^ m) (selectedRankFiveHeight a A T ^ n))
    have hS : (selectedCurvatureHeight a A T : ℤ) ^ m ≤
        (poweredJointPointBoxHeight a A T m n : ℤ) := by
      exact_mod_cast (le_max_left (selectedCurvatureHeight a A T ^ m)
        (selectedRankFiveHeight a A T ^ n)).trans (le_max_right (3 * selectedGapHeight a A T) _)
    have hY : (selectedRankFiveHeight a A T : ℤ) ^ n ≤
        (poweredJointPointBoxHeight a A T m n : ℤ) := by
      exact_mod_cast (le_max_right (selectedCurvatureHeight a A T ^ m)
        (selectedRankFiveHeight a A T ^ n)).trans (le_max_right (3 * selectedGapHeight a A T) _)
    have hcurv (j : Fin 3) : |orbitCurvatureVector a b l j ^ m| ≤
        (poweredJointPointBoxHeight a A T m n : ℤ) := by
      rw [abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _)
        (selected_orbitCurvature_bound hba hmem hsT hl j) m).trans hS
    intro j
    cases j with
    | inl j => exact (selected_node_height hmem hsT hl j).trans hH
    | inr j =>
      fin_cases j
      · exact hcurv 0
      · exact hcurv 1
      · exact hcurv 2
      · change |(J : ℤ) ^ n| ≤ _
        rw [abs_pow, abs_of_nonneg (Int.natCast_nonneg J)]
        exact (pow_le_pow_left₀ (Int.natCast_nonneg J)
          (by exact_mod_cast hheight : (J : ℤ) ≤ selectedRankFiveHeight a A T) n).trans hY

end
end PierceLengthBound.FixedDividend
