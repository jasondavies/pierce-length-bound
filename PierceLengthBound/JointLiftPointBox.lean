/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftNormalizationCut
public import PierceLengthBound.JointLiftGraph
public import PierceLengthBound.JointLiftRankFiveHeight
public import PierceLengthBound.JointLiftCurvatureHeight

/-! Actual integral joint-graph points, uniform over a complete minor pattern. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Finset

/-- The joint rational map depends only on the existing complete minor pattern. -/
theorem orbitJoint_polynomials_congr {a b i l : ℕ} (h : theta a b i = theta a b l) :
    orbitJointNumerators a b i = orbitJointNumerators a b l ∧
      orbitJointDenominator a b i = orbitJointDenominator a b l := by
  obtain ⟨h0, hρ, hu, hv, hρ', hu', hv'⟩ := orbit_pattern_eq_of_theta h
  simp only [orbitJointNumerators, orbitJointDenominator, jointRankFivePolynomial,
    jointGapPolynomials, orbitLiftNumeratorQ, orbitLiftDenominatorQ, orbitCurveCofactorsQ,
    h0, hρ, hu, hv, hρ', hu', hv', and_self]

lemma orbitJointGraph_congr {a b i l : ℕ} (h : theta a b i = theta a b l)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) :
    orbitJointGraphIdeal a b i I = orbitJointGraphIdeal a b l I := by
  obtain ⟨hn, hd⟩ := orbitJoint_polynomials_congr h
  simp only [orbitJointGraphIdeal, hn, hd]

/-- Seven actual integer coordinates: three quotient offsets, W, and J. -/
def orbitJointPoint (a b i J : ℕ) : Fin 3 ⊕ Fin 4 → ℤ :=
  Sum.elim (fun j => sq a b i (j.val + 1))
    ![orbitCurvatureVector a b i 0, orbitCurvatureVector a b i 1,
      orbitCurvatureVector a b i 2, (J : ℤ)]

lemma orbitJointPoint_cast (a b i J : ℕ) :
    (fun j => (orbitJointPoint a b i J j : ℚ)) = Sum.elim (orbitFreeNodesQ a b i)
      ![(orbitCurvatureVector a b i 0 : ℚ), (orbitCurvatureVector a b i 1 : ℚ),
        (orbitCurvatureVector a b i 2 : ℚ), (J : ℚ)] := by
  funext j
  cases j with
  | inl j => simp [orbitJointPoint, sq, orbitFreeNodesQ]
  | inr j => fin_cases j <;> simp [orbitJointPoint]

/-- The original node coordinates, being sums of at most three selected gaps,
have height at most 3H. -/
lemma selected_node_height {a b s T A i : ℕ}
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hi : i ∈ selectedStarts a b s T A) (j : Fin 3) :
    |sq a b i (j.val + 1)| ≤ 3 * (selectedGapHeight a A T : ℤ) := by
  have hk := (selectedStart_spec hmem hsT hi).2.1
  have hj := j.isLt
  have hterm (m : ℕ) (hm : m ∈ Ico i (i + (j.val + 1))) :
      0 ≤ kq a b m ∧ kq a b m ≤ (selectedGapHeight a A T : ℤ) := by
    have hm' := mem_Ico.mp hm
    have h := hk (m - i) (by omega)
    rw [show i + (m - i) = m by omega] at h
    exact ⟨by omega, h.2⟩
  rw [sq_eq_sum, abs_of_nonneg (sum_nonneg fun m hm => (hterm m hm).1)]
  calc _ ≤ ∑ _m ∈ Ico i (i + (j.val + 1)), (selectedGapHeight a A T : ℤ) :=
        sum_le_sum fun m hm => (hterm m hm).2
    _ = (j.val + 1 : ℤ) * selectedGapHeight a A T := by simp
    _ ≤ 3 * (selectedGapHeight a A T : ℤ) := by
      gcongr
      exact_mod_cast (show j.val + 1 ≤ 3 by omega)

/-- The node-coordinate version differs from the candidate's gap box by an
absolute factor of at most three. -/
def jointPointBoxHeight (a A T : ℕ) : ℕ :=
  max (3 * selectedGapHeight a A T)
    (max (selectedCurvatureHeight a A T) (selectedRankFiveHeight a A T))

lemma jointPointBoxHeight_le (a A T : ℕ) :
    jointPointBoxHeight a A T ≤ 3 * max (max (selectedGapHeight a A T)
      (selectedCurvatureHeight a A T)) (selectedRankFiveHeight a A T) := by
  unfold jointPointBoxHeight
  apply max_le
  · exact Nat.mul_le_mul_left 3 ((le_max_left _ _).trans (le_max_left _ _))
  · apply max_le
    · have h := (le_max_right (selectedGapHeight a A T) (selectedCurvatureHeight a A T)).trans
        (le_max_left (max (selectedGapHeight a A T) (selectedCurvatureHeight a A T))
          (selectedRankFiveHeight a A T))
      omega
    · have h := le_max_right (max (selectedGapHeight a A T) (selectedCurvatureHeight a A T))
        (selectedRankFiveHeight a A T)
      omega

/-- Every selected state with a fixed minor pattern gives an actual integer
point in one and the same joint graph, inside the proved uniform box. -/
theorem selected_jointGraph_integerPoint {a b s T A i l : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hl : l ∈ selectedStarts a b s T A)
    (hθ : theta a b i = theta a b l) (I : Ideal (MvPolynomial (Fin 3) ℚ))
    (hz : orbitFreeNodesQ a b l ∈ coordinateZeroLocus I) :
    ∃ J : ℕ, 0 < J ∧
      (fun j => (orbitJointPoint a b l J j : ℚ)) ∈
        coordinateZeroLocus (orbitJointGraphIdeal a b i I) ∧
      ∀ j, |orbitJointPoint a b l J j| ≤ (jointPointBoxHeight a A T : ℤ) := by
  have hP := (selectedStart_spec hmem hsT hl).1
  obtain ⟨J, hpos, hJ, hheight⟩ := selected_rankFive_positive_integer hba hmem hsT hl
  refine ⟨J, hpos, ?_, ?_⟩
  · rw [orbitJointPoint_cast, orbitJointGraph_congr hθ]
    exact orbitJointGraph_point hba (by omega) I hz hJ
  · intro j
    have hH : 3 * (selectedGapHeight a A T : ℤ) ≤ (jointPointBoxHeight a A T : ℤ) := by
      exact_mod_cast (le_max_left (3 * selectedGapHeight a A T)
        (max (selectedCurvatureHeight a A T) (selectedRankFiveHeight a A T)))
    have hS : (selectedCurvatureHeight a A T : ℤ) ≤ (jointPointBoxHeight a A T : ℤ) := by
      exact_mod_cast
        ((le_max_left (selectedCurvatureHeight a A T) (selectedRankFiveHeight a A T)).trans
        (le_max_right (3 * selectedGapHeight a A T)
          (max (selectedCurvatureHeight a A T) (selectedRankFiveHeight a A T))))
    have hY : (selectedRankFiveHeight a A T : ℤ) ≤ (jointPointBoxHeight a A T : ℤ) := by
      exact_mod_cast
        ((le_max_right (selectedCurvatureHeight a A T) (selectedRankFiveHeight a A T)).trans
        (le_max_right (3 * selectedGapHeight a A T)
          (max (selectedCurvatureHeight a A T) (selectedRankFiveHeight a A T))))
    cases j with
    | inl j => exact (selected_node_height hmem hsT hl j).trans hH
    | inr j =>
      fin_cases j
      · exact (selected_orbitCurvature_bound hba hmem hsT hl 0).trans hS
      · exact (selected_orbitCurvature_bound hba hmem hsT hl 1).trans hS
      · exact (selected_orbitCurvature_bound hba hmem hsT hl 2).trans hS
      · change |(J : ℤ)| ≤ _
        rw [abs_of_nonneg (Int.natCast_nonneg J)]
        exact (show (J : ℤ) ≤ selectedRankFiveHeight a A T by exact_mod_cast hheight).trans hY

end
end PierceLengthBound.FixedDividend
