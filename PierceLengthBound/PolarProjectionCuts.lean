/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionOrbit
public import PierceLengthBound.JointLiftNormalizationCut
public import PierceLengthBound.JointLiftPointBox
public import PierceLengthBound.JointLiftGraphDegree

/-! Polynomial cuts retaining the actual affine polar identities on prime curves.
The three identities either hold on the whole component or cut out a uniformly
bounded number of supported states of one complete minor pattern. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Matrix Finset

/-- The affine polar vector, written as rational polynomials in the free nodes. -/
def orbitPolarPolynomial (a b i : ℕ) (j : Fin 3) : MvPolynomial (Fin 3) ℚ :=
  (∑ k : Fin 3, C (polarMatrix (patternRhoQ a b i) (patternUQ a b i)
    (patternVQ a b i) j k) * jointGapPolynomials a b i k.castSucc.castSucc) +
  C (polarLinear (patternRhoQ a b i) (patternUQ a b i) (patternVQ a b i)
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1)) j)

lemma orbitPolarPolynomial_degree (a b i : ℕ) (j : Fin 3) :
    (orbitPolarPolynomial a b i j).totalDegree ≤ 1 := by
  have hm (k : Fin 3) :
      (C (polarMatrix (patternRhoQ a b i) (patternUQ a b i)
        (patternVQ a b i) j k) *
        jointGapPolynomials a b i k.castSucc.castSucc).totalDegree ≤ 1 := by
    exact (totalDegree_mul _ _).trans (by
      simpa only [totalDegree_C, zero_add] using
        jointGapPolynomials_degree a b i k.castSucc.castSucc)
  unfold orbitPolarPolynomial
  simp only [Fin.sum_univ_three]
  apply (totalDegree_add _ _).trans
  refine max_le ?_ (by simp)
  apply (totalDegree_add _ _).trans
  refine max_le ?_ (hm 2)
  exact (totalDegree_add _ _).trans (max_le (hm 0) (hm 1))

lemma orbitPolarPolynomial_eval_cast {a b i : ℕ} (hba : b < a)
    (hi : i + 7 < P a b) (j : Fin 3) :
    (eval (orbitFreeNodesQ a b i) (orbitPolarPolynomial a b i j) : ℝ) =
      orbitPolarVector a b i j := by
  simp only [orbitPolarPolynomial, map_add, map_sum, map_mul, eval_C,
    jointGapPolynomials_eval hba hi, Rat.cast_add, Rat.cast_sum, Rat.cast_mul,
    Rat.cast_intCast, Fin.val_castSucc]
  fin_cases j <;>
    simp [orbitPolarVector, polarVector, polarMatrix, polarLinear, dotProduct,
      Fin.sum_univ_three, patternRhoQ_cast, patternUQ_cast, patternVQ_cast, kq, kk]

/-- The denominator-cleared identity `J W_j = A² V_j`. -/
def orbitPolarIdentityPolynomial (a b i : ℕ) (j : Fin 3) : MvPolynomial (Fin 3) ℚ :=
  jointRankFivePolynomial a b i * orbitJointNumerators a b i j.castSucc -
    C ((Lz a b i : ℚ) ^ 2) * orbitPolarPolynomial a b i j * orbitJointDenominator a b i

lemma orbitPolarIdentityPolynomial_degree (a b i : ℕ) (j : Fin 3) :
    (orbitPolarIdentityPolynomial a b i j).totalDegree ≤ 250 := by
  have hJ := jointRankFivePolynomial_degree a b i
  have hN := (orbitJoint_totalDegree_le a b i).1 j.castSucc
  have hD := (orbitJoint_totalDegree_le a b i).2
  have hV := orbitPolarPolynomial_degree a b i j
  unfold orbitPolarIdentityPolynomial
  apply (totalDegree_sub _ _).trans
  refine max_le ((totalDegree_mul _ _).trans (by omega)) ?_
  have hC := totalDegree_mul (C ((Lz a b i : ℚ) ^ 2)) (orbitPolarPolynomial a b i j)
  simp only [totalDegree_C, zero_add] at hC
  exact (totalDegree_mul _ _).trans (by omega)

lemma orbitPolarIdentityPolynomial_eval {a b i : ℕ} (hba : b < a)
    (hi : i + 7 < P a b) (j : Fin 3) :
    eval (orbitFreeNodesQ a b i) (orbitPolarIdentityPolynomial a b i j) = 0 := by
  have hN := (div_eq_iff (orbitJointDenominator_eval_ne_zero hba hi)).mp
    (orbitJoint_curvature_evaluation hba hi j)
  have he := orbit_rankFive_polar_identity hba hi j
  have hJ := jointRankFivePolynomial_eval_cast hba hi
  rw [joint_rank_five_identity hba hi] at hJ
  have hV := orbitPolarPolynomial_eval_cast hba hi j
  apply (Rat.cast_injective (α := ℝ))
  simp only [orbitPolarIdentityPolynomial, map_sub, map_mul, eval_C, hN,
    Rat.cast_sub, Rat.cast_mul, Rat.cast_pow, Rat.cast_intCast, Rat.cast_zero, hJ, hV]
  linear_combination (eval (orbitFreeNodesQ a b i) (orbitJointDenominator a b i) : ℝ) * he

lemma orbitPolarPolynomial_congr {a b i l : ℕ} (h : theta a b i = theta a b l)
    (j : Fin 3) : orbitPolarPolynomial a b i j = orbitPolarPolynomial a b l j := by
  obtain ⟨h0, hρ, hu, hv, hρ', hu', hv'⟩ := orbit_pattern_eq_of_theta h
  simp only [orbitPolarPolynomial, jointGapPolynomials, hρ, hu, hv, hρ', hu', hv']

lemma orbitPolarIdentityPolynomial_congr {a b i l : ℕ}
    (h : theta a b i = theta a b l) (j : Fin 3) :
    orbitPolarIdentityPolynomial a b i j = orbitPolarIdentityPolynomial a b l j := by
  obtain ⟨hN, hD⟩ := orbitJoint_polynomials_congr h
  have hV := orbitPolarPolynomial_congr h j
  obtain ⟨h0, hρ, hu, hv, hρ', hu', hv'⟩ := orbit_pattern_eq_of_theta h
  simp only [orbitPolarIdentityPolynomial, jointRankFivePolynomial,
    hN, hD, hV, h0, hρ, hu, hv, hρ', hu', hv']

/-- Any failed polar identity gives an absolute degree-250 section. -/
theorem orbitPolarIdentityPolynomial_proper_cut {a b i d : ℕ} (hba : b < a)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hd : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c)
    (j : Fin 3) (hproper : orbitPolarIdentityPolynomial a b i j ∉ I)
    {ι : Type*} [Fintype ι] (l : ι → ℕ)
    (hinj : Function.Injective (fun k => orbitFreeNodesQ a b (l k)))
    (hi : ∀ k, l k + 7 < P a b) (hθ : ∀ k, theta a b i = theta a b (l k))
    (hp : ∀ k, orbitFreeNodesQ a b (l k) ∈ coordinateZeroLocus I) :
    Fintype.card ι ≤ 250 * d := by
  apply polynomial_section_card_le_degree I d hd _ hproper 250
    (orbitPolarIdentityPolynomial_degree a b i j) _ hinj hp
  intro k
  rw [orbitPolarIdentityPolynomial_congr (hθ k)]
  exact orbitPolarIdentityPolynomial_eval hba (hi k) j

/-- Retain all three polar identities, or discard only a bounded set of states. -/
theorem orbitPolarIdentityPolynomial_identity_or_card_bound {a b i d : ℕ} (hba : b < a)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hd : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c)
    {ι : Type*} [Fintype ι] (l : ι → ℕ) (hl : Function.Injective l)
    (hi : ∀ k, l k + 7 < P a b) (hθ : ∀ k, theta a b i = theta a b (l k))
    (hp : ∀ k, orbitFreeNodesQ a b (l k) ∈ coordinateZeroLocus I) :
    (∀ j, orbitPolarIdentityPolynomial a b i j ∈ I) ∨ Fintype.card ι ≤ 250 * d := by
  classical
  by_cases h : ∀ j, orbitPolarIdentityPolynomial a b i j ∈ I
  · exact Or.inl h
  · obtain ⟨j, hj⟩ := not_forall.mp h
    exact Or.inr (orbitPolarIdentityPolynomial_proper_cut hba I hd j hj l
      (orbitFreeNodesQ_injective_of_pattern hba l hl hi hθ) hi hθ hp)

/-- Membership of a polar cut identifies the rational functions over any field. -/
theorem orbitPolarIdentityPolynomial_field_identity {F : Type*} [Field F]
    (ψ : MvPolynomial (Fin 3) ℚ →+* F) {a b i : ℕ} (j : Fin 3)
    (hD : ψ (orbitJointDenominator a b i) ≠ 0)
    (hcut : ψ (orbitPolarIdentityPolynomial a b i j) = 0) :
    ψ (jointRankFivePolynomial a b i) *
        (ψ (orbitJointNumerators a b i j.castSucc) / ψ (orbitJointDenominator a b i)) =
      ψ (C ((Lz a b i : ℚ) ^ 2)) * ψ (orbitPolarPolynomial a b i j) := by
  have he : ψ (jointRankFivePolynomial a b i) * ψ (orbitJointNumerators a b i j.castSucc) =
      ψ (C ((Lz a b i : ℚ) ^ 2)) * ψ (orbitPolarPolynomial a b i j) *
        ψ (orbitJointDenominator a b i) := by
    simpa only [orbitPolarIdentityPolynomial, map_sub, map_mul, sub_eq_zero] using hcut
  rw [← mul_div_assoc, he, mul_div_cancel_right₀ _ hD]

end
end PierceLengthBound.FixedDividend
