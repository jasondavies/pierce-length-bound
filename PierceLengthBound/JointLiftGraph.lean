/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftCoordinates

/-! Graph ideals for several rational functions with a common denominator. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- Old coordinates and any family of rational coordinates in one localization. -/
def jointGraphMap {K σ ι : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (P : ι → MvPolynomial σ K) (Q : MvPolynomial σ K) :
    MvPolynomial (σ ⊕ ι) K →ₐ[K] graphLocalization I Q :=
  MvPolynomial.aeval (Sum.elim
    (fun j => algebraMap (MvPolynomial σ K ⧸ I) (graphLocalization I Q)
      (Ideal.Quotient.mk I (X j)))
    (fun j => algebraMap (MvPolynomial σ K ⧸ I) (graphLocalization I Q)
      (Ideal.Quotient.mk I (P j)) * IsLocalization.Away.invSelf (Ideal.Quotient.mk I Q)))

def jointGraphIdeal {K σ ι : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (P : ι → MvPolynomial σ K) (Q : MvPolynomial σ K) :
    Ideal (MvPolynomial (σ ⊕ ι) K) := RingHom.ker (jointGraphMap I P Q)

theorem jointGraphIdeal_isPrime {K σ ι : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime] (P : ι → MvPolynomial σ K)
    (Q : MvPolynomial σ K) (hQ : Q ∉ I) : (jointGraphIdeal I P Q).IsPrime := by
  have hQ0 : Ideal.Quotient.mk I Q ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hQ
  let : IsDomain (graphLocalization I Q) := Localization.Away.isDomain hQ0
  exact RingHom.ker_isPrime (jointGraphMap I P Q)

set_option synthInstance.maxHeartbeats 200000 in
-- The quotient and denominator localization form a nested algebra tower.
lemma jointGraphMap_rename {K σ ι : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (P : ι → MvPolynomial σ K) (Q f : MvPolynomial σ K) :
    jointGraphMap I P Q (MvPolynomial.rename Sum.inl f) =
      algebraMap (MvPolynomial σ K ⧸ I) (graphLocalization I Q) (Ideal.Quotient.mk I f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    rw [rename_C]
    have h1 : jointGraphMap I P Q (C c) = algebraMap K (graphLocalization I Q) c :=
      (jointGraphMap I P Q).commutes c
    rw [h1]
    exact IsScalarTower.algebraMap_apply K (MvPolynomial σ K ⧸ I) (graphLocalization I Q) c
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, map_add]
  | mul_X f j hf =>
    rw [map_mul, map_mul, hf, map_mul, map_mul, rename_X]
    congr 1
    simp [jointGraphMap]

/-- Projection of the graph is dense in the base: contraction recovers its ideal. -/
theorem jointGraph_rename_mem_iff {K σ ι : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime] (P : ι → MvPolynomial σ K)
    (Q f : MvPolynomial σ K) (hQ : Q ∉ I) :
    MvPolynomial.rename Sum.inl f ∈ jointGraphIdeal I P Q ↔ f ∈ I := by
  have hQ0 : Ideal.Quotient.mk I Q ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hQ
  have hinj : Function.Injective
      (algebraMap (MvPolynomial σ K ⧸ I) (graphLocalization I Q)) := by
    apply IsLocalization.injective (M := Submonoid.powers (Ideal.Quotient.mk I Q))
    intro x hx
    obtain ⟨n, rfl⟩ := hx
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hQ0)
  change jointGraphMap I P Q (MvPolynomial.rename Sum.inl f) = 0 ↔ _
  rw [jointGraphMap_rename, map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]

/-- Each cleared rational-coordinate equation belongs to the graph ideal. -/
theorem jointGraph_equation_mem {K σ ι : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (P : ι → MvPolynomial σ K)
    (Q : MvPolynomial σ K) (j : ι) :
    MvPolynomial.rename Sum.inl Q * X (Sum.inr j) - MvPolynomial.rename Sum.inl (P j) ∈
      jointGraphIdeal I P Q := by
  change jointGraphMap I P Q _ = 0
  rw [map_sub, map_mul, jointGraphMap_rename, jointGraphMap_rename]
  have hX : jointGraphMap I P Q (X (Sum.inr j)) =
      algebraMap (MvPolynomial σ K ⧸ I) (graphLocalization I Q) (Ideal.Quotient.mk I (P j)) *
        IsLocalization.Away.invSelf (S := graphLocalization I Q) (Ideal.Quotient.mk I Q) := by
    simp [jointGraphMap]
  rw [hX, mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one, sub_self]

/-- Every base point with nonzero denominator lifts to the joint graph. -/
theorem jointGraph_point {K σ ι : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (P : ι → MvPolynomial σ K) (Q : MvPolynomial σ K)
    (z : σ → K) (hz : z ∈ coordinateZeroLocus I) (hQ : MvPolynomial.eval z Q ≠ 0) :
    Sum.elim z (fun j => MvPolynomial.eval z (P j) / MvPolynomial.eval z Q) ∈
      coordinateZeroLocus (jointGraphIdeal I P Q) := by
  let w := Sum.elim z (fun j => MvPolynomial.eval z (P j) / MvPolynomial.eval z Q)
  have hc : (graphPointMap I Q z hz hQ).comp (jointGraphMap I P Q) =
      MvPolynomial.aeval w := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j with
    | inl j => simp [jointGraphMap, w, graphPointMap_mk]
    | inr j => simp [jointGraphMap, w, graphPointMap_mk, graphPointMap_invSelf, div_eq_mul_inv]
  intro f hf
  have hf0 : jointGraphMap I P Q f = 0 := hf
  have he := congrArg (fun h : MvPolynomial (σ ⊕ ι) K →ₐ[K] K => h f) hc
  rw [AlgHom.comp_apply, hf0, map_zero] at he
  exact he.symm

/-- The concrete seven-dimensional graph of the three curvature minors and I5. -/
def orbitJointGraphIdeal (a b i : ℕ) (I : Ideal (MvPolynomial (Fin 3) ℚ)) :
    Ideal (MvPolynomial (Fin 3 ⊕ Fin 4) ℚ) :=
  jointGraphIdeal I (orbitJointNumerators a b i) (orbitJointDenominator a b i)

lemma orbitJoint_denominator_not_mem {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (I : Ideal (MvPolynomial (Fin 3) ℚ))
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I) : orbitJointDenominator a b i ∉ I := by
  intro h
  exact orbitJointDenominator_eval_ne_zero hba hi (hz _ h)

theorem orbitJointGraphIdeal_isPrime {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I) :
    (orbitJointGraphIdeal a b i I).IsPrime :=
  jointGraphIdeal_isPrime I _ _ (orbitJoint_denominator_not_mem hba hi I hz)

/-- The actual orbit point, with its four new integer coordinates, lies on this graph. -/
theorem orbitJointGraph_point {a b i J : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (I : Ideal (MvPolynomial (Fin 3) ℚ))
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (hJ : (Lz a b i : ℝ) * orbitNorm a b i = J) :
    Sum.elim (orbitFreeNodesQ a b i)
      ![(orbitCurvatureVector a b i 0 : ℚ), (orbitCurvatureVector a b i 1 : ℚ),
        (orbitCurvatureVector a b i 2 : ℚ), (J : ℚ)] ∈
      coordinateZeroLocus (orbitJointGraphIdeal a b i I) := by
  have h := jointGraph_point I (orbitJointNumerators a b i) (orbitJointDenominator a b i)
    (orbitFreeNodesQ a b i) hz (orbitJointDenominator_eval_ne_zero hba hi)
  have hj : eval (orbitFreeNodesQ a b i) (jointRankFivePolynomial a b i) = (J : ℚ) := by
    apply (algebraMap ℚ ℝ).injective
    exact (jointRankFivePolynomial_eval_cast hba hi).trans hJ
  have he : (fun j => eval (orbitFreeNodesQ a b i) (orbitJointNumerators a b i j) /
      eval (orbitFreeNodesQ a b i) (orbitJointDenominator a b i)) =
      ![(orbitCurvatureVector a b i 0 : ℚ), (orbitCurvatureVector a b i 1 : ℚ),
        (orbitCurvatureVector a b i 2 : ℚ), (J : ℚ)] := by
    funext j
    fin_cases j
    · exact orbitJoint_curvature_evaluation hba hi 0
    · exact orbitJoint_curvature_evaluation hba hi 1
    · exact orbitJoint_curvature_evaluation hba hi 2
    · exact (orbitJoint_rankFive_evaluation hba hi).trans hj
  rw [he] at h
  exact h

/-- Positivity and both selected coordinate boxes hold on the actual prime graph. -/
theorem selected_jointGraph_point {a b s T A i : ℕ} (hba : b < a)
    (hmem : ∀ j < T, A ≤ orb a b (s + j) ∧ orb a b (s + j) < 2 * A)
    (hsT : s + T ≤ P a b) (hi : i ∈ selectedStarts a b s T A)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I) :
    (orbitJointGraphIdeal a b i I).IsPrime ∧
      ∃ J : ℕ, 0 < J ∧ J ≤ selectedRankFiveHeight a A T ∧
        (∀ j, |orbitCurvatureVector a b i j| ≤ (selectedCurvatureHeight a A T : ℤ)) ∧
        Sum.elim (orbitFreeNodesQ a b i)
          ![(orbitCurvatureVector a b i 0 : ℚ), (orbitCurvatureVector a b i 1 : ℚ),
            (orbitCurvatureVector a b i 2 : ℚ), (J : ℚ)] ∈
          coordinateZeroLocus (orbitJointGraphIdeal a b i I) := by
  have hP := (selectedStart_spec hmem hsT hi).1
  obtain ⟨J, hpos, hJ, hheight⟩ := selected_rankFive_positive_integer hba hmem hsT hi
  exact ⟨orbitJointGraphIdeal_isPrime hba (by omega) I hz, J, hpos, hheight,
    fun j => selected_orbitCurvature_bound hba hmem hsT hi j,
    orbitJointGraph_point hba (by omega) I hz hJ⟩

end
end PierceLengthBound.FixedDividend
