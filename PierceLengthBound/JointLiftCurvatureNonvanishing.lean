/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftNormalizationCut

/-! The curvature coordinates have no common zero on the affine joint graph.
This is an identity on the graph, not just a property of orbit points. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- The first three quadratic moment-row entries, expressed in consecutive gaps. -/
def curvatureRow {R : Type*} [CommRing R] (k : Fin 5 → R) : Fin 3 → R :=
  ![k 0 ^ 2 + k 1, k 1 * (2 * k 0 + k 1) + k 2,
    k 2 * (2 * k 0 + 2 * k 1 + k 2) + k 3]

/-- Cleared form of W · r = A. -/
theorem jointLiftNumerators_dot_row (P Q A J : MvPolynomial (Fin 3) ℚ)
    (k : Fin 5 → MvPolynomial (Fin 3) ℚ) :
    ∑ j : Fin 3, jointLiftNumerators P Q A J k j.castSucc * curvatureRow k j =
      A * jointLiftDenominator Q k := by
  simp [Fin.sum_univ_three, jointLiftNumerators, jointLiftDenominator,
    curvatureRow, rawHankelThree]
  ring

/-- The affine graph carries the curvature identity in its coordinate ring. -/
theorem jointGraph_curvature_dot_row
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) (P Q J : MvPolynomial (Fin 3) ℚ)
    (A : ℚ) (k : Fin 5 → MvPolynomial (Fin 3) ℚ) :
    let Ns := jointLiftNumerators P Q (C A) J k
    let D := jointLiftDenominator Q k
    let φ := jointGraphMap I Ns D
    ∑ j : Fin 3, φ (X (Sum.inr j.castSucc)) * φ (rename Sum.inl (curvatureRow k j)) =
      algebraMap ℚ _ A := by
  dsimp only
  let D := jointLiftDenominator Q k
  let Ns := jointLiftNumerators P Q (C A) J k
  let ψ : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] graphLocalization I D :=
    (IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) (graphLocalization I D)).comp
      (Ideal.Quotient.mkₐ ℚ I)
  have he := congrArg ψ (jointLiftNumerators_dot_row P Q (C A) J k)
  simp only [map_sum, map_mul] at he
  have hC : ψ (C A) = algebraMap ℚ (graphLocalization I D) A := ψ.commutes A
  have hu : ψ D * IsLocalization.Away.invSelf (Ideal.Quotient.mk I D) = 1 := by
    change algebraMap (MvPolynomial (Fin 3) ℚ ⧸ I) (graphLocalization I D)
      (Ideal.Quotient.mk I D) * _ = 1
    exact IsLocalization.Away.mul_invSelf (S := graphLocalization I D) _
  change (∑ j : Fin 3, jointGraphMap I Ns D (X (Sum.inr j.castSucc)) *
    jointGraphMap I Ns D (rename Sum.inl (curvatureRow k j))) = _
  simp only [jointGraphMap_rename]
  simp only [jointGraphMap, aeval_X, Sum.elim_inr]
  change (∑ j : Fin 3, (ψ (Ns j.castSucc) *
    IsLocalization.Away.invSelf (Ideal.Quotient.mk I D)) * ψ (curvatureRow k j)) = _
  calc _ = (∑ j : Fin 3, ψ (Ns j.castSucc) * ψ (curvatureRow k j)) *
        IsLocalization.Away.invSelf (Ideal.Quotient.mk I D) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = algebraMap ℚ _ A := by rw [he, hC, mul_assoc, hu, mul_one]

/-- Every point of the affine graph has a nonzero curvature coordinate whenever
A is nonzero. This includes points outside the original denominator chart. -/
theorem jointGraph_curvature_ne_zero
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) (P Q J : MvPolynomial (Fin 3) ℚ)
    (A : ℚ) (hA : A ≠ 0) (k : Fin 5 → MvPolynomial (Fin 3) ℚ)
    (z : Fin 3 ⊕ Fin 4 → ℚ)
    (hz : z ∈ coordinateZeroLocus
      (jointGraphIdeal I (jointLiftNumerators P Q (C A) J k) (jointLiftDenominator Q k))) :
    ∃ j : Fin 3, z (Sum.inr j.castSucc) ≠ 0 := by
  classical
  let f : MvPolynomial (Fin 3 ⊕ Fin 4) ℚ :=
    (∑ j : Fin 3, X (Sum.inr j.castSucc) * rename Sum.inl (curvatureRow k j)) - C A
  have hf : f ∈ jointGraphIdeal I (jointLiftNumerators P Q (C A) J k)
      (jointLiftDenominator Q k) := by
    change jointGraphMap I _ _ f = 0
    simp only [f, map_sub, map_sum, map_mul]
    rw [jointGraph_curvature_dot_row]
    simp [jointGraphMap]
  have he := hz f hf
  by_contra hall
  push Not at hall
  simp only [f, map_sub, map_sum, map_mul, eval_X, eval_C, hall, zero_mul,
    Finset.sum_const_zero, zero_sub, neg_eq_zero] at he
  exact hA he

/-- A nonconstant projective vector admits a nonzero linear combination that
vanishes at any point where the vector itself is nonzero. -/
theorem exists_curvature_combination_vanishing {K R ι : Type*} [Field K]
    [CommRing R] [Algebra K R] [Fintype ι]
    (W : ι → R) (φ : R →ₐ[K] K) (hne : ∃ j, φ (W j) ≠ 0)
    (hdir : ¬∃ (t : R) (v : ι → K), v ≠ 0 ∧ ∀ j, W j = t * algebraMap K R (v j)) :
    ∃ v : ι → K, (∑ j, algebraMap K R (v j) * W j) ≠ 0 ∧
      φ (∑ j, algebraMap K R (v j) * W j) = 0 := by
  classical
  obtain ⟨r, hr⟩ := hne
  by_contra h
  push Not at h
  have hcross (j : ι) :
      algebraMap K R (φ (W r)) * W j = algebraMap K R (φ (W j)) * W r := by
    let v : ι → K := fun k => (if k = j then φ (W r) else 0) -
      (if k = r then φ (W j) else 0)
    have he : (∑ k, algebraMap K R (v k) * W k) =
        algebraMap K R (φ (W r)) * W j - algebraMap K R (φ (W j)) * W r := by
      simp only [v, map_sub, apply_ite (algebraMap K R), map_zero, sub_mul,
        ite_mul, zero_mul, Finset.sum_sub_distrib]
      simp
    apply sub_eq_zero.mp
    by_contra hn
    have hn' : (∑ k, algebraMap K R (v k) * W k) ≠ 0 := by rwa [he]
    have hz : φ (∑ k, algebraMap K R (v k) * W k) = 0 := by
      rw [he]
      simp only [map_sub, map_mul, AlgHom.commutes]
      simp [mul_comm]
    exact h v hn' hz
  apply hdir
  refine ⟨algebraMap K R ((φ (W r))⁻¹) * W r, fun j => φ (W j), ?_, ?_⟩
  · intro hv
    exact hr (congrFun hv r)
  · intro j
    have he := congrArg (fun x : R => algebraMap K R ((φ (W r))⁻¹) * x) (hcross j)
    have hc : algebraMap K R ((φ (W r))⁻¹) * algebraMap K R (φ (W r)) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hr, map_one]
    calc W j = algebraMap K R ((φ (W r))⁻¹) * (algebraMap K R (φ (W r)) * W j) := by
          rw [← mul_assoc, hc, one_mul]
      _ = algebraMap K R ((φ (W r))⁻¹) * (algebraMap K R (φ (W j)) * W r) := he
      _ = _ := by ring

/-- On a retained degree-at-least-three component, a nonzero curvature
combination vanishes at the supported actual point. This supplies the extra
finite zero in the candidate; relating zero and pole degrees is separate. -/
theorem orbitJoint_exists_curvature_combination_vanishing {a b i d : ℕ}
    (hba : b < a) (hi : i + 7 < P a b)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (F : MvPolynomial (Fin 3) ℚ) (hF : Prime F) (hFdeg : F.totalDegree = 2) (hFI : F ∈ I)
    (hd3 : 3 ≤ d)
    (hd : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c) :
    let W := fun j : Fin 3 => jointGraphMap I (orbitJointNumerators a b i)
      (orbitJointDenominator a b i) (X (Sum.inr j.castSucc))
    let φ := graphPointMap I (orbitJointDenominator a b i) (orbitFreeNodesQ a b i)
      hz (orbitJointDenominator_eval_ne_zero hba hi)
    ∃ v : Fin 3 → ℚ, (∑ j, algebraMap ℚ _ (v j) * W j) ≠ 0 ∧
      φ (∑ j, algebraMap ℚ _ (v j) * W j) = 0 := by
  dsimp only
  apply exists_curvature_combination_vanishing
  · refine ⟨2, ?_⟩
    have he : graphPointMap I (orbitJointDenominator a b i) (orbitFreeNodesQ a b i) hz
        (orbitJointDenominator_eval_ne_zero hba hi)
        (jointGraphMap I (orbitJointNumerators a b i) (orbitJointDenominator a b i)
          (X (Sum.inr (2 : Fin 3).castSucc))) = (integralLiftCoordinate a b i : ℚ) := by
      simp only [jointGraphMap, aeval_X, Sum.elim_inr, map_mul,
        graphPointMap_mk, graphPointMap_invSelf]
      rw [← div_eq_mul_inv]
      exact (orbitJoint_curvature_evaluation hba hi 2).trans (by rw [orbitCurvature_third])
    rw [he]
    have hp : (1 : ℚ) ≤ integralLiftCoordinate a b i := by
      exact_mod_cast integralLiftCoordinate_pos hba (by omega : i + 3 < P a b)
    linarith
  · exact orbitJoint_curvature_direction_nonconstant hba hi I hz F hF hFdeg hFI hd3 hd

end
end PierceLengthBound.FixedDividend
