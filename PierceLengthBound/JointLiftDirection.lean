/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftPointBox

/-! Nonconstancy of the projective curvature direction follows algebraically
from the degree-two bound for plane sections of an irreducible quadratic. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Finset

/-- The first three gaps as linear polynomials in the original node coordinates. -/
def curvatureGapVariables (K : Type*) [CommRing K] : Fin 3 → MvPolynomial (Fin 3) K :=
  ![X 0, X 1 - X 0, X 2 - X 1]

def curvatureDirectionPlane {K : Type*} [CommRing K] (v : Fin 3 → K) :
    MvPolynomial (Fin 3) K := ∑ j, C (v j) * curvatureGapVariables K j

lemma curvatureDirectionPlane_formula {K : Type*} [CommRing K] (v : Fin 3 → K) :
    curvatureDirectionPlane v =
      C (v 0 - v 1) * X 0 + C (v 1 - v 2) * X 1 + C (v 2) * X 2 := by
  simp [curvatureDirectionPlane, curvatureGapVariables, Fin.sum_univ_three]
  ring

lemma curvatureDirectionPlane_degree {K : Type*} [Field K] (v : Fin 3 → K) :
    (curvatureDirectionPlane v).totalDegree ≤ 1 := by
  rw [curvatureDirectionPlane_formula]
  exact linear_form_degree_le _ _ _

lemma curvatureDirectionPlane_ne_zero {K : Type*} [Field K] {v : Fin 3 → K} (hv : v ≠ 0) :
    curvatureDirectionPlane v ≠ 0 := by
  intro he
  have h0 := congrArg (eval ![1, 1, 1]) he
  have h1 := congrArg (eval ![0, 1, 1]) he
  have h2 := congrArg (eval ![0, 0, 1]) he
  simp [curvatureDirectionPlane, curvatureGapVariables, Fin.sum_univ_three] at h0 h1 h2
  apply hv
  funext j
  fin_cases j <;> simp_all

/-- A degree at least three curve lying on an irreducible quadratic admits no
nonzero constant linear relation among its first three gap functions. -/
theorem curvatureDirectionPlane_not_mem {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin 3) K)) (F : MvPolynomial (Fin 3) K)
    (hF : Prime F) (hFdeg : F.totalDegree = 2) (hFI : F ∈ I) {d : ℕ} (hd3 : 3 ≤ d)
    (hd : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c)
    {v : Fin 3 → K} (hv : v ≠ 0) : curvatureDirectionPlane v ∉ I := by
  intro hplane
  have hG := curvatureDirectionPlane_degree v
  have hG0 := curvatureDirectionPlane_ne_zero hv
  have hdiv : ¬F ∣ curvatureDirectionPlane v := by
    intro h
    obtain ⟨u, hu⟩ := h
    have hu0 : u ≠ 0 := by intro hz; simp [hz] at hu; exact hG0 hu
    rw [hu, totalDegree_mul_of_isDomain hF.ne_zero hu0, hFdeg] at hG
    omega
  obtain ⟨N, c, hf⟩ := hd
  have hsmall : d ≤ 2 := by
    apply eventual_affine_slope_le (N := max N 3) (c := c) (e := 4)
    intro n hn
    have h := filteredCoordinateSpace_finrank_linear hF hdiv I hFI hplane
      (show F.totalDegree + (curvatureDirectionPlane v).totalDegree ≤ n by omega)
    have h' : Module.finrank K (filteredCoordinateSpace I n) ≤ 2 * (n + 2) :=
      h.trans (Nat.mul_le_mul_right _ (by rw [hFdeg]; omega))
    have hh : (Module.finrank K (filteredCoordinateSpace I n) : ℤ) ≤ 2 * (n + 2) := by
      exact_mod_cast h'
    rw [hf n (by omega)] at hh
    norm_num only [Nat.cast_ofNat] at *
    linarith
  omega

/-- A nonzero curvature vector orthogonal to the gap vector cannot have a
constant projective direction on a degree at least three component of a quadric. -/
theorem curvature_direction_nonconstant {K R : Type*} [Field K] [CommRing R] [IsDomain R]
    [Algebra K R] (ψ : MvPolynomial (Fin 3) K →ₐ[K] R)
    (I : Ideal (MvPolynomial (Fin 3) K)) (hker : RingHom.ker ψ = I)
    (F : MvPolynomial (Fin 3) K) (hF : Prime F) (hFdeg : F.totalDegree = 2) (hFI : F ∈ I)
    {d : ℕ} (hd3 : 3 ≤ d)
    (hd : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c)
    (W : Fin 3 → R) (hW : ∃ j, W j ≠ 0)
    (horth : ∑ j, W j * ψ (curvatureGapVariables K j) = 0) :
    ¬∃ (t : R) (v : Fin 3 → K), v ≠ 0 ∧ ∀ j, W j = t * algebraMap K R (v j) := by
  rintro ⟨t, v, hv, he⟩
  have ht : t ≠ 0 := by
    intro ht
    obtain ⟨j, hj⟩ := hW
    exact hj (by rw [he, ht, zero_mul])
  have hsum : ∑ j, W j * ψ (curvatureGapVariables K j) = t * ψ (curvatureDirectionPlane v) := by
    simp only [curvatureDirectionPlane, map_sum, map_mul, mul_sum, he]
    refine sum_congr rfl fun j _ => ?_
    rw [show ψ (C (v j)) = algebraMap K R (v j) from ψ.commutes _]
    ring
  rw [hsum] at horth
  have hz : ψ (curvatureDirectionPlane v) = 0 := (mul_eq_zero.mp horth).resolve_left ht
  have hm : curvatureDirectionPlane v ∈ I := by rw [← hker]; exact hz
  exact curvatureDirectionPlane_not_mem I F hF hFdeg hFI hd3 hd hv hm

/-- The cleared joint formulas satisfy the gap orthogonality identity identically. -/
lemma jointLiftNumerators_dot_gaps (P Q A J : MvPolynomial (Fin 3) ℚ)
    (k : Fin 5 → MvPolynomial (Fin 3) ℚ) :
    ∑ j : Fin 3, jointLiftNumerators P Q A J k j.castSucc * k j.castSucc.castSucc = 0 := by
  simp [Fin.sum_univ_three, jointLiftNumerators]
  ring

lemma jointGapPolynomials_first_three (a b i : ℕ) (j : Fin 3) :
    jointGapPolynomials a b i j.castSucc.castSucc = curvatureGapVariables ℚ j := by
  fin_cases j <;> simp [jointGapPolynomials, lineGaps, curvatureGapVariables]

/-- The actual joint graph has nonconstant projective curvature direction.
This establishes the algebraic part of the candidate's extra-degree argument;
its divisor-degree conclusion requires the remaining curve theory. -/
theorem orbitJoint_curvature_direction_nonconstant {a b i d : ℕ}
    (hba : b < a) (hi : i + 7 < P a b)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hz : orbitFreeNodesQ a b i ∈ coordinateZeroLocus I)
    (F : MvPolynomial (Fin 3) ℚ) (hF : Prime F) (hFdeg : F.totalDegree = 2) (hFI : F ∈ I)
    (hd3 : 3 ≤ d)
    (hd : ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + c) :
    ¬∃ (t : graphLocalization I (orbitJointDenominator a b i)) (v : Fin 3 → ℚ), v ≠ 0 ∧
      ∀ j : Fin 3, jointGraphMap I (orbitJointNumerators a b i) (orbitJointDenominator a b i)
        (X (Sum.inr j.castSucc)) = t * algebraMap ℚ _ (v j) := by
  let Q := orbitJointDenominator a b i
  let Ns := orbitJointNumerators a b i
  let ψ : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] graphLocalization I Q :=
    (IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 3) ℚ ⧸ I) (graphLocalization I Q)).comp
      (Ideal.Quotient.mkₐ ℚ I)
  let W : Fin 3 → graphLocalization I Q := fun j => jointGraphMap I Ns Q (X (Sum.inr j.castSucc))
  have hQ := orbitJoint_denominator_not_mem hba hi I hz
  have hQ0 : Ideal.Quotient.mk I Q ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hQ
  let : IsDomain (graphLocalization I Q) := Localization.Away.isDomain hQ0
  have hker : RingHom.ker ψ = I := by
    ext f
    change algebraMap (MvPolynomial (Fin 3) ℚ ⧸ I) (graphLocalization I Q)
      (Ideal.Quotient.mk I f) = 0 ↔ f ∈ I
    rw [← jointGraphMap_rename I Ns Q f]
    exact jointGraph_rename_mem_iff I Ns Q f hQ
  have hW : ∃ j, W j ≠ 0 := by
    refine ⟨2, ?_⟩
    have he : graphPointMap I Q (orbitFreeNodesQ a b i) hz
        (orbitJointDenominator_eval_ne_zero hba hi) (W 2) = (integralLiftCoordinate a b i : ℚ) := by
      simp only [W, jointGraphMap, aeval_X, Sum.elim_inr, map_mul,
        graphPointMap_mk, graphPointMap_invSelf]
      rw [← div_eq_mul_inv]
      exact (orbitJoint_curvature_evaluation hba hi 2).trans (by rw [orbitCurvature_third])
    intro hw
    rw [hw, map_zero] at he
    have hp : (1 : ℚ) ≤ integralLiftCoordinate a b i := by
      exact_mod_cast integralLiftCoordinate_pos hba (by omega : i + 3 < P a b)
    linarith
  have horth : ∑ j, W j * ψ (curvatureGapVariables ℚ j) = 0 := by
    have hN := jointLiftNumerators_dot_gaps (orbitLiftNumeratorQ a b i)
      (orbitLiftDenominatorQ a b i) (C (Lz a b i : ℚ)) (jointRankFivePolynomial a b i)
      (jointGapPolynomials a b i)
    have hN' : ∑ j : Fin 3, ψ (Ns j.castSucc) * ψ (curvatureGapVariables ℚ j) = 0 := by
      have hm := congrArg ψ hN
      simp only [map_sum, map_mul, map_zero, jointGapPolynomials_first_three] at hm
      exact hm
    have hw (j : Fin 3) : W j = ψ (Ns j.castSucc) *
        IsLocalization.Away.invSelf (Ideal.Quotient.mk I Q) := by
      simp [W, jointGraphMap, ψ]
    calc (∑ j, W j * ψ (curvatureGapVariables ℚ j)) =
        (∑ j, ψ (Ns j.castSucc) * ψ (curvatureGapVariables ℚ j)) *
          IsLocalization.Away.invSelf (Ideal.Quotient.mk I Q) := by
            rw [sum_mul]
            exact sum_congr rfl fun j _ => by rw [hw]; ring
      _ = 0 := by rw [hN', zero_mul]
  exact curvature_direction_nonconstant ψ I hker F hF hFdeg hFI hd3 hd W hW horth

end
end PierceLengthBound.FixedDividend
