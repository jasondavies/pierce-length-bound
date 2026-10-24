/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.JointLiftDirection

/-! # A curvature combination with an affine zero

The cleared identity behind `W · (r₀, r₁, r₂) = N₀`, which shows that the curvature
coordinates have no common zero on the affine joint graph, and the construction of
Lemma 8.11: on a component of degree at least three of an irreducible quadric through the free
nodes of an orbit state, a nonzero rational combination of `W₀, W₁, W₂` vanishes at that
point. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- The row `r_j = k_j (s_j + s_{j+1}) + k_{j+1}`, `j < 3`, written in the gaps (with
`s₀ = 0`). -/
def curvatureRow {R : Type*} [CommRing R] (k : Fin 5 → R) : Fin 3 → R :=
  ![k 0 ^ 2 + k 1, k 1 * (2 * k 0 + k 1) + k 2,
    k 2 * (2 * k 0 + 2 * k 1 + k 2) + k 3]

/-- Cleared form of `W · r = A`: the curvature numerators dotted with `curvatureRow k` give
`A` times the common denominator. -/
theorem jointLiftNumerators_dot_row (P Q A J : MvPolynomial (Fin 3) ℚ)
    (k : Fin 5 → MvPolynomial (Fin 3) ℚ) :
    ∑ j : Fin 3, jointLiftNumerators P Q A J k j.castSucc * curvatureRow k j =
      A * jointLiftDenominator Q k := by
  simp [Fin.sum_univ_three, jointLiftNumerators, jointLiftDenominator,
    curvatureRow, rawHankelThree]
  ring

/-- If `W` is not of the form `t v` for a fixed nonzero `v`, and some `W_j` is nonzero at the
point `φ`, then some nonzero `K`-linear combination of the `W_j` vanishes at `φ`. -/
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

/-- On a component of degree at least three of an irreducible quadric through the free nodes
of state `i`, some nonzero rational combination of the curvature coordinates on the joint graph
vanishes at that point (Lemma 8.11). -/
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
