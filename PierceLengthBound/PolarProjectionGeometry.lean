/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionLinearSystem

/-! Explicit inverse to projection from the polar base point on the quadric.
All statements concern rational maps on specified open sets; no curve-degree
or normalization-multiplicity conclusion is assumed. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Matrix Finset
noncomputable section

/-- The quadratic part of the centered quadric. -/
def polarCenteredQuadratic {R : Type*} [CommRing R] (ρ u v : R) (y : Fin 3 → R) : R :=
  ∑ j, y j * (polarMatrix ρ u v *ᵥ y) j

/-- The linear part of the centered quadric, with its sign reversed. -/
def polarCenteredLinear {R : Type*} [CommRing R]
    (ρ u v ρ' u' v' : R) (y : Fin 3 → R) : R :=
  ∑ j, y j * polarLinear ρ u v ρ' u' v' j

lemma map_polarVector {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (ρ u v ρ' u' v' : R) (x : Fin 3 → R) :
    (fun j => φ (polarVector ρ u v ρ' u' v' x j)) =
      polarVector (φ ρ) (φ u) (φ v) (φ ρ') (φ u') (φ v') (fun j => φ (x j)) := by
  funext j
  fin_cases j <;> simp [polarVector, polarMatrix, polarLinear, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

/-- Centering at a zero of the polar forms gives the same quadric identity
over arbitrary commutative rings, including rings of formal power series. -/
theorem polar_centered_quadric_of_base {R : Type*} [CommRing R]
    (ρ u v ρ' u' v' : R) (z y : Fin 3 → R)
    (hz : polarVector ρ u v ρ' u' v' z = 0) :
    (∑ j, (z + y) j * polarVector ρ u v ρ' u' v' (z + y) j) =
      polarCenteredQuadratic ρ u v y - polarCenteredLinear ρ u v ρ' u' v' y := by
  have he := polarQuadric_translate ρ u v ρ' u' v' 1 z y
  have hg : polarMatrix ρ u v *ᵥ z = -polarLinear ρ u v ρ' u' v' :=
    eq_neg_of_add_eq_zero_left hz
  have hg' (j : Fin 3) :
      2 * (polarMatrix ρ u v *ᵥ z) j + polarLinear ρ u v ρ' u' v' j =
        -polarLinear ρ u v ρ' u' v' j := by
    rw [hg]
    simp only [Pi.neg_apply]
    ring
  simp only [one_mul, one_smul, one_pow, hz, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add, hg', mul_neg, Finset.sum_neg_distrib] at he
  simp only [Pi.add_apply]
  rw [he]
  unfold polarCenteredQuadratic polarCenteredLinear
  ring

/-- Centering at the base point writes the quadric as `Q(y) - L(y)`. -/
theorem polar_centered_quadric {K : Type*} [Field K] (ρ u v ρ' u' v' : K)
    (hG : (polarMatrix ρ u v).det ≠ 0) (y : Fin 3 → K) :
    let x := polarBasePoint ρ u v ρ' u' v' + y
    (∑ j, x j * polarVector ρ u v ρ' u' v' x j) =
      polarCenteredQuadratic ρ u v y - polarCenteredLinear ρ u v ρ' u' v' y := by
  have he := polarQuadric_translate ρ u v ρ' u' v' 1
    (polarBasePoint ρ u v ρ' u' v') y
  have hg := polarBasePoint_gradient ρ u v ρ' u' v' hG
  have hg' (j : Fin 3) :
      2 * (polarMatrix ρ u v *ᵥ polarBasePoint ρ u v ρ' u' v') j +
        polarLinear ρ u v ρ' u' v' j = -polarLinear ρ u v ρ' u' v' j :=
    congrFun hg j
  simp only [one_mul, one_smul, one_pow,
    polarBasePoint_polarVector ρ u v ρ' u' v' hG, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add, hg', mul_neg, Finset.sum_neg_distrib] at he
  dsimp only
  simp only [Pi.add_apply]
  rw [he]
  unfold polarCenteredQuadratic polarCenteredLinear
  ring

lemma polarCenteredQuadratic_smul {R : Type*} [CommRing R]
    (ρ u v t : R) (y : Fin 3 → R) :
    polarCenteredQuadratic ρ u v (t • y) = t ^ 2 * polarCenteredQuadratic ρ u v y := by
  simp only [polarCenteredQuadratic, mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  funext j
  ring

lemma polarCenteredLinear_smul {R : Type*} [CommRing R]
    (ρ u v ρ' u' v' t : R) (y : Fin 3 → R) :
    polarCenteredLinear ρ u v ρ' u' v' (t • y) =
      t * polarCenteredLinear ρ u v ρ' u' v' y := by
  simp [polarCenteredLinear, Finset.mul_sum, mul_assoc]

/-- An arbitrary direction with `Q(y) ≠ 0` intersects the affine quadric
at the base point and at this explicitly reconstructed point. -/
def polarProjectionInverse {K : Type*} [Field K]
    (ρ u v ρ' u' v' : K) (z : Fin 3 → K) : Fin 3 → K :=
  let y := (polarMatrix ρ u v)⁻¹ *ᵥ z
  polarBasePoint ρ u v ρ' u' v' +
    (polarCenteredLinear ρ u v ρ' u' v' y / polarCenteredQuadratic ρ u v y) • y

/-- The rational inverse lands on the original quadric. -/
theorem polarProjectionInverse_on_quadric {K : Type*} [Field K]
    (ρ u v ρ' u' v' : K) (hG : (polarMatrix ρ u v).det ≠ 0) (z : Fin 3 → K)
    (hQ : polarCenteredQuadratic ρ u v ((polarMatrix ρ u v)⁻¹ *ᵥ z) ≠ 0) :
    let x := polarProjectionInverse ρ u v ρ' u' v' z
    lineQuadratic ρ u v ρ' u' v' (x 0) (x 0 + x 1) (x 0 + x 1 + x 2) = 0 := by
  dsimp only
  rw [← polarVector_dot_gaps]
  unfold polarProjectionInverse
  rw [polar_centered_quadric ρ u v ρ' u' v' hG,
    polarCenteredQuadratic_smul, polarCenteredLinear_smul]
  field_simp
  ring

/-- Projecting the reconstructed point recovers the original direction,
with its explicit scalar factor. -/
theorem polarProjectionInverse_polarVector {K : Type*} [Field K]
    (ρ u v ρ' u' v' : K) (hG : (polarMatrix ρ u v).det ≠ 0) (z : Fin 3 → K) :
    polarVector ρ u v ρ' u' v' (polarProjectionInverse ρ u v ρ' u' v' z) =
      (polarCenteredLinear ρ u v ρ' u' v' ((polarMatrix ρ u v)⁻¹ *ᵥ z) /
        polarCenteredQuadratic ρ u v ((polarMatrix ρ u v)⁻¹ *ᵥ z)) • z := by
  rw [polarVector_eq_centered_mulVec ρ u v ρ' u' v' _
    (polarBasePoint ρ u v ρ' u' v') (polarBasePoint_polarVector ρ u v ρ' u' v' hG)]
  simp only [polarProjectionInverse, add_sub_cancel_left, mulVec_smul,
    mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG), one_mulVec]

/-- Conversely the reconstruction recovers every quadric point on the open
set where the quadratic part of its displacement is nonzero. -/
theorem polarProjectionInverse_left_inverse {K : Type*} [Field K]
    (ρ u v ρ' u' v' : K) (hG : (polarMatrix ρ u v).det ≠ 0) (x : Fin 3 → K)
    (hx : ∑ j, x j * polarVector ρ u v ρ' u' v' x j = 0)
    (hQ : polarCenteredQuadratic ρ u v (x - polarBasePoint ρ u v ρ' u' v') ≠ 0) :
    polarProjectionInverse ρ u v ρ' u' v' (polarVector ρ u v ρ' u' v' x) = x := by
  have hc := polar_centered_quadric ρ u v ρ' u' v' hG
    (x - polarBasePoint ρ u v ρ' u' v')
  simp only [add_sub_cancel] at hc
  rw [hx] at hc
  have hQL := sub_eq_zero.mp hc.symm
  rw [polarVector_eq_centered_mulVec ρ u v ρ' u' v' x
    (polarBasePoint ρ u v ρ' u' v') (polarBasePoint_polarVector ρ u v ρ' u' v' hG)]
  simp only [polarProjectionInverse, mulVec_mulVec,
    nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hG), one_mulVec, ← hQL, div_self hQ,
    one_smul, add_sub_cancel]

end
end PierceLengthBound.FixedDividend
