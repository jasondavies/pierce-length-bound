/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftInvariant
public import PierceLengthBound.IntegralLiftResolvent
public import PierceLengthBound.FixedDividendIdentity
public import PierceLengthBound.MinorHeight

/-! The joint lift's exact curvature identities and the actual rank-five
identity I5 = A D. These algebraic results do not assert the new graph degree. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Matrix Finset

/-- Signed curvature-minor vector, in the order used by the joint lift. -/
def curvatureVector {R : Type*} [CommRing R] (d k : Fin 3 → R) : Fin 3 → R :=
  ![d 1 * k 2 - d 2 * k 1, -(d 0 * k 2 - d 2 * k 0), d 0 * k 1 - d 1 * k 0]

lemma curvature_dot_gaps {R : Type*} [CommRing R] (d k : Fin 3 → R) :
    ∑ j, curvatureVector d k j * k j = 0 := by
  simp [curvatureVector, Fin.sum_univ_three]
  ring

lemma curvature_dot_row {R : Type*} [CommRing R] (d k r : Fin 3 → R) :
    ∑ j, curvatureVector d k j * r j = (Matrix.of ![d, k, r]).det := by
  simp [curvatureVector, Fin.sum_univ_three, Matrix.det_fin_three]
  ring

lemma curvature_reconstruction_identity {R : Type*} [CommRing R] (d k r : Fin 3 → R) :
    (k 1 * r 2 - k 2 * r 1) * (d 0 * k 1 - d 1 * k 0) -
      (k 0 * r 1 - k 1 * r 0) * (d 1 * k 2 - d 2 * k 1) =
      (Matrix.of ![d, k, r]).det * k 1 := by
  simp [Matrix.det_fin_three]
  ring

/-- Both rational reconstruction formulas follow from the actual minors. -/
theorem curvature_reconstruction {K : Type*} [Field K] (d k r : Fin 3 → K)
    (hB : k 0 * r 1 - k 1 * r 0 ≠ 0) (hk : k 1 ≠ 0) :
    let E0 := d 0 * k 1 - d 1 * k 0
    let E12 := ((k 1 * r 2 - k 2 * r 1) * E0 - (Matrix.of ![d, k, r]).det * k 1) /
      (k 0 * r 1 - k 1 * r 0)
    E12 = d 1 * k 2 - d 2 * k 1 ∧
      (k 0 * E12 + k 2 * E0) / k 1 = d 0 * k 2 - d 2 * k 0 := by
  dsimp only
  have he : ((k 1 * r 2 - k 2 * r 1) * (d 0 * k 1 - d 1 * k 0) -
      (Matrix.of ![d, k, r]).det * k 1) / (k 0 * r 1 - k 1 * r 0) =
      d 1 * k 2 - d 2 * k 1 := by
    apply (div_eq_iff hB).mpr
    linear_combination curvature_reconstruction_identity d k r
  refine ⟨he, ?_⟩
  rw [he]
  apply (div_eq_iff hk).mpr
  ring

/-- The two raw minors are the cubic Hankel polynomials. -/
lemma curvature_raw_minors {R : Type*} [CommRing R] (k0 k1 k2 k3 : R) :
    k0 * (k1 * (2 * k0 + k1) + k2) - k1 * (k0 ^ 2 + k1) =
        rawHankelThree k0 k1 k2 ∧
      k1 * (k2 * (2 * k0 + 2 * k1 + k2) + k3) -
        k2 * (k1 * (2 * k0 + k1) + k2) = rawHankelThree k1 k2 k3 := by
  constructor <;> unfold rawHankelThree <;> ring

lemma rawHankelThree_pos_of_gaps {k0 k1 k2 : ℤ}
    (h0 : 1 ≤ k0) (h1 : 1 ≤ k1) (h2 : 1 ≤ k2) : 0 < rawHankelThree k0 k1 k2 := by
  have hp : 0 < k0 ^ 2 * k1 := by positivity
  have hn : 0 ≤ (k0 - 1) * k1 ^ 2 := mul_nonneg (by omega) (sq_nonneg _)
  have ht : 0 ≤ k0 * k2 := by positivity
  unfold rawHankelThree
  omega

/-- These are integer coordinates at every actual state, without a new pattern. -/
def orbitCurvatureVector (a b i : ℕ) : Fin 3 → ℤ :=
  curvatureVector (fun j => dq a b (i + j)) (fun j => kq a b (i + j))

lemma orbitCurvature_third (a b i : ℕ) :
    orbitCurvatureVector a b i 2 = integralLiftCoordinate a b i := by
  simp [orbitCurvatureVector, curvatureVector, integralLiftCoordinate]

lemma orbitCurvature_dot_gaps (a b i : ℕ) :
    ∑ j : Fin 3, orbitCurvatureVector a b i j * kq a b (i + j) = 0 :=
  curvature_dot_gaps _ _

lemma orbitCurvature_dot_r (a b i : ℕ) :
    ∑ j : Fin 3, orbitCurvatureVector a b i j * rq a b i j = Lz a b i := by
  rw [show orbitCurvatureVector a b i = curvatureVector
    (fun j => dq a b (i + j)) (fun j => kq a b (i + j)) from rfl, curvature_dot_row]
  simp [Matrix.det_fin_three, Lz, sixL, rq, sq, kq, Nat.add_assoc]
  ring

/-- The previously constructed cubic norm is precisely the new rank-five invariant. -/
theorem joint_rank_five_identity {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b) :
    (Lz a b i : ℝ) * orbitNorm a b i = hankelInv a b i 5 := by
  rw [hankelInv, orbitNorm_hankel hba hi, orbit_label_hankel hba (by omega)]
  ring

/-- In particular A D is a positive integer, although D itself need not be integral. -/
theorem joint_rank_five_positive_integer {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b) :
    ∃ J : ℕ, 0 < J ∧ (Lz a b i : ℝ) * orbitNorm a b i = J := by
  rw [joint_rank_five_identity hba hi]
  exact hankelInv_pos_int hba (by omega) (by omega)

/-- Cancellation of the common leading drop term controls every curvature minor. -/
theorem curvature_minor_error_bound {d0 d1 k0 k1 c E H : ℝ}
    (he0 : |d0 - c * k0| ≤ E) (he1 : |d1 - c * k1| ≤ E)
    (hk0 : |k0| ≤ H) (hk1 : |k1| ≤ H) :
    |d0 * k1 - d1 * k0| ≤ 2 * E * H := by
  have hE : 0 ≤ E := (abs_nonneg _).trans he0
  have hH : 0 ≤ H := (abs_nonneg _).trans hk0
  calc |d0 * k1 - d1 * k0| = |(d0 - c * k0) * k1 - (d1 - c * k1) * k0| := by congr 1; ring
    _ ≤ |(d0 - c * k0) * k1| + |(d1 - c * k1) * k0| := abs_sub _ _
    _ = |d0 - c * k0| * |k1| + |d1 - c * k1| * |k0| := by rw [abs_mul, abs_mul]
    _ ≤ E * H + E * H := by gcongr
    _ = _ := by ring

end
end PierceLengthBound.FixedDividend
