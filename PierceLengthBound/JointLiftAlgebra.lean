/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftInvariant
public import PierceLengthBound.IntegralLiftResolvent
public import PierceLengthBound.FixedDividendIdentity

/-! # Algebraic identities of the joint lift

The curvature-minor vector `W = (D₁₂, -D₀₂, D₀₁)` of drops and gaps, with its dot-product
identities `W · k = 0` and `W · r = det (d, k, r)` (at an orbit state, `W · r = I₄(i)`), and the
rank-five identity `I₅(i) = I₄(i) · Ψ` expressing the rank-five Hankel invariant as the label
times the quartic norm (Section 8.6), and the cancellation bound for the minors used in the
height estimate (Lemma 8.7). -/

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

/-- `W · r = det (d, k, r)` for the curvature-minor vector `W` of `d` and `k`. -/
lemma curvature_dot_row {R : Type*} [CommRing R] (d k r : Fin 3 → R) :
    ∑ j, curvatureVector d k j * r j = (Matrix.of ![d, k, r]).det := by
  simp [curvatureVector, Fin.sum_univ_three, Matrix.det_fin_three]
  ring

/-- The identity `H₃' D₀₁ - H₃ D₁₂ = det (d, k, r) · k₁`, with `H₃ = k₀ r₁ - k₁ r₀` and
`H₃' = k₁ r₂ - k₂ r₁`, behind the formula `E₁₂ = (H₃' E₀ - N₀ k₁) / H₃`. -/
lemma curvature_reconstruction_identity {R : Type*} [CommRing R] (d k r : Fin 3 → R) :
    (k 1 * r 2 - k 2 * r 1) * (d 0 * k 1 - d 1 * k 0) -
      (k 0 * r 1 - k 1 * r 0) * (d 1 * k 2 - d 2 * k 1) =
      (Matrix.of ![d, k, r]).det * k 1 := by
  simp [Matrix.det_fin_three]
  ring

lemma rawHankelThree_pos_of_gaps {k0 k1 k2 : ℤ}
    (h0 : 1 ≤ k0) (h1 : 1 ≤ k1) (h2 : 1 ≤ k2) : 0 < rawHankelThree k0 k1 k2 := by
  have hp : 0 < k0 ^ 2 * k1 := by positivity
  have hn : 0 ≤ (k0 - 1) * k1 ^ 2 := mul_nonneg (by omega) (sq_nonneg _)
  have ht : 0 ≤ k0 * k2 := by positivity
  unfold rawHankelThree
  omega

/-- The curvature-minor vector at orbit state `i`, built from the integer drops and gaps;
its third coordinate is the curvature `I₃(i)` (`orbitCurvature_third`). -/
def orbitCurvatureVector (a b i : ℕ) : Fin 3 → ℤ :=
  curvatureVector (fun j => dq a b (i + j)) (fun j => kq a b (i + j))

lemma orbitCurvature_third (a b i : ℕ) :
    orbitCurvatureVector a b i 2 = integralLiftCoordinate a b i := by
  simp [orbitCurvatureVector, curvatureVector, integralLiftCoordinate]

lemma orbitCurvature_dot_gaps (a b i : ℕ) :
    ∑ j : Fin 3, orbitCurvatureVector a b i j * kq a b (i + j) = 0 :=
  curvature_dot_gaps _ _

/-- At orbit state `i`, `W · r = L(i) = I₄(i)`. -/
lemma orbitCurvature_dot_r (a b i : ℕ) :
    ∑ j : Fin 3, orbitCurvatureVector a b i j * rq a b i j = Lz a b i := by
  rw [show orbitCurvatureVector a b i = curvatureVector
    (fun j => dq a b (i + j)) (fun j => kq a b (i + j)) from rfl, curvature_dot_row]
  simp [Matrix.det_fin_three, Lz, sixL, rq, sq, kq, Nat.add_assoc]
  ring

/-- The rank-five identity `I₄(i) · Ψ = I₅(i)`: the label `L(i) = I₄(i)` times the quartic norm
`orbitNorm` is the rank-five Hankel invariant. -/
theorem joint_rank_five_identity {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b) :
    (Lz a b i : ℝ) * orbitNorm a b i = hankelInv a b i 5 := by
  rw [hankelInv, orbitNorm_hankel hba hi, orbit_label_hankel hba (by omega)]
  ring

/-- `I₄(i) · Ψ` is a positive integer, although the quartic norm `Ψ` itself need not be
integral. -/
theorem joint_rank_five_positive_integer {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b) :
    ∃ J : ℕ, 0 < J ∧ (Lz a b i : ℝ) * orbitNorm a b i = J := by
  rw [joint_rank_five_identity hba hi]
  exact hankelInv_pos_int hba (by omega) (by omega)

/-- If `d₀, d₁` are within `E` of `c k₀, c k₁` and `|k₀|, |k₁| ≤ H`, the cancellation of the
common leading term gives `|d₀ k₁ - d₁ k₀| ≤ 2 E H`. -/
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
