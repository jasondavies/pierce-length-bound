/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftResolvent
public import PierceLengthBound.IntegralLiftInvariant
public import PierceLengthBound.FixedDividendOrbit

/-! The resolvent formula for the actual finite positive moment functionals. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Finset Polynomial Matrix

lemma monic_quartic_expansion {R : Type*} [CommRing R] (P : R[X])
    (hm : P.Monic) (hd : P.natDegree = 4) :
    P = X ^ 4 + C (P.coeff 0) + C (P.coeff 1) * X +
      C (P.coeff 2) * X ^ 2 + C (P.coeff 3) * X ^ 3 := by
  have he := hm.as_sum
  rw [hd] at he
  simpa [sum_range_succ, add_assoc] using he

lemma orbit_quartic_moment_recurrence {a b i : ℕ} (hba : b < a) (hi : i + 6 < P a b) :
    ∀ j < 3, (orbitQuartic a b i).coeff 0 * hm a b i j +
      (orbitQuartic a b i).coeff 1 * hm a b i (j + 1) +
      (orbitQuartic a b i).coeff 2 * hm a b i (j + 2) +
      (orbitQuartic a b i).coeff 3 * hm a b i (j + 3) + hm a b i (j + 4) = 0 := by
  intro j hj
  have ho := orbitQuartic_orthogonal hba hi j (by omega)
  conv_lhs at ho => rw [monic_quartic_expansion _ (orbitQuartic_monic i) (orbitQuartic_natDegree i)]
  simp only [add_mul, mul_assoc, ← pow_succ', ← pow_add, nuF_add, nuF_C_mul, nuF_X_pow] at ho
  simpa only [Nat.add_comm, add_assoc, add_left_comm, add_comm] using ho

lemma orbit_weighted_raw_moment {a b i : ℕ} (hba : b < a) (j : ℕ) :
    (qq a b i : ℝ) * hm a b i j + hm a b i (j + 1) = muF a b i (X ^ j) := by
  have h := nuF_mul_X_add hba i (X ^ j)
  rw [← pow_succ, nuF_X_pow, nuF_X_pow] at h
  linarith

lemma integralLiftCoordinate_hankelThree {a b i : ℕ} (hba : b < a) (hi : i + 3 < P a b) :
    (integralLiftCoordinate a b i : ℝ) = (a : ℝ) * hankelThree (hm a b i) := by
  rw [integralLiftCoordinate_eq hba hi]
  unfold hankelInv hankelThree
  congr 1

/-- The new resolvent formula is valid for every sufficiently supported actual
orbit start, with the denominator cleared and the invariant identified in ℤ. -/
theorem orbit_integralLift_resolvent {a b i : ℕ} (hba : b < a) (hi : i + 6 < P a b) :
    (integralLiftCoordinate a b i : ℝ) *
        (orbitQuartic a b i).eval (-(qq a b i : ℝ)) =
      (a : ℝ) * (((qq a b i : ℝ) - (orbitQuartic a b i).coeff 3) *
        hankelThree (fun j => muF a b i (X ^ j)) -
          hankelMixed (fun j => muF a b i (X ^ j))) := by
  have h := hankel_three_resolvent ((orbitQuartic a b i).coeff 0)
    ((orbitQuartic a b i).coeff 1) ((orbitQuartic a b i).coeff 2)
    ((orbitQuartic a b i).coeff 3) (qq a b i : ℝ) (hm a b i)
    (orbit_quartic_moment_recurrence hba hi)
  have he : (orbitQuartic a b i).eval (-(qq a b i : ℝ)) =
      (qq a b i : ℝ) ^ 4 - (orbitQuartic a b i).coeff 3 * (qq a b i : ℝ) ^ 3 +
        (orbitQuartic a b i).coeff 2 * (qq a b i : ℝ) ^ 2 -
          (orbitQuartic a b i).coeff 1 * (qq a b i : ℝ) + (orbitQuartic a b i).coeff 0 := by
    conv_lhs => rw [monic_quartic_expansion _ (orbitQuartic_monic i) (orbitQuartic_natDegree i)]
    simp only [eval_add, eval_pow, eval_mul, eval_C, eval_X]
    ring
  have hmu : (fun j => (qq a b i : ℝ) * hm a b i j + hm a b i (j + 1)) =
      (fun j => muF a b i (X ^ j)) := funext (orbit_weighted_raw_moment hba)
  rw [integralLiftCoordinate_hankelThree hba (by omega), he, mul_assoc, h, hmu]

end
end PierceLengthBound.FixedDividend
