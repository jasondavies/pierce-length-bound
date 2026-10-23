/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendMoments

/-! Rational reconstruction identities from the normalized first two moments.
The cofactor construction and its parameter-height bounds remain separate tasks. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open Polynomial

/-- The eight shifted orthogonality rows admit no nontrivial relation.
This is the polynomial divisibility step in the cofactor reconstruction. -/
theorem shifted_quartics_independent {K : Type*} [Field K] {P Z U V : K[X]}
    (hP : P ≠ 0) (hcop : IsCoprime P Z) (hV : V.natDegree < P.natDegree)
    (hrel : U * P + V * Z = 0) : U = 0 ∧ V = 0 := by
  have hd : P ∣ V * Z := by
    refine ⟨-U, ?_⟩
    linear_combination hrel
  have hv : V = 0 := by
    by_contra hv
    exact (not_le_of_gt hV) (Polynomial.natDegree_le_of_dvd
      (hcop.dvd_of_dvd_mul_right hd) hv)
  rw [hv, zero_mul, add_zero] at hrel
  exact ⟨(mul_eq_zero.mp hrel).resolve_right hP, hv⟩

/-- Strict variance of the actual positive moment model. -/
lemma orbit_moment_variance {a b i : ℕ} (hba : b < a) (hi : i + 1 < P a b) :
    hm a b i 1 ^ 2 < hm a b i 0 * hm a b i 2 := by
  have h := (hankel_posDef hba (i := i) (r := 2) (by omega) (by omega)).det_pos
  rw [Matrix.det_fin_two] at h
  simp only [hankel, Matrix.of_apply, Fin.val_zero, Fin.val_one, zero_add, add_zero] at h
  norm_num at h
  nlinarith

/-- The two normalizations hold at every sufficiently supported actual state. -/
lemma orbit_moment_normalizations {a b i : ℕ} (hba : b < a) (hi : i + 1 < P a b) :
    (qq a b i : ℝ) * hm a b i 0 + hm a b i 1 = 1 ∧
      (qq a b i : ℝ) * hm a b i 1 + hm a b i 2 = 1 := by
  have h1 := nuF_mul_X_add hba i 1
  have h2 := nuF_mul_X_add hba i X
  rw [muF_one hba (by omega), one_mul] at h1
  rw [muF_X hba hi, show (X : ℝ[X]) * X = X ^ 2 by ring] at h2
  have hz : nuF a b i 1 = hm a b i 0 := by simpa using nuF_X_pow (a := a) (b := b) i 0
  have ho : nuF a b i X = hm a b i 1 := by simpa using nuF_X_pow (a := a) (b := b) i 1
  rw [hz, ho] at h1
  rw [ho, nuF_X_pow] at h2
  constructor <;> linarith

end PierceLengthBound.FixedDividend
