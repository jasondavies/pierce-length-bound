/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendOrthogonal
public import PierceLengthBound.FixedDividendResultant

/-!
# The fixed-dividend resultant identity at orbit windows

`X` times the shifted next quartic is the fifth orthogonal polynomial up to a multiple
of the fourth, so its resultant with the orbit quartic is `N⁴ / det H₄`. With
`L_i = a det H₄` this gives `L_i · Res(Q_i, X Q_{i+1}) = a N⁴`.
-/

@[expose] public section

namespace PierceLengthBound.FixedDividend

open Finset Polynomial

variable {a b : ℕ}

/-- The next state's quartic expressed in the current state's coordinates. -/
noncomputable def nextQuartic (a b i : ℕ) : ℝ[X] :=
  (orbitQuartic a b (i + 1)).comp (X - C (kk a b i))

lemma nextQuartic_monic (i : ℕ) : (nextQuartic a b i).Monic :=
  (orbitQuartic_monic (i + 1)).comp_X_sub_C _

lemma nextQuartic_natDegree (i : ℕ) : (nextQuartic a b i).natDegree = 4 := by
  rw [nextQuartic, natDegree_comp, orbitQuartic_natDegree, natDegree_X_sub_C, mul_one]

/-- The Christoffel shift is orthogonal through degree three. -/
theorem nextQuartic_orthogonal (hba : b < a) {i : ℕ} (hi : i + 7 < P a b) :
    ∀ m < 4, nuF a b i ((X * nextQuartic a b i) * X ^ m) = 0 := by
  intro m hm
  rw [mul_assoc, nuF_X_mul (by omega), mul_comp, nextQuartic, comp_shift_cancel, pow_comp, X_comp]
  apply nuF_mul_eq_zero_of_orthogonal (orbitQuartic_orthogonal hba (by omega))
  rw [natDegree_pow, natDegree_X_add_C, mul_one]
  exact hm

/-- Any monic quintic with the same first four vanishing moments differs from the
fifth orthogonal polynomial by a scalar multiple of the fourth. -/
theorem quintic_eq_orthPoly_add (hba : b < a) {i : ℕ} (hi : i + 4 < P a b)
    {q : ℝ[X]} (hq : q.Monic) (hd : q.natDegree = 5)
    (ho : ∀ m < 4, nuF a b i (q * X ^ m) = 0) :
    ∃ c : ℝ, q = orthPoly a b i 5 + orthPoly a b i 4 * C c := by
  let r := q - orthPoly a b i 5
  let c := r.coeff 4
  have hr : r.natDegree ≤ 4 := by
    have := IsMonicOfDegree.natDegree_sub_lt (by norm_num : 5 ≠ 0)
      (show IsMonicOfDegree q 5 from ⟨hd, hq⟩)
      (show IsMonicOfDegree (orthPoly a b i 5) 5 from ⟨orthPoly_natDegree i _, orthPoly_monic i _⟩)
    exact Nat.le_of_lt_succ this
  have hlow : (r - C c * orthPoly a b i 4).natDegree < 4 :=
    Nat.lt_succ_of_le (cancel_top_degree hr (orthPoly_natDegree i 4) (orthPoly_monic i 4))
  have hz : r - C c * orthPoly a b i 4 = 0 := by
    apply eq_zero_of_orthogonal hba (by omega) (by omega : 4 ≤ P a b - i) hlow
    intro m hm
    simp only [r, sub_mul, mul_assoc, nuF_sub, nuF_C_mul, ho m hm,
      orthPoly_orthogonal hba (by omega) (by omega : 5 ≤ P a b - i) m (by omega),
      orthPoly_orthogonal hba (by omega) (by omega : 4 ≤ P a b - i) m hm,
      mul_zero, sub_self]
  refine ⟨c, ?_⟩
  dsimp [r] at hz
  linear_combination hz

lemma norm_ratios_telescope {h0 h1 h2 h3 h4 : ℝ}
    (h₀ : h0 ≠ 0) (h₁ : h1 ≠ 0) (h₂ : h2 ≠ 0) (h₃ : h3 ≠ 0) :
    (h1 / h0) * (h2 / h1) ^ 2 * (h3 / h2) ^ 3 * (h4 / h3) ^ 4 =
      h4 ^ 4 / (h3 * (h2 * (h1 * h0))) := by
  field_simp

/-- The consecutive rank-four resultant in terms of the rank-four Hankel determinant. -/
theorem orthPoly_resultant_four (hba : b < a) {i : ℕ} (hi : i + 4 < P a b) :
    resultant (orthPoly a b i 4) (orthPoly a b i 5) 4 5 =
      orthNorm a b i 4 ^ 4 / (hankel a b i 4).det := by
  have hr := resultant_four (p := orthPoly a b i)
    (α := fun j => orthAlpha a b i (j - 1)) (β := fun j => orthBeta a b i (j - 1))
    (orthPoly_zero i) (fun j _ => (orthPoly_natDegree i j).le)
    (fun j _ => orthPoly_coeff_top i j) (fun j hj => by
      simpa using orthPoly_recurrence hba (i := i) (n := j) (by omega))
  norm_num only [Nat.add_sub_cancel, Nat.reduceSub] at hr
  rw [hr, orthBeta, orthBeta, orthBeta, orthBeta,
    norm_ratios_telescope (orthNorm_pos hba (by omega : 0 < P a b - i)).ne'
      (orthNorm_pos hba (by omega : 1 < P a b - i)).ne'
      (orthNorm_pos hba (by omega : 2 < P a b - i)).ne'
      (orthNorm_pos hba (by omega : 3 < P a b - i)).ne']
  have h0 := orthNorm_det hba (i := i) (n := 0) (by omega) (by omega)
  have h1 := orthNorm_det hba (i := i) (n := 1) (by omega) (by omega)
  have h2 := orthNorm_det hba (i := i) (n := 2) (by omega) (by omega)
  have h3 := orthNorm_det hba (i := i) (n := 3) (by omega) (by omega)
  have hz : (hankel a b i 0).det = 1 := Matrix.det_isEmpty
  rw [hz, mul_one] at h0
  rw [h3, h2, h1, h0]

/-- The shifted orbit quartic has the same resultant as the fifth orthogonal polynomial. -/
theorem nextQuartic_resultant (hba : b < a) {i : ℕ} (hi : i + 7 < P a b) :
    resultant (orbitQuartic a b i) (X * nextQuartic a b i) 4 5 =
      orbitNorm a b i ^ 4 / (hankel a b i 4).det := by
  have hq : (X * nextQuartic a b i).Monic := monic_X.mul (nextQuartic_monic i)
  have hd : (X * nextQuartic a b i).natDegree = 5 := by
    rw [natDegree_mul monic_X.ne_zero (nextQuartic_monic i).ne_zero,
      natDegree_X, nextQuartic_natDegree]
  obtain ⟨c, hc⟩ := quintic_eq_orthPoly_add hba (by omega) hq hd (nextQuartic_orthogonal hba hi)
  rw [orbitQuartic_eq_orthPoly hba (by omega), hc,
    resultant_add_mul_right _ _ _ 4 5 (by simp) (orthPoly_degree_le i 4),
    orthPoly_resultant_four hba (by omega)]
  have hnorm : orthNorm a b i 4 = orbitNorm a b i := by
    rw [orbitNorm_eq_square hba hi, orbitQuartic_eq_orthPoly hba (by omega)]
    rfl
  rw [hnorm]

/-- The rank-four label is exactly the determinant normalization required by the identity. -/
theorem orbit_label_hankel (hba : b < a) {i : ℕ} (hi : i + 5 < P a b) :
    (Lz a b i : ℝ) = (a : ℝ) * (hankel a b i 4).det := by
  have h := hankelInv_four hba hi
  simpa only [hankelInv, Lz, kq, dq, Nat.add_assoc] using h.symm

/-- **The fixed-dividend resultant identity** at every orbit window with
`i + 7 < P a b`. -/
theorem orbit_fixed_dividend_identity (hba : b < a) {i : ℕ} (hi : i + 7 < P a b) :
    (Lz a b i : ℝ) * resultant (orbitQuartic a b i) (X * nextQuartic a b i) 4 5 =
      (a : ℝ) * orbitNorm a b i ^ 4 := by
  rw [orbit_label_hankel hba (by omega), nextQuartic_resultant hba hi]
  have ht : (hankel a b i 4).det ≠ 0 := (hankel_posDef hba (by omega) (by omega)).det_pos.ne'
  field_simp

end PierceLengthBound.FixedDividend
