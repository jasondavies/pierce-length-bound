/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendOrbit
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Monic orthogonal polynomials for the finite Pierce moment functional

The coefficients are obtained by solving the positive definite Hankel system.
-/

@[expose] public section

namespace PierceLengthBound.FixedDividend

open Finset Polynomial Matrix

variable {a b : ℕ}

lemma nuF_sub (i : ℕ) (f g : ℝ[X]) :
    nuF a b i (f - g) = nuF a b i f - nuF a b i g := by
  simp [nuF, mul_sub, sub_div, sum_sub_distrib]

/-- The solution of the moment system for the lower coefficients. -/
noncomputable def orthCorrection (a b i n : ℕ) : Fin n → ℝ :=
  (hankel a b i n)⁻¹ *ᵥ (fun j : Fin n => hm a b i ((j : ℕ) + n))

/-- The monic polynomial obtained by orthogonalizing `X^n`. -/
noncomputable def orthPoly (a b i n : ℕ) : ℝ[X] :=
  X ^ n - ∑ j : Fin n, C (orthCorrection a b i n j) * X ^ (j : ℕ)

lemma orthPoly_zero (i : ℕ) : orthPoly a b i 0 = 1 := by simp [orthPoly]

lemma orthPoly_degree_le (i n : ℕ) : (orthPoly a b i n).natDegree ≤ n := by
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · apply natDegree_sum_le_of_forall_le
    intro j _
    exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; omega)

lemma orthPoly_coeff_top (i n : ℕ) : (orthPoly a b i n).coeff n = 1 := by
  simp only [orthPoly, coeff_sub, coeff_X_pow_self, finsetSum_coeff, coeff_C_mul]
  have hz : ∑ j : Fin n, orthCorrection a b i n j * (X ^ (j : ℕ) : ℝ[X]).coeff n = 0 := by
    apply sum_eq_zero
    intro j _
    rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_X_pow]; exact j.isLt), mul_zero]
  rw [hz, sub_zero]

lemma orthPoly_monic (i n : ℕ) : (orthPoly a b i n).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one n (orthPoly_degree_le i n) (orthPoly_coeff_top i n)

lemma orthPoly_natDegree (i n : ℕ) : (orthPoly a b i n).natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero (orthPoly_degree_le i n)
    (by rw [orthPoly_coeff_top]; norm_num)

/-- The Hankel system is invertible throughout the supported range. -/
theorem orthPoly_orthogonal (hba : b < a) {i n : ℕ} (hi : i < P a b)
    (hn : n ≤ P a b - i) : ∀ m < n, nuF a b i (orthPoly a b i n * X ^ m) = 0 := by
  intro m hmn
  have hu : IsUnit (hankel a b i n).det :=
    isUnit_iff_ne_zero.mpr (hankel_posDef hba hi hn).det_pos.ne'
  have he : hankel a b i n *ᵥ orthCorrection a b i n =
      (fun j : Fin n => hm a b i ((j : ℕ) + n)) := by
    rw [orthCorrection, mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have hem := congrFun he (⟨m, hmn⟩ : Fin n)
  simp only [mulVec, dotProduct, hankel, of_apply] at hem
  rw [orthPoly, sub_mul, nuF_sub, ← pow_add, nuF_X_pow, sum_mul, nuF_sum]
  have hs : (∑ j : Fin n, nuF a b i (C (orthCorrection a b i n j) * X ^ (j : ℕ) * X ^ m)) =
      ∑ j : Fin n, hm a b i (m + (j : ℕ)) * orthCorrection a b i n j := by
    apply sum_congr rfl
    intro j _
    rw [mul_assoc, ← pow_add, nuF_C_mul, nuF_X_pow, Nat.add_comm]
    ring
  rw [hs, hem, Nat.add_comm, sub_self]

/-- The squared norm of the monic polynomial. -/
noncomputable def orthNorm (a b i n : ℕ) : ℝ :=
  nuF a b i (orthPoly a b i n * orthPoly a b i n)

theorem orthNorm_pos (hba : b < a) {i n : ℕ} (hn : n < P a b - i) :
    0 < orthNorm a b i n :=
  nuF_square_pos hba (by omega) (orthPoly_monic i n).ne_zero
    (by rw [orthPoly_natDegree]; exact hn)

/-- The leading monomial has the same pairing as the full monic polynomial. -/
theorem orthNorm_top (hba : b < a) {i n : ℕ} (hi : i < P a b) (hn : n ≤ P a b - i) :
    orthNorm a b i n = nuF a b i (orthPoly a b i n * X ^ n) := by
  unfold orthNorm
  conv_lhs => enter [4, 2]; rw [orthPoly]
  rw [mul_sub, nuF_sub, mul_sum, nuF_sum]
  have hz : (∑ j : Fin n, nuF a b i (orthPoly a b i n *
      (C (orthCorrection a b i n j) * X ^ (j : ℕ)))) = 0 := by
    apply sum_eq_zero
    intro j _
    rw [show orthPoly a b i n * (C (orthCorrection a b i n j) * X ^ (j : ℕ)) =
      C (orthCorrection a b i n j) * (orthPoly a b i n * X ^ (j : ℕ)) by ring,
      nuF_C_mul, orthPoly_orthogonal hba hi hn j j.isLt, mul_zero]
  rw [hz, sub_zero]

theorem orthNorm_det (hba : b < a) {i n : ℕ} (hi : i < P a b) (hn : n ≤ P a b - i) :
    (hankel a b i (n + 1)).det = orthNorm a b i n * (hankel a b i n).det :=
  orthogonal_norm_det (orthPoly_monic i n) (orthPoly_natDegree i n) (orthPoly_orthogonal hba hi hn)

/-- A polynomial orthogonal to every monomial through its degree must vanish. -/
lemma eq_zero_of_orthogonal (hba : b < a) {i n : ℕ} (hi : i < P a b)
    (hn : n ≤ P a b - i) {f : ℝ[X]} (hd : f.natDegree < n)
    (ho : ∀ m < n, nuF a b i (f * X ^ m) = 0) : f = 0 := by
  by_contra hf
  have hz := nuF_mul_eq_zero_of_orthogonal ho hd
  have hp := nuF_square_pos hba hi hf (hd.trans_le hn)
  linarith

/-- Uniqueness of the monic orthogonal polynomial for the actual measure. -/
theorem eq_orthPoly (hba : b < a) {i n : ℕ} (hi : i < P a b)
    (hn : n ≤ P a b - i) {p : ℝ[X]} (hp : p.Monic) (hd : p.natDegree = n)
    (ho : ∀ m < n, nuF a b i (p * X ^ m) = 0) : p = orthPoly a b i n := by
  by_cases hn0 : n = 0
  · rw [hn0, orthPoly_zero]
    exact eq_one_of_monic_natDegree_zero hp (hd.trans hn0)
  apply sub_eq_zero.mp
  apply eq_zero_of_orthogonal hba hi hn
    (IsMonicOfDegree.natDegree_sub_lt hn0 ⟨hd, hp⟩ ⟨orthPoly_natDegree i n, orthPoly_monic i n⟩)
  intro m hm
  rw [sub_mul, nuF_sub, ho m hm, orthPoly_orthogonal hba hi hn m hm, sub_self]

/-- The cofactor quartic is the fourth canonical monic orthogonal polynomial. -/
theorem orbitQuartic_eq_orthPoly (hba : b < a) {i : ℕ} (hi : i + 6 < P a b) :
    orbitQuartic a b i = orthPoly a b i 4 :=
  eq_orthPoly hba (by omega) (by omega) (orbitQuartic_monic i) (orbitQuartic_natDegree i)
    (orbitQuartic_orthogonal hba hi)

/-- Removing the highest coefficient lowers the degree bound. -/
lemma cancel_top_degree {p q : ℝ[X]} {n : ℕ} (hp : p.natDegree ≤ n + 1)
    (hq : q.natDegree = n + 1) (hqm : q.Monic) :
    (p - C (p.coeff (n + 1)) * q).natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  by_cases he : m = n + 1
  · subst m
    rw [coeff_sub, coeff_C_mul, ← hq, hqm.coeff_natDegree, mul_one, sub_self]
  · rw [coeff_sub, coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < m),
      coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < m), mul_zero, sub_self]

/-- The coefficient of `p_(n+1)` in the three-term recurrence. -/
noncomputable def orthAlpha (a b i n : ℕ) : ℝ :=
  (orthPoly a b i (n + 1)).coeff n - (orthPoly a b i (n + 2)).coeff (n + 1)

/-- The positive ratio of successive squared norms. -/
noncomputable def orthBeta (a b i n : ℕ) : ℝ :=
  orthNorm a b i (n + 1) / orthNorm a b i n

/-- The three-term recurrence, proved from the actual positive moment functional. -/
theorem orthPoly_recurrence (hba : b < a) {i n : ℕ} (hn : n + 2 ≤ P a b - i) :
    orthPoly a b i (n + 2) = C (-orthBeta a b i n) * orthPoly a b i n +
      orthPoly a b i (n + 1) * (X - C (orthAlpha a b i n)) := by
  let p := orthPoly a b i
  let A := p (n + 2) - p (n + 1) * X
  let c := A.coeff (n + 1)
  let E := A - C c * p (n + 1) + C (orthBeta a b i n) * p n
  have hα : c = -orthAlpha a b i n := by
    simp only [c, A, coeff_sub, coeff_mul_X, orthAlpha, p]
    ring
  have hA : A.natDegree ≤ n + 1 := by
    have hx : IsMonicOfDegree (p (n + 1) * X) (n + 2) := by
      simpa using (IsMonicOfDegree.mul
        (show IsMonicOfDegree (p (n + 1)) (n + 1) from ⟨orthPoly_natDegree i _, orthPoly_monic i _⟩)
        (show IsMonicOfDegree (X : ℝ[X]) 1 from ⟨natDegree_X, monic_X⟩))
    have h := IsMonicOfDegree.natDegree_sub_lt (by omega : n + 2 ≠ 0)
      (show IsMonicOfDegree (p (n + 2)) (n + 2) from
        ⟨orthPoly_natDegree i _, orthPoly_monic i _⟩) hx
    exact Nat.le_of_lt_succ h
  have hE : E.natDegree ≤ n := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact cancel_top_degree hA (orthPoly_natDegree i _) (orthPoly_monic i _)
    · exact (natDegree_C_mul_le _ _).trans (orthPoly_natDegree i n).le
  have ho : ∀ m < n + 1, nuF a b i (E * X ^ m) = 0 := by
    intro m hm
    have h₀ := orthPoly_orthogonal hba (by omega) hn m (by omega)
    have h₁ := orthPoly_orthogonal hba (i := i) (n := n + 1) (by omega) (by omega) m hm
    have hform : E * X ^ m = p (n + 2) * X ^ m - p (n + 1) * X ^ (m + 1) -
        C c * (p (n + 1) * X ^ m) + C (orthBeta a b i n) * (p n * X ^ m) := by
      dsimp [E, A]
      rw [pow_succ]
      ring
    rw [hform, nuF_add, nuF_sub, nuF_sub, nuF_C_mul, nuF_C_mul, h₀, h₁, mul_zero, sub_zero,
      zero_sub]
    by_cases hmn : m < n
    · rw [orthPoly_orthogonal hba (by omega) (by omega : n + 1 ≤ P a b - i) (m + 1) (by omega),
        orthPoly_orthogonal hba (by omega) (by omega : n ≤ P a b - i) m hmn]
      ring
    · have he : m = n := by omega
      subst m
      rw [← orthNorm_top hba (by omega) (by omega : n + 1 ≤ P a b - i),
        ← orthNorm_top hba (by omega) (by omega : n ≤ P a b - i), orthBeta,
        div_mul_cancel₀ _ (orthNorm_pos hba (by omega : n < P a b - i)).ne']
      ring
  have hz : E = 0 := eq_zero_of_orthogonal hba (by omega) (by omega : n + 1 ≤ P a b - i)
    (by omega) ho
  dsimp [E, A] at hz
  rw [hα] at hz
  simp only [map_neg] at hz ⊢
  linear_combination hz

end PierceLengthBound.FixedDividend
