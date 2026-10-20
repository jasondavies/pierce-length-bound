/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendLineResultant

/-!
# Degree ten and leading form of the fixed-dividend resultant

A Newton-basis Bézout matrix has staircase degrees `4 - max i j`.
Only its diagonal determinant term can attain degree ten.
-/

@[expose] public section

namespace PierceLengthBound.FixedDividend

noncomputable section

open Polynomial Matrix

/-- Explicit Bézout matrix in the Newton basis beginning at `s₁,s₂,s₃`. -/
def newtonBezout {R : Type*} [CommRing R] (c e s : Fin 4 → R) : Matrix (Fin 4) (Fin 4) R :=
  let s₁ := s 0; let s₂ := s 1; let s₃ := s 2; let s₄ := s 3
  let c₀ := c 0; let c₁ := c 1; let c₂ := c 2; let c₃ := c 3
  let e₀ := e 0; let e₁ := e 1; let e₂ := e 2; let e₃ := e 3
  let b00 := e₀ * (c₁ + c₂ * s₁ + c₃ * s₁ * (s₁ - s₂) + s₁ * (s₁ - s₂) * (s₁ - s₃)) -
    (c₀ + c₁ * s₁) * (e₁ + e₂ * (s₁ - s₂) + e₃ * (s₁ - s₂) * (s₁ - s₃) +
      (s₁ - s₂) * (s₁ - s₃) * (s₁ - s₄))
  let b01 := e₀ * (c₂ + c₃ * s₁ + s₁ * (s₁ - s₃)) -
    (c₀ + c₁ * s₁) * (e₂ + e₃ * (s₁ - s₃) + (s₁ - s₃) * (s₁ - s₄))
  let b02 := e₀ * (c₃ + s₁) - (c₀ + c₁ * s₁) * (e₃ + s₁ - s₄)
  let b03 := e₀ - c₀ - c₁ * s₁
  let b11 := e₀ * (c₃ + s₁ + s₂ - s₃) + e₁ * (c₂ + c₃ * s₂ + s₂ * (s₂ - s₃)) -
    c₀ * (e₃ + s₁ + s₂ - s₃ - s₄) -
    c₁ * (e₂ + e₃ * (s₁ + s₂ - s₃) + s₁ ^ 2 + s₁ * s₂ - s₁ * s₃ - s₁ * s₄ +
      s₂ ^ 2 - s₂ * s₃ - s₂ * s₄ + s₃ * s₄) -
    c₂ * s₂ * (e₂ + e₃ * (s₂ - s₃) + (s₂ - s₃) * (s₂ - s₄))
  let b12 := e₀ - c₀ + e₁ * (c₃ + s₂) - c₁ * (e₃ + s₁ + s₂ - s₄) -
    c₂ * s₂ * (e₃ + s₂ - s₄)
  let b13 := e₁ - c₁ - c₂ * s₂
  let b22 := e₁ - c₁ + e₂ * (c₃ + s₃) - c₂ * (e₃ + s₂ + s₃ - s₄) -
    c₃ * s₃ * (e₃ + s₃ - s₄)
  let b23 := e₂ - c₂ - c₃ * s₃
  let b33 := e₃ - c₃ - s₄
  !![b00, b01, b02, b03; b01, b11, b12, b13; b02, b12, b22, b23; b03, b13, b23, b33]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
-- Certify the explicit fixed-size change of basis once over an arbitrary coefficient ring.
lemma changedBezout_eq_newtonBezout {R : Type*} [CommRing R] (c e s : Fin 4 → R) :
    changedBezout c e s (s 0) (s 1) (s 2) = newtonBezout c e s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [changedBezout, newtonBasisChange, quarticBezout, firstNewtonCoeffs,
      nextNewtonCoeffs, newtonBezout, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

lemma newtonBezout_det {R : Type*} [CommRing R] (c e s : Fin 4 → R) :
    (newtonBezout c e s).det =
      resultant (firstNewtonQuartic c s) (nextNewtonQuartic e s) 4 4 := by
  rw [firstNewtonQuartic_eq, nextNewtonQuartic_eq, resultant_monicQuartic,
    ← changedBezout_eq_newtonBezout, changedBezout_det]

/-- Four affine node functions, with independent offsets and directions. -/
def affineNodes {R : Type*} [CommRing R] (a z : Fin 4 → R) : Fin 4 → R[X] :=
  fun j => C (a j) + C (z j) * X

/-- Staircase degrees of the Newton Bézout entries. -/
lemma newtonBezout_degree {R : Type*} [CommRing R] (c e a z : Fin 4 → R) (i j : Fin 4) :
    (newtonBezout (C ∘ c) (C ∘ e) (affineNodes a z) i j).natDegree ≤
      4 - max i.val j.val := by
  fin_cases i <;> fin_cases j <;> simp only [newtonBezout, Fin.isValue, Function.comp_apply, affineNodes,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, of_apply, cons_val', cons_val_zero,
      cons_val_fin_one, cons_val_one, cons_val, max_self, tsub_zero, zero_le,
      sup_of_le_right, sup_of_le_left, Nat.add_one_sub_one, Nat.reduceSub,
      Nat.one_le_ofNat, Nat.reduceLeDiff] <;> compute_degree

/-- Leading coefficients of the four diagonal entries. -/
lemma newtonBezout_diagonal_coeffs {R : Type*} [CommRing R] (c e a z : Fin 4 → R) :
    (newtonBezout (C ∘ c) (C ∘ e) (affineNodes a z) 0 0).coeff 4 =
        -c 1 * z 0 * (z 0 - z 1) * (z 0 - z 2) * (z 0 - z 3) ∧
    (newtonBezout (C ∘ c) (C ∘ e) (affineNodes a z) 1 1).coeff 3 =
        -c 2 * z 1 * (z 1 - z 2) * (z 1 - z 3) ∧
    (newtonBezout (C ∘ c) (C ∘ e) (affineNodes a z) 2 2).coeff 2 =
        -c 3 * z 2 * (z 2 - z 3) ∧
    (newtonBezout (C ∘ c) (C ∘ e) (affineNodes a z) 3 3).coeff 1 = -z 3 := by
  constructor
  · dsimp [newtonBezout, affineNodes]
    compute_degree <;> norm_num
    ring
  constructor
  · dsimp [newtonBezout, affineNodes]
    compute_degree <;> norm_num
    ring
  constructor
  · let s := affineNodes a z
    let low := C (e 1) - C (c 1) + C (e 2) * (C (c 3) + s 2) -
      C (c 2) * (C (e 3) + s 1 + s 2 - s 3) - C (c 3) * s 2 * C (e 3)
    have hlo : low.natDegree ≤ 1 := by dsimp [low, s, affineNodes]; compute_degree
    have he : newtonBezout (C ∘ c) (C ∘ e) s 2 2 =
        low - C (c 3) * (s 2 * (s 2 - s 3)) := by
      simp [newtonBezout, low]
      ring
    change (newtonBezout (C ∘ c) (C ∘ e) s 2 2).coeff 2 = _
    rw [he, coeff_sub, coeff_eq_zero_of_natDegree_lt (hlo.trans_lt (by norm_num)), coeff_C_mul]
    have hs : (s 2).natDegree ≤ 1 := by dsimp [s, affineNodes]; compute_degree
    have hd : (s 2 - s 3).natDegree ≤ 1 := by dsimp [s, affineNodes]; compute_degree
    rw [coeff_mul_add_eq_of_natDegree_le hs hd]
    simp [s, affineNodes]
    ring
  · simp [newtonBezout, affineNodes]

/-- A nonidentity permutation loses at least one degree in the staircase matrix. -/
lemma staircase_perm_bound : ∀ σ : Equiv.Perm (Fin 4), σ ≠ Equiv.refl _ →
    (∑ i : Fin 4, (4 - max (σ i).val i.val)) ≤ 9 := by decide

/-- The degree-ten coefficient of a staircase determinant is its diagonal product. -/
theorem staircase_det_coeff {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R[X])
    (h : ∀ i j, (M i j).natDegree ≤ 4 - max i.val j.val) :
    M.det.coeff 10 = (M 0 0).coeff 4 * (M 1 1).coeff 3 * (M 2 2).coeff 2 * (M 3 3).coeff 1 := by
  classical
  rw [Matrix.det_apply, finsetSum_coeff]
  rw [Finset.sum_eq_single (Equiv.refl (Fin 4))]
  · simp only [Equiv.Perm.sign_refl, one_smul, Equiv.refl_apply, Fin.prod_univ_four, mul_assoc]
    have h00 : (M 0 0).natDegree ≤ 4 := h 0 0
    have h11 : (M 1 1).natDegree ≤ 3 := h 1 1
    have h22 : (M 2 2).natDegree ≤ 2 := h 2 2
    have h33 : (M 3 3).natDegree ≤ 1 := h 3 3
    have h23 : (M 2 2 * M 3 3).natDegree ≤ 3 :=
      natDegree_mul_le.trans (add_le_add h22 h33)
    have h123 : (M 1 1 * (M 2 2 * M 3 3)).natDegree ≤ 6 :=
      natDegree_mul_le.trans (add_le_add h11 h23)
    calc (M 0 0 * (M 1 1 * (M 2 2 * M 3 3))).coeff 10
        = (M 0 0).coeff 4 * (M 1 1 * (M 2 2 * M 3 3)).coeff 6 :=
          coeff_mul_add_eq_of_natDegree_le h00 h123
      _ = _ := by
        rw [coeff_mul_add_eq_of_natDegree_le h11 h23,
          coeff_mul_add_eq_of_natDegree_le h22 h33]
  · intro σ hσ hne
    apply coeff_eq_zero_of_natDegree_lt
    have hbound : (Equiv.Perm.sign σ • ∏ i, M (σ i) i).natDegree ≤ 9 := by
      calc (Equiv.Perm.sign σ • ∏ i, M (σ i) i).natDegree
          ≤ (∏ i, M (σ i) i).natDegree := natDegree_smul_le _ _
        _ ≤ ∑ i, (M (σ i) i).natDegree := natDegree_prod_le _ _
        _ ≤ ∑ i, (4 - max (σ i).val i.val) := Finset.sum_le_sum fun i _ => h _ _
        _ ≤ 9 := staircase_perm_bound σ hne
    omega
  · simp

/-- Degree at most ten for arbitrary affine motions of all four nodes. -/
theorem resultant_affine_degree_le_ten {R : Type*} [CommRing R] (c e a z : Fin 4 → R) :
    (resultant (firstNewtonQuartic (C ∘ c) (affineNodes a z))
      (nextNewtonQuartic (C ∘ e) (affineNodes a z)) 4 4).natDegree ≤ 10 := by
  rw [← newtonBezout_det]
  have h := natDegree_det_le_row_col
    (newtonBezout (C ∘ c) (C ∘ e) (affineNodes a z))
    (fun i => 4 - i.val) (fun _ => 0) (fun i j => ?_)
  · simpa [Fin.sum_univ_succ] using h
  · have hd := newtonBezout_degree c e a z i j
    have hj : i.val ≤ max i.val j.val := le_max_left _ _
    omega

/-- The signed product of the ten differences among nodes `0,z₁,z₂,z₃,z₄`. -/
def nodeVandermonde {R : Type*} [CommRing R] (z : Fin 4 → R) : R :=
  z 0 * z 1 * z 2 * z 3 * (z 1 - z 0) * (z 2 - z 0) * (z 3 - z 0) *
    (z 2 - z 1) * (z 3 - z 1) * (z 3 - z 2)

/-- Universal Vandermonde leading form; no nonzero or distinct-node hypotheses. -/
theorem resultant_affine_coeff_ten {R : Type*} [CommRing R] (c e a z : Fin 4 → R) :
    (resultant (firstNewtonQuartic (C ∘ c) (affineNodes a z))
      (nextNewtonQuartic (C ∘ e) (affineNodes a z)) 4 4).coeff 10 =
        c 1 * c 2 * c 3 * nodeVandermonde z := by
  rw [← newtonBezout_det, staircase_det_coeff _ (newtonBezout_degree c e a z)]
  obtain ⟨h0, h1, h2, h3⟩ := newtonBezout_diagonal_coeffs c e a z
  rw [h0, h1, h2, h3]
  unfold nodeVandermonde
  ring

/-- The candidate's degree-ten bound, including the factor `X` in its next polynomial. -/
theorem line_resultant_natDegree_le_ten {R : Type*} [CommRing R] [Nontrivial R]
    (c e a z : Fin 4 → R) :
    (resultant (firstNewtonQuartic (C ∘ c) (affineNodes a z))
      (X * nextNewtonQuartic (C ∘ e) (affineNodes a z)) 4 5).natDegree ≤ 10 := by
  rw [resultant_firstNewton_X_mul_polynomial]
  exact (natDegree_C_mul_le _ _).trans (resultant_affine_degree_le_ten c e a z)

/-- Exact degree-ten leading form in the candidate, for all node offsets and directions. -/
theorem line_resultant_coeff_ten {R : Type*} [CommRing R] [Nontrivial R]
    (c e a z : Fin 4 → R) :
    (resultant (firstNewtonQuartic (C ∘ c) (affineNodes a z))
      (X * nextNewtonQuartic (C ∘ e) (affineNodes a z)) 4 5).coeff 10 =
        c 0 * c 1 * c 2 * c 3 * nodeVandermonde z := by
  rw [resultant_firstNewton_X_mul_polynomial, Function.comp_apply, coeff_C_mul,
    resultant_affine_coeff_ten]
  ring

end
end PierceLengthBound.FixedDividend
