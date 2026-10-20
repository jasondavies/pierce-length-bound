/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Tactic

/-!
# Universal degree-six resultants along exceptional directions

A fixed-size Sylvester/Bézout identity and unit triangular Newton-basis changes
provide algebraic degree certificates valid for every coefficient specialization.
-/

@[expose] public section

namespace PierceLengthBound.FixedDividend

noncomputable section

open Polynomial Matrix

/-- Bézout matrix of two monic quartics, in ascending coefficient order. -/
def quarticBezout {R : Type*} [CommRing R] (a b : Fin 4 → R) : Matrix (Fin 4) (Fin 4) R :=
  !![a 1 * b 0 - a 0 * b 1, a 2 * b 0 - a 0 * b 2,
       a 3 * b 0 - a 0 * b 3, b 0 - a 0;
     a 2 * b 0 - a 0 * b 2, a 3 * b 0 - a 0 * b 3 + a 2 * b 1 - a 1 * b 2,
       b 0 - a 0 + a 3 * b 1 - a 1 * b 3, b 1 - a 1;
     a 3 * b 0 - a 0 * b 3, b 0 - a 0 + a 3 * b 1 - a 1 * b 3,
       b 1 - a 1 + a 3 * b 2 - a 2 * b 3, b 2 - a 2;
     b 0 - a 0, b 1 - a 1, b 2 - a 2, b 3 - a 3]

/-- The Sylvester matrix for the same two monic quartics. -/
def quarticSylvester {R : Type*} [CommRing R] (a b : Fin 4 → R) : Matrix (Fin 8) (Fin 8) R :=
  !![b 0, 0, 0, 0, a 0, 0, 0, 0;
     b 1, b 0, 0, 0, a 1, a 0, 0, 0;
     b 2, b 1, b 0, 0, a 2, a 1, a 0, 0;
     b 3, b 2, b 1, b 0, a 3, a 2, a 1, a 0;
     1, b 3, b 2, b 1, 1, a 3, a 2, a 1;
     0, 1, b 3, b 2, 0, 1, a 3, a 2;
     0, 0, 1, b 3, 0, 0, 1, a 3;
     0, 0, 0, 1, 0, 0, 0, 1]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
-- Expand the fixed-size determinants once to certify the universal Bézout identity.
theorem quarticSylvester_det {R : Type*} [CommRing R] (a b : Fin 4 → R) :
    (quarticSylvester a b).det = (quarticBezout a b).det := by
  simp [quarticSylvester, quarticBezout, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Matrix.submatrix_apply,
    Fin.succAbove]
  ring

/-- A monic quartic from its four lower coefficients. -/
def monicQuartic {R : Type*} [CommRing R] (a : Fin 4 → R) : R[X] :=
  C (a 0) + C (a 1) * X + C (a 2) * X ^ 2 + C (a 3) * X ^ 3 + X ^ 4

lemma monicQuartic_coeff {R : Type*} [CommRing R] (a : Fin 4 → R) (j : ℕ) :
    (monicQuartic a).coeff j =
      if j = 0 then a 0 else if j = 1 then a 1 else if j = 2 then a 2 else
      if j = 3 then a 3 else if j = 4 then 1 else 0 := by
  by_cases h0 : j = 0
  · subst j; simp [monicQuartic]
  by_cases h1 : j = 1
  · subst j; simp [monicQuartic]
  by_cases h2 : j = 2
  · subst j; simp [monicQuartic]
  by_cases h3 : j = 3
  · subst j; simp [monicQuartic]
  by_cases h4 : j = 4
  · subst j; simp [monicQuartic]
  simp [monicQuartic, coeff_C, coeff_X, h0, h1, h2, h3, h4, Ne.symm h1]

/-- Bézout's determinant formula for arbitrary monic quartics, with explicit degrees. -/
theorem resultant_monicQuartic {R : Type*} [CommRing R] (a b : Fin 4 → R) :
    resultant (monicQuartic a) (monicQuartic b) 4 4 = (quarticBezout a b).det := by
  have hs : sylvester (monicQuartic a) (monicQuartic b) 4 4 = quarticSylvester a b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [sylvester, quarticSylvester, monicQuartic_coeff, Fin.addCases]
  rw [resultant, hs, quarticSylvester_det]

/-- Change from monomial coefficients to a Newton basis beginning at `a,b,c`. -/
def newtonBasisChange {R : Type*} [CommRing R] (a b c : R) : Matrix (Fin 4) (Fin 4) R :=
  !![1, a, a ^ 2, a ^ 3;
     0, 1, a + b, a ^ 2 + a * b + b ^ 2;
     0, 0, 1, a + b + c;
     0, 0, 0, 1]

lemma newtonBasisChange_det {R : Type*} [CommRing R] (a b c : R) :
    (newtonBasisChange a b c).det = 1 := by
  simp [newtonBasisChange, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix_apply, Fin.succAbove]

lemma det_newtonBasisChange {R : Type*} [CommRing R]
    (M : Matrix (Fin 4) (Fin 4) R) (a b c : R) :
    (newtonBasisChange a b c * M * (newtonBasisChange a b c).transpose).det = M.det := by
  simp [Matrix.det_mul, Matrix.det_transpose, newtonBasisChange_det]

/-- A row-plus-column degree certificate bounds the determinant degree. -/
theorem natDegree_det_le_row_col {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R[X]) (r c : ι → ℕ)
    (h : ∀ i j, (M i j).natDegree ≤ r i + c j) :
    M.det.natDegree ≤ (∑ i, r i) + ∑ j, c j := by
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ hσ
  calc (Equiv.Perm.sign σ • ∏ i, M (σ i) i).natDegree
      ≤ (∏ i, M (σ i) i).natDegree := natDegree_smul_le _ _
    _ ≤ ∑ i, (M (σ i) i).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ i, (r (σ i) + c i) := Finset.sum_le_sum fun i _ => h (σ i) i
    _ = (∑ i, r i) + ∑ j, c j := by rw [Finset.sum_add_distrib, Equiv.sum_comp σ r]

/-- Coefficients of the first Newton quartic, with initial node zero. -/
def firstNewtonCoeffs {R : Type*} [CommRing R] (c : Fin 4 → R) (s : Fin 4 → R) : Fin 4 → R :=
  ![c 0, c 1 - c 2 * s 0 + c 3 * s 0 * s 1 - s 0 * s 1 * s 2,
    c 2 - c 3 * (s 0 + s 1) + s 0 * s 1 + s 0 * s 2 + s 1 * s 2,
    c 3 - (s 0 + s 1 + s 2)]

/-- Coefficients of the next Newton quartic, beginning at node `s₁`. -/
def nextNewtonCoeffs {R : Type*} [CommRing R] (e : Fin 4 → R) (s : Fin 4 → R) : Fin 4 → R :=
  ![e 0 - e 1 * s 0 + e 2 * s 0 * s 1 - e 3 * s 0 * s 1 * s 2 + s 0 * s 1 * s 2 * s 3,
    e 1 - e 2 * (s 0 + s 1) + e 3 * (s 0 * s 1 + s 0 * s 2 + s 1 * s 2) -
      (s 0 * s 1 * s 2 + s 0 * s 1 * s 3 + s 0 * s 2 * s 3 + s 1 * s 2 * s 3),
    e 2 - e 3 * (s 0 + s 1 + s 2) + s 0 * s 1 + s 0 * s 2 + s 0 * s 3 +
      s 1 * s 2 + s 1 * s 3 + s 2 * s 3,
    e 3 - (s 0 + s 1 + s 2 + s 3)]

/-- The four nodes along the exceptional `(0,3)` direction. -/
def nodes03 {R : Type*} [CommRing R] (a : Fin 4 → R) : Fin 4 → R[X] :=
  ![C (a 0) + X, C (a 1) + X, C (a 2), C (a 3) + X]

/-- Transformed Bézout matrix for any choice of the three initial Newton nodes. -/
def changedBezout {R : Type*} [CommRing R] (c e s : Fin 4 → R) (a b d : R) :=
  newtonBasisChange a b d * quarticBezout (firstNewtonCoeffs c s) (nextNewtonCoeffs e s) *
    (newtonBasisChange a b d).transpose

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
-- Normalize the ten polynomial entries of the fixed-size Bézout certificate.
lemma changedBezout03_degree {R : Type*} [CommRing R] (c e a : Fin 4 → R) (i j : Fin 4) :
    ((changedBezout (C ∘ c) (C ∘ e) (nodes03 a)
      (nodes03 a 0) (nodes03 a 1) 0) i j).natDegree ≤
      (![1, 1, 0, 0] i) + (![1, 1, 1, 1] j) := by
  fin_cases i <;> fin_cases j <;>
    simp [changedBezout, newtonBasisChange, quarticBezout, firstNewtonCoeffs,
      nextNewtonCoeffs, nodes03, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf
  all_goals compute_degree
  all_goals omega

/-- The four nodes along exceptional direction `(1,2)`. -/
def nodes12 {R : Type*} [CommRing R] (a : Fin 4 → R) : Fin 4 → R[X] :=
  ![C (a 0) + X, C (a 1) + X, C (a 2), C (a 3)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
-- Normalize the polynomial entries of the fixed-size Bézout certificate.
lemma changedBezout12_degree {R : Type*} [CommRing R] (c e a : Fin 4 → R) (i j : Fin 4) :
    ((changedBezout (C ∘ c) (C ∘ e) (nodes12 a)
      (nodes12 a 0) 0 (nodes12 a 1)) i j).natDegree ≤
      (![2, 1, 1, 0] i) + (![1, 1, 0, 0] j) := by
  fin_cases i <;> fin_cases j <;>
    simp [changedBezout, newtonBasisChange, quarticBezout, firstNewtonCoeffs,
      nextNewtonCoeffs, nodes12, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf
  all_goals first | (apply Nat.eq_zero_of_le_zero; compute_degree) | compute_degree
  all_goals omega

/-- The four nodes along exceptional direction `(2,3)`. -/
def nodes23 {R : Type*} [CommRing R] (a : Fin 4 → R) : Fin 4 → R[X] :=
  ![C (a 0), C (a 1) + X, C (a 2) + X, C (a 3)]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
-- Normalize the polynomial entries of the fixed-size Bézout certificate.
lemma changedBezout23_degree {R : Type*} [CommRing R] (c e a : Fin 4 → R) (i j : Fin 4) :
    ((changedBezout (C ∘ c) (C ∘ e) (nodes23 a)
      (nodes23 a 0) (nodes23 a 1) 0) i j).natDegree ≤
      (![1, 1, 1, 0] i) + (![1, 1, 1, 0] j) := by
  fin_cases i <;> fin_cases j <;>
    simp [changedBezout, newtonBasisChange, quarticBezout, firstNewtonCoeffs,
      nextNewtonCoeffs, nodes23, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf
  all_goals first | (apply Nat.eq_zero_of_le_zero; compute_degree) | compute_degree
  all_goals omega

/-- The four nodes along exceptional direction `(1,4)`. -/
def nodes14 {R : Type*} [CommRing R] (a : Fin 4 → R) : Fin 4 → R[X] :=
  ![C (a 0) + X, C (a 1), C (a 2), C (a 3) + X]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
-- Normalize the polynomial entries of the fixed-size Bézout certificate.
lemma changedBezout14_degree {R : Type*} [CommRing R] (c e a : Fin 4 → R) (i j : Fin 4) :
    ((changedBezout (C ∘ c) (C ∘ e) (nodes14 a)
      0 (nodes14 a 0) (nodes14 a 1)) i j).natDegree ≤
      (![2, 1, 1, 1] i) + (![1, 0, 0, 0] j) := by
  fin_cases i <;> fin_cases j <;>
    simp [changedBezout, newtonBasisChange, quarticBezout, firstNewtonCoeffs,
      nextNewtonCoeffs, nodes14, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring_nf
  all_goals compute_degree

lemma changedBezout_det {R : Type*} [CommRing R] (c e s : Fin 4 → R) (a b d : R) :
    (changedBezout c e s a b d).det =
      (quarticBezout (firstNewtonCoeffs c s) (nextNewtonCoeffs e s)).det :=
  det_newtonBasisChange _ _ _ _

/-- Universal degree-six bound in exceptional direction `(0,3)`. -/
theorem resultant_degree_03 {R : Type*} [CommRing R] (c e a : Fin 4 → R) :
    (resultant (monicQuartic (firstNewtonCoeffs (C ∘ c) (nodes03 a)))
      (monicQuartic (nextNewtonCoeffs (C ∘ e) (nodes03 a))) 4 4).natDegree ≤ 6 := by
  rw [resultant_monicQuartic, ← changedBezout_det (C ∘ c) (C ∘ e) (nodes03 a)
    (nodes03 a 0) (nodes03 a 1) 0]
  have h := natDegree_det_le_row_col _ ![1, 1, 0, 0] ![1, 1, 1, 1] (changedBezout03_degree c e a)
  simpa [Fin.sum_univ_succ] using h

/-- Universal degree-six bound in exceptional direction `(1,2)`. -/
theorem resultant_degree_12 {R : Type*} [CommRing R] (c e a : Fin 4 → R) :
    (resultant (monicQuartic (firstNewtonCoeffs (C ∘ c) (nodes12 a)))
      (monicQuartic (nextNewtonCoeffs (C ∘ e) (nodes12 a))) 4 4).natDegree ≤ 6 := by
  rw [resultant_monicQuartic, ← changedBezout_det (C ∘ c) (C ∘ e) (nodes12 a)
    (nodes12 a 0) 0 (nodes12 a 1)]
  have h := natDegree_det_le_row_col _ ![2, 1, 1, 0] ![1, 1, 0, 0] (changedBezout12_degree c e a)
  simpa [Fin.sum_univ_succ] using h

/-- Universal degree-six bound in exceptional direction `(2,3)`. -/
theorem resultant_degree_23 {R : Type*} [CommRing R] (c e a : Fin 4 → R) :
    (resultant (monicQuartic (firstNewtonCoeffs (C ∘ c) (nodes23 a)))
      (monicQuartic (nextNewtonCoeffs (C ∘ e) (nodes23 a))) 4 4).natDegree ≤ 6 := by
  rw [resultant_monicQuartic, ← changedBezout_det (C ∘ c) (C ∘ e) (nodes23 a)
    (nodes23 a 0) (nodes23 a 1) 0]
  have h := natDegree_det_le_row_col _ ![1, 1, 1, 0] ![1, 1, 1, 0] (changedBezout23_degree c e a)
  simpa [Fin.sum_univ_succ] using h

/-- Universal degree-six bound in exceptional direction `(1,4)`. -/
theorem resultant_degree_14 {R : Type*} [CommRing R] (c e a : Fin 4 → R) :
    (resultant (monicQuartic (firstNewtonCoeffs (C ∘ c) (nodes14 a)))
      (monicQuartic (nextNewtonCoeffs (C ∘ e) (nodes14 a))) 4 4).natDegree ≤ 6 := by
  rw [resultant_monicQuartic, ← changedBezout_det (C ∘ c) (C ∘ e) (nodes14 a)
    0 (nodes14 a 0) (nodes14 a 1)]
  have h := natDegree_det_le_row_col _ ![2, 1, 1, 1] ![1, 0, 0, 0] (changedBezout14_degree c e a)
  simpa [Fin.sum_univ_succ] using h

lemma monicQuartic_natDegree {R : Type*} [CommRing R] [Nontrivial R] (a : Fin 4 → R) :
    (monicQuartic a).natDegree = 4 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · unfold monicQuartic; compute_degree
  · simp [monicQuartic_coeff]

/-- Multiplying the next quartic by `X` adds only the constant first coefficient. -/
lemma resultant_monicQuartic_X_mul {R : Type*} [CommRing R] [Nontrivial R]
    (a b : Fin 4 → R) :
    resultant (monicQuartic a) (X * monicQuartic b) 4 5 =
      a 0 * resultant (monicQuartic a) (monicQuartic b) 4 4 := by
  have hm := (monicQuartic_natDegree a).le
  have h := resultant_mul_right (monicQuartic a) X (monicQuartic b) 4 hm
  have hx : resultant (monicQuartic a) X 4 1 = a 0 := by
    have hx0 := resultant_X_pow_right (monicQuartic a) 4 1 hm
    have hpow : (X : R[X]) ^ 1 = X := pow_one _
    rw [hpow, show (-1 : R) ^ (4 * 1) = 1 by ring, one_mul] at hx0
    simpa [monicQuartic_coeff] using hx0
  simp only [natDegree_X, monicQuartic_natDegree, hx] at h
  exact h

/-- First Newton quartic, with its initial node fixed at zero. -/
def firstNewtonQuartic {R : Type*} [CommRing R] (c s : Fin 4 → R) : R[X] :=
  C (c 0) + C (c 1) * X + C (c 2) * X * (X - C (s 0)) +
    C (c 3) * X * (X - C (s 0)) * (X - C (s 1)) +
    X * (X - C (s 0)) * (X - C (s 1)) * (X - C (s 2))

/-- The shifted next Newton quartic. -/
def nextNewtonQuartic {R : Type*} [CommRing R] (e s : Fin 4 → R) : R[X] :=
  C (e 0) + C (e 1) * (X - C (s 0)) + C (e 2) * (X - C (s 0)) * (X - C (s 1)) +
    C (e 3) * (X - C (s 0)) * (X - C (s 1)) * (X - C (s 2)) +
    (X - C (s 0)) * (X - C (s 1)) * (X - C (s 2)) * (X - C (s 3))

lemma firstNewtonQuartic_eq {R : Type*} [CommRing R] (c s : Fin 4 → R) :
    firstNewtonQuartic c s = monicQuartic (firstNewtonCoeffs c s) := by
  simp [firstNewtonQuartic, monicQuartic, firstNewtonCoeffs]
  ring

lemma nextNewtonQuartic_eq {R : Type*} [CommRing R] (e s : Fin 4 → R) :
    nextNewtonQuartic e s = monicQuartic (nextNewtonCoeffs e s) := by
  simp [nextNewtonQuartic, monicQuartic, nextNewtonCoeffs]
  ring

/-- Factoring out the extra root without expanding the resultant determinant. -/
lemma resultant_firstNewton_X_mul {R : Type*} [CommRing R] [Nontrivial R]
    (c e s : Fin 4 → R) :
    resultant (firstNewtonQuartic c s) (X * nextNewtonQuartic e s) 4 5 =
      c 0 * resultant (firstNewtonQuartic c s) (nextNewtonQuartic e s) 4 4 := by
  rw [firstNewtonQuartic_eq, nextNewtonQuartic_eq, resultant_monicQuartic_X_mul]
  rfl

/-- The polynomial-coefficient specialization, with multiplication converted
before applying it to the resultant. This prevents kernel reduction from
expanding a determinant while comparing equivalent multiplication instances. -/
lemma resultant_firstNewton_X_mul_polynomial {R : Type*} [CommRing R] [Nontrivial R]
    (c e s : Fin 4 → R[X]) :
    resultant (firstNewtonQuartic c s) (X * nextNewtonQuartic e s) 4 5 =
      c 0 * resultant (firstNewtonQuartic c s) (nextNewtonQuartic e s) 4 4 := by
  have hm : @HMul.hMul R[X] R[X] R[X]
      (@instHMul R[X] (@Distrib.toMul R[X]
        (@instDistribOfSemiring R[X]
          (@CommSemiring.toSemiring R[X]
            (@CommRing.toCommSemiring R[X] Polynomial.commRing))))) =
      (fun p q : R[X] => p * q) := rfl
  exact (resultant_firstNewton_X_mul c e s).trans (congrFun (congrFun hm _) _)

/-- The four normalized possible directions, in the order `(0,3),(1,2),(2,3),(1,4)`.
The entries are nodes `s₁,...,s₄`; node `s₀` is identically zero. -/
def exceptionalNodes {R : Type*} [CommRing R] (a : Fin 4 → R) (d : Fin 4) : Fin 4 → R[X] :=
  ![nodes03 a, nodes12 a, nodes23 a, nodes14 a] d

/-- The curve candidate's universal degree-six lemma. No genericity, separation,
nonvanishing, coefficient signs, or kernel relations are needed. -/
theorem line_resultant_natDegree_le_six {R : Type*} [CommRing R] [Nontrivial R]
    (c e a : Fin 4 → R) (d : Fin 4) :
    (resultant (firstNewtonQuartic (C ∘ c) (exceptionalNodes a d))
      (X * nextNewtonQuartic (C ∘ e) (exceptionalNodes a d)) 4 5).natDegree ≤ 6 := by
  rw [resultant_firstNewton_X_mul_polynomial]
  apply (natDegree_C_mul_le _ _).trans
  rw [firstNewtonQuartic_eq, nextNewtonQuartic_eq]
  fin_cases d
  · exact resultant_degree_03 c e a
  · exact resultant_degree_12 c e a
  · exact resultant_degree_23 c e a
  · exact resultant_degree_14 c e a

end
end PierceLengthBound.FixedDividend
