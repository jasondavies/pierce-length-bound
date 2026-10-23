/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveMultivariateKronecker
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-! The polynomial automorphism used to raise the total degree in the
one-parameter integral-root estimate. It sends `(T,Y)` to `(T,Y+c T^e)`.
This file proves its inverse, preservation of irreducibility, its effect on
evaluation, and lower and upper bounds for the total degree of a sheared
polynomial. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

variable {R : Type*} [CommRing R]

/-- The power shear `(T,Y) ↦ (T,Y+c T^e)`. -/
def branchPowerShearHom (e : ℕ) (c : R) :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  aeval ![X 0, X 1 + C c * X 0 ^ e]

@[simp] lemma branchPowerShearHom_zero (e : ℕ) (c : R) :
    branchPowerShearHom e c (X 0) = X 0 := by simp [branchPowerShearHom]

@[simp] lemma branchPowerShearHom_one (e : ℕ) (c : R) :
    branchPowerShearHom e c (X 1) = X 1 + C c * X 0 ^ e := by
  simp [branchPowerShearHom]

lemma branchPowerShearHom_comp (e : ℕ) (c d : R) :
    (branchPowerShearHom e c).comp (branchPowerShearHom e d) =
      branchPowerShearHom e (c + d) := by
  ext i : 1
  fin_cases i <;> simp [branchPowerShearHom, add_mul, add_assoc]

lemma branchPowerShearHom_zero_coefficient (e : ℕ) :
    branchPowerShearHom e (0 : R) = AlgHom.id R (MvPolynomial (Fin 2) R) := by
  ext i : 1
  fin_cases i <;> simp [branchPowerShearHom]

/-- The power shear is a polynomial automorphism, with inverse the shear by `-c`. -/
def branchPowerShearEquiv (e : ℕ) (c : R) :
    MvPolynomial (Fin 2) R ≃ₐ[R] MvPolynomial (Fin 2) R :=
  AlgEquiv.ofAlgHom (branchPowerShearHom e c) (branchPowerShearHom e (-c))
    (by rw [branchPowerShearHom_comp, add_neg_cancel, branchPowerShearHom_zero_coefficient])
    (by rw [branchPowerShearHom_comp, neg_add_cancel, branchPowerShearHom_zero_coefficient])

theorem branchPowerShear_irreducible (e : ℕ) (c : R)
    {p : MvPolynomial (Fin 2) R} (hp : Irreducible p) :
    Irreducible (branchPowerShearHom e c p) :=
  (MulEquiv.irreducible_iff (f := (branchPowerShearEquiv e c).toMulEquiv)).mpr hp

/-- Evaluating a sheared polynomial at `(t,y)` evaluates the original at
`(t, y + c t^e)`. -/
theorem branchPowerShear_eval (e : ℕ) (c : R) (p : MvPolynomial (Fin 2) R) (t y : R) :
    eval ![t, y] (branchPowerShearHom e c p) = eval ![t, y + c * t ^ e] p := by
  have hh : (eval ![t, y]).comp (branchPowerShearHom e c).toRingHom =
      eval ![t, y + c * t ^ e] := by
    ext i
    · simp
    · fin_cases i <;> simp [branchPowerShearHom]
  exact DFunLike.congr_fun hh p

/-- The Kronecker substitution has degree at least the shear power times the
original degree in the root variable. -/
theorem branchMultiKronecker_two_natDegree_lower {p : MvPolynomial (Fin 2) R}
    (hp : p ≠ 0) {e : ℕ} (he : p.degreeOf 0 < e) :
    e * p.degreeOf 1 ≤ (branchMultiKronecker e 2 p).natDegree := by
  obtain ⟨s, hs, hdeg⟩ := Finset.exists_mem_eq_sup p.support
    (MvPolynomial.support_nonempty.mpr hp) (fun s => s 1)
  rw [← degreeOf_eq_sup] at hdeg
  have hnz : (branchMultiKronecker e 2 p).coeff (s 0 + e * s 1) ≠ 0 := by
    rw [branchMultiKronecker_two_coeff he hs]
    exact mem_support_iff.mp hs
  exact (by rw [hdeg]; omega : e * p.degreeOf 1 ≤ s 0 + e * s 1).trans
    (Polynomial.le_natDegree_of_ne_zero hnz)

/-- Restriction to the axis `Y = 0`. -/
def branchAxisHom : MvPolynomial (Fin 2) R →+* Polynomial R :=
  eval₂Hom Polynomial.C ![Polynomial.X, 0]

lemma branchAxisHom_natDegree_le (p : MvPolynomial (Fin 2) R) :
    (branchAxisHom p).natDegree ≤ p.totalDegree := by
  classical
  change (eval₂ Polynomial.C ![Polynomial.X, 0] p).natDegree ≤ _
  rw [eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  by_cases hy : s 1 = 0
  · simp only [hy, pow_zero, mul_one]
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
      ((le_degreeOf_of_mem_support 0 hs).trans (degreeOf_le_totalDegree p 0))
  · simp [zero_pow hy]

lemma branchAxisHom_shear (p : MvPolynomial (Fin 2) R) (e : ℕ) :
    branchAxisHom (branchPowerShearHom e 1 p) = branchMultiKronecker e 2 p := by
  have hh : branchAxisHom.comp (branchPowerShearHom e (1 : R)).toRingHom =
      branchMultiKronecker e 2 := by
    ext i
    · simp [branchAxisHom, branchMultiKronecker]
    · fin_cases i <;> simp [branchAxisHom, branchMultiKronecker, branchPowerShearHom]
  exact DFunLike.congr_fun hh p

/-- If `e` exceeds the parameter degree, the unit shear has total degree at
least `e` times the root-variable degree. -/
theorem branchPowerShear_totalDegree_lower {p : MvPolynomial (Fin 2) R}
    (hp : p ≠ 0) {e : ℕ} (he : p.degreeOf 0 < e) :
    e * p.degreeOf 1 ≤ (branchPowerShearHom e 1 p).totalDegree := by
  apply (branchMultiKronecker_two_natDegree_lower hp he).trans
  rw [← branchAxisHom_shear]
  exact branchAxisHom_natDegree_le _

/-- The shear multiplies the total degree by at most its exponent. -/
theorem branchPowerShear_totalDegree_upper [Nontrivial R] (p : MvPolynomial (Fin 2) R)
    {e : ℕ} (he : 1 ≤ e) (c : R) :
    (branchPowerShearHom e c p).totalDegree ≤ e * p.totalDegree := by
  classical
  have hX : (X (0 : Fin 2) : MvPolynomial (Fin 2) R).totalDegree ≤ e :=
    by simpa only [totalDegree_X] using he
  have hY : (X (1 : Fin 2) + C c * X 0 ^ e : MvPolynomial (Fin 2) R).totalDegree ≤ e := by
    apply (totalDegree_add _ _).trans
    apply max_le (by simpa only [totalDegree_X] using he)
    apply (totalDegree_mul _ _).trans
    rw [totalDegree_C, zero_add]
    simpa only [totalDegree_X, mul_one] using
      totalDegree_pow (X (0 : Fin 2) : MvPolynomial (Fin 2) R) e
  conv_lhs => rw [p.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro s hs
  simp only [branchPowerShearHom, aeval_monomial, algebraMap_eq]
  change (C (p.coeff s) * s.prod (fun i k =>
    ![X (0 : Fin 2), X 1 + C c * X 0 ^ e] i ^ k)).totalDegree ≤ _
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add, Finsupp.prod_fintype _ _ (by simp)]
  calc
    _ ≤ ∑ i : Fin 2, (![X (0 : Fin 2), X 1 + C c * X 0 ^ e] i ^ s i).totalDegree :=
      totalDegree_finsetProd _ _
    _ ≤ ∑ i : Fin 2, s i * e := by
      apply Finset.sum_le_sum
      intro i _
      apply (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ ?_)
      fin_cases i
      · exact hX
      · exact hY
    _ = e * s.sum (fun _ k => k) := by
      rw [← Finset.sum_mul, Finsupp.sum_fintype _ _ (by simp), Nat.mul_comm]
    _ ≤ e * p.totalDegree := Nat.mul_le_mul_left e (le_totalDegree hs)

end
end PierceLengthBound.FixedDividend
