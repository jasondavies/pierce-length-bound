/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSievePolynomialSubstitution
public import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Tactic

/-! Exact specialization and uniform coefficient bounds for the induction on
the number of Hilbert parameters. The last polynomial variable is kept
separate, so a monic family remains monic after each parameter specialization. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Finset

/-- Specialize the first parameter and retain the remaining ones. -/
def branchHeadSpecialization {r : ℕ} (t : ℤ) :
    MvPolynomial (Fin (r + 1)) ℤ →+* MvPolynomial (Fin r) ℤ :=
  eval₂Hom C (Fin.cases (C t) X)

lemma branchHeadSpecialization_eq_eval {r : ℕ} (t : ℤ)
    (f : MvPolynomial (Fin (r + 1)) ℤ) :
    branchHeadSpecialization t f = (finSuccEquiv ℤ r f).eval (C t) := by
  have h : branchHeadSpecialization t =
      (Polynomial.evalRingHom (C t)).comp (finSuccEquiv ℤ r).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [branchHeadSpecialization]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [branchHeadSpecialization, finSuccEquiv_X_zero, finSuccEquiv_X_succ]
  exact DFunLike.congr_fun h f

lemma branchHeadSpecialization_sum {r d : ℕ} (t : ℤ)
    (f : MvPolynomial (Fin (r + 1)) ℤ) (hd : f.totalDegree ≤ d) :
    branchHeadSpecialization t f =
      ∑ j ∈ range (d + 1), (finSuccEquiv ℤ r f).coeff j * C (t ^ j) := by
  rw [branchHeadSpecialization_eq_eval,
    Polynomial.eval_eq_sum_range' (show (finSuccEquiv ℤ r f).natDegree < d + 1 from by
      rw [natDegree_finSuccEquiv]
      exact lt_of_le_of_lt ((degreeOf_le_totalDegree f 0).trans hd) (by omega))]
  simp only [map_pow]

theorem branchHeadSpecialization_totalDegree_le {r d : ℕ} (t : ℤ)
    (f : MvPolynomial (Fin (r + 1)) ℤ) (hd : f.totalDegree ≤ d) :
    (branchHeadSpecialization t f).totalDegree ≤ d := by
  rw [branchHeadSpecialization_sum t f hd]
  apply totalDegree_finsetSum_le
  intro j hj
  by_cases hz : (finSuccEquiv ℤ r f).coeff j = 0
  · simp [hz]
  · have h := totalDegree_coeff_finSuccEquiv_add_le f j hz
    apply (totalDegree_mul _ _).trans
    change ((finSuccEquiv ℤ r f).coeff j).totalDegree +
      (C (t ^ j) : MvPolynomial (Fin r) ℤ).totalDegree ≤ d
    rw [totalDegree_C, Nat.add_zero]
    omega

/-- Specialization increases coefficient height by at most
`(d+1) B^d`, uniformly in the number of parameters. -/
theorem branchHeadSpecialization_coeff_abs_le {r d H B : ℕ}
    (f : MvPolynomial (Fin (r + 1)) ℤ) (hd : f.totalDegree ≤ d)
    (hH : ∀ s, |f.coeff s| ≤ (H : ℤ)) (hB : 1 ≤ B)
    {t : ℤ} (ht : |t| ≤ (B : ℤ)) (s : Fin r →₀ ℕ) :
    |(branchHeadSpecialization t f).coeff s| ≤ ((d + 1) * H * B ^ d : ℕ) := by
  rw [branchHeadSpecialization_sum t f hd, coeff_sum]
  refine (branch_abs_sum_le_card_mul _ _ (M := (H : ℤ) * (B : ℤ) ^ d) fun j hj => ?_).trans_eq
    (by rw [card_range]; push_cast; ring)
  rw [mul_comm _ (C _), coeff_C_mul, finSuccEquiv_coeff_coeff, abs_mul, abs_pow,
    mul_comm (|t| ^ j)]
  apply mul_le_mul (hH _) ?_ (by positivity) (by positivity)
  exact (pow_le_pow_left₀ (abs_nonneg t) ht j).trans
    (pow_le_pow_right₀ (by exact_mod_cast hB) (by simpa using mem_range.mp hj))

/-- Rational coefficients, without specializing the parameter variables. -/
def branchFamilyRational {r : ℕ} (p : Polynomial (MvPolynomial (Fin r) ℤ)) :
    Polynomial (MvPolynomial (Fin r) ℚ) :=
  p.map (map (Int.castRingHom ℚ))

/-- The polynomial family after specializing its first parameter. -/
def branchFamilyHead {r : ℕ} (t : ℤ)
    (p : Polynomial (MvPolynomial (Fin (r + 1)) ℤ)) :
    Polynomial (MvPolynomial (Fin r) ℤ) := p.map (branchHeadSpecialization t)

/-- Specialize every parameter, leaving the polynomial variable over ℚ. -/
def branchFamilyEval {r : ℕ} (t : Fin r → ℤ)
    (p : Polynomial (MvPolynomial (Fin r) ℤ)) : Polynomial ℚ :=
  p.map (eval₂Hom (Int.castRingHom ℚ) (fun j => (t j : ℚ)))

theorem branchFamilyEval_head {r : ℕ} (t : ℤ) (u : Fin r → ℤ)
    (p : Polynomial (MvPolynomial (Fin (r + 1)) ℤ)) :
    branchFamilyEval u (branchFamilyHead t p) = branchFamilyEval (Fin.cons t u) p := by
  unfold branchFamilyEval branchFamilyHead
  rw [Polynomial.map_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [branchHeadSpecialization]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [RingHom.comp_apply, branchHeadSpecialization, eval₂Hom_X',
        Fin.cases_zero, Fin.cons_zero]
      exact map_intCast (eval₂Hom (Int.castRingHom ℚ) (fun j => (u j : ℚ))) t
    · simp [branchHeadSpecialization]

theorem branchFamilyHead_degree_height {r d H B : ℕ}
    (p : Polynomial (MvPolynomial (Fin (r + 1)) ℤ))
    (hd : p.natDegree ≤ d) (hp : ∀ j, (p.coeff j).totalDegree ≤ d)
    (hH : ∀ j s, |(p.coeff j).coeff s| ≤ (H : ℤ)) (hB : 1 ≤ B)
    {t : ℤ} (ht : |t| ≤ (B : ℤ)) :
    (branchFamilyHead t p).natDegree ≤ d ∧
      (∀ j, ((branchFamilyHead t p).coeff j).totalDegree ≤ d) ∧
      ∀ j s, |((branchFamilyHead t p).coeff j).coeff s| ≤
        ((d + 1) * H * B ^ d : ℕ) := by
  refine ⟨Polynomial.natDegree_map_le.trans hd, ?_, ?_⟩
  · intro j
    simp only [branchFamilyHead, Polynomial.coeff_map]
    exact branchHeadSpecialization_totalDegree_le t (p.coeff j) (hp j)
  · intro j s
    simp only [branchFamilyHead, Polynomial.coeff_map]
    exact branchHeadSpecialization_coeff_abs_le (p.coeff j) (hp j) (hH j) hB ht s

end
end PierceLengthBound.FixedDividend
