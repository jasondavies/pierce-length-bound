/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveIntegralRootCount
import Mathlib.Tactic

/-! A nonzero plane polynomial has at most its parameter degree many
identically zero integer fibers. Hence the integral root count extends to all
parameters, with an additive term equal to the parameter degree. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Finset

/-- Restriction of a plane polynomial to the horizontal line at height `y`. -/
def branchHorizontalPolynomial (y : ℤ) : MvPolynomial (Fin 2) ℤ →+* Polynomial ℤ :=
  eval₂Hom Polynomial.C ![Polynomial.X, Polynomial.C y]

lemma branchHorizontalPolynomial_eval (p : MvPolynomial (Fin 2) ℤ) (t y : ℤ) :
    (branchHorizontalPolynomial y p).eval t = eval ![t, y] p := by
  have hh : (Polynomial.evalRingHom t).comp (branchHorizontalPolynomial y) = eval ![t, y] := by
    ext i
    · simp [branchHorizontalPolynomial]
    · fin_cases i <;> simp [branchHorizontalPolynomial]
  exact DFunLike.congr_fun hh p

lemma branchHorizontalPolynomial_natDegree_le (p : MvPolynomial (Fin 2) ℤ) (y : ℤ) :
    (branchHorizontalPolynomial y p).natDegree ≤ p.degreeOf 0 := by
  classical
  change (eval₂ Polynomial.C ![Polynomial.X, Polynomial.C y] p).natDegree ≤ _
  rw [eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, ← Polynomial.C_pow]
  rw [mul_comm (Polynomial.X ^ s 0) (Polynomial.C (y ^ s 1)),
    ← mul_assoc, ← Polynomial.C_mul]
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (le_degreeOf_of_mem_support 0 hs)

/-- A nonzero plane polynomial has at most its parameter degree many
identically zero integer fibers. -/
theorem branch_zero_fiber_card_le (p : MvPolynomial (Fin 2) ℤ) (hp : p ≠ 0)
    (S : Finset ℤ) (hS : ∀ t ∈ S, branchFiberPolynomial t p = 0) :
    S.card ≤ p.degreeOf 0 := by
  classical
  obtain ⟨v, _hv, hpv⟩ := CCDN.exists_integer_grid_eval_ne_zero p hp p.totalDegree le_rfl
  let q := branchHorizontalPolynomial (v 1) p
  have hq : q ≠ 0 := by
    intro hz
    have hzero := congrArg (fun f : Polynomial ℤ => f.eval (v 0)) hz
    rw [Polynomial.eval_zero] at hzero
    have hvec : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
    have : eval v p = 0 := by
      simpa only [q, branchHorizontalPolynomial_eval, hvec] using hzero
    exact hpv this
  apply (Polynomial.card_le_degree_of_subset_roots (p := q) ?_).trans
    (branchHorizontalPolynomial_natDegree_le p (v 1))
  intro t ht
  apply (Polynomial.mem_roots hq).mpr
  change q.eval t = 0
  rw [show q.eval t = eval ![t, v 1] p from branchHorizontalPolynomial_eval _ _ _]
  rw [← branchFiberPolynomial_eval, hS t ht, Polynomial.eval_zero]

/-- The integral root count over all parameters: those with identically zero
fiber contribute at most the additive term `p.degreeOf 0`. -/
theorem branch_integral_root_count_all_fibers :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : MvPolynomial (Fin 2) ℤ),
      Irreducible (branchRationalPolynomial p) → ∀ H B e : ℕ,
      (∀ s, |p.coeff s| ≤ (H : ℤ)) → 1 ≤ B → p.degreeOf 0 < e →
      ∀ S : Finset ℤ,
      (∀ t ∈ S, |t| ≤ (B : ℤ) ∧ ∃ y : ℤ, eval ![t, y] p = 0) →
      (S.card : ℝ) ≤ C * CCDN.curveBound
        (branchPowerShearHom e 1 (branchRationalPolynomial p)).totalDegree
        (((p.support.card * H + 2) * B ^ e : ℕ) : ℝ) + p.degreeOf 0 := by
  classical
  obtain ⟨C, hC, hcount⟩ := branch_integral_root_count
  refine ⟨C, hC, ?_⟩
  intro p hp H B e hH hB he S hS
  let G := S.filter (fun t => branchFiberPolynomial t p ≠ 0)
  let E := S.filter (fun t => branchFiberPolynomial t p = 0)
  have hgood := hcount p hp H B e hH hB he G (by
    intro t ht
    obtain ⟨htS, htnz⟩ := mem_filter.mp ht
    exact ⟨(hS t htS).1, htnz, (hS t htS).2⟩)
  have hpne : p ≠ 0 := by
    intro hz
    apply hp.ne_zero
    simp only [branchRationalPolynomial, hz, map_zero]
  have hbad := branch_zero_fiber_card_le p hpne E (by
    intro t ht
    exact (mem_filter.mp ht).2)
  have hsplit : E.card + G.card = S.card := by
    exact Finset.card_filter_add_card_filter_not (fun t => branchFiberPolynomial t p = 0)
  have hsplitR : (S.card : ℝ) = E.card + G.card := by exact_mod_cast hsplit.symm
  rw [hsplitR]
  have hbadR : (E.card : ℝ) ≤ p.degreeOf 0 := by exact_mod_cast hbad
  linarith

end
end PierceLengthBound.FixedDividend
