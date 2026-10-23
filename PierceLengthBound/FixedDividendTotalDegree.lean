/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendDirectionExtraction
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Multivariate degree of the fixed-dividend resultant

The staircase Bézout matrix proves degree at most ten directly in the coordinate
ring, without inferring a multivariate bound from specializations.
-/

@[expose] public section

namespace PierceLengthBound.FixedDividend

noncomputable section
open MvPolynomial

private lemma mv_add_degree {R σ : Type*} [CommRing R] {p q : MvPolynomial σ R}
    {a b n : ℕ} (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) (h : max a b ≤ n) :
    (p + q).totalDegree ≤ n := (totalDegree_add _ _).trans ((max_le_max hp hq).trans h)
private lemma mv_sub_degree {R σ : Type*} [CommRing R] {p q : MvPolynomial σ R}
    {a b n : ℕ} (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) (h : max a b ≤ n) :
    (p - q).totalDegree ≤ n := (totalDegree_sub _ _).trans ((max_le_max hp hq).trans h)
private lemma mv_mul_degree {R σ : Type*} [CommRing R] {p q : MvPolynomial σ R}
    {a b n : ℕ} (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) (h : a + b ≤ n) :
    (p * q).totalDegree ≤ n := (totalDegree_mul _ _).trans ((add_le_add hp hq).trans h)
private lemma mv_pow_degree {R σ : Type*} [CommRing R] {p : MvPolynomial σ R}
    {a k n : ℕ} (hp : p.totalDegree ≤ a) (h : k * a ≤ n) :
    (p ^ k).totalDegree ≤ n := (totalDegree_pow _ _).trans ((Nat.mul_le_mul_left k hp).trans h)

-- These local elaboration helpers construct ordinary checked degree proofs; their
-- syntactic bounds are never accepted without the corresponding arithmetic proof.
open Lean Elab Tactic Meta in
private meta partial def mvExprDegree (p : Expr) : Nat :=
  let args := p.getAppArgs
  match p.getAppFn.constName? with
  | some ``HAdd.hAdd | some ``HSub.hSub =>
    max (mvExprDegree args[args.size - 2]!) (mvExprDegree args.back!)
  | some ``HMul.hMul =>
    mvExprDegree args[args.size - 2]! + mvExprDegree args.back!
  | some ``Neg.neg => mvExprDegree args.back!
  | some ``HPow.hPow => mvExprDegree args[args.size - 2]! * (args.back!.nat?.getD 0)
  | _ => if p.getAppFn.isFVar then 1 else 0

open Lean Elab Tactic Meta in
private meta partial def proveMvDegree : TacticM Unit := do
  let target ← instantiateMVars (← getMainTarget)
  let p := target.getAppArgs[target.getAppArgs.size - 2]!.getAppArgs.back!
  let args := p.getAppArgs
  let a := Syntax.mkNumLit (toString (mvExprDegree args[args.size - 2]!))
  let b := Syntax.mkNumLit (toString (mvExprDegree args.back!))
  match p.getAppFn.constName? with
  | some ``HAdd.hAdd =>
    evalTactic (← `(tactic| apply mv_add_degree (a := $a) (b := $b)))
    proveMvDegree
    proveMvDegree
    evalTactic (← `(tactic| norm_num))
  | some ``HSub.hSub =>
    evalTactic (← `(tactic| apply mv_sub_degree (a := $a) (b := $b)))
    proveMvDegree
    proveMvDegree
    evalTactic (← `(tactic| norm_num))
  | some ``HMul.hMul =>
    evalTactic (← `(tactic| apply mv_mul_degree (a := $a) (b := $b)))
    proveMvDegree
    proveMvDegree
    evalTactic (← `(tactic| norm_num))
  | some ``Neg.neg =>
    evalTactic (← `(tactic| rw [MvPolynomial.totalDegree_neg]))
    proveMvDegree
  | some ``HPow.hPow =>
    evalTactic (← `(tactic| apply mv_pow_degree (a := $a)))
    proveMvDegree
    evalTactic (← `(tactic| norm_num))
  | _ =>
    if p.getAppFn.isFVar then evalTactic (← `(tactic| assumption))
    else evalTactic (← `(tactic| exact le_of_eq (MvPolynomial.totalDegree_C _)))

elab "fixed_dividend_mv_degree" : tactic => proveMvDegree

-- Certify all sixteen entries of the explicit Newton-basis matrix.
/-- The Newton matrix degree staircase holds in every multivariate coordinate ring. -/
lemma newtonBezout_totalDegree {R σ : Type*} [CommRing R] (c e : Fin 4 → R)
    (s : Fin 4 → MvPolynomial σ R) (hs : ∀ j, (s j).totalDegree ≤ 1) (i j : Fin 4) :
    (newtonBezout (C ∘ c) (C ∘ e) s i j).totalDegree ≤ 4 - max i.val j.val := by
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  have h3 := hs 3
  fin_cases i <;> fin_cases j <;>
    simp only [newtonBezout, Fin.isValue, Function.comp_apply, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, max_self, tsub_zero, zero_le, sup_of_le_right,
      sup_of_le_left, Nat.add_one_sub_one, Nat.reduceSub, Nat.one_le_ofNat, Nat.reduceLeDiff,
      ge_iff_le]
  all_goals fixed_dividend_mv_degree


/-- A degree staircase bounds the determinant degree by the sum of its row bounds. -/
lemma staircase_det_totalDegree {R σ : Type*} [CommRing R]
    (M : Matrix (Fin 4) (Fin 4) (MvPolynomial σ R))
    (h : ∀ i j, (M i j).totalDegree ≤ 4 - max i.val j.val) :
    M.det.totalDegree ≤ 10 := by
  classical
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro π _
  calc (Equiv.Perm.sign π • ∏ i, M (π i) i).totalDegree
      ≤ (∏ i, M (π i) i).totalDegree := totalDegree_smul_le _ _
    _ ≤ ∑ i, (M (π i) i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ i : Fin 4, (4 - i.val) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := h (π i) i
      have hm := le_max_right (π i).val i.val
      omega
    _ = 10 := by decide

/-- The quartic/quartic resultant has multivariate total degree at most ten whenever
all four node coordinates have total degree at most one. -/
theorem newton_resultant_totalDegree_le_ten {R σ : Type*} [CommRing R]
    (c e : Fin 4 → R) (s : Fin 4 → MvPolynomial σ R)
    (hs : ∀ j, (s j).totalDegree ≤ 1) :
    (Polynomial.resultant (firstNewtonQuartic (C ∘ c) s)
      (nextNewtonQuartic (C ∘ e) s) 4 4).totalDegree ≤ 10 := by
  rw [← newtonBezout_det]
  exact staircase_det_totalDegree _ (newtonBezout_totalDegree c e s hs)

/-- The exact fixed-dividend resultant has multivariate total degree at most ten. -/
theorem fixed_dividend_resultant_totalDegree_le_ten {R σ : Type*} [CommRing R] [Nontrivial R]
    (c e : Fin 4 → R) (s : Fin 4 → MvPolynomial σ R)
    (hs : ∀ j, (s j).totalDegree ≤ 1) :
    (Polynomial.resultant (firstNewtonQuartic (C ∘ c) s)
      (Polynomial.X * nextNewtonQuartic (C ∘ e) s) 4 5).totalDegree ≤ 10 := by
  rw [firstNewtonQuartic_eq, nextNewtonQuartic_eq, resultant_monicQuartic_X_mul]
  have hc : firstNewtonCoeffs (C ∘ c) s 0 = C (c 0) := rfl
  rw [hc]
  apply totalDegree_mul _ _ |>.trans
  simp only [totalDegree_C, zero_add]
  have h := newton_resultant_totalDegree_le_ten c e s hs
  rw [firstNewtonQuartic_eq, nextNewtonQuartic_eq] at h
  exact h


/-- The eliminated first equation remains quadratic in arbitrary affine coordinates. -/
lemma lineQuadratic_totalDegree_le_two {R σ : Type*} [CommRing R]
    (ρ u v ρ' u' v' : R) (s : Fin 3 → MvPolynomial σ R)
    (hs : ∀ j, (s j).totalDegree ≤ 1) :
    (lineQuadratic (C ρ) (C u) (C v) (C ρ') (C u') (C v') (s 0) (s 1) (s 2)).totalDegree ≤ 2 := by
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  simp only [lineQuadratic, coeffs, lineNodes, Fin.isValue, fourthNode, lineGaps, Matrix.cons_val,
    Fin.sum_univ_succ, Matrix.cons_val_zero, Fin.castSucc_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_add, Matrix.cons_val_succ, Fin.castSucc_succ, Nat.reduceAdd,
    Finset.univ_unique, Fin.default_eq_zero, Matrix.cons_val_fin_one, one_mul,
    Finset.sum_singleton, ge_iff_le]
  fixed_dividend_mv_degree

-- Elimination introduces a quadratic last gap; the complete norm is still cubic.
/-- The eliminated norm has total degree at most three. -/
lemma lineNorm_totalDegree_le_three {R σ : Type*} [CommRing R]
    (ρ u v ρ' u' v' : R) (s : Fin 3 → MvPolynomial σ R)
    (hs : ∀ j, (s j).totalDegree ≤ 1) :
    (lineNorm (C ρ) (C u) (C v) (C ρ') (C u') (C v') (s 0) (s 1) (s 2)).totalDegree ≤ 3 := by
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  simp only [lineNorm, coeffs, lineNodes, Fin.isValue, fourthNode, lineGaps, Matrix.cons_val,
    extendedLineGaps, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Fin.sum_univ_succ, Fin.castSucc_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, add_zero, zero_mul, zero_add, Fin.castSucc_succ, Nat.reduceAdd, Finset.univ_unique,
    Fin.default_eq_zero, Matrix.cons_val_fin_one, one_mul, Finset.sum_singleton, ge_iff_le]
  fixed_dividend_mv_degree

end
end PierceLengthBound.FixedDividend
