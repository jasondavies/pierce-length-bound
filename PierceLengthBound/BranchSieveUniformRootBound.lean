/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveOneParameterRoots
import Mathlib.Tactic

/-! The fixed-degree, coefficient-uniform square-root estimate. All dependence
on the polynomial coefficients is confined to a fourth power of a logarithm. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- A polynomial in `σ` variables of total degree `d` has at most `(d+1)^|σ|` monomials. -/
private lemma polynomial_support_card_le {R σ : Type*} [CommSemiring R] [Fintype σ]
    (f : MvPolynomial σ R) :
    f.support.card ≤ (f.totalDegree + 1) ^ Fintype.card σ := by
  classical
  have hb (e : σ →₀ ℕ) (he : e ∈ f.support) (i : σ) : e i ≤ f.totalDegree := by
    have hh := (degreeOf_le_iff.mp (le_refl (f.degreeOf i))) e he
    exact hh.trans (degreeOf_le_totalDegree f i)
  let ψ : {e // e ∈ f.support} → σ → Fin (f.totalDegree + 1) :=
    fun e i => ⟨e.val i, Nat.lt_succ_of_le (hb e.val e.property i)⟩
  have hi : Function.Injective ψ := by
    intro e e' h
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    exact congrArg (fun v => (v i).val) h
  simpa using Fintype.card_le_of_injective ψ hi

/-- For an integer polynomial `p(t,y)` of total degree at most `d`, irreducible
over `ℚ` and of degree at least two in `y`, the number of `|t| ≤ B` with an
integer root `y` is `O_d((1 + log (H + 1))^4 B^(1/2) (1 + log B))`, where `H`
bounds the coefficients. -/
theorem branch_uniform_integral_root_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : MvPolynomial (Fin 2) ℤ),
      Irreducible (branchRationalPolynomial p) → p.totalDegree ≤ d → 2 ≤ p.degreeOf 1 →
      ∀ H B : ℕ, (∀ s, |p.coeff s| ≤ (H : ℤ)) → 1 ≤ B →
      ∀ S : Finset ℤ,
      (∀ t ∈ S, |t| ≤ (B : ℤ) ∧ ∃ y : ℤ, eval ![t, y] p = 0) →
      (S.card : ℝ) ≤ C * (1 + Real.log (H + 1 : ℕ)) ^ 4 *
        (B : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log B) := by
  obtain ⟨C, hC, hroot⟩ := branch_one_parameter_square_root_bound
  let Kd : ℝ := ((d + 1) ^ 2 + 2 : ℕ)
  have hKd : 1 ≤ Kd := by
    dsimp only [Kd]
    exact_mod_cast (show 1 ≤ (d + 1) ^ 2 + 2 by omega)
  have hlogKd : 0 ≤ Real.log Kd := Real.log_nonneg hKd
  let L : ℝ := d + Real.log Kd + 2
  have hL : 1 ≤ L := by
    dsimp only [L]
    linarith [show (0 : ℝ) ≤ d by positivity]
  refine ⟨C * L ^ 4 * (d : ℝ) ^ 3 * (d + 1) + (d + 1), by positivity, ?_⟩
  intro p hp hd hn H B hH hB S hS
  have hdR : (p.totalDegree : ℝ) ≤ d := by exact_mod_cast hd
  have hdt : p.degreeOf 0 ≤ d := (degreeOf_le_totalDegree p 0).trans hd
  have hdtR : (p.degreeOf 0 : ℝ) ≤ d := by exact_mod_cast hdt
  have hBreal : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hlogB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg hBreal
  have hHreal : (1 : ℝ) ≤ (H + 1 : ℕ) := by exact_mod_cast (show 1 ≤ H + 1 by omega)
  have hlogH : 0 ≤ Real.log (H + 1 : ℕ) := Real.log_nonneg hHreal
  have hcard : p.support.card ≤ (d + 1) ^ 2 := by
    apply (polynomial_support_card_le p).trans
    simpa using Nat.pow_le_pow_left (Nat.add_le_add_right hd 1) 2
  have hKpos : (0 : ℝ) < (p.support.card * H + 2 : ℕ) := by positivity
  have hKbound : ((p.support.card * H + 2 : ℕ) : ℝ) ≤ Kd * (H + 1 : ℕ) := by
    dsimp only [Kd]
    exact_mod_cast (show p.support.card * H + 2 ≤ ((d + 1) ^ 2 + 2) * (H + 1) by
      nlinarith [Nat.mul_le_mul_right H hcard])
  have hlogK : Real.log (p.support.card * H + 2 : ℕ) ≤
      Real.log Kd + Real.log (H + 1 : ℕ) := by
    calc
      _ ≤ Real.log (Kd * (H + 1 : ℕ)) := Real.log_le_log hKpos hKbound
      _ = _ := Real.log_mul (by linarith : Kd ≠ 0) (by positivity)
  have hheight : (p.degreeOf 0 : ℝ) + Real.log (p.support.card * H + 2 : ℕ) + 2 ≤
      L * (1 + Real.log (H + 1 : ℕ)) := by
    dsimp only [L]
    nlinarith
  have hlast : 1 + Real.log (B : ℝ) + p.totalDegree ≤
      ((d : ℝ) + 1) * (1 + Real.log B) := by nlinarith
  have hpower : 1 ≤ (B : ℝ) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow hBreal (by positivity)
  have hheightPow : 1 ≤ (1 + Real.log (H + 1 : ℕ)) ^ 4 :=
    one_le_pow₀ (by linarith)
  have hproduct : 1 ≤ (1 + Real.log (H + 1 : ℕ)) ^ 4 *
      (B : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log B) := by
    calc
      (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr; linarith
  have hsmall : (p.degreeOf 0 : ℝ) ≤ ((d : ℝ) + 1) *
      ((1 + Real.log (H + 1 : ℕ)) ^ 4 *
        (B : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log B)) := by nlinarith
  apply (hroot p hp hn H B hH hB S hS).trans
  calc
    C * ((p.degreeOf 0 : ℝ) + Real.log (p.support.card * H + 2 : ℕ) + 2) ^ 4 *
        (p.totalDegree : ℝ) ^ 3 * (B : ℝ) ^ (1 / 2 : ℝ) *
        (1 + Real.log B + p.totalDegree) + p.degreeOf 0
      ≤ C * (L * (1 + Real.log (H + 1 : ℕ))) ^ 4 *
        (d : ℝ) ^ 3 * (B : ℝ) ^ (1 / 2 : ℝ) *
        ((d + 1) * (1 + Real.log B)) + (d + 1) *
        ((1 + Real.log (H + 1 : ℕ)) ^ 4 *
          (B : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log B)) := by
      gcongr
    _ = _ := by ring

end
end PierceLengthBound.FixedDividend
