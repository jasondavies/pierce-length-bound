/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveZeroFibers
public import PierceLengthBound.BranchSieveShearAnalysis
import Mathlib.Tactic

/-! An unconditional arithmetic one-parameter integral-root bound.
The coefficient-height dependence is logarithmic, and the parameter-box
exponent is the reciprocal root-variable degree. This is the counting input
for a subsequent factor-resolvent reduction to Hilbert irreducibility. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- The integral-root form of one-parameter effective Hilbert irreducibility,
with an explicit fourth power of a logarithmic height factor. In particular,
root-variable degree at least two gives a square-root parameter saving.
Every integer parameter is included, including identically zero fibers. -/
theorem branch_one_parameter_integral_root_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : MvPolynomial (Fin 2) ℤ),
      Irreducible (branchRationalPolynomial p) → 0 < p.degreeOf 1 →
      ∀ H B : ℕ, (∀ s, |p.coeff s| ≤ (H : ℤ)) → 1 ≤ B →
      ∀ S : Finset ℤ,
      (∀ t ∈ S, |t| ≤ (B : ℤ) ∧ ∃ y : ℤ, eval ![t, y] p = 0) →
      (S.card : ℝ) ≤ C *
        ((p.degreeOf 0 : ℝ) + Real.log (p.support.card * H + 2 : ℕ) + 2) ^ 4 *
        (p.totalDegree : ℝ) ^ 3 * (B : ℝ) ^ (1 / (p.degreeOf 1 : ℝ)) *
        (1 + Real.log B + p.totalDegree) + p.degreeOf 0 := by
  obtain ⟨C, hC, hcount⟩ := branch_integral_root_count_all_fibers
  refine ⟨C * Real.exp 1, mul_pos hC (Real.exp_pos 1), ?_⟩
  intro p hp hn H B hH hB S hS
  let K : ℝ := (p.support.card * H + 2 : ℕ)
  let e : ℕ := p.degreeOf 0 + ⌈Real.log K⌉₊ + 1
  let D : ℕ := (branchPowerShearHom e 1 (branchRationalPolynomial p)).totalDegree
  have hK : 1 ≤ K := by
    dsimp only [K]
    exact_mod_cast (show 1 ≤ p.support.card * H + 2 by omega)
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have he : p.degreeOf 0 < e := by dsimp [e]; omega
  have hepos : 0 < e := by omega
  have helog : Real.log K ≤ e := by
    have hc := Nat.le_ceil (Real.log K)
    dsimp only [e]
    push_cast
    linarith [show (0 : ℝ) ≤ p.degreeOf 0 by positivity]
  have heupper : (e : ℝ) ≤ (p.degreeOf 0 : ℝ) + Real.log K + 2 := by
    have hc := (Nat.ceil_lt_add_one hlogK).le
    dsimp only [e]
    push_cast
    linarith
  have hDlo : e * p.degreeOf 1 ≤ D := by
    simpa only [D, branchRationalPolynomial_degreeOf] using
      branchPowerShear_totalDegree_lower hp.ne_zero
        (show (branchRationalPolynomial p).degreeOf 0 < e by simpa using he)
  have hDhi : D ≤ e * p.totalDegree := by
    simpa only [D, branchRationalPolynomial_totalDegree] using
      branchPowerShear_totalDegree_upper (branchRationalPolynomial p)
        (by omega : 1 ≤ e) (1 : ℚ)
  have hBreal : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hanalytic := branch_sheared_curveBound_le hK hBreal hepos hn hDlo hDhi helog
  have hraw := hcount p hp H B e hH hB he S hS
  have hR : (((p.support.card * H + 2) * B ^ e : ℕ) : ℝ) = K * (B : ℝ) ^ e := by
    simp only [K, Nat.cast_mul, Nat.cast_pow]
  rw [hR] at hraw
  have hlogB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg hBreal
  calc
    (S.card : ℝ) ≤ C * CCDN.curveBound D (K * (B : ℝ) ^ e) + p.degreeOf 0 := hraw
    _ ≤ C * (Real.exp 1 * (e : ℝ) ^ 4 * (p.totalDegree : ℝ) ^ 3 *
        (B : ℝ) ^ (1 / (p.degreeOf 1 : ℝ)) *
        (1 + Real.log (B : ℝ) + p.totalDegree)) + p.degreeOf 0 := by
      gcongr
    _ ≤ C * (Real.exp 1 *
        ((p.degreeOf 0 : ℝ) + Real.log K + 2) ^ 4 * (p.totalDegree : ℝ) ^ 3 *
        (B : ℝ) ^ (1 / (p.degreeOf 1 : ℝ)) *
        (1 + Real.log (B : ℝ) + p.totalDegree)) + p.degreeOf 0 := by
      gcongr
    _ = _ := by dsimp only [K]; ring

/-- The square-root form needed for proper-factor coefficient equations. -/
theorem branch_one_parameter_square_root_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : MvPolynomial (Fin 2) ℤ),
      Irreducible (branchRationalPolynomial p) → 2 ≤ p.degreeOf 1 →
      ∀ H B : ℕ, (∀ s, |p.coeff s| ≤ (H : ℤ)) → 1 ≤ B →
      ∀ S : Finset ℤ,
      (∀ t ∈ S, |t| ≤ (B : ℤ) ∧ ∃ y : ℤ, eval ![t, y] p = 0) →
      (S.card : ℝ) ≤ C *
        ((p.degreeOf 0 : ℝ) + Real.log (p.support.card * H + 2 : ℕ) + 2) ^ 4 *
        (p.totalDegree : ℝ) ^ 3 * (B : ℝ) ^ (1 / 2 : ℝ) *
        (1 + Real.log B + p.totalDegree) + p.degreeOf 0 := by
  obtain ⟨C, hC, hroot⟩ := branch_one_parameter_integral_root_bound
  refine ⟨C, hC, ?_⟩
  intro p hp hn H B hH hB S hS
  apply (hroot p hp (by omega) H B hH hB S hS).trans
  have hBreal : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hlogB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg hBreal
  have hnreal : (2 : ℝ) ≤ p.degreeOf 1 := by exact_mod_cast hn
  have hpower : (B : ℝ) ^ (1 / (p.degreeOf 1 : ℝ)) ≤ (B : ℝ) ^ (1 / 2 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hBreal
    exact one_div_le_one_div_of_le (by norm_num) hnreal
  gcongr

end
end PierceLengthBound.FixedDividend
