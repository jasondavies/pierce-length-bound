/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib.Tactic
public import ArithmeticHeights.Absolute
public import CCDN.Plane.Plane
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Data.Nat.Choose.Multinomial

/-! The analytic degree-height tradeoff for the arithmetic root count.
A shear exponent at least the logarithm of coefficient height turns the
coefficient contribution to the CCDN radius factor into an absolute constant. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- The large coefficient factor costs only `exp 1` after degree amplification. -/
theorem branch_sheared_radius_rpow_le {K B : ℝ} {e n D : ℕ}
    (hK : 1 ≤ K) (hB : 1 ≤ B) (he : 0 < e) (hn : 0 < n)
    (hD : e * n ≤ D) (hlog : Real.log K ≤ e) :
    (K * B ^ e) ^ (1 / (D : ℝ)) ≤ Real.exp 1 * B ^ (1 / (n : ℝ)) := by
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hDR : (e : ℝ) * n ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le (mul_pos heR hnR) hDR
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hKe : Real.log K ≤ D := hlog.trans (by nlinarith)
  have hcoeff : K ^ (1 / (D : ℝ)) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos (lt_of_lt_of_le zero_lt_one hK)]
    apply Real.exp_le_exp.mpr
    rw [mul_one_div, div_le_one hDpos]
    exact hKe
  have hparameter : (B ^ e) ^ (1 / (D : ℝ)) ≤ B ^ (1 / (n : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ B)]
    apply Real.rpow_le_rpow_of_exponent_le hB
    rw [mul_one_div, div_le_div_iff₀ hDpos hnR]
    simpa only [one_mul] using hDR
  rw [Real.mul_rpow (by linarith : 0 ≤ K) (by positivity : 0 ≤ B ^ e)]
  exact mul_le_mul hcoeff hparameter (by positivity) (Real.exp_pos 1).le

/-- The complete degree-height tradeoff. The exponent of the parameter box
is the reciprocal root-variable degree, independently of coefficient height. -/
theorem branch_sheared_curveBound_le {K B : ℝ} {e n D d : ℕ}
    (hK : 1 ≤ K) (hB : 1 ≤ B) (he : 0 < e) (hn : 0 < n)
    (hDlo : e * n ≤ D) (hDhi : D ≤ e * d) (hlog : Real.log K ≤ e) :
    CCDN.curveBound D (K * B ^ e) ≤
      Real.exp 1 * (e : ℝ) ^ 4 * (d : ℝ) ^ 3 *
        B ^ (1 / (n : ℝ)) * (1 + Real.log B + d) := by
  have heR : (0 : ℝ) ≤ e := by positivity
  have hDhiR : (D : ℝ) ≤ (e : ℝ) * d := by exact_mod_cast hDhi
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hR : 1 ≤ K * B ^ e := by nlinarith [one_le_pow₀ (n := e) hB]
  have hlogRnonneg : 0 ≤ Real.log (K * B ^ e) := Real.log_nonneg hR
  have hlogR : Real.log (K * B ^ e) + D ≤ (e : ℝ) * (1 + Real.log B + d) := by
    rw [Real.log_mul (by linarith : K ≠ 0) (by positivity : B ^ e ≠ 0), Real.log_pow]
    nlinarith
  unfold CCDN.curveBound
  calc
    (D : ℝ) ^ 3 * (K * B ^ e) ^ (1 / (D : ℝ)) * (Real.log (K * B ^ e) + D)
      ≤ ((e : ℝ) * d) ^ 3 * (Real.exp 1 * B ^ (1 / (n : ℝ))) *
          ((e : ℝ) * (1 + Real.log B + d)) := by
        apply mul_le_mul ?_ hlogR (by positivity) (by positivity)
        exact mul_le_mul (pow_le_pow_left₀ (by positivity) hDhiR 3)
          (branch_sheared_radius_rpow_le hK hB he hn hDlo hlog)
          (by positivity) (by positivity)
    _ = _ := by ring

end
end PierceLengthBound.FixedDividend
