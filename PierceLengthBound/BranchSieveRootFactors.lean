/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic
public import PierceLengthBound.BranchSieveMultivariateKronecker

/-! A proper bounded multivariate factorization can be normalized so that its
Kronecker image is monic. This gives the specialized factor witness in the
effective Hilbert argument. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- A reducible polynomial with partial degrees below `a` and monic Kronecker
image different from `1` factors into two nonunits with partial degrees below
`a`, the first having monic Kronecker image. -/
theorem branch_kronecker_proper_factor_witness {a n : ℕ}
    (f : MvPolynomial (Fin n) ℚ) (hdeg : ∀ i, f.degreeOf i < a)
    (hred : ¬Irreducible f) (hmonic : (branchMultiKronecker a n f).Monic)
    (hone : branchMultiKronecker a n f ≠ 1) :
    ∃ g h : MvPolynomial (Fin n) ℚ, f = g * h ∧ ¬IsUnit g ∧ ¬IsUnit h ∧
      (∀ i, g.degreeOf i < a) ∧ (∀ i, h.degreeOf i < a) ∧
      (branchMultiKronecker a n g).Monic := by
  classical
  have hf0 : f ≠ 0 := by
    intro he
    exact hmonic.ne_zero (by simp [he])
  have hfu : ¬IsUnit f := by
    intro hu
    exact hone (hmonic.eq_one_of_isUnit (hu.map (branchMultiKronecker a n)))
  have hn : ¬∀ g h, f = g * h → IsUnit g ∨ IsUnit h := by
    intro hh
    exact hred ⟨hfu, hh⟩
  push Not at hn
  obtain ⟨g, h, he, hgu, hhu⟩ := hn
  have hg0 : g ≠ 0 := by intro hz; apply hf0; simp [he, hz]
  have hh0 : h ≠ 0 := by intro hz; apply hf0; simp [he, hz]
  have hgd : ∀ i, g.degreeOf i < a := by
    intro i
    have hd := hdeg i
    rw [he, degreeOf_mul_eq hg0 hh0] at hd
    omega
  have hhd : ∀ i, h.degreeOf i < a := by
    intro i
    have hd := hdeg i
    rw [he, degreeOf_mul_eq hg0 hh0] at hd
    omega
  let G := branchMultiKronecker a n g
  let c := G.leadingCoeff
  have hG0 : G ≠ 0 := branchMultiKronecker_ne_zero hg0 hgd
  have hc : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hG0
  refine ⟨C c⁻¹ * g, C c * h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show C c⁻¹ * g * (C c * h) = C (c⁻¹ * c) * (g * h) by rw [map_mul]; ring,
      inv_mul_cancel₀ hc, map_one, one_mul]
    exact he
  · intro hu
    exact hgu (isUnit_of_mul_isUnit_right hu)
  · intro hu
    exact hhu (isUnit_of_mul_isUnit_right hu)
  · intro i
    exact (degreeOf_C_mul_le g i c⁻¹).trans_lt (hgd i)
  · intro i
    exact (degreeOf_C_mul_le h i c).trans_lt (hhd i)
  · have hh := Polynomial.monic_mul_leadingCoeff_inv hG0
    simpa only [map_mul, branchMultiKronecker, eval₂Hom_C, G, c, mul_comm] using hh

end
end PierceLengthBound.FixedDividend
