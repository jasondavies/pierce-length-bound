/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveFiberHeight
public import CCDN.Plane.PlaneCount
public import CCDN.Height.PolynomialBoxHeight
import Mathlib.Tactic
public import PierceLengthBound.BranchSieveShear

/-! A coefficient-uniform integral-root count from the CCDN plane-curve bound
(Step 1 in the proof of Theorem 10.5). After the power shear, the parameters
whose fiber has an integral root inject into the integral points of an
irreducible plane curve; the shear trades coefficient height for degree. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial Finset

/-- An integer polynomial in two variables, viewed over `ℚ`. -/
abbrev branchRationalPolynomial (p : MvPolynomial (Fin 2) ℤ) :
    MvPolynomial (Fin 2) ℚ := map (Int.castRingHom ℚ) p

@[simp] lemma branchRationalPolynomial_degreeOf (p : MvPolynomial (Fin 2) ℤ)
    (i : Fin 2) : (branchRationalPolynomial p).degreeOf i = p.degreeOf i := by
  simp only [branchRationalPolynomial, degreeOf,
    degrees_map_of_injective p (f := Int.castRingHom ℚ) Int.cast_injective]

@[simp] lemma branchRationalPolynomial_totalDegree (p : MvPolynomial (Fin 2) ℤ) :
    (branchRationalPolynomial p).totalDegree = p.totalDegree := by
  simp only [branchRationalPolynomial, totalDegree,
    support_map_of_injective p (f := Int.castRingHom ℚ) Int.cast_injective]

lemma branchRationalPolynomial_eval (p : MvPolynomial (Fin 2) ℤ) (t y : ℤ) :
    eval ![(t : ℚ), (y : ℚ)] (branchRationalPolynomial p) = (eval ![t, y] p : ℚ) := by
  have hh : (Int.castRingHom ℚ) ∘ ![t, y] = ![(t : ℚ), (y : ℚ)] := by
    ext i
    fin_cases i <;> rfl
  have hv := MvPolynomial.map_eval (Int.castRingHom ℚ) ![t, y] p
  rw [hh] at hv
  simpa only [branchRationalPolynomial, Int.coe_castRingHom] using hv.symm

/-- Each parameter with an integral root injects into the integral points of
the sheared curve, in a box determined solely by the original height. -/
theorem branch_integral_root_card_le_sheared_count
    (p : MvPolynomial (Fin 2) ℤ) {H B e : ℕ}
    (hH : ∀ s, |p.coeff s| ≤ (H : ℤ)) (hB : 1 ≤ B)
    (he : p.degreeOf 0 < e) (S : Finset ℤ)
    (hS : ∀ t ∈ S, |t| ≤ (B : ℤ) ∧ branchFiberPolynomial t p ≠ 0 ∧
      ∃ y : ℤ, eval ![t, y] p = 0) :
    S.card ≤ CCDN.count
      (CCDN.zeroLocus (branchPowerShearHom e 1 (branchRationalPolynomial p)))
      (((p.support.card * H + 2) * B ^ e : ℕ) : ℝ) := by
  classical
  choose y hy using fun t : S => (hS t.val t.property).2.2
  let y' : ℤ → ℤ := fun t => if ht : t ∈ S then y ⟨t, ht⟩ else 0
  have hy' : ∀ t ∈ S, eval ![t, y' t] p = 0 := by
    intro t ht
    simpa only [y', dite_eq_left ht] using hy ⟨t, ht⟩
  let z : ℤ → Fin 2 → ℤ := fun t => ![t, y' t - t ^ e]
  apply Finset.card_le_card_of_injOn z
  · intro t ht
    apply CCDN.mem_integralPoints.mpr
    constructor
    · intro i
      fin_cases i
      · have hBe : B ≤ (p.support.card * H + 2) * B ^ e := by
          have hpow : B ≤ B ^ e := by
            simpa only [pow_one] using Nat.pow_le_pow_right hB (by omega : 1 ≤ e)
          exact hpow.trans (Nat.le_mul_of_pos_left _ (by omega))
        have hh : |t| ≤ (((p.support.card * H + 2) * B ^ e : ℕ) : ℤ) :=
          (hS t ht).1.trans (by exact_mod_cast hBe)
        change |(t : ℝ)| ≤ _
        exact_mod_cast hh
      · have hh := branchFiberPolynomial_sheared_root_abs_le p hH hB he.le
          (hS t ht).1 (hS t ht).2.1 (hy' t ht)
        change |((y' t - t ^ e : ℤ) : ℝ)| ≤ _
        exact_mod_cast hh
    · change eval (CCDN.rationalPoint (z t))
        (branchPowerShearHom e 1 (branchRationalPolynomial p)) = 0
      have hz : CCDN.rationalPoint (z t) = ![(t : ℚ), (y' t : ℚ) - (t : ℚ) ^ e] := by
        ext i
        fin_cases i <;> simp [CCDN.rationalPoint, z]
      rw [hz, branchPowerShear_eval, one_mul, sub_add_cancel,
        branchRationalPolynomial_eval, hy' t ht, Int.cast_zero]
  · intro t _ u _ h
    exact congrFun h 0

/-- The parameters `t ∈ [-B,B]` with nonzero fiber and an integral root number
at most `C` times the plane-curve bound for the sheared curve, with its degree
and box radius displayed. The shear exponent `e` is free;
`BranchSieveOneParameterRoots` chooses it in terms of the coefficient height. -/
theorem branch_integral_root_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : MvPolynomial (Fin 2) ℤ),
      Irreducible (branchRationalPolynomial p) → ∀ H B e : ℕ,
      (∀ s, |p.coeff s| ≤ (H : ℤ)) → 1 ≤ B → p.degreeOf 0 < e →
      ∀ S : Finset ℤ,
      (∀ t ∈ S, |t| ≤ (B : ℤ) ∧ branchFiberPolynomial t p ≠ 0 ∧
        ∃ y : ℤ, eval ![t, y] p = 0) →
      (S.card : ℝ) ≤ C * CCDN.curveBound
        (branchPowerShearHom e 1 (branchRationalPolynomial p)).totalDegree
        (((p.support.card * H + 2) * B ^ e : ℕ) : ℝ) := by
  obtain ⟨C, hC, hcurve⟩ := CCDN.planeCurveBound
  refine ⟨C, hC, ?_⟩
  intro p hp H B e hH hB he S hS
  have hir := branchPowerShear_irreducible e (1 : ℚ) hp
  have hd := CCDN.totalDegree_pos_of_nonzero_nonunit _ hir.ne_zero hir.not_isUnit
  have hR : 1 ≤ (p.support.card * H + 2) * B ^ e := by
    exact (Nat.one_le_pow _ _ hB).trans (Nat.le_mul_of_pos_left _ (by omega))
  have hcard := branch_integral_root_card_le_sheared_count p hH hB he S hS
  apply (show (S.card : ℝ) ≤ (CCDN.count _ _ : ℝ) from by exact_mod_cast hcard).trans
  exact hcurve _ hir hd _ (by exact_mod_cast hR)

end
end PierceLengthBound.FixedDividend
