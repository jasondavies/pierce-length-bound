/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveIntegralClosure
public import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Tactic

/-! An actual integer specialization supplies an integral coefficient root.
The reduction map is constructed by lying-over; it is not an assumption of
the theorem. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial
open scoped Polynomial.Bivariate

variable {F L : Type*} [Field F] [Algebra ℤ[X] F] [IsFractionRing ℤ[X] F]
  [Field L] [Algebra ℤ[X] L] [Algebra F L] [IsScalarTower ℤ[X] F L]
  [FaithfulSMul ℤ[X] L]

theorem branch_integer_specialization_witness (p : ℤ[X][Y])
    (hp : p.Monic) (hir : Irreducible (p.map (algebraMap ℤ[X] F)))
    (hsplit : (p.map (algebraMap ℤ[X] L)).Splits)
    (t : ℤ) (q : ℤ[X]) (hq : q.Monic) (hdiv : q ∣ p.map (evalRingHom t))
    (hqpos : 0 < q.natDegree) (hqlt : q.natDegree < p.natDegree) :
    ∃ q₀ : Polynomial (integralClosure ℤ[X] L),
      q₀.Monic ∧ q₀ ∣ p.map (algebraMap ℤ[X] (integralClosure ℤ[X] L)) ∧
      ∃ j : ℕ, (minpoly ℤ[X] (q₀.coeff j)).Monic ∧
        Irreducible ((minpoly ℤ[X] (q₀.coeff j)).map (algebraMap ℤ[X] F)) ∧
        2 ≤ (minpoly ℤ[X] (q₀.coeff j)).natDegree ∧
        (minpoly ℤ[X] (q₀.coeff j)).evalEval t (q.coeff j) = 0 := by
  let S := integralClosure ℤ[X] L
  let : FaithfulSMul ℤ[X] S := (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
    intro a b hab
    apply FaithfulSMul.algebraMap_injective ℤ[X] L
    exact congrArg Subtype.val hab)
  obtain ⟨Q, hQ, hchar, hφ⟩ := branch_exists_integer_reduction S t
  let : Q.IsPrime := hQ
  let : CharZero (S ⧸ Q) := hchar
  let φ := Ideal.Quotient.mk Q
  let qK := q.map (Int.castRingHom (S ⧸ Q))
  have hpsplit := branch_monic_splits_integralClosure p hp hsplit
  have hqK : qK.Monic := hq.map _
  have hqKdiv : qK ∣ (p.map (algebraMap ℤ[X] S)).map φ := by
    have hh := Polynomial.map_dvd (Int.castRingHom (S ⧸ Q)) hdiv
    simpa only [qK, φ, Polynomial.map_map, hφ] using hh
  obtain ⟨q₀, hq₀, hq₀div, hq₀map, j, hfmonic, hfir, hfdeg, hfroot⟩ :=
    branch_integral_factor_witness (L := L) φ hp hir hpsplit hqK hqKdiv
      (by simpa only [qK, hq.natDegree_map] using hqpos)
      (by simpa only [qK, hq.natDegree_map] using hqlt)
  refine ⟨q₀, hq₀, hq₀div, j, hfmonic, hfir, hfdeg, ?_⟩
  have hroot : ((minpoly ℤ[X] (q₀.coeff j)).map (evalRingHom t)).eval (q.coeff j) = 0 := by
    have hzero := hfroot
    simp only [qK, Polynomial.coeff_map, φ, hφ] at hzero
    rw [← Polynomial.eval₂_map, Polynomial.eval₂_at_apply] at hzero
    exact (Int.castRingHom (S ⧸ Q)).injective_int (by simpa only [map_zero] using hzero)
  simpa only [Polynomial.eval_map, Polynomial.eval₂_evalRingHom] using hroot

end
end PierceLengthBound.FixedDividend
