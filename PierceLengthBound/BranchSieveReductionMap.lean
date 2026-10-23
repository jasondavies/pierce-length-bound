/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.CharP.Algebra
import Mathlib.Tactic

/-! Lying-over produces a characteristic-zero reduction of an integral
splitting algebra at every integer parameter. The induced map on the
parameter polynomial ring is exactly evaluation at that integer. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

theorem branch_exists_integer_reduction (S : Type*) [CommRing S] [IsDomain S]
    [Algebra ℤ[X] S] [Algebra.IsIntegral ℤ[X] S] [FaithfulSMul ℤ[X] S] (t : ℤ) :
    ∃ Q : Ideal S, Q.IsPrime ∧ CharZero (S ⧸ Q) ∧
      (Ideal.Quotient.mk Q).comp (algebraMap ℤ[X] S) =
        (Int.castRingHom (S ⧸ Q)).comp (Polynomial.evalRingHom t) := by
  let P : Ideal ℤ[X] := RingHom.ker (Polynomial.evalRingHom t)
  let : P.IsPrime := RingHom.ker_isPrime (Polynomial.evalRingHom t)
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S := S) P (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp
        (FaithfulSMul.algebraMap_injective ℤ[X] S)]
      exact bot_le)
  let ψ : ℤ[X] →+* S ⧸ Q := (Ideal.Quotient.mk Q).comp (algebraMap ℤ[X] S)
  have hker : RingHom.ker ψ = P := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    exact hQP
  have hchar : CharZero (S ⧸ Q) := by
    apply charZero_of_inj_zero
    intro n hn
    have hmem : (n : ℤ[X]) ∈ RingHom.ker ψ := by
      change ψ (n : ℤ[X]) = 0
      simpa only [map_natCast] using hn
    rw [hker] at hmem
    have hz : (n : ℤ) = 0 := by
      simpa only [P, RingHom.mem_ker, map_natCast] using hmem
    exact_mod_cast hz
  have hX : ψ Polynomial.X = (t : S ⧸ Q) := by
    have hmem : Polynomial.X - Polynomial.C t ∈ P := by
      simp only [P, RingHom.mem_ker, map_sub, coe_evalRingHom, eval_X, eval_C, sub_self]
    rw [← hker, RingHom.mem_ker, map_sub] at hmem
    have hC : ψ (Polynomial.C t) = (t : S ⧸ Q) := by
      rw [show Polynomial.C t = (t : ℤ[X]) by
        simpa only [Int.cast_id] using Polynomial.C_eq_intCast (R := ℤ) t]
      exact map_intCast ψ t
    rw [hC] at hmem
    exact sub_eq_zero.mp hmem
  refine ⟨Q, hQ, hchar, ?_⟩
  change ψ = _
  ext
  · simp
  · simpa only [RingHom.comp_apply, coe_evalRingHom, eval_X,
      Int.coe_castRingHom] using hX

end
end PierceLengthBound.FixedDividend
