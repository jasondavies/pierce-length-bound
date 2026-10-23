/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveUniformResolvents
public import PierceLengthBound.BranchSieveIntegralEquationFamily
import Mathlib.Tactic

/-! A bounded family of irreducible integral equations covers every proper
monic factor at every integer parameter. All degree and height constants
are independent of the coefficients of the original polynomial. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

theorem branch_uniform_integer_equation_family (n D : ℕ) :
    ∃ M E C : ℕ, 0 < C ∧ ∀ (F L : Type*) [Field F]
      [Algebra ℤ[X] F] [IsFractionRing ℤ[X] F] [Field L]
      [Algebra ℤ[X] L] [Algebra F L] [IsScalarTower ℤ[X] F L]
      [FaithfulSMul ℤ[X] L],
      ∀ (p : ℤ[X][X]), p.Monic → p.natDegree = n →
      Irreducible (p.map (algebraMap ℤ[X] F)) →
      (p.map (algebraMap ℤ[X] L)).Splits →
      ∀ H : ℕ, (∀ j, (p.coeff j).natDegree ≤ D) →
      (∀ i j, |(p.coeff i).coeff j| ≤ (H : ℤ)) →
      ∃ G : Finset ℤ[X][X], G.card ≤ 2 ^ n * (n + 1) ∧
      (∀ f ∈ G, f.Monic ∧ Irreducible (f.map (algebraMap ℤ[X] F)) ∧
        2 ≤ f.natDegree ∧ CCDN.bivariateTotalDegree f ≤ M ∧
        ∀ i j, |(f.coeff i).coeff j| ≤ (C * (H + 1) ^ E : ℕ)) ∧
      ∀ (t : ℤ) (q : ℤ[X]), q.Monic → q ∣ p.map (evalRingHom t) →
        0 < q.natDegree → q.natDegree < n →
        ∃ f ∈ G, ∃ y : ℤ, (f.map (evalRingHom t)).eval y = 0 := by
  obtain ⟨M, E, C, hC, hb⟩ := branch_uniform_integral_minpoly_bounds n D
  refine ⟨M, E, C, hC, ?_⟩
  intro F L _ _ _ _ _ _ _ _ p hp hn hir hsplit H hD hH
  obtain ⟨G, hcard, hG, hcover⟩ :=
    branch_exists_integral_equation_family (F := F) p hp hsplit
  refine ⟨G, by simpa only [hn] using hcard, ?_, ?_⟩
  · intro f hf
    obtain ⟨hfm, hfir, hfdeg, q, hq, hdiv, j, hj, rfl⟩ := hG f hf
    obtain ⟨hdegree, hheight⟩ := hb L p hp hn hsplit H hD hH q hq hdiv j (hn ▸ hj)
    exact ⟨hfm, hfir, hfdeg, hdegree, hheight⟩
  · intro t q hq hdiv hqpos hqlt
    obtain ⟨q₀, hq₀, hq₀div, j, _hfm, _hfir, hfdeg, hroot⟩ :=
      branch_integer_specialization_witness p hp hir hsplit t q hq hdiv hqpos
        (by simpa only [hn] using hqlt)
    refine ⟨_, hcover q₀ hq₀ hq₀div j hfdeg, q.coeff j, ?_⟩
    simpa only [Polynomial.eval_map, Polynomial.eval₂_evalRingHom] using hroot

end
end PierceLengthBound.FixedDividend
