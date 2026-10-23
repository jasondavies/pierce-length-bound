/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveOneParameterHilbert
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic

/-! The monic one-parameter Hilbert estimate (Step 2 in the proof of
Theorem 10.4): for monic `p ∈ ℤ[T][Y]`, irreducible over `ℚ(T)`, of total
degree at most `d` and height at most `H`, the integers `t ∈ [-B,B]` with `p(t, Y)` reducible
over `ℚ` number at most `C (1 + log(H+1))^4 B^(1/2) (1 + log B)`. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial Finset

/-- A reducible monic polynomial other than `1` has a monic factor of degree
strictly between zero and its degree. -/
theorem branch_monic_proper_factor_of_not_irreducible
    {R : Type*} [CommRing R] [IsDomain R] (p : R[X]) (hp : p.Monic)
    (hp1 : p ≠ 1) (hred : ¬Irreducible p) :
    ∃ q : R[X], q.Monic ∧ q ∣ p ∧ 0 < q.natDegree ∧ q.natDegree < p.natDegree := by
  have h : ¬ ∀ f g : R[X], f.Monic → g.Monic → f * g = p →
      f.natDegree = 0 ∨ g.natDegree = 0 := by
    intro h
    exact hred (hp.irreducible_iff_natDegree.mpr ⟨hp1, h⟩)
  push Not at h
  obtain ⟨q, r, hq, hr, hprod, hqdeg, hrdeg⟩ := h
  refine ⟨q, hq, ⟨r, hprod.symm⟩, by omega, ?_⟩
  rw [← hprod, hq.natDegree_mul hr]
  omega

/-- The estimate for a fixed degree `n`, from the proper-factor count with an
algebraic closure as splitting field. -/
theorem branch_one_parameter_monic_irreducibility_bound (n D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Type*) [Field F]
      [Algebra ℤ[X] F] [IsFractionRing ℤ[X] F],
      ∀ (p : ℤ[X][X]), p.Monic → p.natDegree = n →
      Irreducible (p.map (algebraMap ℤ[X] F)) →
      ∀ H B : ℕ, (∀ j, (p.coeff j).natDegree ≤ D) →
      (∀ i j, |(p.coeff i).coeff j| ≤ (H : ℤ)) → 1 ≤ B →
      ∀ S : Finset ℤ,
      (∀ t ∈ S, |t| ≤ (B : ℤ) ∧
        ¬Irreducible ((p.map (evalRingHom t)).map (Int.castRingHom ℚ))) →
      (S.card : ℝ) ≤ C * (1 + Real.log (H + 1 : ℕ)) ^ 4 *
        (B : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log B) := by
  obtain ⟨C, hC, hcount⟩ := branch_one_parameter_proper_factor_bound n D
  refine ⟨C, hC, ?_⟩
  intro F _ _ _ p hp hn hir H B hD hH hB S hS
  let L := AlgebraicClosure F
  let : FaithfulSMul ℤ[X] L := (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
    rw [IsScalarTower.algebraMap_eq ℤ[X] F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective ℤ[X] F))
  have hp1 : p ≠ 1 := by
    intro he
    simp only [he, Polynomial.map_one, not_irreducible_one] at hir
  apply hcount F L p hp hn hir (IsAlgClosed.splits _) H B hD hH hB S
  intro t ht
  obtain ⟨htB, htred⟩ := hS t ht
  have hpm : (p.map (evalRingHom t)).Monic := hp.map _
  have hdeg : (p.map (evalRingHom t)).natDegree = n := by rw [hp.natDegree_map, hn]
  have hp1' : p.map (evalRingHom t) ≠ 1 := by
    apply hpm.natDegree_pos.mp
    rw [hp.natDegree_map]
    exact hp.natDegree_pos.mpr hp1
  have hred : ¬Irreducible (p.map (evalRingHom t)) := by
    intro hir'
    exact htred (hpm.irreducible_iff_irreducible_map_fraction_map (K := ℚ) |>.mp hir')
  obtain ⟨q, hq, hdiv, hqpos, hqlt⟩ :=
    branch_monic_proper_factor_of_not_irreducible _ hpm hp1' hred
  exact ⟨htB, q, hq, hdiv, hqpos, by simpa only [hdeg] using hqlt⟩

/-- The estimate uniform over all degrees up to `d`. -/
theorem branch_uniform_monic_hilbert_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Type*) [Field F]
      [Algebra ℤ[X] F] [IsFractionRing ℤ[X] F],
      ∀ (p : ℤ[X][X]), p.Monic →
      Irreducible (p.map (algebraMap ℤ[X] F)) → CCDN.bivariateTotalDegree p ≤ d →
      ∀ H B : ℕ, (∀ i j, |(p.coeff i).coeff j| ≤ (H : ℤ)) → 1 ≤ B →
      ∀ S : Finset ℤ,
      (∀ t ∈ S, |t| ≤ (B : ℤ) ∧
        ¬Irreducible ((p.map (evalRingHom t)).map (Int.castRingHom ℚ))) →
      (S.card : ℝ) ≤ C * (1 + Real.log (H + 1 : ℕ)) ^ 4 *
        (B : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log B) := by
  classical
  have hex (n : Fin (d + 1)) := branch_one_parameter_monic_irreducibility_bound n.val d
  choose c hc hb using hex
  let C := ∑ n : Fin (d + 1), c n
  have hC : 0 < C := sum_pos (fun n _ => hc n) (by simp)
  refine ⟨C, hC, ?_⟩
  intro F _ _ _ p hp hir hd H B hH hB S hS
  have hn : p.natDegree ≤ d := (CCDN.bivariate_natDegree_le_totalDegree p).trans hd
  let n : Fin (d + 1) := ⟨p.natDegree, by omega⟩
  apply (hb n F p hp rfl hir H B
    (fun j => (CCDN.bivariate_coefficient_natDegree_le_totalDegree p j).trans hd) hH hB S hS).trans
  have hcn : c n ≤ C := single_le_sum (fun i _ => (hc i).le) (mem_univ n)
  have hlogH : 0 ≤ Real.log (H + 1 : ℕ) := Real.log_nonneg
    (by exact_mod_cast (show 1 ≤ H + 1 by omega))
  have hlogB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by exact_mod_cast hB)
  gcongr

end
end PierceLengthBound.FixedDividend
