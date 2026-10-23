/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveKroneckerHilbert
public import PierceLengthBound.BranchSieveParameterRearrangement
public import PierceLengthBound.BranchSieveParameterInduction
public import PierceLengthBound.BranchSieveRootKronecker

/-! The complete fixed-degree monic Hilbert estimate in any number of
integer parameters. Kronecker encoding proves the one-coordinate input;
the finite-fiber induction then counts actual rational reducible fibers. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

theorem branch_head_irreducibility_estimate (r d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ BranchHeadIrreducibilityEstimate r d C := by
  let D := (d + 1) ^ (r + 1) * (2 * d) + d
  obtain ⟨C, hC, hcount⟩ := branch_bounded_kronecker_hilbert_bound (d + 1) (r + 1) D
  refine ⟨C, hC, ?_⟩
  intro p hp hirr hnd htd H B hH hB S hS
  let q := branchFamilyParameterRearrangement ℤ r p
  let f := branchRootLastEquiv ℤ[X] r q
  obtain ⟨hqm, hqnd, hqtd, hqcoeff, hqheight⟩ :=
    branchFamilyParameterRearrangement_bounds p hp hnd htd hH
  change q.natDegree ≤ d at hqnd
  have hradix (i : Fin (r + 1)) : f.degreeOf i < d + 1 :=
    (branchRootLastEquiv_degreeOf_le q hqnd hqtd i).trans_lt (by omega)
  have hfcoeff (s : Fin (r + 1) →₀ ℕ) : (f.coeff s).natDegree ≤ d := by
    rw [show f = branchRootLastEquiv ℤ[X] r q from rfl, branchRootLastEquiv_coeff]
    exact hqcoeff _ _
  have hfheight (s : Fin (r + 1) →₀ ℕ) (j : ℕ) : |(f.coeff s).coeff j| ≤ (H : ℤ) := by
    rw [show f = branchRootLastEquiv ℤ[X] r q from rfl, branchRootLastEquiv_coeff]
    exact hqheight _ _ _
  have hfdegree : f.totalDegree ≤ 2 * d :=
    (branchRootLastEquiv_totalDegree_le q hqtd).trans (by omega)
  have hfirr : Irreducible (MvPolynomial.map (Polynomial.mapRingHom (Int.castRingHom ℚ)) f) := by
    rw [show f = branchRootLastEquiv ℤ[X] r q from rfl, branchRootLastEquiv_map]
    exact (MulEquiv.irreducible_iff
      (f := (branchRootLastEquiv ℚ[X] r).toMulEquiv)).mpr
        (branchFamilyParameterRearrangement_irreducible p hirr)
  have hmonic : (branchMultiKronecker (d + 1) (r + 1) f).Monic := by
    rw [← branchRootKronecker_eq_multi]
    exact branchRootKronecker_monic (by omega) q hqm (fun j i =>
      ((MvPolynomial.degreeOf_le_totalDegree (q.coeff j) i).trans (hqtd j)).trans_lt (by omega))
  have hpositive : 0 < (branchMultiKronecker (d + 1) (r + 1) f).natDegree := by
    apply hmonic.natDegree_pos.mpr
    intro he
    have hfone : f = 1 := branchMultiKronecker_injOn hradix
      (fun i => by simp) (by simpa using he)
    exact hfirr.not_isUnit (by simp [hfone])
  have hPnd : (branchMultiKronecker (d + 1) (r + 1) f).natDegree ≤
      (d + 1) ^ (r + 1) * (2 * d) :=
    (branchMultiKronecker_natDegree_le (by omega) f).trans
      (Nat.mul_le_mul_left _ hfdegree)
  have hPcoeff (k : ℕ) : ((branchMultiKronecker (d + 1) (r + 1) f).coeff k).natDegree ≤ d :=
    branchMultiKronecker_coefficient_degree f hradix hfcoeff k
  have htotal : CCDN.bivariateTotalDegree (branchMultiKronecker (d + 1) (r + 1) f) ≤ D := by
    rw [CCDN.bivariateTotalDegree_le_iff]
    intro i j hij
    have hi : i ≤ (branchMultiKronecker (d + 1) (r + 1) f).natDegree :=
      Polynomial.le_natDegree_of_ne_zero (fun hz => hij (by rw [hz]; simp))
    have hj := (Polynomial.le_natDegree_of_ne_zero hij).trans (hPcoeff i)
    dsimp only [D]
    omega
  have hresult := hcount f hfirr hradix hmonic hpositive htotal
    (fun s => (hfcoeff s).trans (by dsimp only [D]; omega)) H B
    (branchMultiKronecker_nested_height f hradix hfheight) hB S (by
      intro t ht
      refine ⟨(hS t ht).1, ?_⟩
      rw [show f = branchRootLastEquiv ℤ[X] r q from rfl, branchRootLastEquiv_map]
      change ¬ Irreducible (branchRootLastEquiv ℚ r
        ((branchFamilyParameterRearrangement ℤ r p).map
          (MvPolynomial.map ((Int.castRingHom ℚ).comp (evalRingHom t)))))
      rw [branchFamilyParameterRearrangement_eval_rational]
      exact fun h => (hS t ht).2 ((MulEquiv.irreducible_iff
        (f := (branchRootLastEquiv ℚ r).toMulEquiv)).mp h))
  simpa only [Real.sqrt_eq_rpow] using hresult

/-- A coefficient-uniform effective Hilbert irreducibility bound for a
monic polynomial family over any fixed number of integer parameters. -/
theorem branch_multivariate_monic_hilbert_bound (r d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ p : Polynomial (MvPolynomial (Fin r) ℤ), p.Monic →
        Irreducible (branchFamilyRational p) → p.natDegree ≤ d →
        (∀ j, (p.coeff j).totalDegree ≤ d) →
        ∀ H B : ℕ, (∀ j s, |(p.coeff j).coeff s| ≤ (H : ℤ)) → 1 ≤ B →
        ∀ S : Finset (Fin r → ℤ),
          (∀ t ∈ S, (∀ j, |t j| ≤ (B : ℤ)) ∧ ¬ Irreducible (branchFamilyEval t p)) →
          (S.card : ℝ) ≤ C * branchHilbertSize r H B :=
  branch_multivariate_hilbert_bound_of_head_estimates r d
    (fun k _ => branch_head_irreducibility_estimate k d)

end
end PierceLengthBound.FixedDividend
