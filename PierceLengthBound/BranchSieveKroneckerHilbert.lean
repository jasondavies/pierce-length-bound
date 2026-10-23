/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveKroneckerFactors
public import PierceLengthBound.BranchSieveFiniteHilbert
public import PierceLengthBound.BranchSieveRootFactors

/-! A one-parameter Hilbert estimate for multivariate polynomial families,
obtained by actual Kronecker factorization and nonzero coefficient cuts. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial Finset

theorem branch_mv_degreeOf_map_le {σ R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (f : MvPolynomial σ R) (i : σ) :
    (MvPolynomial.map φ f).degreeOf i ≤ f.degreeOf i := by
  classical
  exact Multiset.count_le_of_le i (MvPolynomial.degrees_map_le (p := f))

theorem branch_bounded_kronecker_hilbert_bound (a n D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : MvPolynomial (Fin n) ℤ[X],
      Irreducible (MvPolynomial.map (Polynomial.mapRingHom (Int.castRingHom ℚ)) f) →
      (∀ i, f.degreeOf i < a) →
      (branchMultiKronecker a n f).Monic → 0 < (branchMultiKronecker a n f).natDegree →
      CCDN.bivariateTotalDegree (branchMultiKronecker a n f) ≤ D →
      (∀ s, (f.coeff s).natDegree ≤ D) →
      ∀ H B : ℕ, (∀ i j, |((branchMultiKronecker a n f).coeff i).coeff j| ≤ (H : ℤ)) →
      1 ≤ B → ∀ S : Finset ℤ,
      (∀ t ∈ S, |t| ≤ (B : ℤ) ∧ ¬ Irreducible
        (MvPolynomial.map ((Int.castRingHom ℚ).comp (evalRingHom t)) f)) →
      (S.card : ℝ) ≤ C * (1 + Real.log (H + 1 : ℕ)) ^ 4 *
        (B : ℝ) ^ (1 / 2 : ℝ) * (1 + Real.log B) := by
  classical
  let K := 2 ^ ((D + 1) * D) * ((D + 1) * D + 1) * (D + 1) ^ 2
  obtain ⟨C, hC, hcount⟩ := branch_finite_hilbert_with_cuts_bound D K 1 D (2 ^ D) (2 * D)
  refine ⟨C, hC, ?_⟩
  intro f hirr hradix hmonic hpositive htotal hcoeff H B hH hB S hS
  let P := branchMultiKronecker a n f
  let F := FractionRing ℤ[X]
  obtain ⟨Q, hQprod, hQcard, hQ⟩ := branch_bivariate_monic_factorization
    (F := F) P hmonic htotal hH
  let ψ := Polynomial.mapRingHom (Int.castRingHom ℚ)
  let fQ := MvPolynomial.map ψ f
  let Qrat := Q.map (Polynomial.map ψ)
  have hPdegree : P.natDegree ≤ D := (CCDN.bivariate_natDegree_le_totalDegree P).trans htotal
  have hQrat : ∀ q ∈ Qrat, q.Monic := by
    intro q hq
    obtain ⟨q₀, hq₀, rfl⟩ := Multiset.mem_map.mp hq
    exact (hQ q₀ hq₀).1.map ψ
  have hprod : branchMultiKronecker a n fQ = Qrat.prod := by
    rw [← branchMultiKronecker_map]
    change P.map ψ = Qrat.prod
    rw [hQprod.symm, Polynomial.map_multiset_prod]
  have hcoeffQ (s : Fin n →₀ ℕ) : (fQ.coeff s).natDegree ≤ D := by
    change ((MvPolynomial.map ψ f).coeff s).natDegree ≤ D
    rw [MvPolynomial.coeff_map]
    exact Polynomial.natDegree_map_le.trans (hcoeff s)
  have htotalQ : CCDN.bivariateTotalDegree Qrat.prod ≤ D := by
    rw [← Polynomial.map_multiset_prod, hQprod]
    exact (CCDN.bivariateTotalDegree_map_le (Int.castRingHom ℚ) P).trans htotal
  obtain ⟨E, hEcard, hE, hcover⟩ := branch_kronecker_coefficient_obstructions
    a n fQ hirr Qrat hQrat hprod D hcoeffQ htotalQ
  have hGcard : Q.toFinset.card ≤ D := (Multiset.toFinset_card_le Q).trans
    (hQcard.trans hPdegree)
  have hEbound : E.card ≤ 2 ^ D := hEcard.trans (Nat.pow_le_pow_right (by norm_num)
    (by simpa only [Qrat, Multiset.card_map] using hQcard.trans hPdegree))
  refine hcount F H B Q.toFinset E hGcard hEbound ?_ hE hB S ?_
  · intro q hq
    obtain ⟨hqm, hqir, _, hqd, hqh⟩ := hQ q (Multiset.mem_toFinset.mp hq)
    refine ⟨hqm, hqir, hqd, ?_⟩
    intro i j
    apply (hqh i j).trans
    have hmul : 2 ^ ((D + 1) * D) * ((D + 1) * D + 1) * ((D + 1) ^ 2 * H) ≤
        K * (H + 1) ^ 1 := by
      simpa only [K, pow_one, mul_assoc] using Nat.mul_le_mul_left K (Nat.le_succ H)
    exact_mod_cast hmul
  · intro t ht
    refine ⟨(hS t ht).1, ?_⟩
    by_cases hbad : ∃ q ∈ Q.toFinset,
        ¬ Irreducible ((q.map (evalRingHom t)).map (Int.castRingHom ℚ))
    · exact Or.inl hbad
    · right
      have hcomp : (evalRingHom (t : ℚ)).comp ψ =
          (Int.castRingHom ℚ).comp (evalRingHom t) := by ext <;> simp [ψ]
      have hpoly (q : ℤ[X][X]) :
          (q.map ψ).map (evalRingHom (t : ℚ)) =
            (q.map (evalRingHom t)).map (Int.castRingHom ℚ) := by
        rw [Polynomial.map_map, Polynomial.map_map, hcomp]
      have hirs : ∀ q ∈ Qrat, Irreducible (q.map (evalRingHom (t : ℚ))) := by
        intro q hq
        obtain ⟨q₀, hq₀, rfl⟩ := Multiset.mem_map.mp hq
        rw [hpoly]
        exact not_not.mp (fun h => hbad ⟨q₀, Multiset.mem_toFinset.mpr hq₀, h⟩)
      apply hcover (t : ℚ) hirs
      let ft := MvPolynomial.map (evalRingHom (t : ℚ)) fQ
      have hft : ft = MvPolynomial.map ((Int.castRingHom ℚ).comp (evalRingHom t)) f := by
        change MvPolynomial.map _ (MvPolynomial.map ψ f) = _
        rw [MvPolynomial.map_map, hcomp]
      have hftdegree (i : Fin n) : ft.degreeOf i < a :=
        ((branch_mv_degreeOf_map_le _ fQ i).trans (branch_mv_degreeOf_map_le ψ f i)).trans_lt
          (hradix i)
      have hencoded : branchMultiKronecker a n ft =
          (P.map ψ).map (evalRingHom (t : ℚ)) := by
        rw [← branchMultiKronecker_map, ← branchMultiKronecker_map]
      have hftmonic : (branchMultiKronecker a n ft).Monic := by
        rw [hencoded]
        exact (hmonic.map ψ).map _
      have hftone : branchMultiKronecker a n ft ≠ 1 := by
        apply hftmonic.natDegree_pos.mp
        rw [hencoded, (hmonic.map ψ).natDegree_map, hmonic.natDegree_map]
        exact hpositive
      exact branch_kronecker_proper_factor_witness ft hftdegree
        (by simpa only [hft] using (hS t ht).2) hftmonic hftone

end
end PierceLengthBound.FixedDividend
