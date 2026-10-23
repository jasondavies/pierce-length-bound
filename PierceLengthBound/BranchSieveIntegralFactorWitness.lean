/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveFactorSpecialization
public import PierceLengthBound.BranchSieveFactorWitness
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Tactic

/-! Passing from a proper factor after reduction to an irreducible integral
coefficient equation before reduction. The splitting algebra and its
reduction map are explicit; this is the exact algebraic specialization step
used before any parameter counting. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

variable {R S F L K : Type*}
  [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing S] [IsDomain S] [Algebra R S]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Field L] [Algebra R L] [Algebra S L] [Algebra F L]
  [IsScalarTower R S L] [IsScalarTower R F L]
  [CommRing K] [IsDomain K]

include L in
/-- A proper specialized factor supplies a monic integral equation whose
generic root degree is at least two. The chosen equation is the minimal
polynomial of a coefficient of an actual lifted factor. -/
theorem branch_integral_factor_witness (φ : S →+* K) {p : R[X]}
    (hp : p.Monic) (hir : Irreducible (p.map (algebraMap R F)))
    (hsplit : (p.map (algebraMap R S)).Splits)
    {q : K[X]} (hq : q.Monic)
    (hdiv : q ∣ (p.map (algebraMap R S)).map φ)
    (hqpos : 0 < q.natDegree) (hqlt : q.natDegree < p.natDegree) :
    ∃ q₀ : S[X], q₀.Monic ∧ q₀ ∣ p.map (algebraMap R S) ∧ q₀.map φ = q ∧
      ∃ j : ℕ, (minpoly R (q₀.coeff j)).Monic ∧
        Irreducible ((minpoly R (q₀.coeff j)).map (algebraMap R F)) ∧
        2 ≤ (minpoly R (q₀.coeff j)).natDegree ∧
        (minpoly R (q₀.coeff j)).eval₂ (φ.comp (algebraMap R S)) (q.coeff j) = 0 := by
  obtain ⟨q₀, hq₀, hq₀div, hq₀map, hq₀degree⟩ :=
    branch_split_monic_factor_lifts φ (hp.map _) hsplit hq hdiv
  let qL := q₀.map (algebraMap S L)
  have hqL : qL.Monic := hq₀.map _
  have htower : (p.map (algebraMap R S)).map (algebraMap S L) =
      (p.map (algebraMap R F)).map (algebraMap F L) := by
    simp only [map_map, ← IsScalarTower.algebraMap_eq R S L,
      ← IsScalarTower.algebraMap_eq R F L]
  have hqLdiv : qL ∣ (p.map (algebraMap R F)).map (algebraMap F L) := by
    rw [← htower]
    exact Polynomial.map_dvd (algebraMap S L) hq₀div
  have hqLdegree : qL.natDegree = q.natDegree := (hq₀.natDegree_map _).trans hq₀degree
  obtain ⟨j, hj⟩ := branch_proper_factor_has_nonrational_coefficient hir hqL hqLdiv
    (by omega : 0 < qL.natDegree)
    (by simpa only [hp.natDegree_map, hqLdegree] using hqlt)
  have hint : IsIntegral R (q₀.coeff j) :=
    Polynomial.isIntegral_coeff_of_dvd p q₀ hp hq₀ hq₀div j
  have hintF : IsIntegral F (qL.coeff j) :=
    Polynomial.isIntegral_coeff_of_dvd (p.map (algebraMap R F)) qL
      (hp.map _) hqL hqLdiv j
  have hmin : minpoly F (qL.coeff j) = (minpoly R (q₀.coeff j)).map (algebraMap R F) := by
    simpa only [qL, coeff_map] using minpoly.isIntegrallyClosed_eq_field_fractions F L hint
  refine ⟨q₀, hq₀, hq₀div, hq₀map, j, minpoly.monic hint, ?_, ?_, ?_⟩
  · rw [← hmin]
    exact minpoly.irreducible hintF
  · have hdeg := (minpoly.two_le_natDegree_iff hintF).mpr hj
    rw [hmin, (minpoly.monic hint).natDegree_map] at hdeg
    exact hdeg
  · have hzero := congrArg φ (minpoly.aeval R (q₀.coeff j))
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, map_zero] at hzero
    have hcoeff : q.coeff j = φ (q₀.coeff j) := by rw [← hq₀map, coeff_map]
    rwa [hcoeff]

end
end PierceLengthBound.FixedDividend
