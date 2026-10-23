/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveMonicization
public import Mathlib.Algebra.Polynomial.Eval.Irreducible

/-! Irreducibility transfer through fixed-degree monicization. The coefficient
maps and scalar factors remain abstract so that the transfer also applies to
large, explicitly constructed polynomial families. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

/-- A nonzero scalar multiple of an irreducible degree-`n` polynomial remains
irreducible after fixed-degree monicization and coefficient specialization. -/
theorem branchMonicization_map_irreducible_of_scalar
    {R K : Type*} [CommSemiring R] [Field K]
    (n : ℕ) (p : Polynomial R) (φ : R →+* K) (s : K) (q : Polynomial K)
    (he : p.map φ = Polynomial.C s * q) (hs : s ≠ 0)
    (hq : Irreducible q) (hd : q.natDegree = n) (hn : 1 ≤ n) :
    Irreducible ((branchMonicization n p).map φ) := by
  have hi : Irreducible (p.map φ) := by
    rw [he]
    exact (irreducible_isUnit_mul (isUnit_C.mpr (IsUnit.mk0 _ hs))).mpr hq
  have hdegree : (p.map φ).natDegree = n := by
    rw [he, natDegree_C_mul hs, hd]
  have hlead : (p.map φ).coeff n ≠ 0 := by
    rw [← hdegree, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hi.ne_zero
  rw [branchMonicization_map]
  exact (branchMonicization_irreducible_iff n (p.map φ) hdegree hn hlead).mpr hi

/-- Monicity reflects irreducibility from a scalar-multiple specialization. -/
theorem branchMonicization_irreducible_of_scalar
    {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    (n : ℕ) (p : Polynomial R) (φ : R →+* K) (s : K) (q : Polynomial K)
    (he : p.map φ = Polynomial.C s * q) (hs : s ≠ 0)
    (hq : Irreducible q) (hd : q.natDegree = n) (hn : 1 ≤ n) :
    Irreducible (branchMonicization n p) := by
  exact Polynomial.Monic.irreducible_of_irreducible_map φ _
    (branchMonicization_monic n p)
    (branchMonicization_map_irreducible_of_scalar n p φ s q he hs hq hd hn)

/-- Reflect the preceding transfer through an intermediate coefficient ring. -/
theorem branchMonicization_map_irreducible_of_scalar_comp
    {R S K : Type*} [CommSemiring R] [CommRing S] [IsDomain S] [Field K]
    (n : ℕ) (p : Polynomial R) (ρ : R →+* S) (ψ : S →+* K)
    (s : K) (q : Polynomial K)
    (he : p.map (ψ.comp ρ) = Polynomial.C s * q) (hs : s ≠ 0)
    (hq : Irreducible q) (hd : q.natDegree = n) (hn : 1 ≤ n) :
    Irreducible ((branchMonicization n p).map ρ) := by
  apply Polynomial.Monic.irreducible_of_irreducible_map ψ _
    ((branchMonicization_monic n p).map ρ)
  rw [Polynomial.map_map]
  exact branchMonicization_map_irreducible_of_scalar n p (ψ.comp ρ) s q he hs hq hd hn

/-- An irreducible fixed-degree monicization excludes leading-degree collapse;
therefore a nonzero scalar factor can be removed with the degree preserved. -/
theorem branchMonicization_irreducible_scalar_consequences
    {K : Type*} [Field K] (n : ℕ) (p : Polynomial K)
    (hd : p.natDegree ≤ n) (hn : 2 ≤ n)
    (hir : Irreducible (branchMonicization n p))
    (s : K) (q : Polynomial K) (he : p = Polynomial.C s * q) (hs : s ≠ 0) :
    Irreducible q ∧ q.natDegree = n := by
  have hlead := branchMonicization_leading_ne_zero_of_irreducible n p hn hir
  have hdegree : p.natDegree = n :=
    le_antisymm hd (le_natDegree_of_ne_zero hlead)
  have hi := (branchMonicization_irreducible_iff n p hdegree (by omega) hlead).mp hir
  rw [he] at hi hdegree
  exact ⟨(irreducible_isUnit_mul (isUnit_C.mpr (IsUnit.mk0 _ hs))).mp hi,
    (natDegree_C_mul (p := q) hs).symm.trans hdegree⟩

/-- Canonical rational-ring interface for the scalar consequence. Keeping both
polynomials symbolic isolates the field-instance conversion before evaluation. -/
theorem branchMonicization_rat_scalar_consequences
    (n : ℕ) (p : Polynomial ℚ) (hd : p.natDegree ≤ n) (hn : 2 ≤ n)
    (hir : Irreducible (branchMonicization n p))
    (s : ℚ) (q : Polynomial ℚ) (he : p = Polynomial.C s * q) (hs : s ≠ 0) :
    Irreducible q ∧ q.natDegree = n :=
  branchMonicization_irreducible_scalar_consequences n p hd hn hir s q he hs

/-- The preceding consequence for a coefficient specialization of a family. -/
theorem branchMonicization_map_irreducible_scalar_consequences
    {R K : Type*} [CommSemiring R] [Field K]
    (n : ℕ) (p : Polynomial R) (φ : R →+* K)
    (hd : p.natDegree ≤ n) (hn : 2 ≤ n)
    (hir : Irreducible ((branchMonicization n p).map φ))
    (s : K) (q : Polynomial K) (he : p.map φ = Polynomial.C s * q) (hs : s ≠ 0) :
    Irreducible q ∧ q.natDegree = n := by
  have hi : Irreducible (branchMonicization n (p.map φ)) := by
    simpa only [branchMonicization_map] using hir
  exact branchMonicization_irreducible_scalar_consequences n (p.map φ)
    (natDegree_map_le.trans hd) hn hi s q he hs

end
end PierceLengthBound.FixedDividend
