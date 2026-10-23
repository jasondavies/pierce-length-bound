/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchSieveCertificate
public import PierceLengthBound.BranchSieveSpecialization
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.Tactic

/-! The explicit sextic for the six locations at infinity is generically irreducible.
The proof specializes at `(-7,8,-4)`, uses the exact characteristic-zero certificate,
and preserves the full degree under specialization. This is an algebraic statement,
not a quantitative specialization theorem. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

/-- The degree-six location polynomial, with its seven coefficients factored. -/
def branchLocationSextic {R : Type*} [CommRing R] (c1 c2 c3 : R) : R[X] :=
  C (c2 ^ 2 * (c2 + 1) * (c2 + c3) * (c2 + c3 + 1) ^ 2) * X ^ 6 +
  C (6 * c1 * c2 ^ 2 * (c2 + 1) * (c2 + c3) * (c2 + c3 + 1)) * X ^ 5 +
  C (3 * c1 * c2 ^ 2 * (5 * c1 * c2 ^ 2 + 6 * c1 * c2 * c3 + 6 * c1 * c2 + c1 * c3 ^ 2 + 5 * c1
    * c3 + c1 + c2 ^ 2 * c3 + c2 ^ 2 + 2 * c2 * c3 ^ 2 + 2 * c2 * c3 + 2 * c2 + c3 ^ 3 + c3 ^ 2
    + c3 + 1)) * X ^ 4 +
  C (2 * c1 * c2 * (10 * c1 ^ 2 * c2 ^ 2 + 6 * c1 ^ 2 * c2 * c3 + 6 * c1 ^ 2 * c2 + 2 * c1 ^ 2 *
    c3 + 6 * c1 * c2 ^ 2 * c3 + 6 * c1 * c2 ^ 2 + 6 * c1 * c2 * c3 ^ 2 + 6 * c1 * c2 * c3 + 6 *
    c1 * c2 + 3 * c1 * c3 ^ 2 + 3 * c1 * c3 + 2 * c2 ^ 2 * c3 + 3 * c2 * c3 ^ 2 + 3 * c2 * c3 +
    c3 ^ 3 + 2 * c3 ^ 2 + c3)) * X ^ 3 +
  C (3 * c1 ^ 2 * c2 * (5 * c1 ^ 2 * c2 + c1 ^ 2 * c3 + c1 ^ 2 + 6 * c1 * c2 * c3 + 6 * c1 * c2
    + 2 * c1 * c3 ^ 2 + 2 * c1 * c3 + 2 * c1 + c2 * c3 ^ 2 + 5 * c2 * c3 + c2 + c3 ^ 3 + c3 ^ 2
    + c3 + 1)) * X ^ 2 +
  C (6 * c1 ^ 2 * c2 * (c1 + 1) * (c1 + c3) * (c1 + c3 + 1)) * X +
  C (c1 ^ 2 * (c1 + 1) * (c1 + c3) * (c1 + c3 + 1) ^ 2)

lemma branchLocationSextic_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (c1 c2 c3 : R) :
    (branchLocationSextic c1 c2 c3).map φ = branchLocationSextic (φ c1) (φ c2) (φ c3) := by
  simp [branchLocationSextic, map_ofNat]

lemma branchLocationSextic_natDegree_le {R : Type*} [CommRing R] (c1 c2 c3 : R) :
    (branchLocationSextic c1 c2 c3).natDegree ≤ 6 := by
  unfold branchLocationSextic
  compute_degree

/-- Three independent normalized coefficients. -/
abbrev BranchLocationParameters := MvPolynomial (Fin 3) ℚ

/-- Their rational function field. -/
abbrev BranchLocationField := FractionRing BranchLocationParameters

/-- The location polynomial over the polynomial parameter ring. -/
def branchGenericLocationSextic : BranchLocationParameters[X] :=
  branchLocationSextic (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)

/-- The exact specialization differs from the primitive integer certificate by `24`. -/
lemma branchGenericLocationSextic_specialize :
    branchGenericLocationSextic.map (MvPolynomial.eval ![-7, 8, -4]) =
      24 * branchSexticSpecialization.map (Int.castRingHom ℚ) := by
  rw [branchGenericLocationSextic, branchLocationSextic_map]
  norm_num [branchLocationSextic, branchSexticSpecialization, map_ofNat]
  ring

lemma branchGenericLocationSextic_specialization_natDegree :
    (branchGenericLocationSextic.map (MvPolynomial.eval ![-7, 8, -4])).natDegree = 6 := by
  rw [branchGenericLocationSextic_specialize]
  simp only [branchSexticSpecialization, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_ofNat]
  compute_degree <;> norm_num

lemma branchGenericLocationSextic_natDegree : branchGenericLocationSextic.natDegree = 6 := by
  apply le_antisymm (branchLocationSextic_natDegree_le _ _ _)
  rw [← branchGenericLocationSextic_specialization_natDegree]
  exact natDegree_map_le

lemma branchGenericLocationSextic_specialization_irreducible :
    Irreducible (branchGenericLocationSextic.map (MvPolynomial.eval ![-7, 8, -4])) := by
  rw [branchGenericLocationSextic_specialize]
  apply (irreducible_isUnit_mul ?_).mpr branchSexticSpecialization_irreducible_rat
  change IsUnit (C (24 : ℚ))
  exact isUnit_C.mpr (IsUnit.mk0 _ (by norm_num))

/-- The actual six-location polynomial is irreducible over `ℚ(c₁,c₂,c₃)`. -/
theorem branchGenericLocationSextic_irreducible :
    Irreducible (branchGenericLocationSextic.map
      (algebraMap BranchLocationParameters BranchLocationField)) := by
  let : NormalizedGCDMonoid BranchLocationParameters := Classical.choice inferInstance
  apply fraction_irreducible_of_degree_preserving_specialization
    (MvPolynomial.eval ![-7, 8, -4])
  · rw [branchGenericLocationSextic_specialization_natDegree, branchGenericLocationSextic_natDegree]
  · exact branchGenericLocationSextic_specialization_irreducible

/-- The generic location polynomial retains degree six over the rational function field. -/
lemma branchGenericLocationSextic_fraction_natDegree :
    (branchGenericLocationSextic.map
      (algebraMap BranchLocationParameters BranchLocationField)).natDegree = 6 := by
  rw [natDegree_map_eq_of_injective (IsFractionRing.injective _ _)]
  exact branchGenericLocationSextic_natDegree

/-- The field obtained by adjoining one of the six generic infinity locations. -/
abbrev BranchLocationExtension := AdjoinRoot
  (branchGenericLocationSextic.map (algebraMap BranchLocationParameters BranchLocationField))

instance branchGenericLocationSextic_irreducible_fact :
    Fact (Irreducible (branchGenericLocationSextic.map
      (algebraMap BranchLocationParameters BranchLocationField))) :=
  ⟨branchGenericLocationSextic_irreducible⟩

/-- The generic infinity location has degree six. -/
theorem branchLocationExtension_finrank :
    Module.finrank BranchLocationField BranchLocationExtension = 6 := by
  simpa only [AdjoinRoot.powerBasis_dim, branchGenericLocationSextic_fraction_natDegree] using
    (AdjoinRoot.powerBasis branchGenericLocationSextic_irreducible.ne_zero).finrank

end
end PierceLengthBound.FixedDividend
