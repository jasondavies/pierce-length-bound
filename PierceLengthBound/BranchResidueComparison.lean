/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.BranchValuationComparison
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.RingTheory.Jacobson.Ring

/-! Residue degrees of branches: positive on a Dedekind domain of finite type over `ℚ`, and
unchanged when a branch is represented on another Dedekind model of the same function field,
in particular on the parameter normalization of a function. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

/-- A height-one prime of a Dedekind domain of finite type over `ℚ` has residue field finite
over `ℚ`, so its residue degree is positive; the residue field need not be `ℚ`. -/
theorem branch_residue_degree_pos {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra ℚ R] [Algebra.FiniteType ℚ R]
    (p : IsDedekindDomain.HeightOneSpectrum R) :
    0 < Module.finrank ℚ (R ⧸ p.asIdeal) := by
  let : Field (R ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
  let : Module.Finite ℚ (R ⧸ p.asIdeal) :=
    finite_of_finite_type_of_isJacobsonRing ℚ (R ⧸ p.asIdeal)
  exact Module.finrank_pos

/-- Equality of normalized orders identifies the local valuation rings and
therefore the residue fields of branches on two Dedekind models. -/
theorem branch_residue_degree_eq {R S L : Type*}
    [CommRing R] [IsDedekindDomain R] [Algebra ℚ R]
    [CommRing S] [IsDedekindDomain S] [Algebra ℚ S]
    [Field L] [Algebra R L] [IsFractionRing R L] [Algebra S L] [IsFractionRing S L]
    (p : IsDedekindDomain.HeightOneSpectrum R) (q : IsDedekindDomain.HeightOneSpectrum S)
    (h : normalizedBranchOrder p L = normalizedBranchOrder q L) :
    Module.finrank ℚ (R ⧸ p.asIdeal) = Module.finrank ℚ (S ⧸ q.asIdeal) := by
  let A := p.valuationSubringAtPrime L
  let B := q.valuationSubringAtPrime L
  have hV : (p.valuation L).valuationSubring = (q.valuation L).valuationSubring := by
    rw [← normalizedBranchOrder_valuationSubring p, ← normalizedBranchOrder_valuationSubring q, h]
  have hAB : A = B := by
    change p.valuationSubringAtPrime L = q.valuationSubringAtPrime L
    rw [p.valuationSubringAtPrime_eq_valuationSubring,
      q.valuationSubringAtPrime_eq_valuationSubring, hV]
  let eAB : A ≃+* B := RingEquiv.subringCongr (congrArg ValuationSubring.toSubring hAB)
  let ep := (IsLocalization.AtPrime.equivQuotMaximalIdeal p.asIdeal A).toRingEquiv
  let eq := (IsLocalization.AtPrime.equivQuotMaximalIdeal q.asIdeal B).toRingEquiv
  let e := ep.trans ((IsLocalRing.ResidueField.mapEquiv eAB).trans eq.symm)
  exact e.toRatAlgEquiv.toLinearEquiv.finrank_eq

/-- Transporting a normalized branch to a function parameter preserves both
all function orders and the residue degree used in divisor sums. -/
theorem function_parameter_branch_transport_with_degree {R L : Type*}
    [CommRing R] [IsDedekindDomain R] [Algebra ℚ R]
    [Field L] [Algebra ℚ L] [Algebra R L] [IsScalarTower ℚ R L] [IsFractionRing R L]
    (p : IsDedekindDomain.HeightOneSpectrum R)
    (x : L) (hx : Transcendental ℚ x)
    [FiniteDimensional (IntermediateField.adjoin ℚ {x}) L]
    (hpos : 0 < normalizedBranchOrder p L x) :
    ∃ q : IsDedekindDomain.HeightOneSpectrum (functionParameterNormalization x),
      functionParameterElement x ∈ q.asIdeal ∧
      functionParameterBranchOrder x hx q = normalizedBranchOrder p L ∧
      Module.finrank ℚ ((functionParameterNormalization x) ⧸ q.asIdeal) =
        Module.finrank ℚ (R ⧸ p.asIdeal) := by
  let C := functionParameterNormalization x
  let : IsDedekindDomain C := (function_parameter_normalization x hx).1
  let : IsFractionRing C L := (function_parameter_normalization x hx).2.2
  have hQ (c : ℚ) : 0 ≤ normalizedBranchOrder p L (algebraMap ℚ L c) := by
    rw [IsScalarTower.algebraMap_apply ℚ R L]
    exact normalizedBranchOrder_nonnegative p L (algebraMap ℚ R c)
  obtain ⟨q, hmem, hq⟩ := function_parameter_branch_transport
    (normalizedBranchOrder p L) hQ (normalizedBranchOrder_uniformizer p L) x hx hpos
  exact ⟨q, hmem, hq, branch_residue_degree_eq q p hq⟩

end
end PierceLengthBound.FixedDividend
