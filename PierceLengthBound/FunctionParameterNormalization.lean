/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.NormalizedFiberOrders
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! Normalizing the affine line in a finite function-field extension. The zero
fiber degree is the field-extension degree; replacing the parameter by its
reciprocal will give the corresponding pole fiber degree. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open scoped IntermediateField IntermediateField.algebraAdjoinAdjoin
open scoped BigOperators

/-- The integral closure of the parameter polynomial algebra in the function field. -/
abbrev functionParameterNormalization {L : Type*} [Field L] [Algebra ℚ L] (x : L) :=
  integralClosure (Algebra.adjoin ℚ {x}) L

/-- The parameter as an element of its normalization. -/
def functionParameterElement {L : Type*} [Field L] [Algebra ℚ L] (x : L) :
    functionParameterNormalization x :=
  algebraMap (Algebra.adjoin ℚ {x}) (functionParameterNormalization x)
    ⟨x, Algebra.self_mem_adjoin_singleton ℚ x⟩

@[simp] theorem functionParameterElement_coe {L : Type*} [Field L] [Algebra ℚ L] (x : L) :
    (functionParameterElement x : L) = x := rfl

theorem function_parameter_normalization {L : Type*} [Field L] [Algebra ℚ L]
    (x : L) (hx : Transcendental ℚ x) [FiniteDimensional ℚ⟮x⟯ L] :
    IsDedekindDomain (functionParameterNormalization x) ∧
    Module.Finite (Algebra.adjoin ℚ {x}) (functionParameterNormalization x) ∧
    IsFractionRing (functionParameterNormalization x) L := by
  let T := Algebra.adjoin ℚ {x}
  let K := ℚ⟮x⟯
  let C := functionParameterNormalization x
  let : Fact (Transcendental ℚ x) := ⟨hx⟩
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  exact ⟨IsIntegralClosure.isDedekindDomain T K L C,
    IsIntegralClosure.finite T K L C,
    IsIntegralClosure.isFractionRing_of_finite_extension T K L C⟩

/-- The canonical normalized order at a branch of the parameter normalization. -/
def functionParameterBranchOrder {L : Type*} [Field L] [Algebra ℚ L]
    (x : L) (hx : Transcendental ℚ x) [FiniteDimensional ℚ⟮x⟯ L]
    (q : IsDedekindDomain.HeightOneSpectrum (functionParameterNormalization x)) :
    AddValuation L (WithTop ℤ) :=
  let : IsDedekindDomain (functionParameterNormalization x) :=
    (function_parameter_normalization x hx).1
  let : IsFractionRing (functionParameterNormalization x) L :=
    (function_parameter_normalization x hx).2.2
  normalizedBranchOrder q L

theorem functionParameterBranchOrder_parameter {L : Type*} [Field L] [Algebra ℚ L]
    (x : L) (hx : Transcendental ℚ x) [FiniteDimensional ℚ⟮x⟯ L]
    (q : IsDedekindDomain.HeightOneSpectrum (functionParameterNormalization x)) :
    functionParameterBranchOrder x hx q x =
      ((multiplicity q.asIdeal (Ideal.span {functionParameterElement x}) : ℤ) : WithTop ℤ) := by
  let C := functionParameterNormalization x
  let : IsDedekindDomain C := (function_parameter_normalization x hx).1
  let : IsFractionRing C L := (function_parameter_normalization x hx).2.2
  have hw : functionParameterElement x ≠ 0 := by
    intro h
    exact hx.ne_zero (congrArg (fun z : C => (z : L)) h)
  exact normalizedBranchOrder_eq_multiplicity q L hw

theorem functionParameterBranchOrder_inverse {L : Type*} [Field L] [Algebra ℚ L]
    (x : L) (hx : Transcendental ℚ x) [FiniteDimensional ℚ⟮x⟯ L]
    (q : IsDedekindDomain.HeightOneSpectrum (functionParameterNormalization x)) :
    functionParameterBranchOrder x hx q x⁻¹ =
      ((-(multiplicity q.asIdeal (Ideal.span {functionParameterElement x}) : ℤ)) : WithTop ℤ) := by
  rw [AddValuation.map_inv, functionParameterBranchOrder_parameter]

theorem functionParameterBranchOrder_center {L : Type*} [Field L] [Algebra ℚ L]
    (x : L) (hx : Transcendental ℚ x) [FiniteDimensional ℚ⟮x⟯ L]
    (q : IsDedekindDomain.HeightOneSpectrum (functionParameterNormalization x))
    (r : functionParameterNormalization x) :
    0 < functionParameterBranchOrder x hx q (r : L) ↔ r ∈ q.asIdeal := by
  let C := functionParameterNormalization x
  let : IsDedekindDomain C := (function_parameter_normalization x hx).1
  let : IsFractionRing C L := (function_parameter_normalization x hx).2.2
  exact normalizedBranchOrder_positive_iff q L r

/-- The full zero fiber of a nonconstant rational function, including all
residue-field degrees, has degree equal to its function-field extension degree. -/
theorem function_parameter_fiber_degree {L : Type*} [Field L] [Algebra ℚ L]
    (x : L) (hx : Transcendental ℚ x) [FiniteDimensional ℚ⟮x⟯ L] :
    let C := functionParameterNormalization x
    ∃ B : Finset (IsDedekindDomain.HeightOneSpectrum C),
      (∀ q, q ∈ B ↔ functionParameterElement x ∈ q.asIdeal) ∧
      ∑ q ∈ B, multiplicity q.asIdeal (Ideal.span {functionParameterElement x}) *
        Module.finrank ℚ (C ⧸ q.asIdeal) = Module.finrank ℚ⟮x⟯ L := by
  let T := Algebra.adjoin ℚ {x}
  let C := functionParameterNormalization x
  let : Fact (Transcendental ℚ x) := ⟨hx⟩
  obtain ⟨hD, hfin, hfrac⟩ := function_parameter_normalization x hx
  let : IsDedekindDomain C := hD
  let : Module.Finite T C := hfin
  let : IsFractionRing C L := hfrac
  let e := Polynomial.algEquivOfTranscendental ℚ x hx
  have he : algebraMap T C (e Polynomial.X) = functionParameterElement x := by
    rw [Polynomial.algEquivOfTranscendental_apply_X]
    rfl
  obtain ⟨B, hB, hsum⟩ := polynomial_parameter_branches (C := C) e
  change (∀ q, q ∈ B ↔ algebraMap T C (e Polynomial.X) ∈ q.asIdeal) at hB
  change ∑ q ∈ B, multiplicity q.asIdeal (Ideal.span {algebraMap T C (e Polynomial.X)}) *
    Module.finrank ℚ (C ⧸ q.asIdeal) = Module.finrank T C at hsum
  rw [he] at hB hsum
  exact ⟨B, hB, hsum.trans (IsFractionRing.finrank_eq T ℚ⟮x⟯ C L).symm⟩

theorem intermediateField_adjoin_inv {K L : Type*} [Field K] [Field L] [Algebra K L]
    (x : L) : K⟮x⁻¹⟯ = K⟮x⟯ := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self K x)
  · rw [IntermediateField.adjoin_simple_le_iff]
    simpa only [inv_inv] using
      IntermediateField.inv_mem K⟮x⁻¹⟯ (IntermediateField.mem_adjoin_simple_self K x⁻¹)

/-- Zero and pole fibers have the same degree: they are the zero fibers of x
and x⁻¹, whose parameter fields coincide. -/
theorem function_zero_pole_fiber_degrees {L : Type*} [Field L] [Algebra ℚ L]
    (x : L) (hx : Transcendental ℚ x) [FiniteDimensional ℚ⟮x⟯ L] :
    let C₀ := functionParameterNormalization x
    let Cpole := functionParameterNormalization x⁻¹
    ∃ (B₀ : Finset (IsDedekindDomain.HeightOneSpectrum C₀))
      (Bpole : Finset (IsDedekindDomain.HeightOneSpectrum Cpole)),
      (∀ q, q ∈ B₀ ↔ functionParameterElement x ∈ q.asIdeal) ∧
      (∀ q, q ∈ Bpole ↔ functionParameterElement x⁻¹ ∈ q.asIdeal) ∧
      (∑ q ∈ B₀, multiplicity q.asIdeal (Ideal.span {functionParameterElement x}) *
        Module.finrank ℚ (C₀ ⧸ q.asIdeal)) =
      ∑ q ∈ Bpole, multiplicity q.asIdeal (Ideal.span {functionParameterElement x⁻¹}) *
        Module.finrank ℚ (Cpole ⧸ q.asIdeal) := by
  have hxinv : Transcendental ℚ x⁻¹ := fun h => hx (IsAlgebraic.inv_iff.mp h)
  have hfield := intermediateField_adjoin_inv (K := ℚ) x
  let : FiniteDimensional ℚ⟮x⁻¹⟯ L := by rw [hfield]; infer_instance
  obtain ⟨B₀, hB₀, hs₀⟩ := function_parameter_fiber_degree x hx
  obtain ⟨Bpole, hBpole, hspole⟩ := function_parameter_fiber_degree x⁻¹ hxinv
  refine ⟨B₀, Bpole, hB₀, hBpole, hs₀.trans ?_⟩
  rw [hspole, hfield]

end
end PierceLengthBound.FixedDividend
