/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.NormalizationFiberDegree
public import PierceLengthBound.NormalizedFiberOrders

/-! The total residue-degree weighted order of the old infinity parameter
on the normalization equals the original affine Hilbert degree. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open scoped BigOperators

/-- The branches of a normalized parameter fiber, with multiplicities measured
by the canonical normalized valuations. -/
theorem normalized_parameter_branches {S L : Type*}
    [CommRing S] [IsDomain S] [Algebra ℚ S]
    [Field L] [Algebra ℚ L] [Algebra S L] [IsScalarTower ℚ S L] [IsFractionRing S L]
    (w : S) (hw : Transcendental ℚ w) [Module.Finite (Algebra.adjoin ℚ {w}) S] :
    let C := integralClosure S L
    let wC := algebraMap S C w
    ∃ B : Finset (IsDedekindDomain.HeightOneSpectrum C),
      (∀ q, q ∈ B ↔ wC ∈ q.asIdeal) ∧
      ∑ q ∈ B, multiplicity q.asIdeal (Ideal.span {wC}) *
        Module.finrank ℚ (C ⧸ q.asIdeal) = Module.finrank ℚ (S ⧸ Ideal.span {w}) := by
  let T := Algebra.adjoin ℚ {w}
  let C := integralClosure S L
  let e := Polynomial.algEquivOfTranscendental ℚ w hw
  let : Fact (Transcendental ℚ w) := ⟨hw⟩
  let : IsDedekindDomain C := (finite_parameter_normalization w hw L).1
  let : Module.Finite S C := (finite_parameter_normalization w hw L).2
  let : Module.Finite T C := Module.Finite.trans S C
  have he : algebraMap T S (e Polynomial.X) = w := by
    change ((e Polynomial.X : T) : S) = w
    rw [Polynomial.algEquivOfTranscendental_apply_X]
  have heC : algebraMap T C (e Polynomial.X) = algebraMap S C w := by
    rw [IsScalarTower.algebraMap_apply T S C, he]
  obtain ⟨B, hB, hsum⟩ := polynomial_parameter_branches (C := C) e
  change (∀ q, q ∈ B ↔ algebraMap T C (e Polynomial.X) ∈ q.asIdeal) at hB
  change ∑ q ∈ B, multiplicity q.asIdeal (Ideal.span {algebraMap T C (e Polynomial.X)}) *
    Module.finrank ℚ (C ⧸ q.asIdeal) = Module.finrank T C at hsum
  rw [heC] at hB hsum
  refine ⟨B, ?_, ?_⟩
  · exact hB
  · rw [parameter_fiber_finrank w hw, ← normalization_parameter_rank (L := L) w]
    exact hsum

set_option maxHeartbeats 800000 in
-- The chart, parameter algebra and normalization form nested subalgebra towers.
set_option synthInstance.maxHeartbeats 200000 in
/-- Every normalized infinity branch is counted, and its residue degree times
its order of the old infinity parameter contributes to a sum exactly equal
to the original Hilbert degree d. -/
theorem nonexceptional_normalized_infinity_degree
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ) (ha : a ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : curveQuadratic ρ u v ρ' u' v' ∈ I)
    (hg : curveEquation ρ u v ρ' u' v' A a ∈ I)
    {F : Type*} [Field F] [Algebra ℚ F]
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι)
    {d N : ℕ} {b : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b) :
    let l := Ideal.Quotient.mk I (MvPolynomial.X 0)
    let S := projectiveChart I ι l
    let C := chartNormalization I ι l
    let w := algebraMap S C (chartInfinityCoordinate I ι l)
    ∃ B : Finset (IsDedekindDomain.HeightOneSpectrum C),
      (∀ q, q ∈ B ↔ w ∈ q.asIdeal) ∧
      ∑ q ∈ B, multiplicity q.asIdeal (Ideal.span {w}) *
        Module.finrank ℚ (C ⧸ q.asIdeal) = d := by
  let l := Ideal.Quotient.mk I (MvPolynomial.X 0)
  let S := projectiveChart I ι l
  let w := chartInfinityCoordinate I ι l
  let : Module.Finite (Algebra.adjoin ℚ {w}) S :=
    nonexceptional_chart_finite_over_parameter hρ hu hv hne ρ' u' v' A a ha
      I hf hg ι hι hd hdegree
  have hw : Transcendental ℚ w :=
    nonexceptional_chart_parameter_transcendental hρ hu hv hne ρ' u' v' A a ha
      I hf hg ι hι hd hdegree
  obtain ⟨B, hB, hsum⟩ := normalized_parameter_branches (L := FractionRing S) w hw
  refine ⟨B, hB, hsum.trans ?_⟩
  exact (rational_nonexceptional_chart_infinity_dimension hρ hu hv hne ρ' u' v' A a ha
    I hf hg ι hι hd hdegree).2

end
end PierceLengthBound.FixedDividend
