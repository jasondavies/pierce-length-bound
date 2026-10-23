/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.NormalizedFiberOrders
public import PierceLengthBound.CurveNormalization

/-! The branches of a transcendental parameter's fiber on the normalization:
their residue-degree weighted orders sum to the dimension of the original
fiber. For the reciprocal first node coordinate on the infinity chart this is
`∑_{P ∣ ∞} e_P deg P = d` (§8.8). -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open scoped BigOperators

/-- For a domain `S` finite over `ℚ[w]`, `w` transcendental, the branches of the zero fiber of
`w` on the integral closure `C` of `S` satisfy
`∑_{q ∈ B} mult_q (w) · [C/q : ℚ] = dim_ℚ S/(w)`. -/
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

end
end PierceLengthBound.FixedDividend
