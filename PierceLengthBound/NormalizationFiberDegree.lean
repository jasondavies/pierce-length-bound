/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ParameterFiberDegree
public import PierceLengthBound.ChartNormalization

/-! Normalization preserves the total dimension of a parameter fiber. Applied
to the actual infinity chart, this dimension is the original Hilbert degree. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

theorem normalization_parameter_fiber_finrank {S L : Type*}
    [CommRing S] [IsDomain S] [Algebra ℚ S]
    [Field L] [Algebra ℚ L] [Algebra S L] [IsScalarTower ℚ S L] [IsFractionRing S L]
    (w : S) (hw : Transcendental ℚ w) [Module.Finite (Algebra.adjoin ℚ {w}) S] :
    Module.finrank ℚ ((integralClosure S L) ⧸
      Ideal.span {algebraMap S (integralClosure S L) w}) =
      Module.finrank ℚ (S ⧸ Ideal.span {w}) := by
  let T := Algebra.adjoin ℚ {w}
  let C := integralClosure S L
  let e := Polynomial.algEquivOfTranscendental ℚ w hw
  let : Module.Finite S C := (finite_parameter_normalization w hw L).2
  let : Module.Finite T C := Module.Finite.trans S C
  have he : algebraMap T S (e X) = w := by
    change ((e X : T) : S) = w
    rw [Polynomial.algEquivOfTranscendental_apply_X]
  have heC : algebraMap T C (e X) = algebraMap S C w := by
    rw [IsScalarTower.algebraMap_apply T S C, he]
  calc
    Module.finrank ℚ (C ⧸ Ideal.span {algebraMap S C w}) = Module.finrank T C := by
      rw [← heC]
      exact polynomial_parameter_fiber_finrank e
    _ = Module.finrank T S := normalization_parameter_rank w
    _ = Module.finrank ℚ (S ⧸ Ideal.span {w}) := (parameter_fiber_finrank w hw).symm

set_option maxHeartbeats 800000 in
-- The chart and its normalization introduce several nested subalgebra towers.
set_option synthInstance.maxHeartbeats 200000 in
/-- The normalized old infinity fiber has vector-space dimension exactly d,
the actual affine Hilbert degree, including all branch multiplicities. The
normalization and the chart introduce nested subalgebra towers. -/
theorem nonexceptional_normalized_infinity_dimension
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
    let J := Ideal.span {algebraMap S C (chartInfinityCoordinate I ι l)}
    Module.Finite ℚ (C ⧸ J) ∧ Module.finrank ℚ (C ⧸ J) = d := by
  let l := Ideal.Quotient.mk I (MvPolynomial.X 0)
  let S := projectiveChart I ι l
  let C := chartNormalization I ι l
  let w := chartInfinityCoordinate I ι l
  let J := Ideal.span {algebraMap S C w}
  let : Module.Finite (Algebra.adjoin ℚ {w}) S :=
    nonexceptional_chart_finite_over_parameter hρ hu hv hne ρ' u' v' A a ha
      I hf hg ι hι hd hdegree
  have hw : Transcendental ℚ w :=
    nonexceptional_chart_parameter_transcendental hρ hu hv hne ρ' u' v' A a ha
      I hf hg ι hι hd hdegree
  have he : Module.finrank ℚ (C ⧸ J) = Module.finrank ℚ (S ⧸ Ideal.span {w}) :=
    normalization_parameter_fiber_finrank w hw
  have hdim : Module.finrank ℚ (C ⧸ J) = d := he.trans
    (rational_nonexceptional_chart_infinity_dimension hρ hu hv hne ρ' u' v' A a ha
      I hf hg ι hι hd hdegree).2
  exact ⟨Module.finite_of_finrank_pos (hdim.symm ▸ hd), hdim⟩

end
end PierceLengthBound.FixedDividend
