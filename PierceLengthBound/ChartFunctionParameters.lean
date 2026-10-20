/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FunctionParameterChange
public import PierceLengthBound.ChartFunctionField
public import PierceLengthBound.ChartParameterTranscendence

/-! Every transcendental rational function on an actual nonexceptional curve
is a finite parameter. This supplies the finiteness input for comparing its
normalized zero and pole fibers. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open scoped IntermediateField

theorem nonexceptional_function_finite
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ) (ha : a ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : curveQuadratic ρ u v ρ' u' v' ∈ I)
    (hg : curveEquation ρ u v ρ' u' v' A a ∈ I)
    {F : Type*} [Field F] [Algebra ℚ F]
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι)
    (hfrac : ∀ z : F, ∃ r s : MvPolynomial (Fin 3) ℚ ⧸ I, z = ι r / ι s)
    {d N : ℕ} {b : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b)
    (x : F) (hx : Transcendental ℚ x) : FiniteDimensional ℚ⟮x⟯ F := by
  let l := Ideal.Quotient.mk I (MvPolynomial.X 0)
  let S := projectiveChart I ι l
  obtain ⟨M, hs⟩ := rational_nonexceptional_eventual_first_node_generation hρ hu hv hne
    ρ' u' v' A a ha I hf hg
  have hl : ι l ≠ 0 := by
    intro hz
    apply first_node_ne_zero_of_generation I hd hdegree hs
    exact hι (by simpa using hz)
  let : IsFractionRing S F := projectiveChart_isFractionRing I ι l hl hfrac
  let : Module.Finite (Algebra.adjoin ℚ {chartInfinityCoordinate I ι l}) S :=
    nonexceptional_chart_finite_over_parameter hρ hu hv hne ρ' u' v' A a ha
      I hf hg ι hι hd hdegree
  have hw := nonexceptional_chart_parameter_transcendental hρ hu hv hne ρ' u' v' A a ha
    I hf hg ι hι hd hdegree
  exact finite_fraction_field_over_function (chartInfinityCoordinate I ι l) hw x hx

end
end PierceLengthBound.FixedDividend
