/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.ChartParameterTranscendence
public import PierceLengthBound.CurveNormalization
public import PierceLengthBound.NormalizationBranches

/-! The actual infinity chart has a finite normalization which is a Dedekind
domain, including when the original curve and chart are singular. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section

abbrev chartNormalization {K σ F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial σ K)) (ι : (MvPolynomial σ K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial σ K ⧸ I) :=
  integralClosure (projectiveChart I ι l) (FractionRing (projectiveChart I ι l))

theorem nonexceptional_chart_normalization
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ) (ha : a ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℚ))
    (hf : curveQuadratic ρ u v ρ' u' v' ∈ I)
    (hg : curveEquation ρ u v ρ' u' v' A a ∈ I)
    {F : Type*} [Field F] [Algebra ℚ F]
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι)
    {d N : ℕ} {b : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b) :
    IsDedekindDomain (chartNormalization I ι (Ideal.Quotient.mk I (MvPolynomial.X 0))) ∧
      Module.Finite (projectiveChart I ι (Ideal.Quotient.mk I (MvPolynomial.X 0)))
        (chartNormalization I ι (Ideal.Quotient.mk I (MvPolynomial.X 0))) := by
  let : Module.Finite
      (Algebra.adjoin ℚ {chartInfinityCoordinate I ι (Ideal.Quotient.mk I (MvPolynomial.X 0))})
      (projectiveChart I ι (Ideal.Quotient.mk I (MvPolynomial.X 0))) :=
    nonexceptional_chart_finite_over_parameter hρ hu hv hne ρ' u' v' A a ha
      I hf hg ι hι hd hdegree
  exact finite_parameter_normalization _
    (nonexceptional_chart_parameter_transcendental hρ hu hv hne ρ' u' v' A a ha
      I hf hg ι hι hd hdegree) _

/-- The actual positive-degree infinity fiber has a branch in its normalization. -/
theorem nonexceptional_chart_infinity_branch
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
    ∃ p : IsDedekindDomain.HeightOneSpectrum (chartNormalization I ι l),
      algebraMap (projectiveChart I ι l) (chartNormalization I ι l)
        (chartInfinityCoordinate I ι l) ∈ p.asIdeal := by
  let l := Ideal.Quotient.mk I (MvPolynomial.X 0)
  obtain ⟨M, hs⟩ := rational_nonexceptional_eventual_first_node_generation
    hρ hu hv hne ρ' u' v' A a ha I hf hg
  have hl : ι l ≠ 0 := by
    intro hz
    apply first_node_ne_zero_of_generation I hd hdegree hs
    exact hι (by simpa using hz)
  have hw : chartInfinityCoordinate I ι l ≠ 0 := by
    intro hz
    exact inv_ne_zero hl (congrArg (fun r : projectiveChart I ι l => (r : F)) hz)
  apply normalization_branch_exists_of_fiber_dimension (K := ℚ) _ hw
  have hdim := (rational_nonexceptional_chart_infinity_dimension hρ hu hv hne
    ρ' u' v' A a ha I hf hg ι hι hd hdegree).2
  exact hdim.symm ▸ hd

end
end PierceLengthBound.FixedDividend
