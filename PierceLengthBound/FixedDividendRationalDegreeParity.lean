/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendRationalChartResultant
public import PierceLengthBound.FixedDividendLocalizationParity
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Even Hilbert degree of actual nonexceptional components

The first-node chart captures the full infinity section, whose dimension equals
the affine Hilbert degree. Its resultant is invertible along infinity. After
localization, the actual homogeneous equation identifies a square principal
section with a fourth-power principal section, forcing the degree to be even.
No smoothness, normalization, local valuation, or projective degree hypothesis
is assumed.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- Every positive-degree rational component of the actual nonexceptional
fixed-dividend equations has even affine Hilbert degree. -/
theorem rational_nonexceptional_component_degree_even
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ)
    (hA : A ≠ 0) (ha : a ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : curveQuadratic (ρ : ℚ) u v ρ' u' v' ∈ I)
    (hg : curveEquation (ρ : ℚ) u v ρ' u' v' A a ∈ I)
    {d N : ℕ} {b : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b) :
    Even d := by
  let B := MvPolynomial (Fin 3) ℚ ⧸ I
  let F := FractionRing B
  let ι : B →ₐ[ℚ] F := IsScalarTower.toAlgHom ℚ B F
  have hι : Function.Injective ι := IsFractionRing.injective B F
  let l : B := Ideal.Quotient.mk I (X 0)
  let R := projectiveChart I ι l
  let w : R := chartInfinityCoordinate I ι l
  let φ := chartHomogeneousMap I ι l
  let r : R := φ (curveHomogenize 10 (curveResultant (ρ : ℚ) u v ρ' u' v'))
  obtain ⟨M, hs⟩ := rational_nonexceptional_eventual_first_node_generation
    hρ hu hv hne ρ' u' v' A a ha I hf hg
  have hl : ι l ≠ 0 := by
    intro hh
    apply first_node_ne_zero_of_generation I hd hdegree hs
    exact hι (by simpa using hh)
  obtain ⟨hfin, hdim⟩ := rational_nonexceptional_chart_infinity_dimension hρ hu hv hne
    ρ' u' v' A a ha I hf hg ι hι hd hdegree
  have hfin' : Module.Finite ℚ (R ⧸ Ideal.span {w}) := hfin
  have hdim' : Module.finrank ℚ (R ⧸ Ideal.span {w}) = d := hdim
  have hnontriv : Nontrivial (R ⧸ Ideal.span {w}) := by
    apply Module.nontrivial_of_finrank_pos (R := ℚ)
    simpa only [hdim'] using hd
  have hr : IsUnit (Ideal.Quotient.mk (Ideal.span {w}) r) :=
    rational_nonexceptional_chart_resultant_unit hρ hu hv hne ρ' u' v' A a ha
      I hf hg ι hι hd hdegree
  have hr0 : r ≠ 0 := by
    intro hh
    rw [hh, map_zero] at hr
    exact not_isUnit_zero hr
  have hw : w ≠ 0 := by
    intro hh
    have ht := congrArg (fun x : R => (x : F)) hh
    change (ι l)⁻¹ = 0 at ht
    exact (inv_ne_zero hl) ht
  have he := chartHomogeneousMap_homogenize_eq_zero I ι l hl hg
    (curveEquation_degree_le _ _ _ _ _ _ _ _)
  have huC (c : ℚ) (hc : c ≠ 0) : IsUnit (φ (Polynomial.C (C c))) :=
    ((isUnit_iff_ne_zero.mpr hc).map (Polynomial.C.comp (C : ℚ →+* MvPolynomial (Fin 3) ℚ))).map φ
  have heq : φ (Polynomial.C (C A)) * w ^ 2 * r =
      φ (Polynomial.C (C a)) *
        φ (curveHomogenize 3 (curveNorm (ρ : ℚ) u v ρ' u' v')) ^ 4 := by
    simpa only [φ, chartHomogeneousMap_X, w, r] using
      map_curveEquation_homogenize φ (ρ : ℚ) u v ρ' u' v' A a he
  have hp := finite_infinity_section_even_of_unit_modulo
    (huC A hA) (huC a ha) hr hr0 hw heq (K := ℚ)
  rwa [hdim'] at hp

end
end PierceLengthBound.FixedDividend
