/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendRationalChartResultant
public import PierceLengthBound.FixedDividendConicInfinity
public import PierceLengthBound.FixedDividendLocalizationParity
public import PierceLengthBound.FixedDividendLocalParity
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Unique infinity point of actual rational nonexceptional conics

The actual rational infinity-section algebra has dimension two and a nonzero
norm residue killed by every complex character. Thus all its complex residue
points coincide, without a geometric irreducibility or descent assumption.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- A rational degree-two component of the actual nonexceptional equations has
at most one complex point in its complete infinity section. -/
theorem rational_nonexceptional_conic_unique_infinity
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ)
    (hA : A ≠ 0) (ha : a ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : curveQuadratic (ρ : ℚ) u v ρ' u' v' ∈ I)
    (hg : curveEquation (ρ : ℚ) u v ρ' u' v' A a ∈ I)
    {F : Type*} [Field F] [Algebra ℚ F]
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι)
    {N : ℕ} {b : ℤ}
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = 2 * n + b) :
    Subsingleton ((projectiveChart I ι (Ideal.Quotient.mk I (X 0)) ⧸
      chartInfinityIdeal I ι (Ideal.Quotient.mk I (X 0))) →ₐ[ℚ] ℂ) := by
  have hd : 0 < (2 : ℕ) := by decide
  let l := Ideal.Quotient.mk I (X 0)
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
  have hdim' : Module.finrank ℚ (R ⧸ Ideal.span {w}) = 2 := hdim
  have hr : IsUnit (Ideal.Quotient.mk (Ideal.span {w}) r) :=
    rational_nonexceptional_chart_resultant_unit hρ hu hv hne ρ' u' v' A a ha
      I hf hg ι hι hd hdegree
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
  constructor
  intro ψ χ
  exact square_fourth_two_dimensional_unique_closed_character
    (huC A hA) (huC a ha) hw hdim' hr heq ψ χ

end
end PierceLengthBound.FixedDividend
