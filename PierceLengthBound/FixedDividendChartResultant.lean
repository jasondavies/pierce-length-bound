/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendChart
public import PierceLengthBound.FixedDividendCoefficientHomogenization
public import PierceLengthBound.FixedDividendRationalCurves

/-!
# The resultant is invertible along the infinity section

The finite chart section has only nonexceptional infinity directions as residue
points. Its homogenized resultant is therefore a unit, including at nonreduced
points of this section.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

/-- The homogenized resultant is a unit modulo the infinity equation in the
first-node chart of every positive-degree prime nonexceptional component. -/
theorem nonexceptional_chart_resultant_unit
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ) (ha : a ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℚ)) [I.IsPrime]
    (hf : curveQuadratic (ρ : ℚ) u v ρ' u' v' ∈ I)
    (hg : curveEquation (ρ : ℚ) u v ρ' u' v' A a ∈ I)
    {F : Type*} [Field F] [Algebra ℚ F]
    (ι : (MvPolynomial (Fin 3) ℚ ⧸ I) →ₐ[ℚ] F) (hι : Function.Injective ι)
    {d N : ℕ} {b : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b) :
    IsUnit (Ideal.Quotient.mk (chartInfinityIdeal I ι (Ideal.Quotient.mk I (X 0)))
      (chartHomogeneousMap I ι (Ideal.Quotient.mk I (X 0))
        (curveHomogenize 10 (curveResultant (ρ : ℚ) u v ρ' u' v')))) := by
  let l := Ideal.Quotient.mk I (X 0)
  obtain ⟨hl, M, hs⟩ := nonexceptional_first_node_generation
    hρ hu hv hne ρ' u' v' A a ha I hf hg ι hι hd hdegree
  have hfin := (nonexceptional_chart_infinity_dimension hρ hu hv hne
    ρ' u' v' A a ha I hf hg ι hι hd hdegree).1
  let q := Ideal.Quotient.mkₐ ℚ (chartInfinityIdeal I ι l)
  apply finite_algebra_isUnit_of_closed_points (K := ℚ) (L := ℂ)
  intro φ
  let ψ : projectiveChart I ι l →ₐ[ℚ] ℂ := φ.comp q
  have hw : ψ (chartInfinityCoordinate I ι l) = 0 := by
    change φ (Ideal.Quotient.mk _ _) = 0
    have hm : chartInfinityCoordinate I ι l ∈ chartInfinityIdeal I ι l :=
      Ideal.subset_span (Set.mem_singleton _)
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm, map_zero]
  have hz : ∃ j, ψ (chartNode I ι l j) ≠ 0 := by
    refine ⟨0, ?_⟩
    rw [chartNode_first_eq_one I ι hl, map_one]
    exact one_ne_zero
  have hq := chartHomogeneousMap_homogenize_eq_zero I ι l hl hf
    (curveQuadratic_degree_le_two _ _ _ _ _ _)
  have he := chartHomogeneousMap_homogenize_eq_zero I ι l hl hg
    (curveEquation_degree_le _ _ _ _ _ _ _ _)
  have hq0 := congrArg ψ hq
  have he0 := congrArg ψ he
  rw [chartHomogeneousMap_closed_residue I ι l ψ hw, map_zero] at hq0 he0
  change ψ (chartHomogeneousMap I ι l _) ≠ 0
  rw [chartHomogeneousMap_closed_residue I ι l ψ hw]
  simp only [map_curveHomogenize, map_curveQuadratic, map_curveEquation] at hq0 he0
  rw [map_curveHomogenize, map_curveResultant]
  have hqC := hq0
  have heC := he0
  simp only [eq_ratCast, ← Complex.ofReal_ratCast] at hqC heC ⊢
  exact nonexceptional_resultant_at_infinity_ne_zero
    (by exact_mod_cast hρ) (by exact_mod_cast hu) (by exact_mod_cast hv) hne
    (ρ' : ℂ) u' v' A a (by exact_mod_cast ha) _ hz hqC heC

end
end PierceLengthBound.FixedDividend
