/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendChartHomogenization
public import PierceLengthBound.FixedDividendFiniteResidues

/-!
# The resultant is invertible along the actual infinity section

The finite chart section has only nonexceptional infinity directions as residue
points. Its homogenized resultant is therefore a unit, including at nonreduced
points of this section.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

lemma chartHomogeneousMap_residue {K F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial (Fin 3) K)) (ι : (MvPolynomial (Fin 3) K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial (Fin 3) K ⧸ I) (ψ : projectiveChart I ι l →ₐ[K] K)
    (hw : ψ (chartInfinityCoordinate I ι l) = 0)
    (p : Polynomial (MvPolynomial (Fin 3) K)) :
    ψ (chartHomogeneousMap I ι l p) =
      eval (fun j => ψ (chartNode I ι l j)) (p.eval 0) := by
  have hc : ψ.toRingHom.comp (MvPolynomial.aeval (chartNode I ι l)).toRingHom =
      eval (fun j => ψ (chartNode I ι l j)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [eval_C]
      change ψ (MvPolynomial.aeval (chartNode I ι l) (C c)) = c
      rw [aeval_C]
      simp
    · intro j
      simp
  change ψ.toRingHom (Polynomial.eval₂ _ _ p) = _
  change ψ.toRingHom (chartInfinityCoordinate I ι l) = 0 at hw
  rw [Polynomial.hom_eval₂, hw, hc]
  simp only [Polynomial.eval₂_at_zero, ← Polynomial.coeff_zero_eq_eval_zero]

/-- The homogenized resultant is a unit modulo the infinity equation in the
actual first-node chart of every positive-degree nonexceptional component. -/
theorem nonexceptional_chart_resultant_unit
    {ρ u v : ℝ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern ρ u v) (ρ' u' v' A a : ℂ) (ha : a ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) ℂ)) [I.IsPrime]
    (hf : curveQuadratic (ρ : ℂ) u v ρ' u' v' ∈ I)
    (hg : curveEquation (ρ : ℂ) u v ρ' u' v' A a ∈ I)
    {F : Type*} [Field F] [Algebra ℂ F]
    (ι : (MvPolynomial (Fin 3) ℂ ⧸ I) →ₐ[ℂ] F) (hι : Function.Injective ι)
    {d N : ℕ} {b : ℤ} (hd : 0 < d)
    (hdegree : ∀ n ≥ N,
      (Module.finrank ℂ (filteredCoordinateSpace I n) : ℤ) = (d : ℤ) * n + b) :
    IsUnit (Ideal.Quotient.mk (chartInfinityIdeal I ι (Ideal.Quotient.mk I (X 0)))
      (chartHomogeneousMap I ι (Ideal.Quotient.mk I (X 0))
        (curveHomogenize 10 (curveResultant (ρ : ℂ) u v ρ' u' v')))) := by
  let l := Ideal.Quotient.mk I (X 0)
  obtain ⟨M, hs⟩ := nonexceptional_eventual_first_node_generation
    hρ hu hv hne ρ' u' v' A a ha I hf hg
  have hl : ι l ≠ 0 := by
    intro hh
    apply first_node_ne_zero_of_generation I hd hdegree hs
    exact hι (by simpa using hh)
  have hfin := (nonexceptional_chart_infinity_dimension hρ hu hv hne
    ρ' u' v' A a ha I hf hg ι hι hd hdegree).1
  let q := Ideal.Quotient.mkₐ ℂ (chartInfinityIdeal I ι l)
  apply finite_algebra_isUnit_of_points (K := ℂ)
  intro φ
  let ψ : projectiveChart I ι l →ₐ[ℂ] ℂ := φ.comp q
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
  rw [chartHomogeneousMap_residue I ι l ψ hw, map_zero] at hq0 he0
  change ψ (chartHomogeneousMap I ι l _) ≠ 0
  rw [chartHomogeneousMap_residue I ι l ψ hw]
  exact nonexceptional_resultant_at_infinity_ne_zero hρ hu hv hne
    ρ' u' v' A a ha _ hz hq0 he0

end
end PierceLengthBound.FixedDividend
