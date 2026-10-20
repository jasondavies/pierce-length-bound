/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendChartHomogenization

/-!
# Coordinate generators of the actual chart

The homogenized coordinate map surjects onto the concrete first-node chart.
Modulo infinity the degree-one normalized nodes generate the entire section.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

lemma chartHomogeneousMap_homogenize_value {K F : Type*}
    [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial (Fin 3) K)) (ι : (MvPolynomial (Fin 3) K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial (Fin 3) K ⧸ I) (hl : ι l ≠ 0)
    (f : MvPolynomial (Fin 3) K) {n : ℕ} (hdeg : f.totalDegree ≤ n) :
    (chartHomogeneousMap I ι l (curveHomogenize n f) : F) =
      ι (Ideal.Quotient.mk I f) * (ι l)⁻¹ ^ n := by
  let := invertibleOfNonzero hl
  have he := Polynomial.eval₂_reflect_mul_pow
    ((projectiveChart I ι l).subtype.comp
      (MvPolynomial.aeval (chartNode I ι l)).toRingHom)
    (ι l) n (radialMap f) ((radialMap_natDegree_le f).trans hdeg)
  rw [invOf_eq_inv, chart_radial_evaluation I ι l hl] at he
  change (projectiveChart I ι l).subtype
    (Polynomial.eval₂ (MvPolynomial.aeval (chartNode I ι l)).toRingHom
      (chartInfinityCoordinate I ι l) ((radialMap f).reflect n)) = _
  rw [Polynomial.hom_eval₂]
  change Polynomial.eval₂ _ (ι l)⁻¹ ((radialMap f).reflect n) = _
  apply (mul_left_inj' (pow_ne_zero n hl)).mp
  rw [he]
  simp only [mul_assoc, ← mul_pow, inv_mul_cancel₀ hl, one_pow, mul_one]

/-- Every element of the concrete chart is represented by a homogeneous polynomial. -/
theorem chartHomogeneousMap_surjective {K F : Type*}
    [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial (Fin 3) K)) (ι : (MvPolynomial (Fin 3) K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial (Fin 3) K ⧸ I) (hl : l ∈ filteredCoordinateSpace I 1)
    (hl0 : ι l ≠ 0) : Function.Surjective (chartHomogeneousMap I ι l) := by
  intro g
  obtain ⟨n, a, ha, hag⟩ := (mem_projectiveChart_iff I ι l hl hl0 (g : F)).mp g.property
  obtain ⟨f, hf, rfl⟩ := ha
  have hdeg : f.totalDegree ≤ n := (mem_restrictTotalDegree _ _ _).mp hf
  refine ⟨curveHomogenize n f, ?_⟩
  apply Subtype.ext
  rw [chartHomogeneousMap_homogenize_value I ι l hl0 f hdeg]
  exact hag

/-- The degree-one chart nodes generate its full infinity-section algebra. -/
theorem chart_nodes_generate_infinity {K F : Type*}
    [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial (Fin 3) K)) (ι : (MvPolynomial (Fin 3) K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial (Fin 3) K ⧸ I) (hl : l ∈ filteredCoordinateSpace I 1)
    (hl0 : ι l ≠ 0) :
    Function.Surjective (MvPolynomial.aeval (R := K) (fun j =>
      Ideal.Quotient.mk (chartInfinityIdeal I ι l) (chartNode I ι l j))) := by
  let q := Ideal.Quotient.mkₐ K (chartInfinityIdeal I ι l)
  intro x
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨p, rfl⟩ := chartHomogeneousMap_surjective I ι l hl hl0 g
  refine ⟨p.eval 0, ?_⟩
  have hw : q (chartInfinityCoordinate I ι l) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hc : q.comp (MvPolynomial.aeval (chartNode I ι l)) =
      MvPolynomial.aeval (fun j => q (chartNode I ι l j)) := by ext; simp
  change _ = q.toRingHom (Polynomial.eval₂ _ _ p)
  rw [Polynomial.hom_eval₂]
  change _ = Polynomial.eval₂ (q.comp (MvPolynomial.aeval (chartNode I ι l))).toRingHom
    (q (chartInfinityCoordinate I ι l)) p
  rw [hw, hc, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero]
  rfl


/-- Reduction modulo infinity is evaluation of the leading homogeneous form
at the normalized node residues. -/
lemma chart_infinity_evaluation {K F : Type*}
    [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial (Fin 3) K)) (ι : (MvPolynomial (Fin 3) K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial (Fin 3) K ⧸ I)
    (p : Polynomial (MvPolynomial (Fin 3) K)) :
    Ideal.Quotient.mk (chartInfinityIdeal I ι l) (chartHomogeneousMap I ι l p) =
      MvPolynomial.aeval (fun j => Ideal.Quotient.mk (chartInfinityIdeal I ι l)
        (chartNode I ι l j)) (p.eval 0) := by
  let q := Ideal.Quotient.mkₐ K (chartInfinityIdeal I ι l)
  have hw : q (chartInfinityCoordinate I ι l) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hc : q.comp (MvPolynomial.aeval (chartNode I ι l)) =
      MvPolynomial.aeval (fun j => q (chartNode I ι l j)) := by ext; simp
  change q.toRingHom (Polynomial.eval₂ _ _ p) = _
  rw [Polynomial.hom_eval₂]
  change Polynomial.eval₂ (q.comp (MvPolynomial.aeval (chartNode I ι l))).toRingHom
    (q (chartInfinityCoordinate I ι l)) p = _
  rw [hw, hc, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero]
  rfl

end
end PierceLengthBound.FixedDividend
