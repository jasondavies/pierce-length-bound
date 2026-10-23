/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendChartSection
public import PierceLengthBound.FixedDividendLeadingComponents

/-!
# Homogeneous equations in the actual affine chart

The chart homomorphism sends the homogenizing variable to the infinity equation
and every affine variable to its degree-one chart coordinate. Homogenizations of
members of the affine component ideal vanish under this homomorphism.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

lemma radialMap_natDegree_le {K : Type*} [CommRing K]
    (f : MvPolynomial (Fin 3) K) : (radialMap f).natDegree ≤ f.totalDegree := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [radialMap_coeff_eq_homogeneousComponent]
  exact homogeneousComponent_eq_zero n f hn

/-- The normalized degree-one coordinate in an affine chart. -/
def chartNode {K F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial (Fin 3) K)) (ι : (MvPolynomial (Fin 3) K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial (Fin 3) K ⧸ I) (j : Fin 3) : projectiveChart I ι l :=
  chartMonomialMap I ι l 1 ⟨Ideal.Quotient.mk I (X j),
    ⟨X j, by simp [mem_restrictTotalDegree], rfl⟩⟩

@[simp] lemma chartNode_val {K F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial (Fin 3) K)) (ι : (MvPolynomial (Fin 3) K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial (Fin 3) K ⧸ I) (j : Fin 3) :
    (chartNode I ι l j : F) = ι (Ideal.Quotient.mk I (X j)) * (ι l)⁻¹ := by
  simp only [chartNode, chartMonomialMap_val, pow_one]

/-- Evaluation of homogeneous coordinates in the concrete chart ring. -/
def chartHomogeneousMap {K F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial (Fin 3) K)) (ι : (MvPolynomial (Fin 3) K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial (Fin 3) K ⧸ I) :
    Polynomial (MvPolynomial (Fin 3) K) →+* projectiveChart I ι l :=
  Polynomial.eval₂RingHom (MvPolynomial.aeval (chartNode I ι l)).toRingHom
    (chartInfinityCoordinate I ι l)

@[simp] lemma chartHomogeneousMap_X {K F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial (Fin 3) K)) (ι : (MvPolynomial (Fin 3) K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial (Fin 3) K ⧸ I) :
    chartHomogeneousMap I ι l Polynomial.X = chartInfinityCoordinate I ι l := by
  simp [chartHomogeneousMap]

/-- Undoing the radial scaling recovers evaluation in the affine quotient. -/
lemma chart_radial_evaluation {K F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial (Fin 3) K)) (ι : (MvPolynomial (Fin 3) K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial (Fin 3) K ⧸ I) (hl : ι l ≠ 0)
    (f : MvPolynomial (Fin 3) K) :
    Polynomial.eval₂
      ((projectiveChart I ι l).subtype.comp
        (MvPolynomial.aeval (chartNode I ι l)).toRingHom)
      (ι l) (radialMap f) = ι (Ideal.Quotient.mk I f) := by
  let c : MvPolynomial (Fin 3) K →+* F := (projectiveChart I ι l).subtype.comp
    (MvPolynomial.aeval (chartNode I ι l)).toRingHom
  have he : (Polynomial.eval₂RingHom c (ι l)).comp radialMap =
      ι.toRingHom.comp (Ideal.Quotient.mk I) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, radialMap_C, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C]
      dsimp [c]
      simp only [MvPolynomial.aeval_C]
      change algebraMap K F a = ι (algebraMap K _ a)
      exact (ι.commutes a).symm
    · intro j
      simp only [RingHom.comp_apply, radialMap_X, map_mul,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]
      dsimp [c]
      simp only [MvPolynomial.aeval_X]
      change (chartNode I ι l j : F) * ι l = _
      rw [chartNode_val]
      field_simp
  exact RingHom.congr_fun he f

/-- The actual chart map annihilates the bounded homogenization of every member
of the affine component ideal. -/
theorem chartHomogeneousMap_homogenize_eq_zero {K F : Type*}
    [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial (Fin 3) K)) (ι : (MvPolynomial (Fin 3) K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial (Fin 3) K ⧸ I) (hl : ι l ≠ 0)
    {f : MvPolynomial (Fin 3) K} {n : ℕ} (hf : f ∈ I) (hdeg : f.totalDegree ≤ n) :
    chartHomogeneousMap I ι l (curveHomogenize n f) = 0 := by
  apply Subtype.ext
  change (projectiveChart I ι l).subtype
    (Polynomial.eval₂ (MvPolynomial.aeval (chartNode I ι l)).toRingHom
      (chartInfinityCoordinate I ι l) ((radialMap f).reflect n)) = 0
  rw [Polynomial.hom_eval₂]
  change Polynomial.eval₂
    ((projectiveChart I ι l).subtype.comp
      (MvPolynomial.aeval (chartNode I ι l)).toRingHom)
    (ι l)⁻¹ ((radialMap f).reflect n) = 0
  let := invertibleOfNonzero hl
  rw [← invOf_eq_inv]
  rw [Polynomial.eval₂_reflect_eq_zero_iff _ _ _ _ ((radialMap_natDegree_le f).trans hdeg)]
  rw [chart_radial_evaluation I ι l hl,
    Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]

/-- The chart coordinate used for dehomogenization is normalized to one. -/
lemma chartNode_first_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F]
    (I : Ideal (MvPolynomial (Fin 3) K)) (ι : (MvPolynomial (Fin 3) K ⧸ I) →ₐ[K] F)
    (hl : ι (Ideal.Quotient.mk I (X 0)) ≠ 0) :
    chartNode I ι (Ideal.Quotient.mk I (X 0)) 0 = 1 := by
  apply Subtype.ext
  simpa only [chartNode_val, OneMemClass.coe_one] using mul_inv_cancel₀ hl

end
end PierceLengthBound.FixedDividend
