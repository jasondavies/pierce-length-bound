/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendChartResultant
public import PierceLengthBound.FixedDividendRationalCurves

/-!
# Coefficient maps and residue fields for chart homogenization

Homogenization commutes with coefficient extension. Finite rational chart
sections can therefore be tested at complex residue points directly.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open MvPolynomial

lemma map_radialMap {K L : Type*} [CommRing K] [CommRing L]
    (c : K →+* L) (f : MvPolynomial (Fin 3) K) :
    (radialMap f).map (map c) = radialMap (map c f) := by
  have he : (Polynomial.mapRingHom (map c)).comp radialMap =
      radialMap.comp (map c) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro j
      simp
  exact RingHom.congr_fun he f

lemma map_curveHomogenize {K L : Type*} [CommRing K] [CommRing L]
    (c : K →+* L) (n : ℕ) (f : MvPolynomial (Fin 3) K) :
    (curveHomogenize n f).map (map c) = curveHomogenize n (map c f) := by
  rw [curveHomogenize, ← Polynomial.reflect_map, map_radialMap]
  rfl

/-- Points may be taken in any algebraically closed overfield of the base. -/
theorem finite_algebra_isUnit_of_closed_points {K L R : Type*}
    [Field K] [Field L] [IsAlgClosed L] [Algebra K L]
    [CommRing R] [Algebra K R] [Module.Finite K R] (r : R)
    (hr : ∀ φ : R →ₐ[K] L, φ r ≠ 0) : IsUnit r := by
  by_contra h
  obtain ⟨J, hJ, hrJ⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr h)
  let : J.IsMaximal := hJ
  let : Field (R ⧸ J) := Ideal.Quotient.field J
  have : Module.Finite K (R ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K J).toLinearMap
      Ideal.Quotient.mk_surjective
  let φ : (R ⧸ J) →ₐ[K] L := IsAlgClosed.lift
  apply hr (φ.comp (Ideal.Quotient.mkₐ K J))
  change φ (Ideal.Quotient.mk J r) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hrJ, map_zero]

/-- Chart residues evaluate the coefficient-extended homogeneous polynomial at
an infinity point. -/
lemma chartHomogeneousMap_closed_residue {K F L : Type*}
    [Field K] [Field F] [Algebra K F] [Field L] [Algebra K L]
    (I : Ideal (MvPolynomial (Fin 3) K)) (ι : (MvPolynomial (Fin 3) K ⧸ I) →ₐ[K] F)
    (l : MvPolynomial (Fin 3) K ⧸ I) (ψ : projectiveChart I ι l →ₐ[K] L)
    (hw : ψ (chartInfinityCoordinate I ι l) = 0)
    (p : Polynomial (MvPolynomial (Fin 3) K)) :
    ψ (chartHomogeneousMap I ι l p) =
      eval (fun j => ψ (chartNode I ι l j))
        ((p.map (map (algebraMap K L))).eval 0) := by
  have hc : ψ.toRingHom.comp (MvPolynomial.aeval (chartNode I ι l)).toRingHom =
      (eval (fun j => ψ (chartNode I ι l j))).comp (map (algebraMap K L)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, map_C, eval_C]
      change ψ (MvPolynomial.aeval (chartNode I ι l) (C c)) = algebraMap K L c
      rw [aeval_C]
      exact ψ.commutes c
    · intro j
      simp
  change ψ.toRingHom (Polynomial.eval₂ _ _ p) = _
  change ψ.toRingHom (chartInfinityCoordinate I ι l) = 0 at hw
  rw [Polynomial.hom_eval₂, hw, hc, Polynomial.eval₂_at_zero,
    Polynomial.eval_zero_map, ← Polynomial.coeff_zero_eq_eval_zero]
  rfl

end
end PierceLengthBound.FixedDividend
