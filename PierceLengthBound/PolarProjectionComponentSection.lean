/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.PolarProjectionSectionComparison
public import PierceLengthBound.PolarProjectionSectionCoordinates

/-! The actual component section is a quotient of the explicit smooth
quadratic section. Only the coordinate reconstruction and its origin need
to be supplied when choosing either coordinate-axis hyperplane. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
open MvPolynomial Matrix
noncomputable section

set_option synthInstance.maxHeartbeats 200000 in
-- Source and target are localizations of different polynomial quotients over the same field.
set_option maxHeartbeats 800000 in
-- Elaborating the quotient and localization scalar towers dominates the argument.
/-- The local section of any component through the base point is a
surjective image of the explicit smooth section, and its fixed-dividend
equation is killed by this map. -/
theorem polar_component_section_surjection
    {K R S D : Type*} [Field K] (ρ u v ρ' u' v' A b s t : K)
    (hG : (polarMatrix ρ u v).det ≠ 0)
    (I : Ideal (MvPolynomial (Fin 3) K))
    (hq : curveQuadratic ρ u v ρ' u' v' ∈ I)
    (hg : curveEquation ρ u v ρ' u' v' A b ∈ I)
    (hz : (let z := polarBasePoint ρ u v ρ' u' v'
      ![z 0, z 0 + z 1, z 0 + z 1 + z 2]) ∈ coordinateZeroLocus I)
    [CommRing R] [Algebra K R] [Algebra (MvPolynomial (Fin 3) K ⧸ I) R]
    [IsScalarTower K (MvPolynomial (Fin 3) K ⧸ I) R]
    [IsLocalization.AtPrime R (RingHom.ker (coordinatePoint I _ hz).toRingHom)]
    [CommRing S] [Algebra K S]
    [Algebra (MvPolynomial (Fin 2) K ⧸ polarSectionIdeal ρ u v ρ' u' v' s t) S]
    [IsScalarTower K (MvPolynomial (Fin 2) K ⧸ polarSectionIdeal ρ u v ρ' u' v' s t) S]
    [IsLocalization.AtPrime S (polarSectionBaseIdeal ρ u v ρ' u' v' s t)]
    [CommRing D] [IsLocalRing D] [Algebra K D]
    (γ : R →ₐ[K] D) (hγ : Function.Surjective γ) (δ : D →ₐ[K] K)
    (η : MvPolynomial (Fin 2) K →ₐ[K] D)
    (hδ : ∀ j, δ (η (X j)) = 0)
    (hη : ∀ f, η (polarSectionMap (polarBasePoint ρ u v ρ' u' v') s t f) =
      γ (algebraMap (MvPolynomial (Fin 3) K ⧸ I) R (Ideal.Quotient.mk I f))) :
    ∃ φ : S →ₐ[K] D, Function.Surjective φ ∧
      φ (algebraMap _ S (Ideal.Quotient.mk (polarSectionIdeal ρ u v ρ' u' v' s t)
        (polarSectionMap (polarBasePoint ρ u v ρ' u' v') s t
          (curveEquation ρ u v ρ' u' v' A b)))) = 0 := by
  let z := polarBasePoint ρ u v ρ' u' v'
  let c := polarSectionCoefficients ρ u v ρ' u' v' s t
  let J := polarSectionIdeal ρ u v ρ' u' v' s t
  let B := MvPolynomial (Fin 3) K ⧸ I
  have hquot (f : MvPolynomial (Fin 3) K) (hf : f ∈ I) :
      γ (algebraMap B R (Ideal.Quotient.mk I f)) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero, map_zero]
  have hqη : η (smoothSectionQuadric (c 0) (c 1) (c 2) (c 3) (c 4)) = 0 := by
    rw [← polarSectionMap_quadric ρ u v ρ' u' v' s t hG, hη]
    exact hquot _ hq
  obtain ⟨τ, hτ, hpointτ⟩ := smoothSection_factor
    (c 0) (c 1) (c 2) (c 3) (c 4) η hqη δ hδ
  let θ : MvPolynomial (Fin 3) K →ₐ[K] (MvPolynomial (Fin 2) K ⧸ J) :=
    (Ideal.Quotient.mkₐ K J).comp (polarSectionMap z s t)
  have hpointθ (f : MvPolynomial (Fin 3) K) :
      polarSectionPoint ρ u v ρ' u' v' s t (θ f) = eval ![z 0, z 0 + z 1, z 0 + z 1 + z 2] f := by
    change eval 0 (polarSectionMap z s t f) = _
    exact polarSectionMap_eval_origin z s t f
  have hdiagram (f : MvPolynomial (Fin 3) K) :
      τ (θ f) = γ (algebraMap B R (Ideal.Quotient.mk I f)) := by
    change τ (Ideal.Quotient.mk J (polarSectionMap z s t f)) = _
    rw [hτ]
    exact hη f
  let : IsLocalization.AtPrime S
      (RingHom.ker (polarSectionPoint ρ u v ρ' u' v' s t).toRingHom) := by
    change IsLocalization.AtPrime S (polarSectionBaseIdeal ρ u v ρ' u' v' s t)
    infer_instance
  obtain ⟨φ, hφ, hφmap⟩ := local_coordinate_section_surjection (S := S)
    (polarSectionPoint ρ u v ρ' u' v' s t) I _ hz γ hγ δ θ τ hpointθ hpointτ hdiagram
  refine ⟨φ, hφ, ?_⟩
  rw [hφmap, hτ, hη]
  exact hquot _ hg

end
end PierceLengthBound.FixedDividend
