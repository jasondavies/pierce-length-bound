/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendCoprimality

/-!
# Restricting the fixed-dividend equations to affine lines

The explicit quadratic, norm and resultant restrictions to an affine line used by
the orbit line-exclusion theorem.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

/-- Restriction of a coordinate-ring polynomial to an affine line. -/
def affineRestriction {K : Type*} [CommRing K] (x z : Fin 3 → K) :
    MvPolynomial (Fin 3) K →ₐ[K] Polynomial K :=
  MvPolynomial.aeval (fun k => C (x k) + C (z k) * X)

lemma affineRestriction_quadratic {K : Type*} [CommRing K]
    (ρ u v ρ' u' v' : K) (x z : Fin 3 → K) :
    affineRestriction x z (curveQuadratic ρ u v ρ' u' v') =
      affineQuadratic ρ u v ρ' u' v' x z := by
  change (affineRestriction x z).toRingHom (curveQuadratic ρ u v ρ' u' v') = _
  rw [curveQuadratic, map_lineQuadratic]
  simp [affineRestriction, affineQuadratic]

lemma affineRestriction_norm {K : Type*} [CommRing K]
    (ρ u v ρ' u' v' : K) (x z : Fin 3 → K) :
    affineRestriction x z (curveNorm ρ u v ρ' u' v') =
      affineNorm ρ u v ρ' u' v' x z := by
  change (affineRestriction x z).toRingHom (curveNorm ρ u v ρ' u' v') = _
  rw [curveNorm, map_lineNorm]
  simp [affineRestriction, affineNorm]

lemma affineRestriction_resultant {K : Type*} [CommRing K]
    (ρ u v ρ' u' v' : K) (x z : Fin 3 → K) :
    affineRestriction x z (curveResultant ρ u v ρ' u' v') =
      affineResultant ρ u v ρ' u' v' x z := by
  let ψ := (affineRestriction x z).toRingHom
  have hn : ψ ∘ completeNodes (MvPolynomial.C ρ) (MvPolynomial.C u)
      (MvPolynomial.C v) MvPolynomial.X =
      affineNodes (completeNodes ρ u v x) (completeNodes ρ u v z) := by
    funext j
    fin_cases j <;> simp [ψ, affineRestriction, completeNodes, fourthNode, affineNodes]
    ring
  have hc (r s w : K) :
      ψ ∘ (fun j : Fin 4 => MvPolynomial.C (coeffs r s w j.castSucc)) =
        (fun j : Fin 4 => C (coeffs r s w j.castSucc)) := by
    funext j
    simp [ψ, affineRestriction]
  change ψ (curveResultant ρ u v ρ' u' v') = _
  unfold curveResultant affineResultant
  rw [← resultant_map_map, Polynomial.map_mul, Polynomial.map_X,
    map_firstNewtonQuartic, map_nextNewtonQuartic, hn, hc, hc]

end
end PierceLengthBound.FixedDividend
