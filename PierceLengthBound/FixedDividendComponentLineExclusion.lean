/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendDegreeOne

/-!
# Excluding degree-one components at actual orbit points

The abstract Hilbert-degree-one line theorem is connected to the explicit
quadratic and resultant restrictions used by the orbit line-exclusion theorem.
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

/-- A Hilbert-degree-one prime containing both equations supplies precisely the
polynomial line identities ruled out by the orbit estimates. -/
theorem degree_one_component_gives_contained_line {K : Type*} [Field K] [IsAlgClosed K]
    (ρ u v ρ' u' v' A a : K) (p : Ideal (MvPolynomial (Fin 3) K)) [p.IsPrime]
    (hp : p.height = 2)
    (hdegree : ∃ N : ℕ, ∃ b : ℤ, ∀ n ≥ N,
      (Module.finrank K (filteredCoordinateSpace p n) : ℤ) = n + b)
    (hf : curveQuadratic ρ u v ρ' u' v' ∈ p)
    (hg : curveEquation ρ u v ρ' u' v' A a ∈ p)
    (x : Fin 3 → K) (hx : x ∈ coordinateZeroLocus p) :
    ∃ z : Fin 3 → K, (∃ j, z j ≠ 0) ∧
      affineQuadratic ρ u v ρ' u' v' x z = 0 ∧
      C A * affineResultant ρ u v ρ' u' v' x z =
        C a * affineNorm ρ u v ρ' u' v' x z ^ 4 := by
  obtain ⟨z, hz, hline⟩ := degree_one_line_through_point p hp hdegree x hx
  have hq : affineRestriction x z (curveQuadratic ρ u v ρ' u' v') = 0 := hline _ hf
  have he : affineRestriction x z (curveEquation ρ u v ρ' u' v' A a) = 0 := hline _ hg
  rw [affineRestriction_quadratic] at hq
  simp only [curveEquation, map_sub, map_mul, map_pow,
    affineRestriction_resultant, affineRestriction_norm] at he
  simp only [affineRestriction, MvPolynomial.aeval_C, Polynomial.algebraMap_eq] at he
  exact ⟨z, hz, hq, sub_eq_zero.mp he⟩

/-- A prime component through a large-scale actual orbit point cannot have
Hilbert degree one. -/
theorem orbit_component_not_degree_one {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    {H X₀ : ℤ} (hX : 1 ≤ X₀) (hgaps : ∀ m < 5, kq a b (i + m) ≤ H)
    (hU : |U1z a b i| ≤ X₀) (hV : |U2z a b i| ≤ X₀)
    (hscale : (a : ℤ) * H ^ 5 * (24 * X₀ + 464) < (qq a b i : ℤ) ^ 4)
    (p : Ideal (MvPolynomial (Fin 3) ℂ)) [p.IsPrime] (hp : p.height = 2)
    (hf : curveQuadratic (patternRho a b i : ℂ) (patternU a b i : ℂ) (patternV a b i : ℂ)
      (patternRho a b (i + 1) : ℂ) (patternU a b (i + 1) : ℂ)
      (patternV a b (i + 1) : ℂ) ∈ p)
    (he : curveEquation (patternRho a b i : ℂ) (patternU a b i : ℂ) (patternV a b i : ℂ)
      (patternRho a b (i + 1) : ℂ) (patternU a b (i + 1) : ℂ)
      (patternV a b (i + 1) : ℂ) (Lz a b i : ℂ) (a : ℂ) ∈ p)
    (hx : (fun j => (orbitFreeNodes a b i j : ℂ)) ∈ coordinateZeroLocus p) :
    ¬ ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank ℂ (filteredCoordinateSpace p n) : ℤ) = n + c := by
  intro hdegree
  obtain ⟨z, hz, hq, hresultant⟩ := degree_one_component_gives_contained_line
    (patternRho a b i : ℂ) (patternU a b i : ℂ) (patternV a b i : ℂ)
    (patternRho a b (i + 1) : ℂ) (patternU a b (i + 1) : ℂ)
    (patternV a b (i + 1) : ℂ) (Lz a b i : ℂ) (a : ℂ) p hp hdegree hf he _ hx
  exact orbit_no_complex_line hba hi hX hgaps hU hV hscale z hz hq hresultant

end
end PierceLengthBound.FixedDividend
