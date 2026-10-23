/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendContainedLines
public import PierceLengthBound.FixedDividendDirectionExtraction

/-!
# Exclusion of arbitrary complex lines through orbit points

The direction classification reduces every contained complex line to a scalar
multiple of a normalized real direction. Injectivity of substitution transfers
its defining identities to the real line excluded by the gap estimates.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

lemma map_lineNorm {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (ρ u v ρ' u' v' a b c : R) :
    φ (lineNorm ρ u v ρ' u' v' a b c) =
      lineNorm (φ ρ) (φ u) (φ v) (φ ρ') (φ u') (φ v') (φ a) (φ b) (φ c) := by
  simp [lineNorm, lineNodes, extendedLineGaps, lineGaps, fourthNode, coeffs,
    Fin.sum_univ_succ, map_ofNat]

lemma map_lineQuadratic {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (ρ u v ρ' u' v' a b c : R) :
    φ (lineQuadratic ρ u v ρ' u' v' a b c) =
      lineQuadratic (φ ρ) (φ u) (φ v) (φ ρ') (φ u') (φ v') (φ a) (φ b) (φ c) := by
  simp [lineQuadratic, lineNodes, lineGaps, fourthNode, coeffs, Fin.sum_univ_succ]

lemma map_firstNewtonQuartic {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (c s : Fin 4 → R) :
    (firstNewtonQuartic c s).map φ = firstNewtonQuartic (φ ∘ c) (φ ∘ s) := by
  simp [firstNewtonQuartic]

lemma map_nextNewtonQuartic {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (c s : Fin 4 → R) :
    (nextNewtonQuartic c s).map φ = nextNewtonQuartic (φ ∘ c) (φ ∘ s) := by
  simp [nextNewtonQuartic]

/-- Inclusion of real coefficients followed by a nonzero complex parameter scaling. -/
def complexLineMap (t : ℂ) : ℝ[X] →+* ℂ[X] :=
  (compRingHom (C t * X)).comp (mapRingHom Complex.ofRealHom)

@[simp] lemma complexLineMap_C (t : ℂ) (r : ℝ) :
    complexLineMap t (C r) = C (r : ℂ) := by simp [complexLineMap]

@[simp] lemma complexLineMap_X (t : ℂ) : complexLineMap t X = C t * X := by
  simp [complexLineMap]

lemma complexLineMap_injective {t : ℂ} (ht : t ≠ 0) :
    Function.Injective (complexLineMap t) := by
  intro p q he
  ext n
  have hc := congrArg (fun p : ℂ[X] => p.coeff n) he
  simp only [complexLineMap, RingHom.comp_apply, coe_mapRingHom,
    coe_compRingHom_apply, comp_C_mul_X_coeff, coeff_map] at hc
  exact Complex.ofReal_injective (mul_right_cancel₀ (pow_ne_zero n ht) hc)

lemma complexLineMap_nodes (ρ u v : ℝ) (x : Fin 3 → ℝ) (z : Fin 3 → ℂ)
    (d : Fin 4) (t : ℂ)
    (hz : ∀ j, completeDirection (ρ : ℂ) (u : ℂ) (v : ℂ) z j =
      t * normalizedDirection d j) :
    complexLineMap t ∘ exceptionalNodes (completeNodes ρ u v x) d =
      affineNodes (completeNodes (ρ : ℂ) (u : ℂ) (v : ℂ) (fun j => (x j : ℂ)))
        (completeNodes (ρ : ℂ) (u : ℂ) (v : ℂ) z) := by
  have hn (j : Fin 4) :
      exceptionalNodes (completeNodes ρ u v x) d j =
        C (completeNodes ρ u v x j) + C (normalizedDirection d j.succ : ℝ) * X := by
    fin_cases d <;> fin_cases j <;>
      simp [exceptionalNodes, nodes03, nodes12, nodes23, nodes14, normalizedDirection]
  have hd (j : Fin 4) : completeNodes (ρ : ℂ) (u : ℂ) (v : ℂ) z j =
      completeDirection (ρ : ℂ) (u : ℂ) (v : ℂ) z j.succ := by
    fin_cases j <;> rfl
  have hc (j : Fin 4) : ((completeNodes ρ u v x j : ℝ) : ℂ) =
      completeNodes (ρ : ℂ) (u : ℂ) (v : ℂ) (fun j => (x j : ℂ)) j := by
    fin_cases j <;> simp [completeNodes, fourthNode]
  have he (j : Fin 5) : ((normalizedDirection d j : ℝ) : ℂ) =
      (normalizedDirection d j : ℂ) := by
    fin_cases d <;> fin_cases j <;> simp [normalizedDirection]
  funext j
  simp only [Function.comp_apply, hn, map_add, map_mul, complexLineMap_C,
    complexLineMap_X, affineNodes, hc, hd, hz, he, map_mul]
  ring

lemma complexLineMap_norm (ρ u v ρ' u' v' : ℝ) (x : Fin 3 → ℝ) (z : Fin 3 → ℂ)
    (d : Fin 4) (t : ℂ)
    (hz : ∀ j, completeDirection (ρ : ℂ) (u : ℂ) (v : ℂ) z j =
      t * normalizedDirection d j) :
    complexLineMap t (exceptionalNorm ρ u v ρ' u' v' (x 0) (x 1) (x 2) d) =
      affineNorm (ρ : ℂ) (u : ℂ) (v : ℂ) (ρ' : ℂ) (u' : ℂ) (v' : ℂ)
        (fun j => (x j : ℂ)) z := by
  have hn := complexLineMap_nodes ρ u v x z d t hz
  dsimp only [exceptionalNorm, affineNorm]
  rw [map_lineNorm]
  simp only [complexLineMap_C]
  congr 1
  · exact congrFun hn 0
  · exact congrFun hn 1
  · exact congrFun hn 2

lemma complexLineMap_quadratic (ρ u v ρ' u' v' : ℝ) (x : Fin 3 → ℝ) (z : Fin 3 → ℂ)
    (d : Fin 4) (t : ℂ)
    (hz : ∀ j, completeDirection (ρ : ℂ) (u : ℂ) (v : ℂ) z j =
      t * normalizedDirection d j) :
    complexLineMap t (exceptionalQuadratic ρ u v ρ' u' v' (x 0) (x 1) (x 2) d) =
      affineQuadratic (ρ : ℂ) (u : ℂ) (v : ℂ) (ρ' : ℂ) (u' : ℂ) (v' : ℂ)
        (fun j => (x j : ℂ)) z := by
  have hn := complexLineMap_nodes ρ u v x z d t hz
  dsimp only [exceptionalQuadratic, affineQuadratic]
  rw [map_lineQuadratic]
  simp only [complexLineMap_C]
  congr 1
  · exact congrFun hn 0
  · exact congrFun hn 1
  · exact congrFun hn 2

lemma complexLineMap_resultant (ρ u v ρ' u' v' : ℝ) (x : Fin 3 → ℝ) (z : Fin 3 → ℂ)
    (d : Fin 4) (t : ℂ)
    (hz : ∀ j, completeDirection (ρ : ℂ) (u : ℂ) (v : ℂ) z j =
      t * normalizedDirection d j) :
    complexLineMap t (exceptionalResultant ρ u v ρ' u' v' (x 0) (x 1) (x 2) d) =
      affineResultant (ρ : ℂ) (u : ℂ) (v : ℂ) (ρ' : ℂ) (u' : ℂ) (v' : ℂ)
        (fun j => (x j : ℂ)) z := by
  have hn := complexLineMap_nodes ρ u v x z d t hz
  have hc (r s w : ℝ) :
      complexLineMap t ∘ (fun j : Fin 4 => C (coeffs r s w j.castSucc)) =
      (fun j : Fin 4 => C (coeffs (r : ℂ) (s : ℂ) (w : ℂ) j.castSucc)) := by
    funext j
    simp [coeffs_ofReal]
  dsimp only [exceptionalResultant, affineResultant]
  rw [← resultant_map_map, Polynomial.map_mul, map_X,
    map_firstNewtonQuartic, map_nextNewtonQuartic, hc, hc]
  change resultant (firstNewtonQuartic _ (complexLineMap t ∘ exceptionalNodes
    (completeNodes ρ u v x) d)) (X * nextNewtonQuartic _
    (complexLineMap t ∘ exceptionalNodes (completeNodes ρ u v x) d)) 4 5 = _
  rw [hn]

/-- Containment through a real point descends to one of the four normalized real lines. -/
theorem contained_complex_line_real_identities {A a ρ u v : ℝ}
    (hA : A ≠ 0) (ha : a ≠ 0) (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (ρ' u' v' : ℝ) (x : Fin 3 → ℝ) (z : Fin 3 → ℂ) (hz : ∃ j, z j ≠ 0)
    (hq : affineQuadratic (ρ : ℂ) (u : ℂ) (v : ℂ) (ρ' : ℂ) (u' : ℂ) (v' : ℂ)
      (fun j => (x j : ℂ)) z = 0)
    (he : C (A : ℂ) * affineResultant (ρ : ℂ) (u : ℂ) (v : ℂ)
      (ρ' : ℂ) (u' : ℂ) (v' : ℂ) (fun j => (x j : ℂ)) z =
      C (a : ℂ) * affineNorm (ρ : ℂ) (u : ℂ) (v : ℂ)
      (ρ' : ℂ) (u' : ℂ) (v' : ℂ) (fun j => (x j : ℂ)) z ^ 4) :
    ∃ d : Fin 4, ExceptionalRelation ρ u v d ∧
      exceptionalQuadratic ρ u v ρ' u' v' (x 0) (x 1) (x 2) d = 0 ∧
      C A * exceptionalResultant ρ u v ρ' u' v' (x 0) (x 1) (x 2) d =
      C a * exceptionalNorm ρ u v ρ' u' v' (x 0) (x 1) (x 2) d ^ 4 := by
  obtain ⟨d, t, ht, hd, hr⟩ := contained_complex_line_direction
    (by exact_mod_cast hA) (by exact_mod_cast ha) hρ hu hv
    (ρ' : ℂ) (u' : ℂ) (v' : ℂ) (fun j => (x j : ℂ)) z hz hq he
  refine ⟨d, by simpa [ExceptionalRelation, exceptionalRelation] using hr, ?_, ?_⟩
  · apply complexLineMap_injective ht
    rw [map_zero, complexLineMap_quadratic ρ u v ρ' u' v' x z d t hd]
    exact hq
  · apply complexLineMap_injective ht
    simp only [map_mul, map_pow, complexLineMap_C,
      complexLineMap_resultant ρ u v ρ' u' v' x z d t hd,
      complexLineMap_norm ρ u v ρ' u' v' x z d t hd]
    exact he

/-- The three free coordinates of an orbit window. -/
def orbitFreeNodes (a b i : ℕ) : Fin 3 → ℝ := ![pt a b i 1, pt a b i 2, pt a b i 3]

/-- Unpack the three coordinates while the predicate is still abstract. -/
lemma orbitFreeNodes_prop (a b i : ℕ) (F : ℝ → ℝ → ℝ → Prop)
    (h : F (orbitFreeNodes a b i 0) (orbitFreeNodes a b i 1) (orbitFreeNodes a b i 2)) :
    F (pt a b i 1) (pt a b i 2) (pt a b i 3) := h

/-- Normalize the integer and natural casts before substituting a resultant. -/
lemma complex_polynomial_relation_cast (A : ℤ) (a : ℕ) (R N : ℂ[X])
    (h : C (A : ℂ) * R = C (a : ℂ) * N ^ 4) :
    C ((A : ℝ) : ℂ) * R = C ((a : ℝ) : ℂ) * N ^ 4 := by
  simpa using h

/-- No complex affine line on both equations passes through the orbit point of a
window satisfying the scale condition `a H⁵ (24 X₀ + 464) < q⁴`. Containment is
expressed by polynomial identities along the line. -/
theorem orbit_no_complex_line {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    {H X₀ : ℤ} (hX : 1 ≤ X₀) (hg : ∀ m < 5, kq a b (i + m) ≤ H)
    (hU : |U1z a b i| ≤ X₀) (hV : |U2z a b i| ≤ X₀)
    (hscale : (a : ℤ) * H ^ 5 * (24 * X₀ + 464) < (qq a b i : ℤ) ^ 4)
    (z : Fin 3 → ℂ) (hz : ∃ j, z j ≠ 0)
    (hq : affineQuadratic (patternRho a b i : ℂ) (patternU a b i : ℂ) (patternV a b i : ℂ)
      (patternRho a b (i + 1) : ℂ) (patternU a b (i + 1) : ℂ) (patternV a b (i + 1) : ℂ)
      (fun j => (orbitFreeNodes a b i j : ℂ)) z = 0)
    (he : C (Lz a b i : ℂ) * affineResultant
      (patternRho a b i : ℂ) (patternU a b i : ℂ) (patternV a b i : ℂ)
      (patternRho a b (i + 1) : ℂ) (patternU a b (i + 1) : ℂ) (patternV a b (i + 1) : ℂ)
      (fun j => (orbitFreeNodes a b i j : ℂ)) z =
      C (a : ℂ) * affineNorm
      (patternRho a b i : ℂ) (patternU a b i : ℂ) (patternV a b i : ℂ)
      (patternRho a b (i + 1) : ℂ) (patternU a b (i + 1) : ℂ) (patternV a b (i + 1) : ℂ)
      (fun j => (orbitFreeNodes a b i j : ℂ)) z ^ 4) : False := by
  obtain ⟨hρ, hu, hv⟩ := orbit_pattern_signs hba (by omega : i + 6 < P a b)
  have ha : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  obtain ⟨d, hr, hq', he'⟩ := contained_complex_line_real_identities
    (orbit_label_ne_zero (i := i) hba (by omega)) ha hρ hu hv
    (patternRho a b (i + 1)) (patternU a b (i + 1)) (patternV a b (i + 1))
    (orbitFreeNodes a b i) z hz hq (complex_polynomial_relation_cast _ _ _ _ he)
  apply orbit_no_exceptional_line hba hi hX hg hU hV hscale d hr
  · exact orbitFreeNodes_prop a b i (fun x₀ x₁ x₂ =>
      exceptionalQuadratic (patternRho a b i) (patternU a b i) (patternV a b i)
        (patternRho a b (i + 1)) (patternU a b (i + 1)) (patternV a b (i + 1))
        x₀ x₁ x₂ d = 0) hq'
  · exact orbitFreeNodes_prop a b i (fun x₀ x₁ x₂ =>
      C (Lz a b i : ℝ) * exceptionalResultant
        (patternRho a b i) (patternU a b i) (patternV a b i)
        (patternRho a b (i + 1)) (patternU a b (i + 1)) (patternV a b (i + 1))
        x₀ x₁ x₂ d = C (a : ℝ) * exceptionalNorm
        (patternRho a b i) (patternU a b i) (patternV a b i)
        (patternRho a b (i + 1)) (patternU a b (i + 1)) (patternV a b (i + 1))
        x₀ x₁ x₂ d ^ 4) he'

end
end PierceLengthBound.FixedDividend
