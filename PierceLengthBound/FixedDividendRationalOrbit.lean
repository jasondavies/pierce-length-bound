/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendRationalCurves
public import PierceLengthBound.FixedDividendParity

/-!
# Actual orbit points on rational components

The rational minor ratios and quotient differences map to the existing real
orbit data. Rational degree-one components give complex lines, so the proved
orbit estimates exclude degree one directly over the counting field `ℚ`.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

def patternRhoQ (a b i : ℕ) : ℚ := (Lz a b (i + 1) : ℚ) / Lz a b i
def patternUQ (a b i : ℕ) : ℚ := (U1z a b i : ℚ) / Lz a b i
def patternVQ (a b i : ℕ) : ℚ := (U2z a b i : ℚ) / Lz a b i

def orbitFreeNodesQ (a b i : ℕ) : Fin 3 → ℚ :=
  fun j => (qq a b (i + (j.val + 1)) : ℚ) - qq a b i

@[simp] lemma patternRhoQ_cast (a b i : ℕ) : (patternRhoQ a b i : ℝ) = patternRho a b i := by
  simp [patternRhoQ, patternRho]
@[simp] lemma patternUQ_cast (a b i : ℕ) : (patternUQ a b i : ℝ) = patternU a b i := by
  simp [patternUQ, patternU]
@[simp] lemma patternVQ_cast (a b i : ℕ) : (patternVQ a b i : ℝ) = patternV a b i := by
  simp [patternVQ, patternV]
@[simp] lemma orbitFreeNodesQ_cast (a b i : ℕ) (j : Fin 3) :
    (orbitFreeNodesQ a b i j : ℝ) = orbitFreeNodes a b i j := by
  fin_cases j <;> simp [orbitFreeNodesQ, orbitFreeNodes, pt]

lemma orbit_rational_pattern_signs {a b i : ℕ} (hba : b < a) (hi : i + 6 < P a b) :
    0 < patternRhoQ a b i ∧ 0 < patternUQ a b i ∧ patternVQ a b i < 0 := by
  have h := orbit_pattern_signs hba hi
  have hρ : (0 : ℝ) < (patternRhoQ a b i : ℝ) := by simpa using h.1
  have hu : (0 : ℝ) < (patternUQ a b i : ℝ) := by simpa using h.2.1
  have hv : (patternVQ a b i : ℝ) < 0 := by simpa using h.2.2
  exact ⟨by exact_mod_cast hρ, by exact_mod_cast hu, by exact_mod_cast hv⟩

/-- The real nonexceptional pattern condition, restated for the rational pattern. -/
lemma nonexceptionalPattern_ratCast {a b i : ℕ}
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i)) :
    NonexceptionalPattern (patternRhoQ a b i : ℝ) (patternUQ a b i : ℝ)
      (patternVQ a b i : ℝ) := by
  simpa using hne

/-- The rational data of an actual nonexceptional orbit state used by the chart theorems:
the pattern signs, the rational nonexceptional condition, and nonvanishing of `a` and `L`. -/
theorem orbit_rational_nonexceptional_data {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (hne : NonexceptionalPattern (patternRho a b i) (patternU a b i) (patternV a b i)) :
    0 < patternRhoQ a b i ∧ 0 < patternUQ a b i ∧ patternVQ a b i < 0 ∧
      NonexceptionalPattern (patternRhoQ a b i : ℝ) (patternUQ a b i : ℝ)
        (patternVQ a b i : ℝ) ∧ (a : ℚ) ≠ 0 ∧ (Lz a b i : ℚ) ≠ 0 := by
  obtain ⟨hρ, hu, hv⟩ := orbit_rational_pattern_signs hba (by omega : i + 6 < P a b)
  refine ⟨hρ, hu, hv, nonexceptionalPattern_ratCast hne,
    by exact_mod_cast (show a ≠ 0 by omega), ?_⟩
  exact_mod_cast (ne_of_gt (Lz_pos hba (by omega : i + 5 < P a b)))

/-- The actual rational first equation. -/
def orbitCurveQuadraticQ (a b i : ℕ) : MvPolynomial (Fin 3) ℚ :=
  curveQuadratic (patternRhoQ a b i) (patternUQ a b i) (patternVQ a b i)
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))

/-- The actual rational fixed-dividend equation. -/
def orbitCurveEquationQ (a b i : ℕ) : MvPolynomial (Fin 3) ℚ :=
  curveEquation (patternRhoQ a b i) (patternUQ a b i) (patternVQ a b i)
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1)) (Lz a b i) a

lemma orbit_rational_curve_zeros {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b) :
    MvPolynomial.eval (orbitFreeNodesQ a b i) (orbitCurveQuadraticQ a b i) = 0 ∧
      MvPolynomial.eval (orbitFreeNodesQ a b i) (orbitCurveEquationQ a b i) = 0 := by
  have hx : (algebraMap ℚ ℝ) ∘ orbitFreeNodesQ a b i = orbitFreeNodes a b i := by
    funext j
    exact orbitFreeNodesQ_cast a b i j
  constructor
  · apply (algebraMap ℚ ℝ).injective
    rw [map_zero, MvPolynomial.map_eval, hx]
    simpa [orbitCurveQuadraticQ, map_curveQuadratic] using
      orbit_curveQuadratic_zero hba (by omega : i + 6 < P a b)
  · apply (algebraMap ℚ ℝ).injective
    rw [map_zero, MvPolynomial.map_eval, hx]
    simpa [orbitCurveEquationQ, map_curveEquation] using orbit_curveEquation_zero hba hi

/-- Affine line restriction commutes with a coefficient map. -/
lemma map_affineRestriction {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (x z : Fin 3 → K) (p : MvPolynomial (Fin 3) K) :
    Polynomial.map f (affineRestriction x z p) =
      affineRestriction (f ∘ x) (f ∘ z) (MvPolynomial.map f p) := by
  have he : (Polynomial.mapRingHom f).comp (affineRestriction x z).toRingHom =
      (affineRestriction (f ∘ x) (f ∘ z)).toRingHom.comp (MvPolynomial.map f) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [affineRestriction]
    · intro j
      simp [affineRestriction]
  exact congrArg (fun φ : MvPolynomial (Fin 3) K →+* Polynomial L => φ p) he

/-- Restrict the equation before substituting the large orbit resultant. -/
lemma affineRestriction_equation_polynomials {K : Type*} [CommRing K]
    (A a : K) (R N : MvPolynomial (Fin 3) K) (x z : Fin 3 → K) :
    affineRestriction x z (MvPolynomial.C A * R - MvPolynomial.C a * N ^ 4) =
      C A * affineRestriction x z R - C a * (affineRestriction x z N) ^ 4 := by
  simp only [map_sub, map_mul, map_pow]
  simp only [affineRestriction, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]

/-- Normalize operations using the identity for two abstract polynomials. -/
lemma affineRestriction_equation {K : Type*} [CommRing K]
    (ρ u v ρ' u' v' A a : K) (x z : Fin 3 → K) :
    affineRestriction x z (curveEquation ρ u v ρ' u' v' A a) =
      C A * affineResultant ρ u v ρ' u' v' x z -
        C a * affineNorm ρ u v ρ' u' v' x z ^ 4 := by
  rw [curveEquation, affineRestriction_equation_polynomials,
    affineRestriction_resultant, affineRestriction_norm]

/-- The equation with integer and natural coefficients, over an abstract ring. -/
def castResultantNormRelation {K : Type*} [CommRing K]
    (A : ℤ) (a : ℕ) (R N : K[X]) : Prop :=
  resultantNormRelation (A : K) (a : K) R N

/-- Reconcile the complex polynomial operations before substituting a resultant. -/
lemma resultantNormRelation_complex_elim {A : ℤ} {a : ℕ}
    {R N : @Polynomial ℂ (CommRing.toCommSemiring.toSemiring)}
    (h : castResultantNormRelation A a R N) :
    C (A : ℂ) * R = C (a : ℂ) * N ^ 4 := h

/-- Map and restrict the equation using consistent abstract ring structures. -/
lemma map_affineRestriction_equation_zero {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (ρ u v ρ' u' v' : K) (A : ℤ) (a : ℕ) (x z : Fin 3 → K)
    (h : affineRestriction x z (curveEquation ρ u v ρ' u' v' A a) = 0) :
    castResultantNormRelation A a
      (affineResultant (f ρ) (f u) (f v) (f ρ') (f u') (f v') (f ∘ x) (f ∘ z))
      (affineNorm (f ρ) (f u) (f v) (f ρ') (f u') (f v') (f ∘ x) (f ∘ z)) := by
  have hg := congrArg (Polynomial.map f) h
  rw [map_affineRestriction, Polynomial.map_zero, map_curveEquation] at hg
  have hA : f (A : K) = (A : L) := map_intCast f A
  have ha : f (a : K) = (a : L) := map_natCast f a
  rw [hA, ha] at hg
  rw [affineRestriction_equation] at hg
  exact sub_eq_zero.mp hg

/-- A rational prime component through an actual large-scale orbit point cannot
have degree one. The resulting rational line is mapped into the checked complex
line-exclusion theorem. -/
theorem orbit_rational_component_not_degree_one {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    {H X₀ : ℤ} (hX : 1 ≤ X₀) (hgaps : ∀ m < 5, kq a b (i + m) ≤ H)
    (hU : |U1z a b i| ≤ X₀) (hV : |U2z a b i| ≤ X₀)
    (hscale : (a : ℤ) * H ^ 5 * (24 * X₀ + 464) < (qq a b i : ℤ) ^ 4)
    (p : Ideal (MvPolynomial (Fin 3) ℚ)) [p.IsPrime] (hp : p.height = 2)
    (hf : orbitCurveQuadraticQ a b i ∈ p) (he : orbitCurveEquationQ a b i ∈ p)
    (hx : orbitFreeNodesQ a b i ∈ coordinateZeroLocus p) :
    ¬ ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace p n) : ℤ) = n + c := by
  intro hdegree
  obtain ⟨z, hz, hline⟩ := degree_one_line_through_rational_point p hp hdegree _ hx
  -- Match the ring structures in the generic mapping lemmas before substituting
  -- the resultant. Converting the entire resulting identity is much more costly.
  let f : @RingHom ℚ ℂ
      (CommRing.toCommSemiring.toSemiring.toNonAssocSemiring)
      (CommRing.toCommSemiring.toSemiring.toNonAssocSemiring) := algebraMap ℚ ℂ
  have hxmap : f ∘ orbitFreeNodesQ a b i = fun j => (orbitFreeNodes a b i j : ℂ) := by
    funext j
    have h := congrArg Complex.ofReal (orbitFreeNodesQ_cast a b i j)
    exact h
  have hρ (j : ℕ) : f (patternRhoQ a b j) = (patternRho a b j : ℂ) := by
    exact congrArg Complex.ofReal (patternRhoQ_cast a b j)
  have hu (j : ℕ) : f (patternUQ a b j) = (patternU a b j : ℂ) := by
    exact congrArg Complex.ofReal (patternUQ_cast a b j)
  have hv (j : ℕ) : f (patternVQ a b j) = (patternV a b j : ℂ) := by
    exact congrArg Complex.ofReal (patternVQ_cast a b j)
  have hq := congrArg (Polynomial.map f) (hline _ hf)
  have hg := map_affineRestriction_equation_zero f
    (patternRhoQ a b i) (patternUQ a b i) (patternVQ a b i)
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i) a (orbitFreeNodesQ a b i) z (hline _ he)
  change Polynomial.map f (affineRestriction _ _ _) = Polynomial.map f 0 at hq
  rw [map_affineRestriction, Polynomial.map_zero, hxmap] at hq
  simp only [orbitCurveQuadraticQ, map_curveQuadratic, hρ, hu, hv,
    affineRestriction_quadratic] at hq
  simp only [hρ, hu, hv, hxmap] at hg
  have hz' : ∃ j, (f ∘ z) j ≠ 0 := by
    obtain ⟨j, hj⟩ := hz
    exact ⟨j, fun hzero => hj (f.injective (by simpa using hzero))⟩
  exact orbit_no_complex_line hba hi hX hgaps hU hV hscale (f ∘ z) hz' hq
    (resultantNormRelation_complex_elim hg)

/-- Rational components through actual large-scale orbit windows have exactly
the degree range `2 ≤ d ≤ 24` required by the square-root curve count. -/
theorem orbit_rational_component_degree_range {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    {H X₀ : ℤ} (hX : 1 ≤ X₀) (hgaps : ∀ m < 5, kq a b (i + m) ≤ H)
    (hU : |U1z a b i| ≤ X₀) (hV : |U2z a b i| ≤ X₀)
    (hscale : (a : ℤ) * H ^ 5 * (24 * X₀ + 464) < (qq a b i : ℤ) ^ 4)
    (p : Ideal (MvPolynomial (Fin 3) ℚ)) [p.IsPrime] (hp : p.height = 2)
    (hf : orbitCurveQuadraticQ a b i ∈ p) (he : orbitCurveEquationQ a b i ∈ p)
    (hx : orbitFreeNodesQ a b i ∈ coordinateZeroLocus p) :
    ∃ d : ℕ, 2 ≤ d ∧ d ≤ 24 ∧ ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace p n) : ℤ) = (d : ℤ) * n + c := by
  obtain ⟨hρ, hu, hv⟩ := orbit_rational_pattern_signs hba (by omega : i + 6 < P a b)
  obtain ⟨d, hd, hd24, N, c, hlinear⟩ := rational_curve_component_degree_exists hρ hu hv
    (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1)) (patternVQ a b (i + 1))
    (Lz a b i : ℚ) (a : ℚ) (by exact_mod_cast (show a ≠ 0 by omega)) p hp hf he _ hx
  have hd1 : d ≠ 1 := by
    intro heq
    apply orbit_rational_component_not_degree_one hba hi hX hgaps hU hV hscale p hp hf he hx
    refine ⟨N, c, ?_⟩
    intro n hn
    simpa [heq] using hlinear n hn
  exact ⟨d, by omega, hd24, N, c, hlinear⟩

end
end PierceLengthBound.FixedDividend
