/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendRationalComponents

/-!
# Rational fixed-dividend curves

The defining equations and their degree bounds are compatible with coefficient
maps. The checked complex nondivisibility theorem therefore proves genuine
coprimality over the rationals. Rational components containing actual points have
positive, bounded affine Hilbert degree directly over their counting field.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

lemma map_curveQuadratic {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (ρ u v ρ' u' v' : K) :
    MvPolynomial.map f (curveQuadratic ρ u v ρ' u' v') =
      curveQuadratic (f ρ) (f u) (f v) (f ρ') (f u') (f v') := by
  rw [curveQuadratic, map_lineQuadratic]
  simp [curveQuadratic]

lemma map_curveNorm {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (ρ u v ρ' u' v' : K) :
    MvPolynomial.map f (curveNorm ρ u v ρ' u' v') =
      curveNorm (f ρ) (f u) (f v) (f ρ') (f u') (f v') := by
  rw [curveNorm, map_lineNorm]
  simp [curveNorm]

lemma map_curveResultant {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (ρ u v ρ' u' v' : K) :
    MvPolynomial.map f (curveResultant ρ u v ρ' u' v') =
      curveResultant (f ρ) (f u) (f v) (f ρ') (f u') (f v') := by
  have hn : MvPolynomial.map f ∘ completeNodes (MvPolynomial.C ρ) (MvPolynomial.C u)
      (MvPolynomial.C v) MvPolynomial.X =
      completeNodes (MvPolynomial.C (f ρ)) (MvPolynomial.C (f u))
        (MvPolynomial.C (f v)) MvPolynomial.X := by
    funext j
    fin_cases j <;> simp [completeNodes, fourthNode]
  have hc (r s w : K) :
      MvPolynomial.map (σ := Fin 3) f ∘
        (fun j : Fin 4 => MvPolynomial.C (coeffs r s w j.castSucc)) =
        (fun j : Fin 4 => MvPolynomial.C (coeffs (f r) (f s) (f w) j.castSucc)) := by
    funext j
    fin_cases j <;> simp [coeffs]
  unfold curveResultant
  rw [← resultant_map_map, Polynomial.map_mul, Polynomial.map_X,
    map_firstNewtonQuartic, map_nextNewtonQuartic, hn, hc, hc]

lemma map_curveEquation {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    (ρ u v ρ' u' v' A a : K) :
    MvPolynomial.map f (curveEquation ρ u v ρ' u' v' A a) =
      curveEquation (f ρ) (f u) (f v) (f ρ') (f u') (f v') (f A) (f a) := by
  simp [curveEquation, map_curveResultant, map_curveNorm]

/-- Rational nondivisibility follows by mapping a hypothetical divisibility
witness into the already checked complex coefficient ring. -/
theorem rational_curveQuadratic_not_dvd {ρ u v : ℚ}
    (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0) (ρ' u' v' A a : ℚ) (ha : a ≠ 0) :
    ¬ curveQuadratic ρ u v ρ' u' v' ∣ curveEquation ρ u v ρ' u' v' A a := by
  intro hdiv
  have hmap := map_dvd (MvPolynomial.map (algebraMap ℚ ℂ)) hdiv
  rw [map_curveQuadratic, map_curveEquation] at hmap
  have hnot := curveQuadratic_not_dvd_fixed_dividend
    (ρ := (ρ : ℝ)) (u := (u : ℝ)) (v := (v : ℝ))
    (by exact_mod_cast hρ) (by exact_mod_cast hu) (by exact_mod_cast hv)
    (ρ' : ℂ) (u' : ℂ) (v' : ℂ) (A : ℂ) (a : ℂ) (by exact_mod_cast ha)
  apply hnot
  simpa [curveEquation] using hmap

lemma rational_curveQuadratic_prime {ρ u v : ℚ}
    (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0) (ρ' u' v' : ℚ) :
    Prime (curveQuadratic ρ u v ρ' u' v') := by
  apply Irreducible.prime
  apply lineQuadratic_irreducible
  all_goals linarith

/-- The rational equations have a finite decomposition into prime curves. -/
theorem rational_curve_finite_prime_decomposition {ρ u v : ℚ}
    (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0) (ρ' u' v' A a : ℚ) (ha : a ≠ 0) :
    ∃ S : Finset (Ideal (MvPolynomial (Fin 3) ℚ)),
      (∀ p ∈ S, p.IsPrime ∧ p.height = 2) ∧
      (∀ x, (MvPolynomial.eval x (curveQuadratic ρ u v ρ' u' v') = 0 ∧
        MvPolynomial.eval x (curveEquation ρ u v ρ' u' v' A a) = 0) ↔
        ∃ p ∈ S, x ∈ coordinateZeroLocus p) :=
  finite_prime_decomposition_height_two (rational_curveQuadratic_prime hρ hu hv ρ' u' v')
    (rational_curveQuadratic_not_dvd hρ hu hv ρ' u' v' A a ha)

/-- The rational quotient filtration has the same coefficient-uniform slope bound. -/
theorem rational_curve_filtered_bound {ρ u v : ℚ}
    (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0) (ρ' u' v' A a : ℚ) (ha : a ≠ 0)
    (p : Ideal (MvPolynomial (Fin 3) ℚ))
    (hf : curveQuadratic ρ u v ρ' u' v' ∈ p) (hg : curveEquation ρ u v ρ' u' v' A a ∈ p)
    {N : ℕ} (hN : 14 ≤ N) :
    Module.finrank ℚ (filteredCoordinateSpace p N) ≤ 24 * (N + 2) := by
  have hfd := curveQuadratic_degree_le_two ρ u v ρ' u' v'
  have hgd := curveEquation_degree_le ρ u v ρ' u' v' A a
  have h := filteredCoordinateSpace_finrank_linear
    (rational_curveQuadratic_prime hρ hu hv ρ' u' v')
    (rational_curveQuadratic_not_dvd hρ hu hv ρ' u' v' A a ha) p hf hg (by omega :
      (curveQuadratic ρ u v ρ' u' v').totalDegree +
        (curveEquation ρ u v ρ' u' v' A a).totalDegree ≤ N)
  exact h.trans (Nat.mul_le_mul_right _ (by nlinarith))

/-- Each rational prime component containing a rational point has the exact
positive affine Hilbert degree required by the external counting interface. -/
theorem rational_curve_component_degree_exists {ρ u v : ℚ}
    (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0) (ρ' u' v' A a : ℚ) (ha : a ≠ 0)
    (p : Ideal (MvPolynomial (Fin 3) ℚ)) [p.IsPrime] (hp : p.height = 2)
    (hf : curveQuadratic ρ u v ρ' u' v' ∈ p) (hg : curveEquation ρ u v ρ' u' v' A a ∈ p)
    (z : Fin 3 → ℚ) (hz : z ∈ coordinateZeroLocus p) :
    ∃ d : ℕ, 0 < d ∧ d ≤ 24 ∧ ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
      (Module.finrank ℚ (filteredCoordinateSpace p n) : ℤ) = (d : ℤ) * n + c := by
  apply height_two_degree_exists_of_point p hp z hz 24
  intro N hN
  exact rational_curve_filtered_bound hρ hu hv ρ' u' v' A a ha p hf hg hN

/-- Rational zero loci are covered by at most twenty-four rational prime curves,
each with a genuine positive affine Hilbert degree at most twenty-four. Components
with no rational point can be discarded from the rational counting problem. -/
theorem rational_curve_decomposition_with_degrees {ρ u v : ℚ}
    (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0) (ρ' u' v' A a : ℚ) (ha : a ≠ 0) :
    ∃ S : Finset (Ideal (MvPolynomial (Fin 3) ℚ)), S.card ≤ 24 ∧
      (∀ p ∈ S, p.IsPrime ∧ p.height = 2 ∧
        curveQuadratic ρ u v ρ' u' v' ∈ p ∧ curveEquation ρ u v ρ' u' v' A a ∈ p ∧
        ∃ d : ℕ, 0 < d ∧ d ≤ 24 ∧ ∃ N : ℕ, ∃ c : ℤ, ∀ n ≥ N,
          (Module.finrank ℚ (filteredCoordinateSpace p n) : ℤ) = (d : ℤ) * n + c) ∧
      (∀ x, (MvPolynomial.eval x (curveQuadratic ρ u v ρ' u' v') = 0 ∧
        MvPolynomial.eval x (curveEquation ρ u v ρ' u' v' A a) = 0) ↔
        ∃ p ∈ S, x ∈ coordinateZeroLocus p) := by
  classical
  let f := curveQuadratic ρ u v ρ' u' v'
  let g := curveEquation ρ u v ρ' u' v' A a
  let I : Ideal (MvPolynomial (Fin 3) ℚ) := Ideal.span ({f, g} : Set _)
  let hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin 3) ℚ) I
  let S := hfin.toFinset.filter (fun p => (coordinateZeroLocus p).Nonempty)
  have hS (p : Ideal (MvPolynomial (Fin 3) ℚ)) (hp : p ∈ S) :
      p ∈ I.minimalPrimes ∧ (coordinateZeroLocus p).Nonempty := by
    have h := Finset.mem_filter.mp hp
    exact ⟨hfin.mem_toFinset.mp h.1, h.2⟩
  have hheight (p : Ideal (MvPolynomial (Fin 3) ℚ)) (hp : p ∈ S) : p.height = 2 :=
    minimalPrime_pair_height_two (rational_curveQuadratic_prime hρ hu hv ρ' u' v')
      (rational_curveQuadratic_not_dvd hρ hu hv ρ' u' v' A a ha) (hS p hp).1
  have hIf : f ∈ I := Ideal.subset_span (by simp)
  have hIg : g ∈ I := Ideal.subset_span (by simp)
  have hcard : S.card ≤ 24 := by
    refine minimalPrime_card_le_of_transcendental_coordinates I S
      (fun p hp => ⟨(hS p hp).1, hheight p hp⟩) ?_ 24 ?_
    · intro p hp
      let : p.IsPrime := (hS p hp).1.isPrime
      obtain ⟨z, hz⟩ := (hS p hp).2
      exact height_two_transcendental_coordinate_of_point p (hheight p hp) z hz
    · intro N hN
      exact rational_curve_filtered_bound hρ hu hv ρ' u' v' A a ha I hIf hIg hN
  refine ⟨S, hcard, ?_, ?_⟩
  · intro p hp
    let : p.IsPrime := (hS p hp).1.isPrime
    have hpf : f ∈ p := (hS p hp).1.le hIf
    have hpg : g ∈ p := (hS p hp).1.le hIg
    obtain ⟨z, hz⟩ := (hS p hp).2
    exact ⟨inferInstance, hheight p hp, hpf, hpg,
      rational_curve_component_degree_exists hρ hu hv ρ' u' v' A a ha p
        (hheight p hp) hpf hpg z hz⟩
  · intro x
    rw [common_zero_iff_minimalPrime]
    constructor
    · rintro ⟨p, hp, hx⟩
      exact ⟨p, Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hp, ⟨x, hx⟩⟩, hx⟩
    · rintro ⟨p, hp, hx⟩
      exact ⟨p, (hS p hp).1, hx⟩

end
end PierceLengthBound.FixedDividend
