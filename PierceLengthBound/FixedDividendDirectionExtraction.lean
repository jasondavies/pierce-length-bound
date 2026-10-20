/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendDirections
public import PierceLengthBound.FixedDividendLines

/-!
# Directions of arbitrary contained complex lines

The two polynomial containment identities force the four weighted moments and
vanishing of the degree-ten Vandermonde form. Thus every nonconstant contained
complex line has one of the four normalized real directions.
-/

@[expose] public section

namespace PierceLengthBound.FixedDividend

noncomputable section
open Polynomial

/-- All five node directions, including the eliminated fourth node. -/
def completeDirection {R : Type*} [CommRing R] (ρ u v : R) (z : Fin 3 → R) : Fin 5 → R :=
  ![0, z 0, z 1, z 2, fourthNode ρ u v (z 0) (z 1) (z 2)]

/-- Four nonzero-index nodes, with the fourth linear relation imposed. -/
def completeNodes {R : Type*} [CommRing R] (ρ u v : R) (a : Fin 3 → R) : Fin 4 → R :=
  ![a 0, a 1, a 2, fourthNode ρ u v (a 0) (a 1) (a 2)]

/-- The cubic norm restricted to an arbitrary affine line in the three free nodes. -/
def affineNorm {R : Type*} [CommRing R] (ρ u v ρ' u' v' : R) (a z : Fin 3 → R) : R[X] :=
  lineNorm (C ρ) (C u) (C v) (C ρ') (C u') (C v')
    (C (a 0) + C (z 0) * X) (C (a 1) + C (z 1) * X) (C (a 2) + C (z 2) * X)

/-- The quadratic restricted to the same affine line. -/
def affineQuadratic {R : Type*} [CommRing R] (ρ u v ρ' u' v' : R) (a z : Fin 3 → R) : R[X] :=
  lineQuadratic (C ρ) (C u) (C v) (C ρ') (C u') (C v')
    (C (a 0) + C (z 0) * X) (C (a 1) + C (z 1) * X) (C (a 2) + C (z 2) * X)

/-- The fixed-dividend resultant restricted to the same affine line. -/
def affineResultant {R : Type*} [CommRing R] (ρ u v ρ' u' v' : R) (a z : Fin 3 → R) : R[X] :=
  let s := affineNodes (completeNodes ρ u v a) (completeNodes ρ u v z)
  resultant (firstNewtonQuartic (fun j : Fin 4 => C (coeffs ρ u v j.castSucc)) s)
    (X * nextNewtonQuartic (fun j : Fin 4 => C (coeffs ρ' u' v' j.castSucc)) s) 4 5

lemma completeDirection_moment_zero {R : Type*} [CommRing R] (ρ u v : R) (z : Fin 3 → R) :
    ∑ j : Fin 5, coeffs ρ u v j * completeDirection ρ u v z j ^ 0 = 0 := by
  simp [coeffs, Fin.sum_univ_succ]

lemma completeDirection_moment_one {R : Type*} [CommRing R] (ρ u v : R) (z : Fin 3 → R) :
    ∑ j : Fin 5, coeffs ρ u v j * completeDirection ρ u v z j ^ 1 = 0 := by
  simp [coeffs, completeDirection, fourthNode, Fin.sum_univ_succ]
  ring

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
-- Expand the eliminated-node formulas and certify their leading coefficients.
lemma affineQuadratic_coeff_two {R : Type*} [CommRing R] (ρ u v ρ' u' v' : R) (a z : Fin 3 → R) :
    (affineQuadratic ρ u v ρ' u' v' a z).coeff 2 =
      ∑ j : Fin 5, coeffs ρ u v j * completeDirection ρ u v z j ^ 2 := by
  dsimp [affineQuadratic, lineQuadratic, lineNodes, lineGaps, fourthNode, coeffs]
  simp only [Fin.sum_univ_succ, Fin.castSucc_zero, Fin.castSucc_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, zero_pow (by decide : 2 ≠ 0), zero_add]
  compute_degree <;> simp [completeDirection, fourthNode]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
-- Expand the eliminated-node formulas and certify their leading coefficients.
lemma affineNorm_coeff_three {R : Type*} [CommRing R] (ρ u v ρ' u' v' : R) (a z : Fin 3 → R) :
    (affineNorm ρ u v ρ' u' v' a z).coeff 3 =
      ∑ j : Fin 5, coeffs ρ u v j * completeDirection ρ u v z j ^ 3 := by
  simp only [affineNorm, lineNorm, lineNodes, extendedLineGaps, lineGaps, fourthNode,
    coeffs, Fin.sum_univ_succ]
  dsimp
  compute_degree <;> simp [completeDirection, fourthNode]


/-- Polynomial form of the fixed-dividend identity. Keeping the polynomials
abstract allows algebra instances to be reconciled before a large substitution. -/
def resultantNormRelation {K : Type*} [CommRing K] (A a : K) (R N : K[X]) : Prop :=
  C A * R = C a * N ^ 4

lemma resultantNormRelation_complex {A a : ℂ} {R N : ℂ[X]}
    (h : C A * R = C a * N ^ 4) : resultantNormRelation A a R N := h

/-- Degree ten and a fourth power force degree at most two for the norm. -/
lemma affineNorm_degree_le_two {K : Type*} [CommRing K] [IsDomain K] {A a : K}
    (hA : A ≠ 0) (ha : a ≠ 0) (ρ u v ρ' u' v' : K) (x z : Fin 3 → K)
    (he : resultantNormRelation A a (affineResultant ρ u v ρ' u' v' x z)
      (affineNorm ρ u v ρ' u' v' x z)) :
    (affineNorm ρ u v ρ' u' v' x z).natDegree ≤ 2 := by
  have hR := line_resultant_natDegree_le_ten
    (fun j : Fin 4 => coeffs ρ u v j.castSucc)
    (fun j : Fin 4 => coeffs ρ' u' v' j.castSucc)
    (completeNodes ρ u v x) (completeNodes ρ u v z)
  change (affineResultant ρ u v ρ' u' v' x z).natDegree ≤ 10 at hR
  have h := congrArg Polynomial.natDegree he
  rw [natDegree_C_mul hA, natDegree_C_mul ha, natDegree_pow] at h
  omega

/-- The same equation then lowers the resultant degree from ten to eight. -/
lemma affineResultant_degree_le_eight {K : Type*} [CommRing K] [IsDomain K] {A a : K}
    (hA : A ≠ 0) (ha : a ≠ 0) (ρ u v ρ' u' v' : K) (x z : Fin 3 → K)
    (he : resultantNormRelation A a (affineResultant ρ u v ρ' u' v' x z)
      (affineNorm ρ u v ρ' u' v' x z)) :
    (affineResultant ρ u v ρ' u' v' x z).natDegree ≤ 8 := by
  have hd := affineNorm_degree_le_two hA ha ρ u v ρ' u' v' x z he
  have h := congrArg Polynomial.natDegree he
  rw [natDegree_C_mul hA, natDegree_C_mul ha, natDegree_pow] at h
  omega

/-- Transport the leading coefficient through the polynomial identity first,
so kernel conversion does not expand the resultant under `Polynomial.coeff`. -/
lemma affineResultant_coeff_ten {K : Type*} [CommRing K] [Nontrivial K]
    (ρ u v ρ' u' v' : K) (x z : Fin 3 → K) :
    (affineResultant ρ u v ρ' u' v' x z).coeff 10 =
      coeffs ρ u v (0 : Fin 4).castSucc * coeffs ρ u v (1 : Fin 4).castSucc *
      coeffs ρ u v (2 : Fin 4).castSucc * coeffs ρ u v (3 : Fin 4).castSucc *
      nodeVandermonde (completeNodes ρ u v z) := by
  have he : affineResultant ρ u v ρ' u' v' x z =
      resultant
        (firstNewtonQuartic (C ∘ fun j : Fin 4 => coeffs ρ u v j.castSucc)
          (affineNodes (completeNodes ρ u v x) (completeNodes ρ u v z)))
        (X * nextNewtonQuartic (C ∘ fun j : Fin 4 => coeffs ρ' u' v' j.castSucc)
          (affineNodes (completeNodes ρ u v x) (completeNodes ρ u v z))) 4 5 := rfl
  exact (congrArg (fun p : K[X] => p.coeff 10) he).trans
    (line_resultant_coeff_ten
      (fun j : Fin 4 => coeffs ρ u v j.castSucc)
      (fun j : Fin 4 => coeffs ρ' u' v' j.castSucc)
      (completeNodes ρ u v x) (completeNodes ρ u v z))

/-- A factored coefficient above the degree has zero second factor if the first
factor is nonzero. Keeping the polynomial abstract avoids expanding it. -/
lemma high_coefficient_factor_eq_zero {K : Type*} [CommRing K] [IsDomain K]
    (p : K[X]) (c v : K) (n : ℕ) (hd : p.natDegree < n) (hc : c ≠ 0)
    (ht : p.coeff n = c * v) : v = 0 := by
  have hz : p.coeff n = 0 := coeff_eq_zero_of_natDegree_lt hd
  exact (mul_eq_zero.mp (ht.symm.trans hz)).resolve_left hc

/-- The top resultant coefficient vanishes for every contained line. -/
lemma affineResultant_vandermonde_zero {K : Type*} [CommRing K] [IsDomain K] {A a : K}
    (hA : A ≠ 0) (ha : a ≠ 0) (ρ u v ρ' u' v' : K) (x z : Fin 3 → K)
    (hc : ∀ j : Fin 4, coeffs ρ u v j.castSucc ≠ 0)
    (he : resultantNormRelation A a (affineResultant ρ u v ρ' u' v' x z)
      (affineNorm ρ u v ρ' u' v' x z)) :
    nodeVandermonde (completeNodes ρ u v z) = 0 := by
  have hd := affineResultant_degree_le_eight hA ha ρ u v ρ' u' v' x z he
  exact high_coefficient_factor_eq_zero _ _ _ 10 (by omega)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (hc 0) (hc 1)) (hc 2)) (hc 3))
    (affineResultant_coeff_ten ρ u v ρ' u' v' x z)


/-- Every nonconstant complex affine line contained in both defining equations has
one of the four exceptional directions, with the corresponding coefficient relation. -/
theorem contained_complex_line_direction {A a : ℂ} {ρ u v : ℝ}
    (hA : A ≠ 0) (ha : a ≠ 0) (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (ρ' u' v' : ℂ) (x z : Fin 3 → ℂ) (hz : ∃ j, z j ≠ 0)
    (hq : affineQuadratic (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v' x z = 0)
    (he : C A * affineResultant (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v' x z =
      C a * affineNorm (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v' x z ^ 4) :
    ∃ d : Fin 4, ∃ t : ℂ, t ≠ 0 ∧
      (∀ j, completeDirection (ρ : ℂ) (u : ℂ) (v : ℂ) z j = t * normalizedDirection d j) ∧
      exceptionalRelation ρ u v d := by
  have he' := resultantNormRelation_complex he
  have hn := affineNorm_degree_le_two hA ha (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v' x z he'
  have hm3 := coeff_eq_zero_of_natDegree_lt (show
    (affineNorm (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v' x z).natDegree < 3 by omega)
  rw [affineNorm_coeff_three] at hm3
  have hm2 := congrArg (fun p : ℂ[X] => p.coeff 2) hq
  rw [affineQuadratic_coeff_two, coeff_zero] at hm2
  have hc : ∀ j : Fin 4, coeffs (ρ : ℂ) (u : ℂ) (v : ℂ) j.castSucc ≠ 0 := by
    intro j
    rw [coeffs_ofReal]
    have hr : coeffs ρ u v j.castSucc ≠ 0 := by
      fin_cases j <;> simp [coeffs] <;> linarith
    exact_mod_cast hr
  have hV := affineResultant_vandermonde_zero hA ha
    (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v' x z hc he'
  apply complex_direction_of_leading_equations hρ hu hv
    (completeDirection (ρ : ℂ) (u : ℂ) (v : ℂ) z)
  · obtain ⟨j, hj⟩ := hz
    fin_cases j
    · exact ⟨1, 0, by simpa [completeDirection] using hj⟩
    · exact ⟨2, 0, by simpa [completeDirection] using hj⟩
    · exact ⟨3, 0, by simpa [completeDirection] using hj⟩
  · rfl
  · simpa [nodeVandermonde, completeDirection, completeNodes] using hV
  · intro m hm
    interval_cases m
    · exact completeDirection_moment_zero _ _ _ _
    · exact completeDirection_moment_one _ _ _ _
    · exact hm2
    · exact hm3

end
end PierceLengthBound.FixedDividend
