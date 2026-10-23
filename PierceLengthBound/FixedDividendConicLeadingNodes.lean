/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendPolynomialSubstitution
public import PierceLengthBound.IntegralLiftParabola
public import PierceLengthBound.FixedDividendLeadingComponents
public import PierceLengthBound.ConicRawDeterminant
public import PierceLengthBound.FixedDividendComponents

/-! Distinct leading nodes and exact raw determinant degrees for quadratic
parametrizations of nonexceptional fixed-dividend components. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

/-- Along a parametrization of degree at most two, the quadratic and fixed-dividend
equations force the leading quadratic and cubic to vanish at the leading coefficients. -/
theorem quadratic_parameter_leading_equations {K : Type*} [Field K]
    (ρ u v ρ' u' v' A a : K) (ha : a ≠ 0)
    (z : Fin 3 → Polynomial K) (hz : ∀ j, (z j).natDegree ≤ 2)
    (hq : MvPolynomial.aeval z (curveQuadratic ρ u v ρ' u' v') = 0)
    (hg : MvPolynomial.aeval z (curveEquation ρ u v ρ' u' v' A a) = 0) :
    MvPolynomial.eval (fun j => (z j).coeff 2)
      (leadingQuadratic (-ρ - u) (u - v) (v - 1)) = 0 ∧
    MvPolynomial.eval (fun j => (z j).coeff 2)
      (leadingCubic (-ρ - u) (u - v) (v - 1)) = 0 := by
  have h1 := polynomial_substitution_top_coefficient z (by decide : 0 < 2) hz
    (curveQuadratic ρ u v ρ' u' v') (curveQuadratic_degree_le_two ..)
  rw [hq, coeff_zero, curveQuadratic_top_component] at h1
  have h2 := polynomial_substitution_top_coefficient z (by decide : 0 < 2) hz
    (curveEquation ρ u v ρ' u' v' A a) (curveEquation_degree_le ..)
  rw [hg, coeff_zero, curveEquation_top_component] at h2
  simp only [map_mul, map_neg, map_pow, MvPolynomial.eval_C] at h2
  refine ⟨h1.symm, ?_⟩
  have hh := (mul_eq_zero.mp h2.symm).resolve_left (neg_ne_zero.mpr ha)
  exact (pow_eq_zero_iff (by decide : 4 ≠ 0)).mp hh

/-- For a nonexceptional pattern, the leading nodes of a quadratic parametrization
are distinct. -/
theorem rational_quadratic_parameter_leading_nodes
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ)
    (ha : a ≠ 0) (z : Fin 3 → Polynomial ℚ) (hz : ∀ j, (z j).natDegree ≤ 2)
    (hfirst : (z 0).coeff 2 ≠ 0)
    (hq : MvPolynomial.aeval z (curveQuadratic ρ u v ρ' u' v') = 0)
    (hg : MvPolynomial.aeval z (curveEquation ρ u v ρ' u' v' A a) = 0) :
    Function.Injective (completeDirection ρ u v (fun j => (z j).coeff 2)) := by
  obtain ⟨hquad, hcubic⟩ := quadratic_parameter_leading_equations ρ u v ρ' u' v' A a ha z hz hq hg
  apply leading_nodes_injective_of_pair_sums_ne_zero (coeffs ρ u v)
  · intro j
    fin_cases j <;> norm_num [coeffs] <;> linarith
  · have hpair := (nonexceptional_iff_pair_sums_ne_zero
      (by exact_mod_cast hρ) (by exact_mod_cast hu) (by exact_mod_cast hv)).mp hne
    have hcast (j : Fin 5) : ((coeffs ρ u v j : ℚ) : ℝ) =
        coeffs (ρ : ℝ) (u : ℝ) (v : ℝ) j := by
      fin_cases j <;> simp [coeffs]
    intro j l hjl he
    apply hpair j l hjl
    rw [← hcast j, ← hcast l]
    exact_mod_cast he
  · exact completeDirection_not_constant ρ u v _ ⟨0, hfirst⟩
  · intro m hm
    interval_cases m
    · exact completeDirection_moment_zero _ _ _ _
    · exact completeDirection_moment_one _ _ _ _
    · simpa only [eval_leadingQuadratic_moment] using hquad
    · simpa only [eval_leadingCubic_moment] using hcubic

/-- The eliminated gaps of a quadratic parametrization have degree at most two. -/
lemma parameter_lineGaps_degree {K : Type*} [Field K]
    (ρ u v ρ' u' v' : K) (z : Fin 3 → Polynomial K)
    (hz : ∀ j, (z j).natDegree ≤ 2) :
    ∀ j, (lineGaps (C ρ) (C u) (C v) (C ρ') (C u') (C v') (z 0) (z 1) (z 2) j).natDegree ≤ 2 := by
  have h0 := hz 0
  have h1 := hz 1
  have h2 := hz 2
  intro j
  fin_cases j <;> dsimp [lineGaps, fourthNode] <;> compute_degree <;> omega

/-- Distinct leading nodes give degrees exactly six and twelve for the raw
three-gap determinant and `μH₄`, and degree at most eight for the mixed determinant. -/
theorem quadratic_parameter_raw_degrees
    {ρ u v : ℚ} (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0)
    (hne : NonexceptionalPattern (ρ : ℝ) (u : ℝ) (v : ℝ)) (ρ' u' v' A a : ℚ)
    (ha : a ≠ 0) (z : Fin 3 → Polynomial ℚ) (hz : ∀ j, (z j).natDegree ≤ 2)
    (hfirst : (z 0).coeff 2 ≠ 0)
    (hq : MvPolynomial.aeval z (curveQuadratic ρ u v ρ' u' v') = 0)
    (hg : MvPolynomial.aeval z (curveEquation ρ u v ρ' u' v' A a) = 0) :
    let k := lineGaps (C ρ) (C u) (C v) (C ρ') (C u') (C v') (z 0) (z 1) (z 2)
    (rawHankelThree (k 0) (k 1) (k 2)).natDegree = 6 ∧
      (muH4 (k 0) (k 1) (k 2) (k 3) (k 4)).natDegree = 12 ∧
      (rawHankelMixed (k 0) (k 1) (k 2) (k 3)).natDegree ≤ 8 := by
  let k := lineGaps (C ρ) (C u) (C v) (C ρ') (C u') (C v') (z 0) (z 1) (z 2)
  have hk : ∀ j, (k j).natDegree ≤ 2 := parameter_lineGaps_degree ρ u v ρ' u' v' z hz
  have hinj := rational_quadratic_parameter_leading_nodes hρ hu hv hne
    ρ' u' v' A a ha z hz hfirst hq hg
  have hneq (j l : Fin 5) (hjl : j ≠ l) :
      completeDirection ρ u v (fun j => (z j).coeff 2) j ≠
      completeDirection ρ u v (fun j => (z j).coeff 2) l := fun h => hjl (hinj h)
  have hb : (z 1).coeff 2 ≠ 0 := hneq 2 0 (by decide)
  have hc : (z 2).coeff 2 ≠ 0 := hneq 3 0 (by decide)
  have hba : (z 1).coeff 2 - (z 0).coeff 2 ≠ 0 :=
    sub_ne_zero.mpr (hneq 2 1 (by decide))
  have hcb : (z 2).coeff 2 - (z 1).coeff 2 ≠ 0 :=
    sub_ne_zero.mpr (hneq 3 2 (by decide))
  have hca : (z 2).coeff 2 - (z 0).coeff 2 ≠ 0 :=
    sub_ne_zero.mpr (hneq 3 1 (by decide))
  have hk0 : (k 0).natDegree = 2 := natDegree_eq_of_le_of_coeff_ne_zero (hk 0) hfirst
  have hk1 : (k 1).natDegree = 2 := natDegree_eq_of_le_of_coeff_ne_zero (hk 1)
    (by simpa only [k, lineGaps, Matrix.cons_val_one, Matrix.cons_val_zero,
      coeff_sub] using hba)
  have hks : (k 0 + k 1).natDegree = 2 := by
    have he : k 0 + k 1 = z 1 := by dsimp [k, lineGaps]; ring
    rw [he]
    exact natDegree_eq_of_le_of_coeff_ne_zero (hz 1) hb
  refine ⟨rawHankelThree_parabola_degree _ _ _ hk0 hk1 (hk 2) hks,
    muH4_quadratic_degree_eq k hk ?_, rawHankelMixed_parabola_degree _ _ _ _
      (hk 0) (hk 1) (hk 2) (hk 3)⟩
  have hh := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero hfirst hba) hcb) hb) hca) hc
  convert hh using 1
  simp only [k, lineGaps, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, coeff_sub]
  ring

end
end PierceLengthBound.FixedDividend
