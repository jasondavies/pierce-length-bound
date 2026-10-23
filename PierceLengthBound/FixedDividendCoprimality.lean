/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.FixedDividendCubicGeometry
public import PierceLengthBound.FixedDividendComplexLines

/-!
# No common quadratic surface component

Universal radial substitution converts multivariate divisibility to a coefficient
identity in one variable. Its degree-twelve term would force the irreducible
leading quadratic to divide the leading cubic, which is impossible.
-/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial

/-- A prime quadratic leading coefficient incompatible with the cubic leading
coefficient prevents divisibility of the fixed-dividend polynomial. -/
theorem not_dvd_fixed_dividend_of_leading {S : Type*} [CommRing S] [IsDomain S]
    {f D R : S[X]} {F G A a : S} (hF : Prime F) (hFG : ¬ F ∣ G) (ha : IsUnit a)
    (hf : f.natDegree ≤ 2) (hf2 : f.coeff 2 = F)
    (hD : D.natDegree ≤ 3) (hD3 : D.coeff 3 = G) (hR : R.natDegree ≤ 10) :
    ¬ f ∣ C A * R - C a * D ^ 4 := by
  have hf0 : f ≠ 0 := by intro h; apply hF.ne_zero; simpa [h] using hf2.symm
  have hfd : f.natDegree = 2 := by
    have hcoeff : f.coeff 2 ≠ 0 := hf2.trans_ne hF.ne_zero
    have := le_natDegree_of_ne_zero hcoeff
    omega
  have hdeg : (C A * R - C a * D ^ 4).natDegree ≤ 12 := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · calc
        (C A * R).natDegree ≤ 0 + 10 := natDegree_mul_le.trans (add_le_add (by simp) hR)
        _ ≤ 12 := by norm_num
    · calc
        (C a * D ^ 4).natDegree ≤ 0 + 4 * 3 :=
          natDegree_mul_le.trans (add_le_add (by simp)
            (natDegree_pow_le.trans (Nat.mul_le_mul_left 4 hD)))
        _ = 12 := by norm_num
  have htop : (C A * R - C a * D ^ 4).coeff 12 = -a * G ^ 4 := by
    rw [coeff_sub, coeff_C_mul, coeff_C_mul,
      coeff_eq_zero_of_natDegree_lt (show R.natDegree < 12 by omega)]
    have hp := coeff_pow_of_natDegree_le (m := 4) hD
    norm_num only at hp
    rw [hp, hD3]
    ring
  rintro ⟨q, he⟩
  have hq : q.natDegree ≤ 10 := by
    by_cases hq0 : q = 0
    · simp [hq0]
    rw [he, natDegree_mul hf0 hq0, hfd] at hdeg
    omega
  have hc := congrArg (fun p : S[X] => p.coeff 12) he
  rw [htop, show 12 = 2 + 10 by decide,
    coeff_mul_add_eq_of_natDegree_le hf hq, hf2] at hc
  have hdvd : F ∣ -a * G ^ 4 := ⟨q.coeff 10, hc⟩
  exact hFG (hF.dvd_of_dvd_pow ((ha.neg.dvd_mul_left).mp hdvd))

/-- Replace every coordinate by itself times a universal scalar parameter. -/
def radialMap {K : Type*} [CommRing K] :
    MvPolynomial (Fin 3) K →+* Polynomial (MvPolynomial (Fin 3) K) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun j => Polynomial.C (MvPolynomial.X j) * Polynomial.X)

@[simp] lemma radialMap_C {K : Type*} [CommRing K] (c : K) :
    radialMap (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by
  simp [radialMap]

@[simp] lemma radialMap_X {K : Type*} [CommRing K] (j : Fin 3) :
    radialMap (MvPolynomial.X j : MvPolynomial (Fin 3) K) =
      Polynomial.C (MvPolynomial.X j) * Polynomial.X := by simp [radialMap]


/-- The first eliminated equation in its three free coordinates. -/
def curveQuadratic {K : Type*} [CommRing K] (ρ u v ρ' u' v' : K) : MvPolynomial (Fin 3) K :=
  lineQuadratic (MvPolynomial.C ρ) (MvPolynomial.C u) (MvPolynomial.C v)
    (MvPolynomial.C ρ') (MvPolynomial.C u') (MvPolynomial.C v')
    (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)

/-- The eliminated norm in the same coordinate ring. -/
def curveNorm {K : Type*} [CommRing K] (ρ u v ρ' u' v' : K) : MvPolynomial (Fin 3) K :=
  lineNorm (MvPolynomial.C ρ) (MvPolynomial.C u) (MvPolynomial.C v)
    (MvPolynomial.C ρ') (MvPolynomial.C u') (MvPolynomial.C v')
    (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)

/-- The fixed-dividend resultant in the same coordinate ring. -/
def curveResultant {K : Type*} [CommRing K] (ρ u v ρ' u' v' : K) : MvPolynomial (Fin 3) K :=
  let s := completeNodes (MvPolynomial.C ρ) (MvPolynomial.C u) (MvPolynomial.C v)
    (fun j => MvPolynomial.X j)
  resultant
    (firstNewtonQuartic (fun j : Fin 4 => MvPolynomial.C (coeffs ρ u v j.castSucc)) s)
    (Polynomial.X * nextNewtonQuartic
      (fun j : Fin 4 => MvPolynomial.C (coeffs ρ' u' v' j.castSucc)) s) 4 5

lemma radialMap_quadratic {K : Type*} [CommRing K] (ρ u v ρ' u' v' : K) :
    radialMap (curveQuadratic ρ u v ρ' u' v') =
      affineQuadratic (MvPolynomial.C ρ) (MvPolynomial.C u) (MvPolynomial.C v)
        (MvPolynomial.C ρ') (MvPolynomial.C u') (MvPolynomial.C v') 0 MvPolynomial.X := by
  simp [curveQuadratic, map_lineQuadratic, affineQuadratic]

lemma radialMap_norm {K : Type*} [CommRing K] (ρ u v ρ' u' v' : K) :
    radialMap (curveNorm ρ u v ρ' u' v') =
      affineNorm (MvPolynomial.C ρ) (MvPolynomial.C u) (MvPolynomial.C v)
        (MvPolynomial.C ρ') (MvPolynomial.C u') (MvPolynomial.C v') 0 MvPolynomial.X := by
  simp [curveNorm, map_lineNorm, affineNorm]

lemma radialMap_quadratic_coeff {K : Type*} [CommRing K] (ρ u v ρ' u' v' : K) :
    (radialMap (curveQuadratic ρ u v ρ' u' v')).coeff 2 =
      leadingQuadratic (-ρ - u) (u - v) (v - 1) := by
  rw [radialMap_quadratic, affineQuadratic_coeff_two]
  simp [leadingQuadratic, ternaryQuadratic, coeffs, completeDirection, fourthNode,
    Fin.sum_univ_succ]
  ring

lemma radialMap_norm_coeff {K : Type*} [CommRing K] (ρ u v ρ' u' v' : K) :
    (radialMap (curveNorm ρ u v ρ' u' v')).coeff 3 =
      leadingCubic (-ρ - u) (u - v) (v - 1) := by
  rw [radialMap_norm, affineNorm_coeff_three]
  simp [leadingCubic, coeffs, completeDirection, fourthNode, Fin.sum_univ_succ]
  ring

lemma radialMap_quadratic_degree {K : Type*} [CommRing K] (ρ u v ρ' u' v' : K) :
    (radialMap (curveQuadratic ρ u v ρ' u' v')).natDegree ≤ 2 := by
  rw [radialMap_quadratic]
  simp only [affineQuadratic, lineQuadratic, coeffs, lineNodes, Pi.zero_apply, map_zero,
    Fin.isValue, zero_add, fourthNode, lineGaps, Matrix.cons_val, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Fin.castSucc_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Matrix.cons_val_succ, Fin.castSucc_succ, Nat.reduceAdd, Finset.univ_unique,
    Fin.default_eq_zero, Matrix.cons_val_fin_one, one_mul, Finset.sum_singleton]
  compute_degree

-- Check the degree after both gap eliminations in the complete norm formula.
lemma radialMap_norm_degree {K : Type*} [CommRing K] (ρ u v ρ' u' v' : K) :
    (radialMap (curveNorm ρ u v ρ' u' v')).natDegree ≤ 3 := by
  rw [radialMap_norm]
  simp only [affineNorm, lineNorm, coeffs, lineNodes, Pi.zero_apply, map_zero, Fin.isValue,
    zero_add, fourthNode, lineGaps, Matrix.cons_val, extendedLineGaps, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_succ, Fin.sum_univ_succ, Fin.castSucc_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero, zero_mul,
    Fin.castSucc_succ, Nat.reduceAdd, Finset.univ_unique, Fin.default_eq_zero,
    Matrix.cons_val_fin_one, one_mul, Finset.sum_singleton]
  compute_degree


lemma radialMap_resultant {K : Type*} [CommRing K] (ρ u v ρ' u' v' : K) :
    radialMap (curveResultant ρ u v ρ' u' v') =
      affineResultant (MvPolynomial.C ρ) (MvPolynomial.C u) (MvPolynomial.C v)
        (MvPolynomial.C ρ') (MvPolynomial.C u') (MvPolynomial.C v') 0 MvPolynomial.X := by
  have hn : radialMap ∘ completeNodes (MvPolynomial.C ρ) (MvPolynomial.C u)
      (MvPolynomial.C v) MvPolynomial.X =
      affineNodes (completeNodes (MvPolynomial.C ρ) (MvPolynomial.C u) (MvPolynomial.C v) 0)
        (completeNodes (MvPolynomial.C ρ) (MvPolynomial.C u) (MvPolynomial.C v)
          MvPolynomial.X) := by
    funext j
    fin_cases j <;> simp [completeNodes, fourthNode, affineNodes]
    ring
  have hc (ρ u v : K) :
      radialMap ∘ (fun j : Fin 4 => MvPolynomial.C (coeffs ρ u v j.castSucc)) =
        (fun j : Fin 4 => Polynomial.C
          (coeffs (MvPolynomial.C ρ) (MvPolynomial.C u) (MvPolynomial.C v) j.castSucc)) := by
    funext j
    fin_cases j <;> simp [coeffs]
  unfold curveResultant affineResultant
  rw [← resultant_map_map, Polynomial.map_mul, Polynomial.map_X,
    map_firstNewtonQuartic, map_nextNewtonQuartic, hn, hc, hc]

lemma radialMap_resultant_degree {K : Type*} [CommRing K] [Nontrivial K]
    (ρ u v ρ' u' v' : K) :
    (radialMap (curveResultant ρ u v ρ' u' v')).natDegree ≤ 10 := by
  rw [radialMap_resultant]
  exact line_resultant_natDegree_le_ten _ _ _ _

/-- The actual quadratic cannot divide the fixed-dividend equation over the complex numbers. -/
theorem curveQuadratic_not_dvd_fixed_dividend {ρ u v : ℝ}
    (hρ : 0 < ρ) (hu : 0 < u) (hv : v < 0) (ρ' u' v' A a : ℂ) (ha : a ≠ 0) :
    ¬ curveQuadratic (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v' ∣
      MvPolynomial.C A * curveResultant (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v' -
      MvPolynomial.C a * curveNorm (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v' ^ 4 := by
  have hq : Irreducible (leadingQuadratic (-(ρ : ℂ) - u) ((u : ℂ) - v) ((v : ℂ) - 1)) := by
    apply irreducible_of_hessian_det_ne_zero
      (ternaryQuadratic_degree_le _ _ _ _ _ _)
    rw [ternaryQuadratic_hessian_det]
    have hdet : (8 : ℂ) * (-(ρ : ℂ) - u) * ((u : ℂ) - v) * ((v : ℂ) - 1) *
        (1 + (-(ρ : ℂ) - u) + ((u : ℂ) - v) + ((v : ℂ) - 1)) ≠ 0 := by
      have h1 : -(ρ : ℂ) - u ≠ 0 := by exact_mod_cast (show -ρ - u ≠ 0 by linarith)
      have h2 : (u : ℂ) - v ≠ 0 := by exact_mod_cast (show u - v ≠ 0 by linarith)
      have h3 : (v : ℂ) - 1 ≠ 0 := by exact_mod_cast (show v - 1 ≠ 0 by linarith)
      have h4 : 1 + (-(ρ : ℂ) - u) + ((u : ℂ) - v) + ((v : ℂ) - 1) = -(ρ : ℂ) := by ring
      rw [h4]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h1) h2) h3)
        (neg_ne_zero.mpr (by exact_mod_cast ne_of_gt hρ))
    exact hdet
  have hcoprime := not_dvd_fixed_dividend_of_leading hq.prime
    (pattern_leadingQuadratic_not_dvd_cubic hρ hu hv)
    ((isUnit_iff_ne_zero.mpr ha).map MvPolynomial.C)
    (radialMap_quadratic_degree (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v')
    (radialMap_quadratic_coeff (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v')
    (radialMap_norm_degree (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v')
    (radialMap_norm_coeff (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v')
    (radialMap_resultant_degree (ρ : ℂ) (u : ℂ) (v : ℂ) ρ' u' v') (A := MvPolynomial.C A)
  rintro ⟨q, he⟩
  apply hcoprime
  refine ⟨radialMap q, ?_⟩
  have hm := congrArg radialMap he
  simpa only [map_sub, map_mul, map_pow, radialMap_C] using hm

end
end PierceLengthBound.FixedDividend
