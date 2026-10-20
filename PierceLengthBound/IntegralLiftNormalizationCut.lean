/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import PierceLengthBound.IntegralLiftQuotientNormalization
public import PierceLengthBound.FixedDividendConicLeadingNodes

/-! A bounded-degree normalization cut, proved to vanish at actual orbit states. -/

@[expose] public section
namespace PierceLengthBound.FixedDividend
noncomputable section
open Polynomial
set_option maxHeartbeats 1000000

def orbitParameterGaps (a b i : ℕ) (z : Fin 3 → Polynomial ℚ) : Fin 5 → Polynomial ℚ :=
  lineGaps (C (patternRhoQ a b i)) (C (patternUQ a b i)) (C (patternVQ a b i))
    (C (patternRhoQ a b (i + 1))) (C (patternUQ a b (i + 1)))
    (C (patternVQ a b (i + 1))) (z 0) (z 1) (z 2)

def orbitNormalizationCut (a b i : ℕ) (z : Fin 3 → Polynomial ℚ) : Polynomial ℚ :=
  let n := MvPolynomial.aeval z (orbitQuotientNumeratorQ a b i)
  let d := MvPolynomial.aeval z (orbitQuotientDenominatorQ a b i)
  let k := orbitParameterGaps a b i z
  C (Lz a b i : ℚ) * clearedNewtonQuartic
    (fun j : Fin 4 => C (coeffs (patternRhoQ a b i) (patternUQ a b i)
      (patternVQ a b i) j.castSucc)) z n d -
    C (a : ℚ) * muH4 (k 0) (k 1) (k 2) (k 3) (k 4) * d ^ 4

lemma clearedNewtonQuartic_degree {K : Type*} [Field K]
    (c : Fin 4 → K) (z : Fin 3 → Polynomial K)
    (hz : ∀ j, (z j).natDegree ≤ 2) (n d : Polynomial K)
    (hn : n.natDegree ≤ 80) (hd : d.natDegree ≤ 80) :
    (clearedNewtonQuartic (fun j => C (c j)) z n d).natDegree ≤ 326 := by
  have h0 := hz 0
  have h1 := hz 1
  have h2 := hz 2
  unfold clearedNewtonQuartic
  compute_degree
  omega

/-- The normalization cut has an absolute parameter degree bound. -/
theorem orbitNormalizationCut_degree (a b i : ℕ) (z : Fin 3 → Polynomial ℚ)
    (hz : ∀ j, (z j).natDegree ≤ 2) : (orbitNormalizationCut a b i z).natDegree ≤ 332 := by
  have hn := (polynomial_substitution_degree z hz (orbitQuotientNumeratorQ a b i)).trans
    (Nat.mul_le_mul_left 2 (orbitQuotient_polynomial_degrees a b i).1)
  have hd := (polynomial_substitution_degree z hz (orbitQuotientDenominatorQ a b i)).trans
    (Nat.mul_le_mul_left 2 (orbitQuotient_polynomial_degrees a b i).2)
  have hp := clearedNewtonQuartic_degree
    (fun j : Fin 4 => coeffs (patternRhoQ a b i) (patternUQ a b i)
      (patternVQ a b i) j.castSucc) z hz _ _ hn hd
  have hk := parameter_lineGaps_degree (patternRhoQ a b i) (patternUQ a b i)
    (patternVQ a b i) (patternRhoQ a b (i + 1)) (patternUQ a b (i + 1))
    (patternVQ a b (i + 1)) z hz
  have hm := muH4_quadratic_degree_le (orbitParameterGaps a b i z) hk
  unfold orbitNormalizationCut
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact (natDegree_C_mul_le _ _).trans (hp.trans (by omega))
  · apply natDegree_mul_le.trans
    have hleft := (natDegree_C_mul_le (a : ℚ) _).trans hm
    have hright := natDegree_pow_le_of_le 4 hd
    omega

lemma orbitParameterGaps_eval {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (z : Fin 3 → Polynomial ℚ) (t : ℚ)
    (hz : ∀ j, (z j).eval t = orbitFreeNodesQ a b i j) (j : Fin 5) :
    (orbitParameterGaps a b i z j).eval t = (kq a b (i + j.val) : ℚ) := by
  unfold orbitParameterGaps
  rw [show Polynomial.eval t = Polynomial.evalRingHom t from rfl, map_lineGaps]
  simp only [coe_evalRingHom, eval_C, hz]
  exact orbit_rational_lineGaps (i := i) hba (by omega) j

/-- This polynomial cut genuinely vanishes at every supported orbit state
represented by the parameter. -/
theorem orbitNormalizationCut_eval {a b i : ℕ} (hba : b < a) (hi : i + 7 < P a b)
    (z : Fin 3 → Polynomial ℚ) (t : ℚ)
    (hz : ∀ j, (z j).eval t = orbitFreeNodesQ a b i j) :
    (orbitNormalizationCut a b i z).eval t = 0 := by
  have he (f : MvPolynomial (Fin 3) ℚ) :
      (MvPolynomial.aeval z f).eval t = MvPolynomial.eval (orbitFreeNodesQ a b i) f := by
    rw [polynomial_substitution_eval]
    rw [show (fun j => (z j).eval t) = orbitFreeNodesQ a b i from funext hz]
  have hn := orbit_newton_normalization hba hi
  have hq := orbitQuotient_evaluation hba hi
  have hk := orbitParameterGaps_eval hba hi z t hz
  have hm : (muH4 (orbitParameterGaps a b i z 0) (orbitParameterGaps a b i z 1)
      (orbitParameterGaps a b i z 2) (orbitParameterGaps a b i z 3)
      (orbitParameterGaps a b i z 4)).eval t =
      muH4 (kq a b i : ℚ) (kq a b (i + 1) : ℚ) (kq a b (i + 2) : ℚ)
        (kq a b (i + 3) : ℚ) (kq a b (i + 4) : ℚ) := by
    have h := map_muH4 (Polynomial.evalRingHom t) (orbitParameterGaps a b i z 0)
      (orbitParameterGaps a b i z 1) (orbitParameterGaps a b i z 2)
      (orbitParameterGaps a b i z 3) (orbitParameterGaps a b i z 4)
    change (muH4 _ _ _ _ _ : Polynomial ℚ).eval t = muH4 ((orbitParameterGaps a b i z 0).eval t)
      ((orbitParameterGaps a b i z 1).eval t) ((orbitParameterGaps a b i z 2).eval t)
      ((orbitParameterGaps a b i z 3).eval t) ((orbitParameterGaps a b i z 4).eval t) at h
    simpa [hk] using h
  unfold orbitNormalizationCut
  simp only [eval_sub, eval_mul, eval_C, eval_pow, clearedNewtonQuartic,
    eval_add, he, hz, hm]
  change (Lz a b i : ℚ) * clearedNewtonQuartic
    (fun j : Fin 4 => coeffs (patternRhoQ a b i) (patternUQ a b i)
      (patternVQ a b i) j.castSucc) (orbitFreeNodesQ a b i)
    (MvPolynomial.eval (orbitFreeNodesQ a b i) (orbitQuotientNumeratorQ a b i))
    (MvPolynomial.eval (orbitFreeNodesQ a b i) (orbitQuotientDenominatorQ a b i)) - _ = 0
  rw [clearedNewtonQuartic_div _ _ _ _ hq.1, ← hq.2, ← mul_assoc, hn]
  ring

lemma orbit_pattern_eq_of_theta {a b i l : ℕ} (h : theta a b i = theta a b l) :
    Lz a b i = Lz a b l ∧
    patternRhoQ a b i = patternRhoQ a b l ∧
    patternUQ a b i = patternUQ a b l ∧
    patternVQ a b i = patternVQ a b l ∧
    patternRhoQ a b (i + 1) = patternRhoQ a b (l + 1) ∧
    patternUQ a b (i + 1) = patternUQ a b (l + 1) ∧
    patternVQ a b (i + 1) = patternVQ a b (l + 1) := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  have h6 := congrFun h 6
  simp only [theta, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2 h3 h4 h5 h6
  refine ⟨h0, ?_⟩
  simp only [patternRhoQ, patternUQ, patternVQ, h0, h1, h2, h3, h4, h5, h6,
    Nat.add_assoc, Nat.reduceAdd, and_self]

lemma orbitNormalizationCut_congr {a b i l : ℕ} (h : theta a b i = theta a b l)
    (z : Fin 3 → Polynomial ℚ) : orbitNormalizationCut a b i z = orbitNormalizationCut a b l z := by
  obtain ⟨h0, hρ, hu, hv, hρ', hu', hv'⟩ := orbit_pattern_eq_of_theta h
  simp only [orbitNormalizationCut, orbitQuotientNumeratorQ, orbitQuotientDenominatorQ,
    orbitCurveCofactorsQ, orbitParameterGaps, h0, hρ, hu, hv, hρ', hu', hv']

/-- More than 332 distinct parameter values of actual states sharing a minor
pattern force the full normalization identity. No identity on arbitrary
component points is assumed. -/
theorem orbitNormalizationCut_zero_of_many_states {a b i : ℕ} (hba : b < a)
    (z : Fin 3 → Polynomial ℚ) (hz : ∀ j, (z j).natDegree ≤ 2)
    {ι : Type*} [Fintype ι] (l : ι → ℕ) (t : ι → ℚ) (ht : Function.Injective t)
    (hi : ∀ j, l j + 7 < P a b) (hθ : ∀ j, theta a b i = theta a b (l j))
    (hp : ∀ j k, (z k).eval (t j) = orbitFreeNodesQ a b (l j) k)
    (hcard : 332 < Fintype.card ι) : orbitNormalizationCut a b i z = 0 := by
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ ht
  · intro j
    rw [orbitNormalizationCut_congr (hθ j)]
    exact orbitNormalizationCut_eval hba (hi j) z (t j) (hp j)
  · exact (orbitNormalizationCut_degree a b i z hz).trans_lt hcard

end
end PierceLengthBound.FixedDividend
